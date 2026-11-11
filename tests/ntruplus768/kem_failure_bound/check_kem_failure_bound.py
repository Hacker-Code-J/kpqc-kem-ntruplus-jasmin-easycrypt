#!/usr/bin/env python3
"""Pin the proof/import closure and independently check the experiment boundary."""
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
TEST = Path(__file__).resolve().parent
ROOT = TEST.parents[2]
PROOF = ROOT / 'ntruplus/proof/768/ref/kem_failure_bound'
SCRIPT = ROOT / 'scripts/verify-ntruplus768-kem-failure-bound.sh'
SHARED_POLICY = TEST.parent / 'poly_frombytes_checked/check_poly_frombytes_checked.py'
sys.path.insert(0, str(SHARED_POLICY.parent))
from check_poly_frombytes_checked import require, sha, without_comments, check_proof_text

MAINS = ('NTRUPlus768KEMFailureModel.ec', 'NTRUPlus768KEMFailureSpec.ec', 'NTRUPlus768KEMFailureProof.ec',
         'NTRUPlus768KEMFailureIID.ec')
RNG_MODEL = 'ntruplus/proof/768/ref/encap_complete/NTRUPlus768EncapCompleteRNG.ec'
KEYGEN_MODEL = 'ntruplus/proof/768/ref/keygen_complete/NTRUPlus768KeygenCompleteProof.ec'
ENCAP_C = 'ntruplus/c/768/ref/encap_complete.c'


def include_arguments():
    args, directories, seen = [], [], set()
    for raw in (PROOF / 'easycrypt.project').read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith(('#', '[')):
            continue
        key, separator, value = line.partition('=')
        key, value = key.strip(), value.strip()
        require(separator and key in ('rdirs', 'idirs', 'timeout'), 'unsupported project setting')
        if key == 'timeout':
            continue
        namespace, colon, relative = value.partition(':')
        if not colon:
            namespace, relative = '', value
        path = (PROOF / relative).resolve()
        require(path.is_dir() and path.is_relative_to(ROOT), 'include directory outside checkout')
        flag = '-R' if key == 'rdirs' else '-I'
        value = namespace + ':' + str(path) if colon else str(path)
        if (flag, value) not in seen:
            seen.add((flag, value))
            args += [flag, value]
            directories.append(path)
    return args, directories


def source_paths():
    # Conservative closure: every .ec reachable from the explicit include roots.
    # These imports are hash-bound prior proofs, not newly checked replay mains.
    _, directories = include_arguments()
    paths = {SHARED_POLICY}
    for directory in directories:
        paths.update(directory.rglob('*.ec'))
        for name in ('Makefile', 'easycrypt.project'):
            path = directory / name
            if path.is_file():
                paths.add(path)
    for name in ('keygen_complete', 'encap_complete', 'decap_complete'):
        paths.update(ROOT / f'ntruplus/c/768/ref/{name}{suffix}' for suffix in ('.c', '.h'))
    paths.update(PROOF / name for name in (*MAINS, 'Makefile', 'easycrypt.project'))
    require(all(p.is_file() and not p.is_symlink() for p in paths), 'missing or symlink source')
    return paths


def snapshot():
    paths = source_paths() | {SCRIPT}
    paths.update(p for p in TEST.iterdir() if p.is_file() and p.suffix in ('.py', '.json'))
    return {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in sorted(paths)}


def compact(text):
    return re.sub(r'\s+', '', without_comments(text))


def ordered(text, tokens):
    position = 0
    for token in tokens:
        offset = text.find(compact(token), position)
        require(offset >= 0, 'missing or reordered operation: ' + token)
        position = offset + len(compact(token))


def check_structure(sources=None):
    sources = sources or {}
    def read(relative):
        return compact(sources.get(relative, (ROOT / relative).read_text()))
    rng = read(RNG_MODEL).split('moduleEncapRandom(', 1)[1].split('moduleEncapRandomSpec(', 1)[0]
    ordered(rng, ('coins <@ R.sample();',
                  '(ct,ss,status,workspace) <@ EncapDerand(F,G,H).run(pk,coins,workspace);',
                  'coins <@ NTRUPlus768EncapClearCoins.M.jade_ntruplus_ntruplus768_amd64_ref_encap_clear_coins(coins);',
                  'return(ct,ss,status,workspace,coins);'))
    require(rng.count('R.sample()') == 1, 'exactly one actual RNG96 draw')
    keygen = read(KEYGEN_MODEL).split('moduleKeygen(', 1)[1].split('lemmakeygen_instrumented_functional', 1)[0]
    ordered(keygen, ('(w,cleared) <@ KeygenInstrumented(R,E,F).run(witness);',
                     'return(w.`kg_pk,w.`kg_sk);'))
    require('proc run() : W8.t Array1152.t * W8.t Array2336.t'.replace(' ', '') in keygen,
            'public KeyGen must project only pk/sk')
    native = re.sub(r'\s+', '', sources.get(ENCAP_C, (ROOT / ENCAP_C).read_text()))
    native = native.split('intntruplus768_encaps(', 1)[1]
    ordered(native, ('uint8_t coins[96]', 'randombytes(coins, sizeof coins)',
                     'ntruplus768_encaps_derand(ct, ss, pk, coins)',
                     'jade_ntruplus_ntruplus768_amd64_ref_encap_clear_coins(coins)', 'return status'))
    require(native.count('randombytes(') == 1, 'native RNG call count')
    # New-model checks are listed explicitly after the proof model is frozen.
    from model_contract import check_new_model
    check_new_model(read, ordered, require)


def check():
    pins = json.loads((TEST / 'source-pins.json').read_text())
    actual = {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in sorted(source_paths())}
    require(set(actual) == set(pins), 'source/import inventory drift')
    for name, value in actual.items():
        require(value == pins[name], 'source/import pin drift: ' + name)
    require({p.name for p in PROOF.glob('*.ec')} == set(MAINS), 'new proof inventory drift')
    for name in MAINS:
        check_proof_text((PROOF / name).read_text())
    check_structure()
    return actual


if __name__ == '__main__':
    print(json.dumps({'status': 'PASS', 'pinned_sources': len(check())}))
