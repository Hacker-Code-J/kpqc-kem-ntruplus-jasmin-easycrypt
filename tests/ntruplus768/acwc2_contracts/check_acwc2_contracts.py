#!/usr/bin/env python3
"""Hash-bind the conservative import closure and check the ACWC2 RR/SOTP contracts trust boundaries."""
import hashlib
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
TEST = Path(__file__).resolve().parent
ROOT = TEST.parents[2]
BASE = ROOT / 'ntruplus/proof/768/ref'
GROUPS = ('acwc2_contracts',)
SCRIPT = ROOT / 'scripts/verify-ntruplus768-acwc2-contracts.sh'

# Final inventory is reviewed with the proof owners before source pins are made.
MAINS = (
    'acwc2_contracts/NTRUPlus768RRecWordChecks.ec',
    'acwc2_contracts/NTRUPlus768RRecPublicInverse.ec',
    'acwc2_contracts/NTRUPlus768RRecInverseAlgebra.ec',
    'acwc2_contracts/NTRUPlus768RRecModel.ec',
    'acwc2_contracts/NTRUPlus768RRecProcedures.ec',
    'acwc2_contracts/NTRUPlus768RRecCodec.ec',
    'acwc2_contracts/NTRUPlus768RRecAlgebra.ec',
    'acwc2_contracts/NTRUPlus768RRecCallProof.ec',
    'acwc2_contracts/NTRUPlus768SOTPRigidity.ec',
    'acwc2_contracts/NTRUPlus768SOTPContracts.ec',
    'acwc2_contracts/NTRUPlus768ACWC2HashG.ec',
)



def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def without_comments(text):
    depth, parts = 0, []
    for token in re.split(r'(\(\*|\*\))', text):
        if token == '(*':
            depth += 1
            parts.append(' ')
        elif token == '*)':
            require(depth > 0, 'unmatched EasyCrypt comment terminator')
            depth -= 1
        elif not depth:
            parts.append(token)
    require(depth == 0, 'unclosed EasyCrypt comment')
    return ''.join(parts)


def check_proof_text(text):
    code = without_comments(text)
    require(not re.search(r'\b(admit|admitted|abort|assume|axiom|sorry|pragma)\b', code),
            'local proof escape, axiom or checker pragma')
    require(not re.search(r'\baxiomatized\s+by\b', code), 'opaque proof assumption')
    require(not re.search(r'(?m)^\s*print\s+(?:goal|all)\b', code), 'debug proof command')
    for statement in re.split(r'\.(?=\s|$)', code):
        if re.match(r'\s*(?:local\s+)?(?:op|type)\b', statement):
            require('=' in statement, 'abstract project declaration')
            require('{' not in statement.partition('=')[0], 'constrained project declaration')


def compact(text):
    return re.sub(r'\s+', '', without_comments(text))


def ordered(text, tokens):
    position = 0
    for token in tokens:
        token = compact(token)
        offset = text.find(token, position)
        require(offset >= 0, 'missing or reordered operation: ' + token)
        position = offset + len(token)


def include_arguments(group):
    project = BASE / group / 'easycrypt.project'
    args, directories, seen = [], [], set()
    for raw in project.read_text().splitlines():
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
        path = (project.parent / relative).resolve()
        require(path.is_dir() and path.is_relative_to(ROOT), 'include directory outside checkout')
        flag = '-R' if key == 'rdirs' else '-I'
        value = namespace + ':' + str(path) if colon else str(path)
        if (flag, value) not in seen:
            seen.add((flag, value))
            args += [flag, value]
            directories.append(path)
    return args, directories


def source_paths():
    # Imported old and standard project theories are pinned, not replayed as mains.
    paths = set()
    for group in GROUPS:
        _, directories = include_arguments(group)
        for directory in directories:
            paths.update(directory.rglob('*.ec'))
            for name in ('Makefile', 'easycrypt.project'):
                path = directory / name
                if path.is_file():
                    paths.add(path)
        paths.update(BASE / group / name for name in ('Makefile', 'easycrypt.project'))
    paths.update(BASE / name for name in MAINS)
    require(all(p.is_file() and not p.is_symlink() for p in paths), 'missing or symlink source')
    return paths


def snapshot():
    paths = source_paths() | {SCRIPT}
    paths.update(p for p in TEST.iterdir() if p.is_file() and p.suffix in ('.py', '.json'))
    return {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in sorted(paths)}


def check_structure(sources=None):
    sources = sources or {}
    def read(relative):
        return compact(sources.get(relative, (ROOT / relative).read_text()))
    from model_contract import check_model
    check_model(read, ordered, require)


def check():
    require((TEST / 'source-pins.json').is_file(), 'source pins are pending the reviewed proof freeze')
    pins = json.loads((TEST / 'source-pins.json').read_text())
    actual = {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in sorted(source_paths())}
    require(set(actual) == set(pins), 'source/import inventory drift')
    for name, value in actual.items():
        require(value == pins[name], 'source/import pin drift: ' + name)
    inventory = {str(p.relative_to(BASE)) for group in GROUPS for p in (BASE / group).glob('*.ec')}
    require(inventory == set(MAINS), 'new proof inventory drift')
    for name in MAINS:
        check_proof_text((BASE / name).read_text())
    check_structure()
    return actual


if __name__ == '__main__':
    print(json.dumps({'status': 'PASS', 'pinned_sources': len(check()), 'new_mains': len(MAINS)}))
