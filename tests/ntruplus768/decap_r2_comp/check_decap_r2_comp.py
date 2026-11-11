#!/usr/bin/env python3
"""Source, exact official reference, proof policy and whole extraction gates."""
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
import prepare_reference as reference
ROOT, TEST = reference.ROOT, reference.TEST
require, sha = reference.require, reference.sha
sys.path.insert(0, str(TEST.parent / 'poly_frombytes_checked'))
import check_poly_frombytes_checked as checked
check_proof_text = checked.check_proof_text
SOURCE = ROOT / 'ntruplus/jasmin/768/ref/decap_r2.jazz'
SLICE = 'jade_ntruplus_ntruplus768_amd64_ref_decap_r2'
EXTRACTION_FILES = {'Array4.ec', 'Array96.ec', 'Array768.ec', 'WArray8.ec', 'WArray1536.ec',
                    'WArray192.ec', 'NTRUPlus768DecapR2Comp.ec'}


def source_dependencies(path=SOURCE):
    result = {path.resolve()}
    for relative in re.findall(r'\brequire\s+"([^"\n]+)"', path.read_text()):
        target = (path.parent / relative).resolve()
        require(target.is_relative_to(SOURCE.parent.resolve()), 'Jasmin dependency escapes source directory')
        result |= source_dependencies(target)
    return result


def check_source(data=None):
    pins = json.loads((TEST / 'source-pins.json').read_text())
    dependencies = source_dependencies()
    require(set(pins) == {str(p.relative_to(ROOT)) for p in dependencies}, 'Jasmin dependency inventory drift')
    for path in dependencies:
        value = data if data is not None and path == SOURCE else path.read_bytes()
        require(sha(value) == pins[str(path.relative_to(ROOT))], 'r2 source/dependency pin drift: ' + str(path))
    code = re.sub(r'//[^\n]*|/\*.*?\*/', '', (SOURCE.read_bytes() if data is None else data).decode(), flags=re.S)
    require('#declassify' not in code, 'r2 must not disclose predicates or input values')
    require('#[ct = "secret × secret × secret × secret → secret"]' in code, 'r2 CT policy drift')
    require('export fn ' + SLICE in code, 'r2 export drift')
    for suffix in ('ntt', 'poly_sub', 'poly_basemul'):
        require(code.count('jade_ntruplus_ntruplus768_amd64_ref_' + suffix + '(') == 1,
                'r2 must call selected arithmetic exactly once: ' + suffix)


def check_extraction(stored, fresh):
    def contents(directory):
        paths = list(directory.rglob('*'))
        require(all(not p.is_symlink() for p in paths), 'symlink in extraction')
        require(all(p.suffix == '.ec' for p in paths if p.is_file()), 'unexpected extraction file')
        return {str(p.relative_to(directory)): p.read_bytes() for p in paths if p.is_file()}
    before, after = contents(stored), contents(fresh)
    require(set(before) == set(after) == EXTRACTION_FILES, 'whole extraction inventory drift')
    require(before == after, 'raw extraction byte drift')
    return {name: sha(data) for name, data in before.items()}


def check():
    reference.guard.check_reference()
    check_source()
    for relative, pin in json.loads((TEST / 'baseline-pins.json').read_text()).items():
        require(sha((ROOT / relative).read_bytes()) == pin, 'arithmetic baseline pin drift: ' + relative)
    original = (reference.REFERENCE / 'kem.c').read_bytes()
    for with_guard in (False, True):
        reference.check_mixed(original, reference.splice(original, with_guard), with_guard)


if __name__ == '__main__':
    check()
    print('PASS: exact r2/dependency, official fixture and one/three-block splice pins')
