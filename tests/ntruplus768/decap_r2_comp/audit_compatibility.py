#!/usr/bin/env python3
"""Identify the exact official/frozen arithmetic changes; no C equivalence claim."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
TEST = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('candidate_audit', TEST.parent / 'decap_candidate/audit_compatibility.py')
candidate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(candidate)
function_body, normalized = candidate.function_body, candidate.normalized


def audit(root):
    old = root / 'NTRU+/NTRU+768'
    official = root / 'tests/ntruplus768/decap_guard/reference'
    before = normalized(function_body(old / 'ntt.c', 'ntt'))
    assert before.count('a[') == 4
    assert before.count('barrett_reduce(r[i]-t1)') == 1
    assert before.count('barrett_reduce(r[i]+t1)') == 1
    before = before.replace('a[', 'r[')
    after = normalized(function_body(official / 'ntt.c', 'ntt'))
    before = before.replace('barrett_reduce(r[i]-t1)', 'r[i]-t1').replace('barrett_reduce(r[i]+t1)', 'r[i]+t1')
    final = 'for(inti=0;i<NTRUPLUS_N;i++)r[i]=barrett_reduce(r[i]);'
    checks = {
        'known_ntt_change_only_inplace_input_and_relocated_barrett':
            after.count(final) == 1 and before == after.replace(final, ''),
        'poly_sub_identical': normalized(function_body(old / 'poly.c', 'poly_sub')) ==
            normalized(function_body(official / 'poly.c', 'poly_sub')),
        'montgomery_reduce_identical': normalized(function_body(old / 'ntt.c', 'montgomery_reduce')) ==
            normalized(function_body(official / 'ntt.c', 'montgomery_reduce')),
        'barrett_reduce_identical': normalized(function_body(old / 'ntt.c', 'barrett_reduce')) ==
            normalized(function_body(official / 'ntt.c', 'barrett_reduce')),
        'fqmul_identical': normalized(function_body(old / 'ntt.c', 'fqmul')) ==
            normalized(function_body(official / 'ntt.c', 'fqmul')),
        'basemul_substituted_outputs_identical': candidate.substituted_outputs(function_body(old / 'ntt.c', 'basemul')) ==
            candidate.substituted_outputs(function_body(official / 'ntt.c', 'basemul')),
    }
    twiddles = lambda p: re.sub(r'\s+', '', re.search(r'zetas\[192\] = \{(.*?)\}', p.read_text(), re.S)[1])
    checks['all_twiddles_identical'] = twiddles(old / 'ntt.c') == twiddles(official / 'ntt.c')
    def constant(path, name):
        return int(re.search(r'^#define\s+' + name + r'\s+(-?\d+)\b', path.read_text(), re.M)[1])
    for filename, name, expected in [('params.h','NTRUPLUS_N',768),('params.h','NTRUPLUS_Q',3457),
                                    ('ntt.c','NTRUPLUS_QINV',12929),('ntt.c','NTRUPLUS_OMEGA',-886)]:
        checks[name + '_bound_to_expected_value'] = constant(old/filename,name) == constant(official/filename,name) == expected
    if not all(checks.values()):
        raise ValueError('compatibility audit failed: ' + str(checks))
    paths = [old / 'ntt.c', old / 'poly.c', old / 'params.h', official / 'ntt.c', official / 'poly.c', official / 'params.h']
    return {'result': 'PASS', 'official_commit': '3991b2ae08d6f0008d37e41b8aceaaab27b4ec89',
        'checks': checks,
        'scope': 'Identifies the frozen/official source differences only. Relocating Barrett reductions '
            'changes intermediate words and traces; exact final r2 equality is checked by native '
            'boundary/random and full API regressions, not proved as a C-AST equivalence. '
            'EasyCrypt proves the extracted frozen-kernel Jasmin composition against its separate specification.',
        'files': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    print(json.dumps(audit(parser.parse_args().root.resolve()), indent=2))
