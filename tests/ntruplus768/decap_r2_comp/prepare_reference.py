#!/usr/bin/env python3
"""Exact r2-only and guard/candidate/r2 splices of the pinned official C."""
import argparse
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
TEST = Path(__file__).resolve().parent
ROOT = TEST.parents[2]
GUARD = TEST.parent / 'decap_guard'
CANDIDATE = TEST.parent / 'decap_candidate'
spec = importlib.util.spec_from_file_location('candidate_reference', CANDIDATE / 'prepare_reference.py')
candidate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(candidate)
guard = candidate.guard
require, sha, REFERENCE = guard.require, guard.sha, GUARD / 'reference'
OLD_BLOCK = b'''    m2 = m1;
    poly_ntt(&m2);
    poly_sub(&c, &c, &m2);
    poly_basemul(&r2, &c, &hinv);'''
NEW_BLOCK = b'''    jade_ntruplus_ntruplus768_amd64_ref_decap_r2(
        (uint16_t *)r2.coeffs, (const uint16_t *)c.coeffs,
        (const uint16_t *)m1.coeffs, (const uint16_t *)hinv.coeffs);'''


def splice(original, with_previous=False):
    require(sha(original) == guard.REFERENCE_PINS['kem.c'], 'official kem.c pin drift')
    require(original.count(OLD_BLOCK) == 1, 'expected one exact r2 block')
    mixed = candidate.splice(original, True) if with_previous else original
    return mixed.replace(OLD_BLOCK, NEW_BLOCK)


def check_mixed(original, mixed, with_previous=False):
    require(mixed == splice(original, with_previous), 'mixed code changed outside approved splices')


def generate(output):
    guard.check_reference()
    original = (REFERENCE / 'kem.c').read_bytes()
    output.mkdir(parents=True, exist_ok=True)
    records = {}
    for name, body in [('official', original), ('mixed', splice(original)), ('both', splice(original, True))]:
        preamble = '#include "trace.h"\n'
        preamble += ''.join('#define ' + dep + ' trace_' + dep + '\n' for dep in guard.DEPENDENCIES)
        for suffix, label in [('guard', 'guard'), ('candidate', 'candidate'), ('r2', 'r2')]:
            preamble += '#define jade_ntruplus_ntruplus768_amd64_ref_decap_' + suffix + ' trace_' + label + '\n'
        preamble += ''.join('#define crypto_kem_' + suffix + ' ' + name + '_' + local + '\n'
                            for suffix, local in [('keypair','keypair'), ('enc','enc'), ('dec','dec')])
        path = output / (name + '_kem.c')
        path.write_bytes(preamble.encode() + body)
        records[path.name] = {'sha256': sha(path.read_bytes()), 'body_sha256': sha(body),
                              'preamble_bytes': len(preamble.encode()), 'body_bytes': len(body)}
    records['contract'] = ('mixed replaces only the exact r2 NTT/subtraction/basemul block; '
        'both additionally replaces the exact guard and candidate blocks. All other official bytes, '
        'including later rejection, shared-key masking and cleanup, remain unchanged. '
        'The r2 splice leaves c/m2 untouched; they are not subsequently read except by cleanup. '
        'Jasmin call events do not expose internal load counts. No erasure equivalence is asserted.')
    records['reference_directory'] = str(REFERENCE.relative_to(ROOT))
    (output / 'splice.json').write_text(json.dumps(records, indent=2) + '\n')
    return records


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    generate(parser.parse_args().output)
