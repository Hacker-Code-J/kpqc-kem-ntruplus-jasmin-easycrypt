#!/usr/bin/env python3
"""Reuse pinned official3991b2a fixtures and splice only the selected calls."""
import argparse
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
TEST = Path(__file__).resolve().parent
ROOT = TEST.parents[2]
GUARD = TEST.parent / 'decap_guard'
spec = importlib.util.spec_from_file_location('guard_reference', GUARD / 'prepare_reference.py')
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
require, sha = guard.require, guard.sha
REFERENCE = GUARD / 'reference'
OLD_BLOCK = b'''    poly_basemul(&m1, &c, &f);
    poly_invntt(&m1);
    poly_crepmod3(&m1);'''
NEW_BLOCK = b'''    jade_ntruplus_ntruplus768_amd64_ref_decap_candidate(
        (uint16_t *)m1.coeffs, (const uint16_t *)c.coeffs,
        (const uint16_t *)f.coeffs);'''


def splice(original, with_guard=False):
    require(sha(original) == guard.REFERENCE_PINS['kem.c'], 'official kem.c pin drift')
    require(original.count(OLD_BLOCK) == 1, 'expected one exact candidate block')
    mixed = original.replace(OLD_BLOCK, NEW_BLOCK)
    if with_guard:
        require(mixed.count(guard.OLD_BLOCK) == 1, 'expected one exact guard block')
        mixed = mixed.replace(guard.OLD_BLOCK, guard.NEW_BLOCK)
    return mixed


def check_mixed(original, mixed, with_guard=False):
    require(mixed == splice(original, with_guard), 'mixed code changed outside approved splices')


def generate(output):
    guard.check_reference()
    original = (REFERENCE / 'kem.c').read_bytes()
    output.mkdir(parents=True, exist_ok=True)
    records = {}
    for name, body in [('official', original), ('mixed', splice(original)), ('both', splice(original, True))]:
        preamble = '#include "trace.h"\n'
        preamble += ''.join('#define ' + dep + ' trace_' + dep + '\n' for dep in guard.DEPENDENCIES)
        preamble += '#define jade_ntruplus_ntruplus768_amd64_ref_decap_guard trace_guard\n'
        preamble += '#define jade_ntruplus_ntruplus768_amd64_ref_decap_candidate trace_candidate\n'
        preamble += ''.join('#define crypto_kem_' + suffix + ' ' + name + '_' + local + '\n'
                            for suffix, local in [('keypair','keypair'), ('enc','enc'), ('dec','dec')])
        path = output / (name + '_kem.c')
        path.write_bytes(preamble.encode() + body)
        records[path.name] = {'sha256': sha(path.read_bytes()), 'body_sha256': sha(body),
                              'preamble_bytes': len(preamble.encode()), 'body_bytes': len(body)}
    records['contract'] = 'mixed replaces only the exact candidate BIM block; both also replaces the exact checked-decoder guard block. Every other official byte, including failure handling and cleanup, is unchanged. Macros namespace APIs and trace real calls; each Jasmin export is one trace event, not an internal-load trace.'
    records['reference_directory'] = str(REFERENCE.relative_to(ROOT))
    (output / 'splice.json').write_text(json.dumps(records, indent=2) + '\n')
    return records


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    generate(parser.parse_args().output)
