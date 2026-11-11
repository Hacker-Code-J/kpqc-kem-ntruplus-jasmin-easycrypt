#!/usr/bin/env python3
"""Exact three-call message splice, alone or after the three verified stages."""
import argparse
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
TEST = Path(__file__).resolve().parent
ROOT = TEST.parents[2]
R2 = TEST.parent / 'decap_r2_comp'
spec = importlib.util.spec_from_file_location('r2_reference', R2 / 'prepare_reference.py')
r2 = importlib.util.module_from_spec(spec); spec.loader.exec_module(r2)
guard, CANDIDATE, GUARD = r2.guard, r2.CANDIDATE, r2.GUARD
require, sha, REFERENCE = guard.require, guard.sha, r2.REFERENCE
OLD_BLOCK = b'''    poly_tobytes(buf1, &r2);
    hash_g(buf2, buf1);
    fail = poly_sotp_decode(msg, &m1, buf2);'''
NEW_BLOCK = b'''    fail = (int)ntruplus768_decap_message(msg, buf1,
        (const uint16_t *)m1.coeffs, (const uint16_t *)r2.coeffs);'''


def splice(original, with_previous=False):
    require(sha(original) == guard.REFERENCE_PINS['kem.c'], 'official kem.c pin drift')
    require(original.count(OLD_BLOCK) == 1, 'expected one exact message block')
    mixed = r2.splice(original, True) if with_previous else original
    return mixed.replace(OLD_BLOCK, NEW_BLOCK)


def check_mixed(original, mixed, with_previous=False):
    require(mixed == splice(original, with_previous), 'mixed source changed outside exact splices')


def generate(output):
    guard.check_reference()
    original = (REFERENCE / 'kem.c').read_bytes()
    output.mkdir(parents=True, exist_ok=True)
    records = {}
    for name, body in [('official', original), ('mixed', splice(original)), ('both', splice(original, True))]:
        preamble = '#include "trace.h"\n'
        preamble += ''.join('#define ' + dep + ' trace_' + dep + '\n' for dep in guard.DEPENDENCIES)
        for suffix in ('guard', 'candidate', 'r2'):
            preamble += '#define jade_ntruplus_ntruplus768_amd64_ref_decap_' + suffix + ' trace_' + suffix + '\n'
        preamble += '#define ntruplus768_decap_message trace_message\n'
        preamble += ''.join('#define crypto_kem_' + suffix + ' ' + name + '_' + local + '\n'
                            for suffix, local in [('keypair','keypair'), ('enc','enc'), ('dec','dec')])
        path = output / (name + '_kem.c'); path.write_bytes(preamble.encode() + body)
        records[path.name] = {'sha256':sha(path.read_bytes()), 'body_sha256':sha(body),
                              'preamble_bytes':len(preamble.encode()), 'body_bytes':len(body)}
    records['contract'] = ('Only the exact poly_tobytes/hash_g/poly_sotp_decode block is replaced in mixed; '
        'both additionally replaces exact guard/candidate/r2 blocks. Later HashH, regeneration, verify, '
        'shared-key masking, cleanup and return bytes are unchanged. serialized buf1 is retained for verify. '
        'Shared test macros trace calls without replacing the hash primitive. C glue uses pinned official SHAKE256; '
        'neither the C glue nor SHAKE256 is formally verified here. No whole-API CT/SCT or erasure equivalence claim.')
    (output / 'splice.json').write_text(json.dumps(records, indent=2) + '\n')
    return records


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument('--output', required=True, type=Path)
    generate(parser.parse_args().output)
