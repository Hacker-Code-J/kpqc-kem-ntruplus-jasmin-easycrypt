#!/usr/bin/env python3
"""Bind an immutable official body to one reviewed C-to-Jasmin guard splice."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
TEST = Path(__file__).resolve().parent
ROOT = TEST.parents[2]
REFERENCE_MANIFEST_SHA = "e3d3afc8935b977cc115835d3d73bfc0a99a77627add65ed4fb1d757c2a77b5c"
REFERENCE_PINS = {
    "kem.c": "70fbe16681ff24798d3a1feb88095088b80aacebfb2b9f60ccf2395454fa0134",
    "poly.c": "923990d51c526f2c46d1a40dc6fb6ef4e50ada35f74647ad73fd597a25fda592",
    "poly.h": "9a3ac9414dd75412d7dbc888aab82cf7659531b7993256123eee687e85f1d743",
    "params.h": "420bef5432154798239e1f09b18f31947e3afff248ff98d4e83346b84d27ebb8",
    "ntt.c": "ac85aea518d2b4251b08d68c372e3fda3d232917542677ae20353433d67f4911",
    "ntt.h": "1edc2346f1705cc98af0f64b2f0ac974f3d58ab9b6603ebbfa415f4e135f5851",
    "symmetric.c": "6b7a829328545067d3095c49953d534dd7436bf8d1e4624aa9076cdae775501e",
    "symmetric.h": "d56d67dbf50c7b89de87eb5acbcfb11ece0fe90e7744762c0bc9a47350d80f65",
    "util.h": "561a5b1e0611985890d9eff695f1ac34f88605631dcef620100ab6aed1b1276d",
    "api.h": "1912c6a38e7f1449321520570020266836a4cace70f7e5901d0e8c172a707865",
    "randombytes.h": "5ece412ed498abfd892ecec23480910b76cb8ea1b605da10adc5584ede79f048",
    "fips202/fips202.c": "7a150641dd886261d299d0addb6c3474fdf69e2382e88357a1c088b2ce631181",
    "fips202/fips202.h": "86d3adefd72a25231b26d14b345648359db534790abd25148ccdfdba2800c298",
    "kat/rng.c": "ff48cce3002ab7fe2413e75036b870afd24f551ddcfcf138f8df539b92f44134",
    "kat/rng.h": "81209b4388f6171e71b2885fbdaf239435342d2621be3c3cfd34a50374bbc959",
    "kat/aes.c": "a3dc332bd2660ed4a57855674b0596223c1ef4affc6662b0507ab587e8fe41eb",
    "kat/aes.h": "313dfd81cb86d9cb6655b9741390e18b332142bafe159252bc54ef3f5418c215",
    "LICENSE": "fc50cdff5695ed2aedde871816fbd86cb0e33a3b315b25948489418dacd9c81a",
    "PQCkemKAT_2336.rsp": "22c72039845361ff142273150a59785bada5146c04018ce0a8b67b99a647eaa8"
}
OLD_BLOCK = b"""    if(poly_frombytes(&c, ct) ||
       poly_frombytes(&f, sk) ||
       poly_frombytes(&hinv, sk + NTRUPLUS_POLYBYTES))
    {
        secure_clear(ss, NTRUPLUS_SSBYTES);

        goto cleanup;
    }"""
NEW_BLOCK = b"""    if (jade_ntruplus_ntruplus768_amd64_ref_decap_guard(
            (uint16_t *)c.coeffs, (uint16_t *)f.coeffs,
            (uint16_t *)hinv.coeffs, ss, ct, sk))
        goto cleanup;"""
DEPENDENCIES = ['randombytes', 'poly_frombytes', 'hash_f', 'hash_g', 'hash_h',
                'poly_cbd1', 'poly_ntt', 'poly_invntt', 'poly_tobytes',
                'poly_sotp_decode', 'poly_basemul', 'poly_sub', 'poly_crepmod3']


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check_reference(reference=None, manifest_path=None):
    reference = reference or TEST / 'reference'
    manifest_path = manifest_path or TEST / 'reference-manifest.json'
    manifest = manifest_path.read_bytes()
    require(sha(manifest) == REFERENCE_MANIFEST_SHA, 'reference manifest drift')
    require(json.loads(manifest)['files'] == REFERENCE_PINS, 'reference pins drift')
    paths = list(reference.rglob('*'))
    require(all(not path.is_symlink() for path in paths), 'symlink in reference')
    files = {str(p.relative_to(reference)): p for p in paths if p.is_file()}
    require(set(files) == set(REFERENCE_PINS), 'reference inventory drift')
    for name, expected in REFERENCE_PINS.items():
        require(not files[name].is_symlink() and sha(files[name].read_bytes()) == expected,
                'reference file drift: ' + name)


def splice(original):
    require(sha(original) == REFERENCE_PINS['kem.c'], 'official kem.c pin drift')
    require(original.count(OLD_BLOCK) == 1, 'expected one exact validation block')
    before, after = original.split(OLD_BLOCK)
    require(b'poly_basemul(&m1, &c, &f);' in after, 'success continuation missing')
    return before + NEW_BLOCK + after


def check_mixed(original, mixed):
    require(mixed == splice(original), 'mixed source changed outside approved guard splice')


def generate(output):
    check_reference()
    original = (TEST / 'reference/kem.c').read_bytes()
    mixed = splice(original)
    check_mixed(original, mixed)
    output.mkdir(parents=True, exist_ok=True)
    records = {}
    for name, body in [('official', original), ('mixed', mixed)]:
        preamble = '#include "trace.h"\n'
        preamble += ''.join('#define ' + dep + ' trace_' + dep + '\n' for dep in DEPENDENCIES)
        preamble += '#define jade_ntruplus_ntruplus768_amd64_ref_decap_guard trace_guard\n'
        preamble += ''.join('#define crypto_kem_' + suffix + ' ' + name + '_' + local + '\n'
                            for suffix, local in [('keypair','keypair'),('enc','enc'),('dec','dec')])
        suffix = ''
        if name == 'official':
            # Exact official guard with caller-owned polynomial lvalues.
            # Its cleanup label only returns status; full API cleanup remains
            # byte-identical in both complete generated KEM bodies.
            suffix = ('\nint official_prefix(poly *cp, poly *fp, poly *hp, uint8_t *ss,\n'
                      '                    const uint8_t *ct, const uint8_t *sk)\n'
                      '{\n#define c (*cp)\n#define f (*fp)\n#define hinv (*hp)\n' +
                      OLD_BLOCK.decode() + '\n#undef c\n#undef f\n#undef hinv\n'
                      '    return 0;\ncleanup: return 1;\n}\n')
        path = output / (name + '_kem.c')
        path.write_bytes(preamble.encode() + body + suffix.encode())
        records[path.name] = {'sha256': sha(path.read_bytes()), 'body_sha256': sha(body),
                              'preamble_bytes': len(preamble.encode()), 'body_bytes': len(body)}
    records['contract'] = 'Only the exact original validation block is spliced; remainder of official kem.c is byte-identical. Shared macro adapters namespace APIs and trace real dependency calls. Native prefix uses original block with c/f/hinv bound to caller outputs and its cleanup label returning failure.'
    (output/'splice.json').write_text(json.dumps(records,indent=2)+'\n')
    return records


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    generate(parser.parse_args().output)
