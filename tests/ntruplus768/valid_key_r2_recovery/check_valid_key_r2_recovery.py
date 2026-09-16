#!/usr/bin/env python3
"""Fail closed on changes to the production byte/hash caller seams.

These are source-shape checks, not a C-AST equivalence proof.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path


def body(source: str, name: str) -> str:
    source = re.sub(r"/\*.*?\*/|//[^\n]*", "", source, flags=re.S)
    match = re.search(rf"\b{name}\s*\([^)]*\)\s*\{{", source)
    if match is None:
        raise ValueError(f"missing function {name}")
    start = match.end()
    depth = 1
    for index in range(start, len(source)):
        depth += (source[index] == "{") - (source[index] == "}")
        if depth == 0:
            return re.sub(r"\s+", "", source[start:index])
    raise ValueError(f"unterminated function {name}")


CHAINS = {
    "crypto_kem_keypair_derand": (
        "poly_basemul(&h, g, finv);",
        "poly_basemul(&hinv, f, ginv);",
        "poly_tobytes(pk, &h);",
        "poly_tobytes(sk, f);",
        "poly_tobytes(sk + NTRUPLUS_POLYBYTES, &hinv);",
        "hash_f(sk + 2 * NTRUPLUS_POLYBYTES, pk);",
    ),
    "crypto_kem_enc_derand": (
        "poly_tobytes(buf2, &r);",
        "hash_g(buf2, buf2);",
        "poly_sotp_encode(&m, msg, buf2);",
        "poly_ntt(&m, &m);",
        "poly_frombytes(&h, pk);",
        "poly_basemul_add(&c, &h, &r, &m);",
        "poly_tobytes(ct, &c);",
    ),
    "crypto_kem_dec": (
        "poly_frombytes(&c, ct);",
        "poly_frombytes(&f, sk);",
        "poly_frombytes(&hinv, sk + NTRUPLUS_POLYBYTES);",
        "poly_basemul(&m1, &c, &f);",
        "poly_invntt(&m1, &m1);",
        "poly_crepmod3(&m1, &m1);",
        "poly_ntt(&m2, &m1);",
        "poly_sub(&c, &c, &m2);",
        "poly_basemul(&r2, &c, &hinv);",
        "poly_tobytes(buf1, &r2);",
        "hash_g(buf2, buf1);",
        "fail = poly_sotp_decode(msg, &m1, buf2);",
    ),
}


def verify(source: str) -> None:
    for name, statements in CHAINS.items():
        actual = body(source, name)
        expected = tuple(re.sub(r"\s+", "", statement) for statement in statements)
        if "".join(expected) not in actual or any(actual.count(s) != 1 for s in expected):
            raise ValueError(f"{name}: serialization/hash seam changed")


def self_test(source: str) -> None:
    mutations = (
        ("poly_tobytes(sk + NTRUPLUS_POLYBYTES, &hinv);",
         "poly_tobytes(sk, &hinv);"),
        ("poly_tobytes(sk + NTRUPLUS_POLYBYTES, &hinv);",
         "poly_tobytes(sk + 2 * NTRUPLUS_POLYBYTES, &hinv);"),
        ("poly_frombytes(&hinv, sk + NTRUPLUS_POLYBYTES);",
         "poly_frombytes(&hinv, sk);"),
        ("poly_frombytes(&c, ct);", "poly_frombytes(&c, ct + 1);"),
        ("poly_tobytes(ct, &c);", "poly_tobytes(ct + 1, &c);"),
        ("poly_frombytes(&h, pk);", "poly_frombytes(&h, sk);"),
        ("poly_sub(&c, &c, &m2);", "poly_sub(&c, &m2, &c);"),
        ("poly_basemul(&r2, &c, &hinv);", "poly_basemul(&r2, &c, &f);"),
        ("poly_tobytes(buf1, &r2);", "poly_tobytes(buf1, &r1);"),
        ("hash_g(buf2, buf1);", "hash_g(buf2, buf2);"),
        ("hash_g(buf2, buf2);", "hash_g(buf2, buf1);"),
        ("poly_sotp_decode(msg, &m1, buf2);", "poly_sotp_decode(msg, &m1, buf1);"),
        ("poly_tobytes(buf1, &r2);", "/* poly_tobytes(buf1, &r2); */"),
        ("poly_tobytes(buf1, &r2);",
         "poly_tobytes(buf1, &r2); poly_tobytes(buf1, &r2);"),
    )
    for original, replacement in mutations:
        if source.count(original) != 1:
            raise ValueError(f"mutation target is not unique: {original}")
        try:
            verify(source.replace(original, replacement, 1))
        except ValueError:
            continue
        raise ValueError(f"checker accepted mutation: {replacement}")
    print(f"PASS caller-seam checker: {len(mutations)} mutations rejected")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    source_path = Path(__file__).resolve().parents[3] / "NTRU+" / "NTRU+768" / "kem.c"
    source = source_path.read_text()
    verify(source)
    if args.self_test:
        self_test(source)
    else:
        print("PASS production source seams: hinv offset, ciphertext, r2 bytes, hash_g/SOTP order")


if __name__ == "__main__":
    main()
