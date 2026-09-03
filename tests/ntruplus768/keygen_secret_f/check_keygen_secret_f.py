#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True


class VerificationError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def strip_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    return re.sub(r"//.*", "", text)


def compact(text: str) -> str:
    text = re.sub(r"\s+", " ", strip_comments(text)).strip()
    text = re.sub(r"\[\s+", "[", text)
    return re.sub(r"\s+\]", "]", text)


def extract_function_signature(text: str, name: str) -> str:
    match = re.search(rf"\b(?:int|void|static inline int|static inline void)\s+{name}\s*\([^)]*\)", text, flags=re.S)
    require(match is not None, f"could not find signature for `{name}`")
    return compact(match.group(0))


def extract_function_body(text: str, name: str) -> str:
    match = re.search(rf"\b{name}\s*\([^)]*\)[^{{;]*\{{", text, flags=re.S)
    require(match is not None, f"could not find function `{name}`")
    start = match.end() - 1
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1 : index]
    raise VerificationError(f"unterminated body for `{name}`")


def verify_params_text(text: str) -> None:
    require(
        re.search(r"^\s*#define\s+NTRUPLUS_N\s+768\s*$", text, flags=re.M) is not None,
        "params.h must keep NTRUPLUS_N == 768",
    )
    require(
        re.search(r"^\s*#define\s+NTRUPLUS_Q\s+3457\s*$", text, flags=re.M) is not None,
        "params.h must keep NTRUPLUS_Q == 3457",
    )
    require(
        re.search(r"^\s*#define\s+NTRUPLUS_POLYBYTES\s+1152\s*$", text, flags=re.M) is not None,
        "params.h must keep NTRUPLUS_POLYBYTES == 1152",
    )


def verify_poly_header_text(text: str) -> None:
    require(
        compact(extract_function_signature(text, "poly_tobytes"))
        == "void poly_tobytes(uint8_t r[NTRUPLUS_POLYBYTES], const poly *a)",
        "poly.h must keep the canonical poly_tobytes declaration",
    )
    require(
        compact(extract_function_signature(text, "poly_frombytes"))
        == "void poly_frombytes(poly *r, const uint8_t a[NTRUPLUS_POLYBYTES])",
        "poly.h must keep the canonical poly_frombytes declaration",
    )


def verify_poly_source_text(text: str) -> None:
    require(
        compact(extract_function_signature(text, "poly_tobytes"))
        == "void poly_tobytes(uint8_t r[NTRUPLUS_POLYBYTES], const poly *a)",
        "poly.c must keep the canonical poly_tobytes signature",
    )
    require(
        compact(extract_function_signature(text, "poly_frombytes"))
        == "void poly_frombytes(poly *r, const uint8_t a[NTRUPLUS_POLYBYTES])",
        "poly.c must keep the canonical poly_frombytes signature",
    )


def verify_keypair_seam(kem_text: str) -> None:
    body = compact(extract_function_body(kem_text, "crypto_kem_keypair_derand"))
    expected_chain = (
        "poly_tobytes(pk, &h); "
        "poly_tobytes(sk, f); "
        "poly_tobytes(sk + NTRUPLUS_POLYBYTES, &hinv); "
        "hash_f(sk + 2 * NTRUPLUS_POLYBYTES, pk);"
    )
    require(
        body.count("poly_tobytes(sk, f);") == 1,
        "crypto_kem_keypair_derand() must contain exactly one poly_tobytes(sk, f)",
    )
    require(
        "poly_tobytes(sk + NTRUPLUS_POLYBYTES, f);" not in body,
        "crypto_kem_keypair_derand() must not serialize f at the hinv offset",
    )
    require(
        "poly_tobytes(sk, &hinv);" not in body,
        "crypto_kem_keypair_derand() must not serialize hinv into the first secret-key block",
    )
    require(
        expected_chain in body,
        "crypto_kem_keypair_derand() must keep the verified pk/f/hinv/hash secret-key prefix order",
    )


def verify_decap_seam(kem_text: str) -> None:
    body = compact(extract_function_body(kem_text, "crypto_kem_dec"))
    expected_chain = (
        "poly_frombytes(&c, ct); "
        "poly_frombytes(&f, sk); "
        "poly_frombytes(&hinv, sk + NTRUPLUS_POLYBYTES); "
        "poly_basemul(&m1, &c, &f); "
        "poly_invntt(&m1, &m1);"
    )
    require(
        body.count("poly_frombytes(&f, sk);") == 1,
        "crypto_kem_dec() must contain exactly one poly_frombytes(&f, sk)",
    )
    require(
        "poly_frombytes(&f, sk + NTRUPLUS_POLYBYTES);" not in body,
        "crypto_kem_dec() must not deserialize f from the hinv block",
    )
    require(
        "poly_frombytes(&hinv, sk);" not in body,
        "crypto_kem_dec() must not deserialize hinv from the first secret-key block",
    )
    require(
        expected_chain in body,
        "crypto_kem_dec() must keep the verified ct/f/hinv/basemul/invntt seam order",
    )


def verify_makefile_text(text: str) -> None:
    clean = strip_comments(text)
    logical = compact(text.replace("\\\n", " "))
    runtime_sources = '"$(DRIVER)" "$(POLY_SOURCE)" "$(NTT_SOURCE)"'

    require(
        re.search(r"^all:\s+check selfcheck run ubsan\s*$", clean, flags=re.M) is not None,
        "Makefile must keep all: check selfcheck run ubsan",
    )
    require(
        re.search(r"^\s*PARAMS_SOURCE\s*:=\s*\.\./\.\./\.\./NTRU\+/NTRU\+768/params\.h\s*$", clean, flags=re.M)
        is not None,
        "Makefile must pin params.h from NTRU+768",
    )
    require(
        re.search(r"^\s*POLY_SOURCE\s*:=\s*\.\./\.\./\.\./NTRU\+/NTRU\+768/poly\.c\s*$", clean, flags=re.M)
        is not None,
        "Makefile must pin poly.c from NTRU+768",
    )
    require(
        re.search(r"^\s*NTT_SOURCE\s*:=\s*\.\./\.\./\.\./NTRU\+/NTRU\+768/ntt\.c\s*$", clean, flags=re.M)
        is not None,
        "Makefile must pin ntt.c from NTRU+768",
    )
    require(
        logical.count(runtime_sources) == 2,
        "Makefile run and UBSan targets must both compile the driver with poly.c and ntt.c",
    )
    require(
        '"$(DRIVER)" "$(POLY_SOURCE)" "$(KEM_SOURCE)"' not in logical,
        "Makefile runtime targets must not compile the driver with kem.c",
    )
    require(
        re.search(r'^\t"\$\(OUTDIR\)/keygen_secret_f_driver"\s*$', clean, flags=re.M) is not None,
        "Makefile run target must execute keygen_secret_f_driver",
    )
    require(
        re.search(r'^\t"\$\(OUTDIR\)/keygen_secret_f_driver_ubsan"\s*$', clean, flags=re.M) is not None,
        "Makefile UBSan target must execute keygen_secret_f_driver_ubsan",
    )


def verify_all(
    params_text: str,
    poly_header_text: str,
    poly_source_text: str,
    kem_text: str,
    makefile_text: str,
) -> None:
    verify_params_text(params_text)
    verify_poly_header_text(poly_header_text)
    verify_poly_source_text(poly_source_text)
    verify_keypair_seam(kem_text)
    verify_decap_seam(kem_text)
    verify_makefile_text(makefile_text)


def mutate_once(text: str, old: str, new: str, label: str) -> str:
    mutated = text.replace(old, new, 1)
    require(mutated != text, f"could not construct mutation: {label}")
    return mutated


def expect_rejected(
    params_text: str,
    poly_header_text: str,
    poly_source_text: str,
    kem_text: str,
    makefile_text: str,
    *,
    label: str,
) -> None:
    try:
        verify_all(params_text, poly_header_text, poly_source_text, kem_text, makefile_text)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(
    params_text: str,
    poly_header_text: str,
    poly_source_text: str,
    kem_text: str,
    makefile_text: str,
) -> None:
    verify_all(params_text, poly_header_text, poly_source_text, kem_text, makefile_text)

    expect_rejected(
        mutate_once(params_text, "#define NTRUPLUS_POLYBYTES 1152", "#define NTRUPLUS_POLYBYTES 1153", "polybytes constant"),
        poly_header_text,
        poly_source_text,
        kem_text,
        makefile_text,
        label="polybytes constant",
    )
    expect_rejected(
        params_text,
        mutate_once(
            poly_header_text,
            "void poly_frombytes(poly *r, const uint8_t a[NTRUPLUS_POLYBYTES]);",
            "void poly_frombytes(poly *r, const unsigned char a[NTRUPLUS_POLYBYTES]);",
            "poly_frombytes declaration type",
        ),
        poly_source_text,
        kem_text,
        makefile_text,
        label="poly_frombytes declaration type",
    )
    expect_rejected(
        params_text,
        poly_header_text,
        poly_source_text,
        mutate_once(kem_text, "poly_tobytes(sk, f);", "poly_tobytes(pk, f);", "keypair destination"),
        makefile_text,
        label="keypair destination",
    )
    expect_rejected(
        params_text,
        poly_header_text,
        poly_source_text,
        mutate_once(kem_text, "poly_tobytes(sk, f);", "poly_tobytes(sk, &h);", "keypair source"),
        makefile_text,
        label="keypair source",
    )
    expect_rejected(
        params_text,
        poly_header_text,
        poly_source_text,
        mutate_once(
            kem_text,
            "poly_tobytes(sk, f);",
            "poly_tobytes(sk + NTRUPLUS_POLYBYTES, f);",
            "keypair offset",
        ),
        makefile_text,
        label="keypair offset",
    )
    expect_rejected(
        params_text,
        poly_header_text,
        poly_source_text,
        mutate_once(
            kem_text,
            "poly_tobytes(sk, f);\n    poly_tobytes(sk + NTRUPLUS_POLYBYTES, &hinv);",
            "poly_tobytes(sk + NTRUPLUS_POLYBYTES, &hinv);\n    poly_tobytes(sk, f);",
            "keypair call order",
        ),
        makefile_text,
        label="keypair call order",
    )
    expect_rejected(
        params_text,
        poly_header_text,
        poly_source_text,
        mutate_once(kem_text, "poly_frombytes(&f, sk);", "poly_frombytes(&f, sk + NTRUPLUS_POLYBYTES);", "decap offset"),
        makefile_text,
        label="decap offset",
    )
    expect_rejected(
        params_text,
        poly_header_text,
        poly_source_text,
        mutate_once(kem_text, "poly_frombytes(&f, sk);", "poly_frombytes(&hinv, sk);", "decap destination"),
        makefile_text,
        label="decap destination",
    )
    expect_rejected(
        params_text,
        poly_header_text,
        poly_source_text,
        mutate_once(
            kem_text,
            "poly_frombytes(&f, sk);\n    poly_frombytes(&hinv, sk + NTRUPLUS_POLYBYTES);",
            "poly_frombytes(&hinv, sk + NTRUPLUS_POLYBYTES);\n    poly_frombytes(&f, sk);",
            "decap call order",
        ),
        makefile_text,
        label="decap call order",
    )
    expect_rejected(
        params_text,
        poly_header_text,
        poly_source_text,
        kem_text,
        mutate_once(
            makefile_text,
            '"$(DRIVER)" "$(POLY_SOURCE)" "$(NTT_SOURCE)"',
            '"$(DRIVER)" "$(POLY_SOURCE)" "$(KEM_SOURCE)"',
            "makefile runtime sources",
        ),
        label="makefile runtime sources",
    )
    expect_rejected(
        params_text,
        poly_header_text,
        poly_source_text,
        kem_text,
        mutate_once(
            makefile_text,
            '"$(DRIVER)" "$(POLY_SOURCE)" "$(NTT_SOURCE)" $(LDFLAGS) \\\n\t  -o "$(OUTDIR)/keygen_secret_f_driver_ubsan"',
            '"$(DRIVER)" "$(POLY_SOURCE)" "$(KEM_SOURCE)" $(LDFLAGS) \\\n\t  -o "$(OUTDIR)/keygen_secret_f_driver_ubsan"',
            "makefile ubsan runtime sources",
        ),
        label="makefile ubsan runtime sources",
    )


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fail-closed checker for the NTRU+768 secret-key f serialization seam",
    )
    parser.add_argument("--params-source", required=True, help="path to NTRU+/NTRU+768/params.h")
    parser.add_argument("--poly-header", required=True, help="path to NTRU+/NTRU+768/poly.h")
    parser.add_argument("--poly-source", required=True, help="path to NTRU+/NTRU+768/poly.c")
    parser.add_argument("--kem-source", required=True, help="path to NTRU+/NTRU+768/kem.c")
    parser.add_argument("--makefile", required=True, help="path to the local Makefile")
    parser.add_argument(
        "--self-check",
        action="store_true",
        help="also require representative bad mutations to be rejected",
    )
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        params_text = Path(args.params_source).read_text(encoding="utf-8")
        poly_header_text = Path(args.poly_header).read_text(encoding="utf-8")
        poly_source_text = Path(args.poly_source).read_text(encoding="utf-8")
        kem_text = Path(args.kem_source).read_text(encoding="utf-8")
        makefile_text = Path(args.makefile).read_text(encoding="utf-8")
        verify_all(params_text, poly_header_text, poly_source_text, kem_text, makefile_text)
        if args.self_check:
            run_self_check(params_text, poly_header_text, poly_source_text, kem_text, makefile_text)
    except VerificationError as exc:
        print(f"keygen_secret_f checker failed: {exc}", file=sys.stderr)
        return 1

    print("keygen_secret_f checker passed")
    if args.self_check:
        print("keygen_secret_f checker self-check passed: 11 mutations rejected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
