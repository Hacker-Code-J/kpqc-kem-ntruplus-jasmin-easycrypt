#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


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
    match = re.search(rf"\bvoid\s+{name}\s*\([^)]*\)", text, flags=re.S)
    require(match is not None, f"could not find signature for `{name}`")
    return compact(match.group(0))


def extract_function_body(text: str, name: str) -> str:
    match = re.search(rf"\b{name}\s*\([^)]*\)[^{{]*\{{", text)
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
    raise VerificationError(f"unterminated body for function `{name}`")


def verify_crypto_kem_dec_text(text: str) -> None:
    body = compact(extract_function_body(text, "crypto_kem_dec"))
    call_pattern = re.compile(
        r".*"
        r"poly_frombytes\(&c, ct\); "
        r"poly_frombytes\(&f, sk\); "
        r"poly_frombytes\(&hinv, sk \+ NTRUPLUS_POLYBYTES\); "
        r"poly_basemul\(&m1, &c, &f\); "
        r"poly_invntt\(&m1, &m1\);"
        r".*"
    )
    require(
        call_pattern.fullmatch(body) is not None,
        "crypto_kem_dec no longer contains the verified ordered poly_frombytes/poly_basemul/poly_invntt seam",
    )


def verify_poly_frombytes_text(text: str) -> None:
    signature = extract_function_signature(text, "poly_frombytes")
    require(
        signature == "void poly_frombytes(poly *r, const uint8_t a[NTRUPLUS_POLYBYTES])",
        f"unexpected poly_frombytes signature: {signature}",
    )

    body = compact(extract_function_body(text, "poly_frombytes"))

    loop_pattern = re.compile(
        r"for\(size_t i = 0; i < NTRUPLUS_N/2; i\+\+\) "
        r"\{ "
        r"r->coeffs\[2\*i\] = "
        r"\(\(a\[3\*i\+0\] >> 0\) \| \(\(uint16_t\)a\[3\*i\+1\] << 8\)\) & 0xFFF; "
        r"r->coeffs\[2\*i\+1\] = "
        r"\(\(a\[3\*i\+1\] >> 4\) \| \(\(uint16_t\)a\[3\*i\+2\] << 4\)\) & 0xFFF; "
        r"\}"
    )
    require(
        loop_pattern.fullmatch(body) is not None,
        "poly_frombytes body no longer matches verified N/2 loop, 3*i byte access, 2*i outputs, shifts, casts, and 0xFFF masks",
    )


def expect_rejected(check, text: str, label: str) -> None:
    try:
        check(text)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def mutate_once(text: str, old: str, new: str, label: str) -> str:
    mutated = text.replace(old, new, 1)
    require(mutated != text, f"could not construct mutation: {label}")
    return mutated


def run_self_check(poly_text: str, kem_text: str) -> None:
    normalized_poly = compact(poly_text)
    poly_text = (
        f"{extract_function_signature(normalized_poly, 'poly_frombytes')} "
        f"{{ {extract_function_body(normalized_poly, 'poly_frombytes')} }}"
    )
    kem_text = compact(kem_text)

    expect_rejected(
        verify_poly_frombytes_text,
        mutate_once(
            poly_text,
            "const uint8_t a[NTRUPLUS_POLYBYTES]",
            "const unsigned char a[NTRUPLUS_POLYBYTES]",
            "signature type",
        ),
        "signature type",
    )
    expect_rejected(
        verify_poly_frombytes_text,
        mutate_once(
            poly_text,
            "i < NTRUPLUS_N/2",
            "i < NTRUPLUS_N/3",
            "loop bound",
        ),
        "loop bound",
    )
    expect_rejected(
        verify_poly_frombytes_text,
        mutate_once(
            poly_text,
            "a[3*i+1] << 8",
            "a[3*i+2] << 8",
            "first coefficient byte index",
        ),
        "first coefficient byte index",
    )
    expect_rejected(
        verify_poly_frombytes_text,
        mutate_once(
            poly_text,
            "a[3*i+1] >> 4",
            "a[3*i+1] >> 3",
            "second coefficient shift",
        ),
        "second coefficient shift",
    )
    expect_rejected(
        verify_poly_frombytes_text,
        mutate_once(
            poly_text,
            "r->coeffs[2*i+1]",
            "r->coeffs[2*i+2]",
            "second output index",
        ),
        "second output index",
    )
    expect_rejected(
        verify_poly_frombytes_text,
        mutate_once(
            poly_text,
            "(uint16_t)a[3*i+2] << 4",
            "(uint32_t)a[3*i+2] << 4",
            "cast width",
        ),
        "cast width",
    )
    expect_rejected(
        verify_poly_frombytes_text,
        mutate_once(
            poly_text,
            "& 0xFFF",
            "& 0x7FF",
            "mask",
        ),
        "mask",
    )
    expect_rejected(
        verify_poly_frombytes_text,
        mutate_once(
            poly_text,
            "r->coeffs[2*i+1] = ((a[3*i+1] >> 4) | ((uint16_t)a[3*i+2] << 4)) & 0xFFF;",
            "r->coeffs[2*i+1] = ((a[3*i+1] >> 4) | ((uint16_t)a[3*i+2] << 4)) & 0xFFF; r->coeffs[0] = 0;",
            "extra output write",
        ),
        "extra output write",
    )
    expect_rejected(
        verify_crypto_kem_dec_text,
        mutate_once(
            kem_text,
            "poly_frombytes(&hinv, sk + NTRUPLUS_POLYBYTES); poly_basemul(&m1, &c, &f);",
            "poly_basemul(&m1, &c, &f); poly_frombytes(&hinv, sk + NTRUPLUS_POLYBYTES);",
            "caller seam order",
        ),
        "caller seam order",
    )


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Fail-closed checker for NTRU+768 poly_frombytes in poly.c")
    parser.add_argument("--c-source", required=True, help="path to NTRU+/NTRU+768/poly.c")
    parser.add_argument("--kem-source", required=True, help="path to NTRU+/NTRU+768/kem.c")
    parser.add_argument("--self-check", action="store_true", help="also require representative bad mutations to be rejected")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        poly_text = Path(args.c_source).read_text(encoding="utf-8")
        kem_text = Path(args.kem_source).read_text(encoding="utf-8")
        verify_poly_frombytes_text(poly_text)
        verify_crypto_kem_dec_text(kem_text)
        if args.self_check:
            run_self_check(poly_text, kem_text)
    except (OSError, VerificationError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1

    if args.self_check:
        print("PASS: poly_frombytes checker rejected representative bad mutations")
    print("PASS: NTRU+768 poly_frombytes source structure and crypto_kem_dec seam")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
