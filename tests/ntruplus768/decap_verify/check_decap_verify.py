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
    return re.sub(r"\s+", " ", strip_comments(text)).strip()


def extract_function_signature(text: str, name: str) -> str:
    match = re.search(rf"\b(?:static\s+inline\s+)?int\s+{name}\s*\([^)]*\)", text, flags=re.S)
    require(match is not None, f"could not find signature for `{name}`")
    return compact(match.group(0))


def extract_function_body(text: str, name: str) -> str:
    matches = list(re.finditer(rf"\b{name}\s*\([^)]*\)[^{{;]*\{{", text))
    require(len(matches) == 1, f"expected exactly one definition of `{name}`")
    start = matches[0].end() - 1
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1 : index]
    raise VerificationError(f"unterminated body for function `{name}`")


def require_single_line(text: str, pattern: str, message: str) -> None:
    require(len(re.findall(pattern, strip_comments(text), flags=re.M)) == 1, message)


def verify_params_text(params_text: str) -> None:
    require_single_line(
        params_text,
        r"^\s*#\s*define\s+NTRUPLUS_POLYBYTES\s+1152\s*$",
        "params.h must define NTRUPLUS_POLYBYTES as exactly 1152",
    )


def verify_kem_text(kem_text: str) -> None:
    verify_signature = extract_function_signature(kem_text, "verify")
    require(
        verify_signature == "static inline int verify(const uint8_t *a, const uint8_t *b, size_t len)",
        f"unexpected verify() signature: {verify_signature}",
    )

    verify_body = compact(extract_function_body(kem_text, "verify"))
    expected_verify = (
        "uint8_t acc = 0; "
        "for (size_t i = 0; i < len; i++) "
        "acc |= (uint8_t)(a[i] ^ b[i]); "
        "return (-(uint64_t)acc) >> 63;"
    )
    require(
        verify_body == expected_verify,
        "verify() must keep the exact fixed-length XOR-accumulate reduction",
    )

    decap_body = compact(extract_function_body(kem_text, "crypto_kem_dec"))
    tobytes_call = "poly_tobytes(buf2, &r1);"
    verify_call = "fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);"
    require(
        decap_body.count(tobytes_call) == 1,
        "crypto_kem_dec() must serialize r1 into buf2 exactly once before verify",
    )
    require(
        decap_body.count(verify_call) == 1,
        "crypto_kem_dec() must call fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES) exactly once",
    )
    require(
        f"{tobytes_call} {verify_call}" in decap_body,
        "crypto_kem_dec() must keep the exact poly_tobytes(buf2, &r1) -> fail |= verify(...) seam",
    )


def verify_all(params_text: str, kem_text: str) -> None:
    verify_params_text(params_text)
    verify_kem_text(kem_text)


def replace_once(text: str, old: str, new: str, label: str) -> str:
    mutated = text.replace(old, new, 1)
    require(mutated != text, f"could not construct mutation: {label}")
    return mutated


def expect_rejected(params_text: str, kem_text: str, label: str) -> None:
    try:
        verify_all(params_text, kem_text)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(params_text: str, kem_text: str) -> None:
    verify_all(params_text, kem_text)

    params_mutations = (
        ("#define NTRUPLUS_POLYBYTES 1152", "#define NTRUPLUS_POLYBYTES 1151", "polybytes parameter"),
    )
    for old, new, label in params_mutations:
        expect_rejected(replace_once(params_text, old, new, label), kem_text, label)

    verify_mutations = (
        (
            "static inline int verify(const uint8_t *a, const uint8_t *b, size_t len)",
            "static inline int verify(uint8_t *a, const uint8_t *b, size_t len)",
            "verify const qualifier",
        ),
        ("uint8_t acc = 0;", "uint8_t acc = 1;", "verify accumulator init"),
        ("i < len", "i < len - 1", "verify loop bound"),
        ("acc |= (uint8_t)(a[i] ^ b[i]);", "acc ^= (uint8_t)(a[i] ^ b[i]);", "verify reduction operator"),
        ("a[i] ^ b[i]", "a[i] - b[i]", "verify byte comparison"),
        ("return (-(uint64_t)acc) >> 63;", "return acc;", "verify return normalization"),
    )
    for old, new, label in verify_mutations:
        expect_rejected(params_text, replace_once(kem_text, old, new, label), label)

    seam_mutations = (
        (
            "fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);",
            "fail |= verify(buf2, buf1, NTRUPLUS_POLYBYTES);",
            "verify argument order",
        ),
        (
            "fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);",
            "fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES - 1);",
            "verify length",
        ),
        (
            "fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);",
            "fail = verify(buf1, buf2, NTRUPLUS_POLYBYTES);",
            "verify fail accumulation",
        ),
        (
            "    poly_tobytes(buf2, &r1);\n    \n    fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);\n",
            "    fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);\n    \n    poly_tobytes(buf2, &r1);\n",
            "tobytes/verify order",
        ),
        (
            "    fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);\n",
            "    fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);\n    fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);\n",
            "duplicate verify call",
        ),
    )
    for old, new, label in seam_mutations:
        expect_rejected(params_text, replace_once(kem_text, old, new, label), label)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fail-closed checker for the NTRU+768 verify helper and decapsulation compare seam",
    )
    parser.add_argument("--params-source", required=True, help="path to NTRU+/NTRU+768/params.h")
    parser.add_argument("--kem-source", required=True, help="path to NTRU+/NTRU+768/kem.c")
    parser.add_argument("--self-check", action="store_true", help="also require representative bad mutations to be rejected")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        params_text = Path(args.params_source).read_text(encoding="utf-8")
        kem_text = Path(args.kem_source).read_text(encoding="utf-8")
        verify_all(params_text, kem_text)
        if args.self_check:
            run_self_check(params_text, kem_text)
    except (OSError, VerificationError) as exc:
        print(f"decap-verify checker failed: {exc}", file=sys.stderr)
        return 1

    print("decap-verify checker passed")
    if args.self_check:
        print("decap-verify checker self-check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
