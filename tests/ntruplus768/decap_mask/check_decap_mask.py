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


def require_exact_source_line(text: str, expected: str, message: str) -> None:
    require(sum(1 for line in text.splitlines() if line.strip() == expected) == 1, message)


def verify_params_text(params_text: str) -> None:
    require_single_line(
        params_text,
        r"^\s*#\s*define\s+NTRUPLUS_SSBYTES\s+32\s*$",
        "params.h must define NTRUPLUS_SSBYTES as exactly 32",
    )


def verify_kem_text(kem_text: str) -> None:
    require_single_line(
        kem_text,
        r"^\s*int\s+crypto_kem_dec\s*\(\s*uint8_t\s*\*\s*ss\s*,\s*const\s+uint8_t\s*\*\s*ct\s*,\s*const\s+uint8_t\s*\*\s*sk\s*\)\s*$",
        "crypto_kem_dec() must keep uint8_t output and input pointer types",
    )
    require_single_line(
        kem_text,
        r"^\s*int8_t\s+fail\s*;\s*$",
        "crypto_kem_dec() must declare fail as exactly int8_t fail;",
    )
    raw_body = extract_function_body(kem_text, "crypto_kem_dec")
    require_exact_source_line(
        raw_body,
        "uint8_t buf3[NTRUPLUS_POLYBYTES + NTRUPLUS_SYMBYTES];",
        "crypto_kem_dec() must keep buf3 as a uint8_t array",
    )
    require_exact_source_line(
        raw_body,
        "for (size_t i = 0; i < NTRUPLUS_SSBYTES; i++)",
        "crypto_kem_dec() must keep the exact NTRUPLUS_SSBYTES-bounded mask loop header",
    )
    require_exact_source_line(
        raw_body,
        "ss[i] = buf3[i] & ~(-fail);",
        "crypto_kem_dec() must keep the exact ss[i] = buf3[i] & ~(-fail) mask assignment",
    )

    body = compact(raw_body)
    verify_or = "fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);"
    mask_loop = "for (size_t i = 0; i < NTRUPLUS_SSBYTES; i++) ss[i] = buf3[i] & ~(-fail);"
    return_stmt = "return fail;"

    require(body.count(mask_loop) == 1, "crypto_kem_dec() must contain exactly one 32-byte ss mask loop")
    require(body.count(verify_or) == 1, "crypto_kem_dec() must contain exactly one fail |= verify(...) before masking")
    require(body.count(return_stmt) == 1, "crypto_kem_dec() must return fail exactly once")
    require(
        body.count(f"{verify_or} {mask_loop} {return_stmt}") == 1,
        "crypto_kem_dec() must keep the contiguous verify -> mask loop -> return fail tail",
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
        ("#define NTRUPLUS_SSBYTES   32", "#define NTRUPLUS_SSBYTES   31", "ssbytes parameter"),
    )
    for old, new, label in params_mutations:
        expect_rejected(replace_once(params_text, old, new, label), kem_text, label)

    seam_mutations = (
        (
            "int crypto_kem_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *sk)",
            "int crypto_kem_dec(int8_t *ss, const uint8_t *ct, const uint8_t *sk)",
            "shared-secret output type",
        ),
        (
            "uint8_t buf3[NTRUPLUS_POLYBYTES + NTRUPLUS_SYMBYTES];",
            "int8_t buf3[NTRUPLUS_POLYBYTES + NTRUPLUS_SYMBYTES];",
            "mask source type",
        ),
        ("int8_t fail;", "uint8_t fail;", "fail type"),
        (
            "fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);",
            "fail = verify(buf1, buf2, NTRUPLUS_POLYBYTES);",
            "verify overwrite",
        ),
        (
            "    for (size_t i = 0; i < NTRUPLUS_SSBYTES; i++)\n        ss[i] = buf3[i] & ~(-fail);\n",
            "    for (size_t i = 0; i < NTRUPLUS_SSBYTES - 1; i++)\n        ss[i] = buf3[i] & ~(-fail);\n",
            "mask loop bound",
        ),
        (
            "ss[i] = buf3[i] & ~(-fail);",
            "buf3[i] = ss[i] & ~(-fail);",
            "mask destination/source",
        ),
        (
            "ss[i] = buf3[i] & ~(-fail);",
            "ss[i] = buf3[i + 1] & ~(-fail);",
            "mask source index",
        ),
        (
            "ss[i] = buf3[i] & ~(-fail);",
            "ss[i] = buf3[i] & fail;",
            "mask expression",
        ),
        (
            "    fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);\n    \n    for (size_t i = 0; i < NTRUPLUS_SSBYTES; i++)\n        ss[i] = buf3[i] & ~(-fail);\n    \n    return fail;\n",
            "    for (size_t i = 0; i < NTRUPLUS_SSBYTES; i++)\n        ss[i] = buf3[i] & ~(-fail);\n    \n    fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);\n    \n    return fail;\n",
            "mask before verify",
        ),
        (
            "    fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);\n    \n    for (size_t i = 0; i < NTRUPLUS_SSBYTES; i++)\n",
            "    fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);\n    fail = 0;\n    \n    for (size_t i = 0; i < NTRUPLUS_SSBYTES; i++)\n",
            "failure byte reset before masking",
        ),
        (
            "    return fail;\n",
            "    return 0;\n",
            "return fail preservation",
        ),
    )
    for old, new, label in seam_mutations:
        expect_rejected(params_text, replace_once(kem_text, old, new, label), label)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fail-closed checker for the NTRU+768 post-verify ss mask loop",
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
        print(f"decap-mask checker failed: {exc}", file=sys.stderr)
        return 1

    print("decap-mask checker passed")
    if args.self_check:
        print("decap-mask checker self-check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
