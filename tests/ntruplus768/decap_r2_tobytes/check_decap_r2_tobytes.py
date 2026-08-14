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


def verify_kem_text(kem_text: str) -> None:
    body = compact(extract_function_body(kem_text, "crypto_kem_dec"))
    declaration = "uint8_t buf1[NTRUPLUS_POLYBYTES];"
    second_basemul = "poly_basemul(&r2, &c, &hinv);"
    serialization = "poly_tobytes(buf1, &r2);"
    hash_successor = "hash_g(buf2, buf1);"
    expected_chain = (
        "poly_sub(&c, &c, &m2); "
        f"{second_basemul} "
        f"{serialization} "
        f"{hash_successor}"
    )

    require(
        body.count(declaration) == 1,
        "crypto_kem_dec() must declare exactly one NTRUPLUS_POLYBYTES-sized buf1",
    )
    require(
        expected_chain in body,
        "crypto_kem_dec() must keep the verified poly_sub -> second poly_basemul -> "
        "r2 serialization seam immediately before hash_g",
    )
    require(
        body.count(second_basemul) == 1,
        "crypto_kem_dec() must contain exactly one second poly_basemul call",
    )
    require(
        body.count(serialization) == 1,
        "crypto_kem_dec() must contain exactly one poly_tobytes(buf1, &r2) call",
    )
    require(
        body.count(hash_successor) == 1,
        "crypto_kem_dec() must contain exactly one hash_g(buf2, buf1) successor call",
    )


def expect_rejected(kem_text: str, label: str) -> None:
    try:
        verify_kem_text(kem_text)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def replace_once(text: str, old: str, new: str, label: str) -> str:
    mutated = text.replace(old, new, 1)
    require(mutated != text, f"could not construct mutation: {label}")
    return mutated


def run_self_check(kem_text: str) -> None:
    verify_kem_text(kem_text)

    expect_rejected(
        replace_once(
            kem_text,
            "uint8_t buf1[NTRUPLUS_POLYBYTES];",
            "uint8_t buf1[NTRUPLUS_POLYBYTES - 1];",
            "buf1 extent",
        ),
        "buf1 extent",
    )
    expect_rejected(
        replace_once(
            kem_text,
            "poly_tobytes(buf1, &r2);",
            "poly_tobytes(buf2, &r2);",
            "serialization destination",
        ),
        "serialization destination",
    )
    expect_rejected(
        replace_once(
            kem_text,
            "poly_tobytes(buf1, &r2);",
            "poly_tobytes(buf1, &r1);",
            "serialization source",
        ),
        "serialization source",
    )
    expect_rejected(
        replace_once(
            kem_text,
            "    poly_tobytes(buf1, &r2);\n",
            "    poly_tobytes(buf1, &r2);\n    poly_tobytes(buf1, &r2);\n",
            "duplicate serialization",
        ),
        "duplicate serialization",
    )
    expect_rejected(
        replace_once(
            kem_text,
            "    poly_basemul(&r2, &c, &hinv);\n\n    poly_tobytes(buf1, &r2);\n",
            "    poly_tobytes(buf1, &r2);\n\n    poly_basemul(&r2, &c, &hinv);\n",
            "serialization order",
        ),
        "serialization order",
    )
    expect_rejected(
        replace_once(
            kem_text,
            "hash_g(buf2, buf1);",
            "hash_g(buf2, buf2);",
            "hash successor input",
        ),
        "hash successor input",
    )


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fail-closed checker for the NTRU+768 decap-r2 serialization seam",
    )
    parser.add_argument("--kem-source", required=True, help="path to NTRU+/NTRU+768/kem.c")
    parser.add_argument(
        "--self-check",
        action="store_true",
        help="also require representative bad source mutations to be rejected",
    )
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        kem_text = Path(args.kem_source).read_text(encoding="utf-8")
        verify_kem_text(kem_text)
        if args.self_check:
            run_self_check(kem_text)
    except (OSError, VerificationError) as exc:
        print(f"decap-r2 poly_tobytes checker failed: {exc}", file=sys.stderr)
        return 1

    print("decap-r2 poly_tobytes checker passed")
    if args.self_check:
        print("decap-r2 poly_tobytes checker self-check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
