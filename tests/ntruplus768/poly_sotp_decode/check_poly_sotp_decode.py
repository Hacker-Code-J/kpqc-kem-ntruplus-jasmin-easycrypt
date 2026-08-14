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
    match = re.search(rf"\bint\s+{name}\s*\([^)]*\)", text, flags=re.S)
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
        r"^\s*#\s*define\s+NTRUPLUS_N\s+768\s*$",
        "params.h must define NTRUPLUS_N as exactly 768",
    )
    require_single_line(
        params_text,
        r"^\s*#\s*define\s+NTRUPLUS_POLYBYTES\s+1152\s*$",
        "params.h must define NTRUPLUS_POLYBYTES as exactly 1152",
    )


def verify_header_text(header_text: str) -> None:
    require_single_line(
        header_text,
        r"^\s*int\s+poly_sotp_decode\s*\(\s*uint8_t\s+msg\[NTRUPLUS_N/8\]\s*,\s*const\s+poly\s+\*a\s*,\s*const\s+uint8_t\s+buf\[NTRUPLUS_N/4\]\s*\)\s*;\s*$",
        "poly.h must declare the exact poly_sotp_decode interface",
    )


def verify_poly_text(poly_text: str) -> None:
    signature = extract_function_signature(poly_text, "poly_sotp_decode")
    require(
        signature
        == "int poly_sotp_decode(uint8_t msg[NTRUPLUS_N/8], const poly *a, const uint8_t buf[NTRUPLUS_N/4])",
        f"unexpected poly_sotp_decode signature: {signature}",
    )

    body = compact(extract_function_body(poly_text, "poly_sotp_decode"))
    expected_body = compact(
        """
        uint8_t t1, t2, t3;
        uint16_t t4;
        uint32_t r = 0;
        uint8_t mask;

        for(size_t i = 0; i < NTRUPLUS_N / 8; i++)
        {
            t1 = buf[i                 ];
            t2 = buf[i + NTRUPLUS_N / 8];
            t3 = 0;

            for(size_t j = 0; j < 8; j++)
            {
                t4 = t2 & 0x1;
                t4 += a->coeffs[8*i + j];
                r |= t4;
                t4 = (t4 ^ t1) & 0x1;
                t3 ^= (uint8_t)(t4 << j);

                t1 >>= 1;
                t2 >>= 1;
            }

            msg[i] = t3;
        }

        r = r >> 1;
        r = (-(uint32_t)r) >> 31;

        mask = (uint8_t)(r - 1);

        for (size_t i = 0; i < NTRUPLUS_N / 8; i++)
            msg[i] &= mask;

        return r;
        """
    )
    require(
        body == expected_body,
        "poly_sotp_decode() must keep the exact authoritative decode loop and fail-masking tail",
    )


def verify_kem_text(kem_text: str) -> None:
    body = compact(extract_function_body(kem_text, "crypto_kem_dec"))
    expected_chain = "poly_tobytes(buf1, &r2); hash_g(buf2, buf1); fail = poly_sotp_decode(msg, &m1, buf2);"
    require(
        expected_chain in body,
        "crypto_kem_dec() must keep poly_tobytes -> hash_g -> poly_sotp_decode order",
    )
    require(
        body.count("fail = poly_sotp_decode(msg, &m1, buf2);") == 1,
        "crypto_kem_dec() must contain exactly one poly_sotp_decode(msg, &m1, buf2) call",
    )


def verify_all(params_text: str, poly_text: str, header_text: str, kem_text: str) -> None:
    verify_params_text(params_text)
    verify_header_text(header_text)
    verify_poly_text(poly_text)
    verify_kem_text(kem_text)


def replace_once(text: str, old: str, new: str, label: str) -> str:
    mutated = text.replace(old, new, 1)
    require(mutated != text, f"could not construct mutation: {label}")
    return mutated


def expect_rejected(
    params_text: str,
    poly_text: str,
    header_text: str,
    kem_text: str,
    label: str,
) -> None:
    try:
        verify_all(params_text, poly_text, header_text, kem_text)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(params_text: str, poly_text: str, header_text: str, kem_text: str) -> None:
    verify_all(params_text, poly_text, header_text, kem_text)

    params_mutations = (
        ("#define NTRUPLUS_N 768", "#define NTRUPLUS_N 864", "N parameter"),
        ("#define NTRUPLUS_POLYBYTES 1152", "#define NTRUPLUS_POLYBYTES 1151", "polybytes parameter"),
    )
    for old, new, label in params_mutations:
        expect_rejected(
            replace_once(params_text, old, new, label),
            poly_text,
            header_text,
            kem_text,
            label,
        )

    expect_rejected(
        params_text,
        poly_text,
        replace_once(
            header_text,
            "int  poly_sotp_decode(uint8_t msg[NTRUPLUS_N/8], const poly *a, const uint8_t buf[NTRUPLUS_N/4]);",
            "int  poly_sotp_decode(uint8_t msg[NTRUPLUS_N/8], poly *a, const uint8_t buf[NTRUPLUS_N/4]);",
            "header lost const input",
        ),
        kem_text,
        "header lost const input",
    )

    poly_mutations = (
        (
            "t1 = buf[i                 ];\n\t\tt2 = buf[i + NTRUPLUS_N / 8];\n\t\tt3 = 0;",
            "t1 = buf[i                 ];\n\t\tt2 = buf[i + NTRUPLUS_N / 8 + 1];\n\t\tt3 = 0;",
            "tail-byte offset",
        ),
        ("r |= t4;", "r ^= t4;", "accumulator operator"),
        ("t4 = (t4 ^ t1) & 0x1;", "t4 = (t4 | t1) & 0x1;", "bit recovery operator"),
        ("r = r >> 1;", "r = r >> 2;", "failure fold"),
        ("mask = (uint8_t)(r - 1);", "mask = (uint8_t)(r + 1);", "mask derivation"),
        ("msg[i] &= mask;", "msg[i] ^= mask;", "fail-closed masking"),
    )
    for old, new, label in poly_mutations:
        expect_rejected(
            params_text,
            replace_once(poly_text, old, new, label),
            header_text,
            kem_text,
            label,
        )

    kem_mutations = (
        ("fail = poly_sotp_decode(msg, &m1, buf2);", "fail = poly_sotp_decode(msg, &m1, buf1);", "wrong decode input"),
        (
            "    fail = poly_sotp_decode(msg, &m1, buf2);\n",
            "    fail = poly_sotp_decode(msg, &m1, buf2);\n    fail = poly_sotp_decode(msg, &m1, buf2);\n",
            "duplicate decode call",
        ),
        (
            "    hash_g(buf2, buf1);\n    fail = poly_sotp_decode(msg, &m1, buf2);\n",
            "    fail = poly_sotp_decode(msg, &m1, buf2);\n    hash_g(buf2, buf1);\n",
            "decode before hash",
        ),
    )
    for old, new, label in kem_mutations:
        expect_rejected(
            params_text,
            poly_text,
            header_text,
            replace_once(kem_text, old, new, label),
            label,
        )


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fail-closed checker for the NTRU+768 poly_sotp_decode source seam",
    )
    parser.add_argument("--params-source", required=True)
    parser.add_argument("--poly-source", required=True)
    parser.add_argument("--poly-header", required=True)
    parser.add_argument("--kem-source", required=True)
    parser.add_argument("--self-check", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        params_text = Path(args.params_source).read_text(encoding="utf-8")
        poly_text = Path(args.poly_source).read_text(encoding="utf-8")
        header_text = Path(args.poly_header).read_text(encoding="utf-8")
        kem_text = Path(args.kem_source).read_text(encoding="utf-8")
        if args.self_check:
            run_self_check(params_text, poly_text, header_text, kem_text)
        else:
            verify_all(params_text, poly_text, header_text, kem_text)
    except (OSError, VerificationError) as exc:
        print(f"poly_sotp_decode checker failed: {exc}", file=sys.stderr)
        return 1

    mode = "self-check passed" if args.self_check else "source check passed"
    print(f"poly_sotp_decode {mode}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
