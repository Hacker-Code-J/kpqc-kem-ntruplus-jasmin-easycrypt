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


def verify_symmetric_text(symmetric_text: str) -> None:
    require_single_line(
        symmetric_text,
        r"^\s*#\s*define\s+HASH_G_INBYTES\s+\(NTRUPLUS_POLYBYTES\)\s*$",
        "HASH_G_INBYTES must be exactly NTRUPLUS_POLYBYTES",
    )
    require_single_line(
        symmetric_text,
        r"^\s*#\s*define\s+HASH_G_OUTBYTES\s+\(NTRUPLUS_N\s*/\s*4\)\s*$",
        "HASH_G_OUTBYTES must be exactly NTRUPLUS_N / 4",
    )
    require_single_line(
        symmetric_text,
        r"^\s*void\s+hash_g\s*\(\s*uint8_t\s*\*\s*buf\s*,\s*const\s+uint8_t\s*\*\s*msg\s*\)\s*$",
        "hash_g must keep its exact output/input signature",
    )

    body = compact(extract_function_body(symmetric_text, "hash_g"))
    expected_body = compact(
        """
        uint8_t data[1 + HASH_G_INBYTES];
        data[0] = 0x01;
        memcpy(data + 1, msg, HASH_G_INBYTES);
        shake256(buf, HASH_G_OUTBYTES, data, HASH_G_INBYTES + 1);
        """
    )
    require(
        body == expected_body,
        "hash_g must be exactly SHAKE256(0x01 || msg, 192 bytes)",
    )


def verify_header_text(header_text: str) -> None:
    require_single_line(
        header_text,
        r"^\s*void\s+hash_g\s*\(\s*uint8_t\s*\*\s*buf\s*,\s*const\s+uint8_t\s*\*\s*msg\s*\)\s*;\s*$",
        "symmetric.h must declare the exact hash_g interface",
    )


def verify_kem_text(kem_text: str) -> None:
    body = compact(extract_function_body(kem_text, "crypto_kem_dec"))
    buf1_decl = "uint8_t buf1[NTRUPLUS_POLYBYTES];"
    buf2_decl = "uint8_t buf2[NTRUPLUS_POLYBYTES];"
    serialization = "poly_tobytes(buf1, &r2);"
    hash_call = "hash_g(buf2, buf1);"
    decode_successor = "fail = poly_sotp_decode(msg, &m1, buf2);"
    expected_chain = f"{serialization} {hash_call} {decode_successor}"

    require(body.count(buf1_decl) == 1, "crypto_kem_dec() must declare one 1152-byte buf1")
    require(body.count(buf2_decl) == 1, "crypto_kem_dec() must declare one 1152-byte buf2")
    require(
        expected_chain in body,
        "crypto_kem_dec() must keep poly_tobytes -> hash_g -> poly_sotp_decode order",
    )
    require(body.count(serialization) == 1, "crypto_kem_dec() must serialize r2 exactly once")
    require(body.count(hash_call) == 1, "crypto_kem_dec() must call hash_g(buf2, buf1) exactly once")
    require(
        body.count(decode_successor) == 1,
        "crypto_kem_dec() must pass the hash_g output to poly_sotp_decode exactly once",
    )


def verify_all(
    params_text: str,
    symmetric_text: str,
    header_text: str,
    kem_text: str,
) -> None:
    verify_params_text(params_text)
    verify_symmetric_text(symmetric_text)
    verify_header_text(header_text)
    verify_kem_text(kem_text)


def replace_once(text: str, old: str, new: str, label: str) -> str:
    mutated = text.replace(old, new, 1)
    require(mutated != text, f"could not construct mutation: {label}")
    return mutated


def expect_rejected(
    params_text: str,
    symmetric_text: str,
    header_text: str,
    kem_text: str,
    label: str,
) -> None:
    try:
        verify_all(params_text, symmetric_text, header_text, kem_text)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(
    params_text: str,
    symmetric_text: str,
    header_text: str,
    kem_text: str,
) -> None:
    verify_all(params_text, symmetric_text, header_text, kem_text)

    params_mutations = (
        ("#define NTRUPLUS_N 768", "#define NTRUPLUS_N 864", "N parameter"),
        ("#define NTRUPLUS_POLYBYTES 1152", "#define NTRUPLUS_POLYBYTES 1151", "input length"),
    )
    for old, new, label in params_mutations:
        expect_rejected(
            replace_once(params_text, old, new, label),
            symmetric_text,
            header_text,
            kem_text,
            label,
        )

    symmetric_mutations = (
        (
            "#define HASH_G_INBYTES  (NTRUPLUS_POLYBYTES)",
            "#define HASH_G_INBYTES  (NTRUPLUS_POLYBYTES - 1)",
            "hash input extent",
        ),
        (
            "#define HASH_G_OUTBYTES (NTRUPLUS_N / 4)",
            "#define HASH_G_OUTBYTES (NTRUPLUS_N / 8)",
            "hash output extent",
        ),
        ("data[0] = 0x01;", "data[0] = 0x02;", "domain byte"),
        ("memcpy(data + 1, msg, HASH_G_INBYTES);", "memcpy(data, msg, HASH_G_INBYTES);", "payload offset"),
        (
            "memcpy(data + 1, msg, HASH_G_INBYTES);",
            "memcpy(data + 1, msg, HASH_G_INBYTES - 1);",
            "payload length",
        ),
        (
            "shake256(buf, HASH_G_OUTBYTES, data, HASH_G_INBYTES + 1);",
            "shake256(buf, HASH_G_OUTBYTES - 1, data, HASH_G_INBYTES + 1);",
            "SHAKE output length",
        ),
        (
            "shake256(buf, HASH_G_OUTBYTES, data, HASH_G_INBYTES + 1);",
            "shake256(buf, HASH_G_OUTBYTES, data, HASH_G_INBYTES);",
            "SHAKE input length",
        ),
    )
    for old, new, label in symmetric_mutations:
        expect_rejected(
            params_text,
            replace_once(symmetric_text, old, new, label),
            header_text,
            kem_text,
            label,
        )

    expect_rejected(
        params_text,
        symmetric_text,
        replace_once(
            header_text,
            "void hash_g(uint8_t *buf, const uint8_t *msg);",
            "void hash_g(uint8_t *buf, uint8_t *msg);",
            "header signature",
        ),
        kem_text,
        "header signature",
    )

    kem_mutations = (
        ("hash_g(buf2, buf1);", "hash_g(buf1, buf2);", "caller arguments"),
        (
            "    hash_g(buf2, buf1);\n",
            "    hash_g(buf2, buf1);\n    hash_g(buf2, buf1);\n",
            "duplicate hash call",
        ),
        (
            "    poly_tobytes(buf1, &r2);\n    hash_g(buf2, buf1);\n",
            "    hash_g(buf2, buf1);\n    poly_tobytes(buf1, &r2);\n",
            "hash call order",
        ),
        (
            "fail = poly_sotp_decode(msg, &m1, buf2);",
            "fail = poly_sotp_decode(msg, &m1, buf1);",
            "decode hash input",
        ),
    )
    for old, new, label in kem_mutations:
        expect_rejected(
            params_text,
            symmetric_text,
            header_text,
            replace_once(kem_text, old, new, label),
            label,
        )


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fail-closed checker for the NTRU+768 decapsulation hash_g seam",
    )
    parser.add_argument("--params-source", required=True)
    parser.add_argument("--symmetric-source", required=True)
    parser.add_argument("--symmetric-header", required=True)
    parser.add_argument("--kem-source", required=True)
    parser.add_argument("--self-check", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        params_text = Path(args.params_source).read_text(encoding="utf-8")
        symmetric_text = Path(args.symmetric_source).read_text(encoding="utf-8")
        header_text = Path(args.symmetric_header).read_text(encoding="utf-8")
        kem_text = Path(args.kem_source).read_text(encoding="utf-8")
        verify_all(params_text, symmetric_text, header_text, kem_text)
        if args.self_check:
            run_self_check(params_text, symmetric_text, header_text, kem_text)
    except (OSError, VerificationError) as exc:
        print(f"decap hash_g checker failed: {exc}", file=sys.stderr)
        return 1

    print("decap hash_g checker passed")
    if args.self_check:
        print("decap hash_g checker self-check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
