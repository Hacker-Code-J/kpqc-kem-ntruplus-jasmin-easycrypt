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
        r"^\s*#\s*define\s+NTRUPLUS_SYMBYTES\s+32\s*$",
        "params.h must define NTRUPLUS_SYMBYTES as exactly 32",
    )
    require_single_line(
        params_text,
        r"^\s*#\s*define\s+NTRUPLUS_POLYBYTES\s+1152\s*$",
        "params.h must define NTRUPLUS_POLYBYTES as exactly 1152",
    )
    require_single_line(
        params_text,
        r"^\s*#\s*define\s+NTRUPLUS_SECRETKEYBYTES\s+\(\(NTRUPLUS_POLYBYTES\s*<<\s*1\)\s*\+\s*NTRUPLUS_SYMBYTES\)\s*$",
        "params.h must keep the exact secret-key length formula",
    )


def verify_symmetric_text(symmetric_text: str) -> None:
    require_single_line(
        symmetric_text,
        r"^\s*#\s*define\s+HASH_F_INBYTES\s+\(NTRUPLUS_POLYBYTES\)\s*$",
        "HASH_F_INBYTES must be exactly NTRUPLUS_POLYBYTES",
    )
    require_single_line(
        symmetric_text,
        r"^\s*#\s*define\s+HASH_F_OUTBYTES\s+\(32\)\s*$",
        "HASH_F_OUTBYTES must be exactly 32",
    )
    require_single_line(
        symmetric_text,
        r"^\s*void\s+hash_f\s*\(\s*uint8_t\s*\*\s*buf\s*,\s*const\s+uint8_t\s*\*\s*msg\s*\)\s*$",
        "hash_f must keep its exact output/input signature",
    )

    body = compact(extract_function_body(symmetric_text, "hash_f"))
    expected_body = compact(
        """
        uint8_t data[1 + HASH_F_INBYTES];
        data[0] = 0x00;
        memcpy(data + 1, msg, HASH_F_INBYTES);
        shake256(buf, HASH_F_OUTBYTES, data, HASH_F_INBYTES + 1);
        """
    )
    require(
        body == expected_body,
        "hash_f must be exactly SHAKE256(0x00 || pk, 32 bytes)",
    )


def verify_header_text(header_text: str) -> None:
    require_single_line(
        header_text,
        r"^\s*void\s+hash_f\s*\(\s*uint8_t\s*\*\s*buf\s*,\s*const\s+uint8_t\s*\*\s*msg\s*\)\s*;\s*$",
        "symmetric.h must declare the exact hash_f interface",
    )


def verify_kem_text(kem_text: str) -> None:
    keypair_body = compact(
        extract_function_body(kem_text, "crypto_kem_keypair_derand"),
    )
    decap_body = compact(extract_function_body(kem_text, "crypto_kem_dec"))
    hash_f_store = "hash_f(sk + 2 * NTRUPLUS_POLYBYTES, pk);"
    suffix_loop = (
        "for (size_t i = 0; i < NTRUPLUS_SYMBYTES; i++) "
        "msg[i + NTRUPLUS_N / 8] = sk[i + 2 * NTRUPLUS_POLYBYTES];"
    )
    hash_h_call = "hash_h(buf3, msg);"

    require(
        keypair_body.count(hash_f_store) == 1,
        "crypto_kem_keypair_derand() must write hash_f at "
        "sk + 2 * NTRUPLUS_POLYBYTES exactly once",
    )
    require(
        decap_body.count(suffix_loop) == 1,
        "crypto_kem_dec() must copy exactly 32 suffix bytes from "
        "sk + 2 * NTRUPLUS_POLYBYTES into msg[96..127]",
    )
    require(
        decap_body.count(hash_h_call) == 1,
        "crypto_kem_dec() must call hash_h(buf3, msg) exactly once",
    )
    require(
        f"{suffix_loop} {hash_h_call}" in decap_body,
        "crypto_kem_dec() must keep suffix copy immediately before hash_h",
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
        (
            "#define NTRUPLUS_SYMBYTES  32",
            "#define NTRUPLUS_SYMBYTES  31",
            "symbytes parameter",
        ),
        (
            "#define NTRUPLUS_POLYBYTES 1152",
            "#define NTRUPLUS_POLYBYTES 1151",
            "polybytes parameter",
        ),
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
        ("data[0] = 0x00;", "data[0] = 0x01;", "domain byte"),
        (
            "memcpy(data + 1, msg, HASH_F_INBYTES);",
            "memcpy(data + 1, msg, HASH_F_INBYTES - 1);",
            "payload length",
        ),
        (
            "memcpy(data + 1, msg, HASH_F_INBYTES);",
            "memcpy(data, msg, HASH_F_INBYTES);",
            "payload offset",
        ),
        (
            "shake256(buf, HASH_F_OUTBYTES, data, HASH_F_INBYTES + 1);",
            "shake256(buf, HASH_F_OUTBYTES - 1, data, HASH_F_INBYTES + 1);",
            "SHAKE output length",
        ),
        (
            "shake256(buf, HASH_F_OUTBYTES, data, HASH_F_INBYTES + 1);",
            "shake256(buf, HASH_F_OUTBYTES, data, HASH_F_INBYTES);",
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
            "void hash_f(uint8_t *buf, const uint8_t *msg);",
            "void hash_f(uint8_t *msg, const uint8_t *buf);",
            "header signature",
        ),
        kem_text,
        "header signature",
    )

    kem_mutations = (
        (
            "hash_f(sk + 2 * NTRUPLUS_POLYBYTES, pk);",
            "hash_f(sk + NTRUPLUS_POLYBYTES, pk);",
            "keypair suffix offset",
        ),
        (
            "hash_f(sk + 2 * NTRUPLUS_POLYBYTES, pk);",
            "hash_f(pk, sk + 2 * NTRUPLUS_POLYBYTES);",
            "keypair hash_f args",
        ),
        (
            "msg[i + NTRUPLUS_N / 8] = sk[i + 2 * NTRUPLUS_POLYBYTES];",
            "msg[i] = sk[i + 2 * NTRUPLUS_POLYBYTES];",
            "decap destination offset",
        ),
        (
            "msg[i + NTRUPLUS_N / 8] = sk[i + 2 * NTRUPLUS_POLYBYTES];",
            "msg[i + NTRUPLUS_N / 8] = sk[i + NTRUPLUS_POLYBYTES];",
            "decap source offset",
        ),
        (
            "for (size_t i = 0; i < NTRUPLUS_SYMBYTES; i++)",
            "for (size_t i = 0; i < NTRUPLUS_SYMBYTES - 1; i++)",
            "decap copy length",
        ),
        (
            "    for (size_t i = 0; i < NTRUPLUS_SYMBYTES; i++)\n"
            "        msg[i + NTRUPLUS_N / 8] = "
            "sk[i + 2 * NTRUPLUS_POLYBYTES];\n"
            "    \n"
            "    hash_h(buf3, msg);\n",
            "    hash_h(buf3, msg);\n"
            "    \n"
            "    for (size_t i = 0; i < NTRUPLUS_SYMBYTES; i++)\n"
            "        msg[i + NTRUPLUS_N / 8] = "
            "sk[i + 2 * NTRUPLUS_POLYBYTES];\n",
            "copy/hash_h order",
        ),
        (
            "    hash_f(sk + 2 * NTRUPLUS_POLYBYTES, pk);\n",
            "    hash_f(sk + 2 * NTRUPLUS_POLYBYTES, pk);\n"
            "    hash_f(sk + 2 * NTRUPLUS_POLYBYTES, pk);\n",
            "duplicate keypair suffix hash",
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
        description=(
            "Fail-closed checker for the NTRU+768 hash_f suffix "
            "generation and decap copy seam"
        ),
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
        print(f"keygen-hash-f checker failed: {exc}", file=sys.stderr)
        return 1

    print("keygen-hash-f checker passed")
    if args.self_check:
        print("keygen-hash-f checker self-check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
