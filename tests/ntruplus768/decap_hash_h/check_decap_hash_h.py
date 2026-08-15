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
        r"^\s*#\s*define\s+NTRUPLUS_SSBYTES\s+32\s*$",
        "params.h must define NTRUPLUS_SSBYTES as exactly 32",
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
        r"^\s*#\s*define\s+HASH_H_INBYTES\s+\(NTRUPLUS_N\s*/\s*8\s*\+\s*NTRUPLUS_SYMBYTES\)\s*$",
        "HASH_H_INBYTES must be exactly NTRUPLUS_N / 8 + NTRUPLUS_SYMBYTES",
    )
    require_single_line(
        symmetric_text,
        r"^\s*#\s*define\s+HASH_H_OUTBYTES\s+\(NTRUPLUS_SSBYTES\s*\+\s*NTRUPLUS_N\s*/\s*4\)\s*$",
        "HASH_H_OUTBYTES must be exactly NTRUPLUS_SSBYTES + NTRUPLUS_N / 4",
    )
    require_single_line(
        symmetric_text,
        r"^\s*void\s+hash_h\s*\(\s*uint8_t\s*\*\s*buf\s*,\s*const\s+uint8_t\s*\*\s*msg\s*\)\s*$",
        "hash_h must keep its exact output/input signature",
    )

    body = compact(extract_function_body(symmetric_text, "hash_h"))
    expected_body = compact(
        """
        uint8_t data[1 + HASH_H_INBYTES];
        data[0] = 0x02;
        memcpy(data + 1, msg, HASH_H_INBYTES);
        shake256(buf, HASH_H_OUTBYTES, data, HASH_H_INBYTES + 1);
        """
    )
    require(
        body == expected_body,
        "hash_h must be exactly SHAKE256(0x02 || msg, 224 bytes)",
    )


def verify_header_text(header_text: str) -> None:
    require_single_line(
        header_text,
        r"^\s*void\s+hash_h\s*\(\s*uint8_t\s*\*\s*buf\s*,\s*const\s+uint8_t\s*\*\s*msg\s*\)\s*;\s*$",
        "symmetric.h must declare the exact hash_h interface",
    )


def verify_kem_text(kem_text: str) -> None:
    body = compact(extract_function_body(kem_text, "crypto_kem_dec"))
    keygen_body = compact(extract_function_body(kem_text, "crypto_kem_keypair_derand"))
    msg_decl = "uint8_t msg[NTRUPLUS_N / 8 + NTRUPLUS_SYMBYTES];"
    buf3_decl = "uint8_t buf3[NTRUPLUS_POLYBYTES + NTRUPLUS_SYMBYTES];"
    decode_call = "fail = poly_sotp_decode(msg, &m1, buf2);"
    suffix_loop = (
        "for (size_t i = 0; i < NTRUPLUS_SYMBYTES; i++) "
        "msg[i + NTRUPLUS_N / 8] = sk[i + 2 * NTRUPLUS_POLYBYTES];"
    )
    hash_call = "hash_h(buf3, msg);"
    cbd_call = "poly_cbd1(&r1, buf3 + NTRUPLUS_SSBYTES);"
    expected_chain = f"{decode_call} {suffix_loop} {hash_call} {cbd_call}"
    keygen_marker = "hash_f(sk + 2 * NTRUPLUS_POLYBYTES, pk);"

    require(body.count(msg_decl) == 1, "crypto_kem_dec() must declare one 96 + 32-byte msg buffer")
    require(body.count(buf3_decl) == 1, "crypto_kem_dec() must declare one buf3 sized as 1152 + 32")
    require(body.count(decode_call) == 1, "crypto_kem_dec() must decode with poly_sotp_decode exactly once")
    require(body.count(suffix_loop) == 1, "crypto_kem_dec() must copy exactly 32 secret-key suffix bytes into msg[96..127]")
    require(body.count(hash_call) == 1, "crypto_kem_dec() must call hash_h(buf3, msg) exactly once")
    require(body.count(cbd_call) == 1, "crypto_kem_dec() must feed buf3 + NTRUPLUS_SSBYTES into poly_cbd1 exactly once")
    require(expected_chain in body, "crypto_kem_dec() must keep decode -> suffix copy -> hash_h -> poly_cbd1 ordering")
    require(
        keygen_body.count(keygen_marker) == 1 and kem_text.count(keygen_marker) == 1,
        "crypto_kem_keypair_derand() must write the source-only hash_f suffix marker exactly once",
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


def replace_last_once(text: str, old: str, new: str, label: str) -> str:
    prefix, separator, suffix = text.rpartition(old)
    require(bool(separator), f"could not construct mutation: {label}")
    return prefix + new + suffix


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
        ("#define NTRUPLUS_SYMBYTES  32", "#define NTRUPLUS_SYMBYTES  31", "symbytes parameter"),
        ("#define NTRUPLUS_SSBYTES   32", "#define NTRUPLUS_SSBYTES   31", "ssbytes parameter"),
        ("#define NTRUPLUS_POLYBYTES 1152", "#define NTRUPLUS_POLYBYTES 1151", "polybytes parameter"),
        (
            "#define NTRUPLUS_SECRETKEYBYTES  ((NTRUPLUS_POLYBYTES << 1) + NTRUPLUS_SYMBYTES)",
            "#define NTRUPLUS_SECRETKEYBYTES  ((NTRUPLUS_POLYBYTES << 1) + NTRUPLUS_SSBYTES)",
            "secret-key formula",
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
        (
            "#define HASH_H_INBYTES  (NTRUPLUS_N / 8 + NTRUPLUS_SYMBYTES)",
            "#define HASH_H_INBYTES  (NTRUPLUS_N / 8)",
            "hash input extent",
        ),
        (
            "#define HASH_H_OUTBYTES (NTRUPLUS_SSBYTES + NTRUPLUS_N / 4)",
            "#define HASH_H_OUTBYTES (NTRUPLUS_N / 4)",
            "hash output extent",
        ),
        ("data[0] = 0x02;", "data[0] = 0x01;", "domain byte"),
        ("memcpy(data + 1, msg, HASH_H_INBYTES);", "memcpy(data, msg, HASH_H_INBYTES);", "payload offset"),
        (
            "memcpy(data + 1, msg, HASH_H_INBYTES);",
            "memcpy(data + 1, msg, HASH_H_INBYTES - 1);",
            "payload length",
        ),
        (
            "shake256(buf, HASH_H_OUTBYTES, data, HASH_H_INBYTES + 1);",
            "shake256(buf, HASH_H_OUTBYTES - 1, data, HASH_H_INBYTES + 1);",
            "SHAKE output length",
        ),
        (
            "shake256(buf, HASH_H_OUTBYTES, data, HASH_H_INBYTES + 1);",
            "shake256(buf, HASH_H_OUTBYTES, data, HASH_H_INBYTES);",
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
            "void hash_h(uint8_t *buf, const uint8_t *msg);",
            "void hash_h(uint8_t *msg, const uint8_t *buf);",
            "header signature",
        ),
        kem_text,
        "header signature",
    )

    expect_rejected(
        params_text,
        symmetric_text,
        header_text,
        replace_last_once(
            kem_text,
            "uint8_t msg[NTRUPLUS_N / 8 + NTRUPLUS_SYMBYTES];",
            "uint8_t msg[NTRUPLUS_N / 8];",
            "decapsulation message buffer extent",
        ),
        "decapsulation message buffer extent",
    )

    kem_mutations = (
        (
            "uint8_t buf3[NTRUPLUS_POLYBYTES + NTRUPLUS_SYMBYTES];",
            "uint8_t buf3[NTRUPLUS_POLYBYTES];",
            "hash output buffer extent",
        ),
        (
            "hash_f(sk + 2 * NTRUPLUS_POLYBYTES, pk);",
            "hash_f(sk + NTRUPLUS_POLYBYTES, pk);",
            "keygen suffix offset",
        ),
        ("hash_h(buf3, msg);", "hash_h(msg, buf3);", "caller arguments"),
        (
            "    hash_h(buf3, msg);\n",
            "    hash_h(buf3, msg);\n    hash_h(buf3, msg);\n",
            "duplicate hash call",
        ),
        (
            "    fail = poly_sotp_decode(msg, &m1, buf2);\n    \n    for (size_t i = 0; i < NTRUPLUS_SYMBYTES; i++)\n        msg[i + NTRUPLUS_N / 8] = sk[i + 2 * NTRUPLUS_POLYBYTES];\n    \n    hash_h(buf3, msg);\n",
            "    hash_h(buf3, msg);\n    \n    fail = poly_sotp_decode(msg, &m1, buf2);\n    \n    for (size_t i = 0; i < NTRUPLUS_SYMBYTES; i++)\n        msg[i + NTRUPLUS_N / 8] = sk[i + 2 * NTRUPLUS_POLYBYTES];\n",
            "hash call order",
        ),
        (
            "for (size_t i = 0; i < NTRUPLUS_SYMBYTES; i++)",
            "for (size_t i = 0; i < NTRUPLUS_SYMBYTES - 1; i++)",
            "suffix loop bound",
        ),
        (
            "msg[i + NTRUPLUS_N / 8] = sk[i + 2 * NTRUPLUS_POLYBYTES];",
            "msg[i + NTRUPLUS_N / 8] = sk[i + NTRUPLUS_POLYBYTES];",
            "suffix source offset",
        ),
        (
            "msg[i + NTRUPLUS_N / 8] = sk[i + 2 * NTRUPLUS_POLYBYTES];",
            "buf3[i + NTRUPLUS_N / 8] = sk[i + 2 * NTRUPLUS_POLYBYTES];",
            "suffix destination",
        ),
        (
            "msg[i + NTRUPLUS_N / 8] = sk[i + 2 * NTRUPLUS_POLYBYTES];",
            "msg[i + NTRUPLUS_SSBYTES] = sk[i + 2 * NTRUPLUS_POLYBYTES];",
            "suffix destination offset",
        ),
        (
            "poly_cbd1(&r1, buf3 + NTRUPLUS_SSBYTES);",
            "poly_cbd1(&r1, buf3 + NTRUPLUS_SSBYTES - 1);",
            "next-consumer offset",
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
        description="Fail-closed checker for the NTRU+768 decapsulation hash_h seam",
    )
    parser.add_argument("--params-source", required=True)
    parser.add_argument("--symmetric-source", required=True)
    parser.add_argument("--symmetric-header", required=True)
    parser.add_argument("--kem-source", required=True)
    parser.add_argument("--self-check", action="store_true")
    return parser.parse_args(argv)


def read_text(path_str: str) -> str:
    return Path(path_str).read_text(encoding="utf-8")


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        params_text = read_text(args.params_source)
        symmetric_text = read_text(args.symmetric_source)
        header_text = read_text(args.symmetric_header)
        kem_text = read_text(args.kem_source)
        if args.self_check:
            run_self_check(params_text, symmetric_text, header_text, kem_text)
            print("hash_h seam self-check passed")
        else:
            verify_all(params_text, symmetric_text, header_text, kem_text)
            print("hash_h seam check passed")
    except (OSError, VerificationError) as exc:
        print(f"hash_h seam check failed: {exc}", file=sys.stderr)
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
