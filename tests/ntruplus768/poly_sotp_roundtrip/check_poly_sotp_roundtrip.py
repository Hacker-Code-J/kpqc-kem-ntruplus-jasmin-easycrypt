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


def extract_function_signature(text: str, name: str, kind: str) -> str:
    match = re.search(rf"\b{kind}\s+{name}\s*\([^)]*\)", text, flags=re.S)
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
        r"^\s*#\s*define\s+NTRUPLUS_SYMBYTES\s+32\s*$",
        "params.h must define NTRUPLUS_SYMBYTES as exactly 32",
    )
    require_single_line(
        params_text,
        r"^\s*#\s*define\s+NTRUPLUS_POLYBYTES\s+1152\s*$",
        "params.h must define NTRUPLUS_POLYBYTES as exactly 1152",
    )


def verify_header_text(header_text: str) -> None:
    require_single_line(
        header_text,
        r"^\s*void\s+poly_sotp_encode\s*\(\s*poly\s+\*r\s*,\s*const\s+uint8_t\s+msg\[NTRUPLUS_N/8\]\s*,\s*const\s+uint8_t\s+buf\[NTRUPLUS_N/4\]\s*\)\s*;\s*$",
        "poly.h must declare the exact poly_sotp_encode interface",
    )


def verify_poly_text(poly_text: str) -> None:
    signature = extract_function_signature(poly_text, "poly_sotp_encode", "void")
    require(
        signature
        == "void poly_sotp_encode(poly *r, const uint8_t msg[NTRUPLUS_N/8], "
        "const uint8_t buf[NTRUPLUS_N/4])",
        f"unexpected poly_sotp_encode signature: {signature}",
    )
    body = compact(extract_function_body(poly_text, "poly_sotp_encode"))
    expected_body = compact(
        """
        uint8_t tmp[NTRUPLUS_N / 4];

        for(int i = 0; i < NTRUPLUS_N / 8; i++)
        {
             tmp[i] = buf[i]^msg[i];
        }

        for(int i = NTRUPLUS_N / 8; i < NTRUPLUS_N / 4; i++)
        {
             tmp[i] = buf[i];
        }

        poly_cbd1(r, tmp);
        """
    )
    require(
        body == expected_body,
        "poly_sotp_encode() must keep the exact tmp head XOR / tail copy / "
        "poly_cbd1 body",
    )


def verify_kem_text(kem_text: str) -> None:
    body = compact(extract_function_body(kem_text, "crypto_kem_enc_derand"))
    expected_chain = (
        "poly_tobytes(buf2, &r); "
        "hash_g(buf2, buf2); "
        "poly_sotp_encode(&m, msg, buf2); "
        "poly_ntt(&m, &m);"
    )
    require(
        expected_chain in body,
        "crypto_kem_enc_derand() must keep poly_tobytes -> hash_g -> "
        "poly_sotp_encode -> poly_ntt order",
    )
    require(
        body.count("poly_sotp_encode(&m, msg, buf2);") == 1,
        "crypto_kem_enc_derand() must contain exactly one "
        "poly_sotp_encode(&m, msg, buf2) call",
    )


def verify_all(
    params_text: str,
    poly_text: str,
    header_text: str,
    kem_text: str,
) -> None:
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


def run_self_check(
    params_text: str,
    poly_text: str,
    header_text: str,
    kem_text: str,
) -> None:
    verify_all(params_text, poly_text, header_text, kem_text)

    params_mutations = (
        ("#define NTRUPLUS_N 768", "#define NTRUPLUS_N 864", "N parameter"),
        (
            "#define NTRUPLUS_POLYBYTES 1152",
            "#define NTRUPLUS_POLYBYTES 1151",
            "polybytes parameter",
        ),
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
            "void poly_sotp_encode(poly *r, const uint8_t msg[NTRUPLUS_N/8], "
            "const uint8_t buf[NTRUPLUS_N/4]);",
            "void poly_sotp_encode(poly *r, uint8_t msg[NTRUPLUS_N/8], "
            "const uint8_t buf[NTRUPLUS_N/4]);",
            "header lost const msg",
        ),
        kem_text,
        "header lost const msg",
    )

    poly_mutations = (
        (
            "tmp[i] = buf[i]^msg[i];",
            "tmp[i] = buf[i]|msg[i];",
            "head xor operator",
        ),
        (
            "tmp[i] = buf[i]^msg[i];",
            "tmp[i] = buf[i]^msg[i + 1];",
            "head msg offset",
        ),
        ("tmp[i] = buf[i];", "tmp[i] = buf[i - 1];", "tail source offset"),
        (
            "for(int i = NTRUPLUS_N / 8; i < NTRUPLUS_N / 4; i++)",
            "for(int i = NTRUPLUS_N / 8; i < NTRUPLUS_N / 4 - 1; i++)",
            "tail length",
        ),
        ("poly_cbd1(r, tmp);", "poly_cbd1(r, buf);", "encode cbd input"),
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
        (
            "poly_sotp_encode(&m, msg, buf2);",
            "poly_sotp_encode(&m, msg, buf1);",
            "wrong pad source",
        ),
        (
            "    hash_g(buf2, buf2);\n    poly_sotp_encode(&m, msg, buf2);\n",
            "    poly_sotp_encode(&m, msg, buf2);\n    hash_g(buf2, buf2);\n",
            "encode before hash_g",
        ),
        (
            "    poly_sotp_encode(&m, msg, buf2);\n    poly_ntt(&m, &m);\n",
            "    poly_ntt(&m, &m);\n    poly_sotp_encode(&m, msg, buf2);\n",
            "ntt before encode",
        ),
        (
            "    poly_sotp_encode(&m, msg, buf2);\n",
            "    poly_sotp_encode(&m, msg, buf2);\n"
            "    poly_sotp_encode(&m, msg, buf2);\n",
            "duplicate encode call",
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
        description=(
            "Fail-closed checker for the NTRU+768 poly_sotp_encode "
            "roundtrip seam"
        ),
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
        print(f"poly_sotp_roundtrip checker failed: {exc}", file=sys.stderr)
        return 1

    mode = "self-check passed" if args.self_check else "source check passed"
    print(f"poly_sotp_roundtrip {mode}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
