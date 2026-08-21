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
        r"^\s*#\s*define\s+NTRUPLUS_SSBYTES\s+32\s*$",
        "params.h must define NTRUPLUS_SSBYTES as exactly 32",
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


def verify_poly_header_text(header_text: str) -> None:
    require_single_line(
        header_text,
        r"^\s*void\s+poly_cbd1\s*\(\s*poly\s*\*\s*r\s*,\s*const\s+uint8_t\s+buf\s*\[\s*NTRUPLUS_N\s*/\s*4\s*\]\s*\)\s*;\s*$",
        "poly.h must declare the exact poly_cbd1 interface",
    )


def verify_poly_source_text(poly_text: str) -> None:
    require_single_line(
        poly_text,
        r"^\s*void\s+poly_cbd1\s*\(\s*poly\s*\*\s*r\s*,\s*const\s+unsigned\s+char\s+buf\s*\[\s*NTRUPLUS_N\s*/\s*4\s*\]\s*\)\s*$",
        "poly.c must define poly_cbd1 with the exact buffer shape",
    )

    body = compact(extract_function_body(poly_text, "poly_cbd1"))
    expected = compact(
        """
        uint8_t t1, t2;
        for(size_t i = 0; i < NTRUPLUS_N / 8; i++)
        {
            t1 = buf[i];
            t2 = buf[i + NTRUPLUS_N / 8];
            for(size_t j = 0; j < 8; j++)
            {
                r->coeffs[8*i + j] = (t1 & 0x1) - (t2 & 0x1);
                t1 >>= 1;
                t2 >>= 1;
            }
        }
        """
    )
    require(
        body == expected,
        "poly_cbd1 must sample coefficients from the paired low bits of the 192-byte tail",
    )


def verify_kem_text(kem_text: str) -> None:
    body = compact(extract_function_body(kem_text, "crypto_kem_dec"))
    buf3_decl = "uint8_t buf3[NTRUPLUS_POLYBYTES + NTRUPLUS_SYMBYTES];"
    hash_call = "hash_h(buf3, msg);"
    cbd_call = "poly_cbd1(&r1, buf3 + NTRUPLUS_SSBYTES);"
    ntt_call = "poly_ntt(&r1, &r1);"
    require(body.count(buf3_decl) == 1, "crypto_kem_dec() must declare one buf3 staging buffer")
    require(body.count(hash_call) == 1, "crypto_kem_dec() must call hash_h(buf3, msg) exactly once")
    require(
        body.count(cbd_call) == 1,
        "crypto_kem_dec() must call poly_cbd1(&r1, buf3 + NTRUPLUS_SSBYTES) exactly once",
    )
    require(body.count(ntt_call) == 1, "crypto_kem_dec() must transform r1 in place exactly once")
    require(
        f"{hash_call} {cbd_call} {ntt_call}" in body,
        "crypto_kem_dec() must keep hash_h -> poly_cbd1 -> poly_ntt ordering",
    )


def verify_all(params_text: str, poly_header_text: str, poly_source_text: str, kem_text: str) -> None:
    verify_params_text(params_text)
    verify_poly_header_text(poly_header_text)
    verify_poly_source_text(poly_source_text)
    verify_kem_text(kem_text)


def replace_once(text: str, old: str, new: str, label: str) -> str:
    mutated = text.replace(old, new, 1)
    require(mutated != text, f"could not construct mutation: {label}")
    return mutated


def expect_rejected(
    params_text: str,
    poly_header_text: str,
    poly_source_text: str,
    kem_text: str,
    label: str,
) -> None:
    try:
        verify_all(params_text, poly_header_text, poly_source_text, kem_text)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(
    params_text: str,
    poly_header_text: str,
    poly_source_text: str,
    kem_text: str,
) -> None:
    verify_all(params_text, poly_header_text, poly_source_text, kem_text)

    params_mutations = (
        ("#define NTRUPLUS_N 768", "#define NTRUPLUS_N 864", "N parameter"),
        ("#define NTRUPLUS_SSBYTES   32", "#define NTRUPLUS_SSBYTES   31", "ssbytes parameter"),
        ("#define NTRUPLUS_SYMBYTES  32", "#define NTRUPLUS_SYMBYTES  31", "symbytes parameter"),
        ("#define NTRUPLUS_POLYBYTES 1152", "#define NTRUPLUS_POLYBYTES 1151", "polybytes parameter"),
    )
    for old, new, label in params_mutations:
        expect_rejected(
            replace_once(params_text, old, new, label),
            poly_header_text,
            poly_source_text,
            kem_text,
            label,
        )

    header_mutations = (
        (
            "void poly_cbd1(poly *r, const uint8_t buf[NTRUPLUS_N/4]);",
            "void poly_cbd1(poly *r, const uint8_t buf[NTRUPLUS_N/4 - 1]);",
            "header buffer extent",
        ),
        (
            "void poly_cbd1(poly *r, const uint8_t buf[NTRUPLUS_N/4]);",
            "void poly_cbd1(poly *r, uint8_t buf[NTRUPLUS_N/4]);",
            "header const qualifier",
        ),
    )
    for old, new, label in header_mutations:
        expect_rejected(
            params_text,
            replace_once(poly_header_text, old, new, label),
            poly_source_text,
            kem_text,
            label,
        )

    source_mutations = (
        (
            "void poly_cbd1(poly *r, const unsigned char buf[NTRUPLUS_N/4])",
            "void poly_cbd1(poly *r, const unsigned char buf[NTRUPLUS_N/4 - 1])",
            "source buffer extent",
        ),
        ("i < NTRUPLUS_N / 8", "i < NTRUPLUS_N / 8 - 1", "outer loop bound"),
        ("j < 8", "j < 7", "inner loop bound"),
        ("t1 = buf[i];", "t1 = buf[i + 1];", "first-half offset"),
        ("t2 = buf[i + NTRUPLUS_N / 8];", "t2 = buf[i + NTRUPLUS_N / 8 - 1];", "second-half offset"),
        ("r->coeffs[8*i + j]", "r->coeffs[8*i + j + 1]", "coefficient index"),
        ("r->coeffs[8*i + j] = (t1 & 0x1) - (t2 & 0x1);", "r->coeffs[8*i + j] = (t2 & 0x1) - (t1 & 0x1);", "coefficient sign"),
        ("(t1 & 0x1)", "(t1 & 0x2)", "first low-bit mask"),
        ("(t2 & 0x1)", "(t2 & 0x2)", "second low-bit mask"),
        ("t1 >>= 1;", "t1 <<= 1;", "first bit shift"),
        ("t2 >>= 1;", "t2 <<= 1;", "second bit shift"),
    )
    for old, new, label in source_mutations:
        expect_rejected(
            params_text,
            poly_header_text,
            replace_once(poly_source_text, old, new, label),
            kem_text,
            label,
        )

    kem_mutations = (
        (
            "poly_cbd1(&r1, buf3 + NTRUPLUS_SSBYTES);",
            "poly_cbd1(&r1, buf3 + NTRUPLUS_SSBYTES - 1);",
            "caller offset",
        ),
        (
            "poly_cbd1(&r1, buf3 + NTRUPLUS_SSBYTES);",
            "poly_cbd1(&r1, buf3);",
            "caller base pointer",
        ),
        (
            "    hash_h(buf3, msg);\n",
            "",
            "missing hash_h producer",
        ),
        (
            "    hash_h(buf3, msg);\n    \n    poly_cbd1(&r1, buf3 + NTRUPLUS_SSBYTES);\n",
            "    poly_cbd1(&r1, buf3 + NTRUPLUS_SSBYTES);\n    \n    hash_h(buf3, msg);\n",
            "producer/consumer order",
        ),
        (
            "    poly_cbd1(&r1, buf3 + NTRUPLUS_SSBYTES);\n    poly_ntt(&r1, &r1);\n",
            "    poly_ntt(&r1, &r1);\n    poly_cbd1(&r1, buf3 + NTRUPLUS_SSBYTES);\n",
            "sampler/transform order",
        ),
        (
            "    poly_cbd1(&r1, buf3 + NTRUPLUS_SSBYTES);\n",
            "    poly_cbd1(&r1, buf3 + NTRUPLUS_SSBYTES);\n    poly_cbd1(&r1, buf3 + NTRUPLUS_SSBYTES);\n",
            "duplicate sampler call",
        ),
    )
    for old, new, label in kem_mutations:
        expect_rejected(
            params_text,
            poly_header_text,
            poly_source_text,
            replace_once(kem_text, old, new, label),
            label,
        )


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fail-closed checker for the NTRU+768 decapsulation poly_cbd1 seam",
    )
    parser.add_argument("--params-source", required=True)
    parser.add_argument("--poly-header", required=True)
    parser.add_argument("--poly-source", required=True)
    parser.add_argument("--kem-source", required=True)
    parser.add_argument("--self-check", action="store_true")
    return parser.parse_args(argv)


def read_text(path: str) -> str:
    return Path(path).read_text(encoding="utf-8")


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        params_text = read_text(args.params_source)
        poly_header_text = read_text(args.poly_header)
        poly_source_text = read_text(args.poly_source)
        kem_text = read_text(args.kem_source)
        if args.self_check:
            run_self_check(params_text, poly_header_text, poly_source_text, kem_text)
            print("poly_cbd1 seam self-check passed")
        else:
            verify_all(params_text, poly_header_text, poly_source_text, kem_text)
            print("poly_cbd1 seam check passed")
        return 0
    except (OSError, VerificationError) as exc:
        print(f"poly_cbd1 seam check failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
