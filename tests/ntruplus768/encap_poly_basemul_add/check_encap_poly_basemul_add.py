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


def require_single_line(text: str, pattern: str, message: str) -> None:
    require(len(re.findall(pattern, strip_comments(text), flags=re.M)) == 1, message)


def extract_function_signature(text: str, name: str) -> str:
    match = re.search(rf"\b(?:int|void)\s+{name}\s*\([^)]*\)", text, flags=re.S)
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


def verify_params_text(params_text: str) -> None:
    require_single_line(
        params_text,
        r"^\s*#\s*define\s+NTRUPLUS_N\s+768\s*$",
        "params.h must define NTRUPLUS_N as exactly 768",
    )
    require_single_line(
        params_text,
        r"^\s*#\s*define\s+NTRUPLUS_Q\s+3457\s*$",
        "params.h must define NTRUPLUS_Q as exactly 3457",
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


def verify_ntt_header_text(ntt_header_text: str) -> None:
    require_single_line(
        ntt_header_text,
        r"^\s*void\s+basemul_add\s*\(\s*int16_t\s+r\s*\[\s*4\s*\]\s*,\s*const\s+int16_t\s+a\s*\[\s*4\s*\]\s*,\s*const\s+int16_t\s+b\s*\[\s*4\s*\]\s*,\s*const\s+int16_t\s+c\s*\[\s*4\s*\]\s*,\s*const\s+int16_t\s+zeta\s*\)\s*;\s*$",
        "ntt.h must declare the exact basemul_add interface",
    )


def verify_poly_header_text(poly_header_text: str) -> None:
    require_single_line(
        poly_header_text,
        r"^\s*void\s+poly_basemul_add\s*\(\s*poly\s*\*\s*r\s*,\s*const\s+poly\s*\*\s*a\s*,\s*const\s+poly\s*\*\s*b\s*,\s*const\s+poly\s*\*\s*c\s*\)\s*;\s*$",
        "poly.h must declare the exact poly_basemul_add interface",
    )
    require_single_line(
        poly_header_text,
        r"^\s*void\s+poly_frombytes\s*\(\s*poly\s*\*\s*r\s*,\s*const\s+uint8_t\s+a\s*\[\s*NTRUPLUS_POLYBYTES\s*\]\s*\)\s*;\s*$",
        "poly.h must declare the exact poly_frombytes interface",
    )
    require_single_line(
        poly_header_text,
        r"^\s*void\s+poly_tobytes\s*\(\s*uint8_t\s+r\s*\[\s*NTRUPLUS_POLYBYTES\s*\]\s*,\s*const\s+poly\s*\*\s*a\s*\)\s*;\s*$",
        "poly.h must declare the exact poly_tobytes interface",
    )


def verify_ntt_source_text(ntt_text: str) -> None:
    signature = extract_function_signature(ntt_text, "basemul_add")
    require(
        signature
        == "void basemul_add(int16_t r[4], const int16_t a[4], const int16_t b[4], const int16_t c[4], const int16_t zeta)",
        f"unexpected basemul_add signature: {signature}",
    )
    body = compact(extract_function_body(ntt_text, "basemul_add"))
    expected = compact(
        """
        r[0] = montgomery_reduce(a[1]*b[3]+a[2]*b[2]+a[3]*b[1]);
        r[1] = montgomery_reduce(a[2]*b[3]+a[3]*b[2]);
        r[2] = montgomery_reduce(a[3]*b[3]);
        r[0] = montgomery_reduce(r[0]*zeta+a[0]*b[0]);
        r[1] = montgomery_reduce(r[1]*zeta+a[0]*b[1]+a[1]*b[0]);
        r[2] = montgomery_reduce(r[2]*zeta+a[0]*b[2]+a[1]*b[1]+a[2]*b[0]);
        r[3] = montgomery_reduce(a[0]*b[3]+a[1]*b[2]+a[2]*b[1]+a[3]*b[0]);
        r[0] = montgomery_reduce(c[0]*NTRUPLUS_R + r[0]*NTRUPLUS_RSQ);
        r[1] = montgomery_reduce(c[1]*NTRUPLUS_R + r[1]*NTRUPLUS_RSQ);
        r[2] = montgomery_reduce(c[2]*NTRUPLUS_R + r[2]*NTRUPLUS_RSQ);
        r[3] = montgomery_reduce(c[3]*NTRUPLUS_R + r[3]*NTRUPLUS_RSQ);
        """
    )
    require(
        body == expected,
        "basemul_add() must keep the authoritative multiply-then-add sequence and exact final addition lines",
    )


def verify_poly_source_text(poly_text: str) -> None:
    signature = extract_function_signature(poly_text, "poly_basemul_add")
    require(
        signature
        == "void poly_basemul_add(poly *r, const poly *a, const poly *b, const poly *c)",
        f"unexpected poly_basemul_add signature: {signature}",
    )
    body = compact(extract_function_body(poly_text, "poly_basemul_add"))
    expected = compact(
        """
        for(int i = 0; i < NTRUPLUS_N/8; ++i)
        {
            basemul_add(r->coeffs + 8*i, a->coeffs + 8*i, b->coeffs + 8*i, c->coeffs + 8*i, zetas[96 + i]);
            basemul_add(r->coeffs + 8*i + 4, a->coeffs + 8*i + 4, b->coeffs + 8*i + 4, c->coeffs + 8*i + 4, -zetas[96 + i]);
        }
        """
    )
    require(
        body == expected,
        "poly_basemul_add() must keep the exact two-call ±zetas loop",
    )


def verify_kem_text(kem_text: str) -> None:
    body = compact(extract_function_body(kem_text, "crypto_kem_enc_derand"))
    frombytes_call = "poly_frombytes(&h, pk);"
    basemul_add_call = "poly_basemul_add(&c, &h, &r, &m);"
    tobytes_call = "poly_tobytes(ct, &c);"
    require(
        body.count(frombytes_call) == 1,
        "crypto_kem_enc_derand() must call poly_frombytes(&h, pk) exactly once",
    )
    require(
        body.count(basemul_add_call) == 1,
        "crypto_kem_enc_derand() must call poly_basemul_add(&c, &h, &r, &m) exactly once",
    )
    require(
        body.count(tobytes_call) == 1,
        "crypto_kem_enc_derand() must call poly_tobytes(ct, &c) exactly once",
    )
    require(
        f"{frombytes_call} {basemul_add_call} {tobytes_call}" in body,
        "crypto_kem_enc_derand() must keep the exact poly_frombytes -> poly_basemul_add -> poly_tobytes seam",
    )


def verify_all(
    params_text: str,
    ntt_header_text: str,
    poly_header_text: str,
    ntt_text: str,
    poly_text: str,
    kem_text: str,
) -> None:
    verify_params_text(params_text)
    verify_ntt_header_text(ntt_header_text)
    verify_poly_header_text(poly_header_text)
    verify_ntt_source_text(ntt_text)
    verify_poly_source_text(poly_text)
    verify_kem_text(kem_text)


def replace_once(text: str, old: str, new: str, label: str) -> str:
    mutated = text.replace(old, new, 1)
    require(mutated != text, f"could not construct mutation: {label}")
    return mutated


def expect_rejected(
    params_text: str,
    ntt_header_text: str,
    poly_header_text: str,
    ntt_text: str,
    poly_text: str,
    kem_text: str,
    label: str,
) -> None:
    try:
        verify_all(params_text, ntt_header_text, poly_header_text, ntt_text, poly_text, kem_text)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(
    params_text: str,
    ntt_header_text: str,
    poly_header_text: str,
    ntt_text: str,
    poly_text: str,
    kem_text: str,
) -> None:
    verify_all(params_text, ntt_header_text, poly_header_text, ntt_text, poly_text, kem_text)
    compact_poly = compact(poly_text)
    compact_kem = compact(kem_text)
    basemul_add_text = (
        f"{extract_function_signature(ntt_text, 'basemul_add')} "
        f"{{ {extract_function_body(ntt_text, 'basemul_add')} }}"
    )
    basemul_add_text = compact(basemul_add_text)

    params_mutations = (
        ("#define NTRUPLUS_N 768", "#define NTRUPLUS_N 864", "params N"),
        ("#define NTRUPLUS_Q 3457", "#define NTRUPLUS_Q 3456", "params Q"),
        ("#define NTRUPLUS_POLYBYTES 1152", "#define NTRUPLUS_POLYBYTES 1151", "params POLYBYTES"),
    )
    for old, new, label in params_mutations:
        expect_rejected(
            replace_once(params_text, old, new, label),
            ntt_header_text,
            poly_header_text,
            ntt_text,
            poly_text,
            kem_text,
            label,
        )

    expect_rejected(
        params_text,
        replace_once(
            ntt_header_text,
            "void basemul_add(int16_t r[4], const int16_t a[4], const int16_t b[4], const int16_t c[4], const int16_t zeta);",
            "void basemul_add(int16_t r[4], const int16_t a[4], const int16_t b[4], const int16_t c[4], int16_t zeta);",
            "ntt.h zeta const",
        ),
        poly_header_text,
        ntt_text,
        poly_text,
        kem_text,
        "ntt.h zeta const",
    )
    expect_rejected(
        params_text,
        ntt_header_text,
        replace_once(
            poly_header_text,
            "void poly_basemul_add(poly *r, const poly *a, const poly *b, const poly *c);",
            "void poly_basemul_add(poly *r, const poly *a, const poly *b, poly *c);",
            "poly.h third operand const",
        ),
        ntt_text,
        poly_text,
        kem_text,
        "poly.h third operand const",
    )

    ntt_mutations = (
        (
            "r[0] = montgomery_reduce(c[0]*NTRUPLUS_R + r[0]*NTRUPLUS_RSQ);",
            "r[0] = montgomery_reduce(c[0]*NTRUPLUS_R - r[0]*NTRUPLUS_RSQ);",
            "ntt.c final operator",
        ),
        (
            "r[1] = montgomery_reduce(c[1]*NTRUPLUS_R + r[1]*NTRUPLUS_RSQ);",
            "r[1] = montgomery_reduce(c[0]*NTRUPLUS_R + r[1]*NTRUPLUS_RSQ);",
            "ntt.c final addend",
        ),
        (
            "r[2] = montgomery_reduce(r[2]*zeta+a[0]*b[2]+a[1]*b[1]+a[2]*b[0]);",
            "r[2] = montgomery_reduce(r[2]*(-zeta)+a[0]*b[2]+a[1]*b[1]+a[2]*b[0]);",
            "ntt.c zeta sign",
        ),
        (
            "r[3] = montgomery_reduce(c[3]*NTRUPLUS_R + r[3]*NTRUPLUS_RSQ);",
            "r[3] = montgomery_reduce(c[3]*NTRUPLUS_R + r[3]*NTRUPLUS_RSQ); r[3] = montgomery_reduce(c[3]*NTRUPLUS_R + r[3]*NTRUPLUS_RSQ);",
            "ntt.c duplicate final write",
        ),
    )
    for old, new, label in ntt_mutations:
        expect_rejected(
            params_text,
            ntt_header_text,
            poly_header_text,
            replace_once(basemul_add_text, old, new, label),
            poly_text,
            kem_text,
            label,
        )

    poly_mutations = (
        (
            "basemul_add(r->coeffs + 8*i, a->coeffs + 8*i, b->coeffs + 8*i, c->coeffs + 8*i, zetas[96 + i]);",
            "basemul_add(r->coeffs + 8*i, a->coeffs + 8*i, b->coeffs + 8*i, c->coeffs + 8*i, zetas[95 + i]);",
            "poly.c zeta offset",
        ),
        (
            "basemul_add(r->coeffs + 8*i + 4, a->coeffs + 8*i + 4, b->coeffs + 8*i + 4, c->coeffs + 8*i + 4, -zetas[96 + i]);",
            "basemul_add(r->coeffs + 8*i + 4, a->coeffs + 8*i + 4, b->coeffs + 8*i + 4, c->coeffs + 8*i + 4, zetas[96 + i]);",
            "poly.c negative zeta",
        ),
        (
            "basemul_add(r->coeffs + 8*i, a->coeffs + 8*i, b->coeffs + 8*i, c->coeffs + 8*i, zetas[96 + i]); basemul_add(r->coeffs + 8*i + 4, a->coeffs + 8*i + 4, b->coeffs + 8*i + 4, c->coeffs + 8*i + 4, -zetas[96 + i]);",
            "basemul_add(r->coeffs + 8*i + 4, a->coeffs + 8*i + 4, b->coeffs + 8*i + 4, c->coeffs + 8*i + 4, -zetas[96 + i]); basemul_add(r->coeffs + 8*i, a->coeffs + 8*i, b->coeffs + 8*i, c->coeffs + 8*i, zetas[96 + i]);",
            "poly.c call order",
        ),
    )
    for old, new, label in poly_mutations:
        expect_rejected(
            params_text,
            ntt_header_text,
            poly_header_text,
            ntt_text,
            replace_once(compact_poly, old, new, label),
            kem_text,
            label,
        )

    kem_mutations = (
        (
            "poly_basemul_add(&c, &h, &r, &m);",
            "poly_basemul_add(&c, &r, &h, &m);",
            "kem.c argument order",
        ),
        (
            "poly_frombytes(&h, pk); poly_basemul_add(&c, &h, &r, &m);",
            "poly_basemul_add(&c, &h, &r, &m); poly_frombytes(&h, pk);",
            "kem.c seam order",
        ),
        (
            "poly_tobytes(ct, &c);",
            "poly_tobytes(buf2, &c);",
            "kem.c tobytes target",
        ),
        (
            "poly_basemul_add(&c, &h, &r, &m);",
            "poly_basemul_add(&c, &h, &r, &m); poly_basemul_add(&c, &h, &r, &m);",
            "kem.c duplicate basemul_add",
        ),
    )
    for old, new, label in kem_mutations:
        expect_rejected(
            params_text,
            ntt_header_text,
            poly_header_text,
            ntt_text,
            poly_text,
            replace_once(compact_kem, old, new, label),
            label,
        )


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fail-closed checker for the NTRU+768 encapsulation poly_basemul_add seam",
    )
    parser.add_argument("--params-header", required=True, help="path to NTRU+/NTRU+768/params.h")
    parser.add_argument("--ntt-header", required=True, help="path to NTRU+/NTRU+768/ntt.h")
    parser.add_argument("--poly-header", required=True, help="path to NTRU+/NTRU+768/poly.h")
    parser.add_argument("--ntt-source", required=True, help="path to NTRU+/NTRU+768/ntt.c")
    parser.add_argument("--poly-source", required=True, help="path to NTRU+/NTRU+768/poly.c")
    parser.add_argument("--kem-source", required=True, help="path to NTRU+/NTRU+768/kem.c")
    parser.add_argument("--self-check", action="store_true", help="also require representative bad mutations to be rejected")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        params_text = Path(args.params_header).read_text(encoding="utf-8")
        ntt_header_text = Path(args.ntt_header).read_text(encoding="utf-8")
        poly_header_text = Path(args.poly_header).read_text(encoding="utf-8")
        ntt_text = Path(args.ntt_source).read_text(encoding="utf-8")
        poly_text = Path(args.poly_source).read_text(encoding="utf-8")
        kem_text = Path(args.kem_source).read_text(encoding="utf-8")
        verify_all(params_text, ntt_header_text, poly_header_text, ntt_text, poly_text, kem_text)
        if args.self_check:
            run_self_check(params_text, ntt_header_text, poly_header_text, ntt_text, poly_text, kem_text)
    except (OSError, VerificationError) as err:
        print(f"FAILED: {err}", file=sys.stderr)
        return 1

    print("encap poly_basemul_add seam verified")
    if args.self_check:
        print("self-check mutations rejected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
