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
    raise VerificationError(f"unterminated body for `{name}`")


def require_single_line(text: str, pattern: str, message: str) -> None:
    count = len(re.findall(pattern, strip_comments(text), flags=re.M))
    require(count == 1, message)


def verify_params(text: str) -> None:
    require_single_line(
        text,
        r"^\s*#\s*define\s+NTRUPLUS_N\s+768\s*$",
        "params.h must define NTRUPLUS_N as exactly 768",
    )
    require_single_line(
        text,
        r"^\s*#\s*define\s+NTRUPLUS_Q\s+3457\s*$",
        "params.h must define NTRUPLUS_Q as exactly 3457",
    )


def verify_header(text: str) -> None:
    declarations = (
        (
            r"^\s*void\s+poly_cbd1\s*\(\s*poly\s*\*\s*r\s*,\s*const\s+uint8_t\s+buf\s*\[\s*NTRUPLUS_N\s*/\s*4\s*\]\s*\)\s*;\s*$",
            "poly_cbd1 ABI",
        ),
        (
            r"^\s*void\s+poly_triple\s*\(\s*poly\s*\*\s*r\s*,\s*const\s+poly\s*\*\s*a\s*\)\s*;\s*$",
            "poly_triple ABI",
        ),
        (
            r"^\s*void\s+poly_ntt\s*\(\s*poly\s*\*\s*r\s*,\s*const\s+poly\s*\*\s*a\s*\)\s*;\s*$",
            "poly_ntt ABI",
        ),
        (
            r"^\s*int\s+poly_baseinv\s*\(\s*poly\s*\*\s*r\s*,\s*const\s+poly\s*\*\s*a\s*\)\s*;\s*$",
            "poly_baseinv ABI",
        ),
    )
    for pattern, label in declarations:
        require_single_line(text, pattern, f"poly.h must retain the exact {label}")


def verify_poly_source(text: str) -> None:
    body = compact(extract_function_body(text, "poly_triple"))
    expected = compact(
        """
        for(int i = 0; i < NTRUPLUS_N; ++i)
            r->coeffs[i] = 3*a->coeffs[i];
        """
    )
    require(
        body == expected,
        "poly_triple must be the exact 768-coefficient multiply-by-three loop",
    )


def verify_kem_source(text: str) -> None:
    genf = compact(extract_function_body(text, "genf_derand"))
    expected_f = compact(
        """
        uint8_t buf[NTRUPLUS_N / 4];
        shake256(buf, sizeof buf, coins, 32);
        poly_cbd1(f, buf);
        poly_triple(f, f);
        f->coeffs[0] += 1;
        poly_ntt(f, f);
        return poly_baseinv(finv, f);
        """
    )
    require(
        genf == expected_f,
        "genf_derand must retain CBD1 -> triple -> +1 -> NTT -> baseinv",
    )

    geng = compact(extract_function_body(text, "geng_derand"))
    expected_g = compact(
        """
        uint8_t buf[NTRUPLUS_N / 4];
        shake256(buf, sizeof buf, coins, 32);
        poly_cbd1(g, buf);
        poly_triple(g, g);
        poly_ntt(g, g);
        return poly_baseinv(ginv, g);
        """
    )
    require(
        geng == expected_g,
        "geng_derand must retain CBD1 -> triple -> NTT -> baseinv",
    )


def verify_all(params: str, header: str, poly_source: str, kem_source: str) -> None:
    verify_params(params)
    verify_header(header)
    verify_poly_source(poly_source)
    verify_kem_source(kem_source)


def replace_once(text: str, old: str, new: str, label: str) -> str:
    mutated = text.replace(old, new, 1)
    require(mutated != text, f"could not construct mutation: {label}")
    return mutated


def expect_rejected(
    params: str,
    header: str,
    poly_source: str,
    kem_source: str,
    label: str,
) -> None:
    try:
        verify_all(params, header, poly_source, kem_source)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(params: str, header: str, poly_source: str, kem_source: str) -> int:
    verify_all(params, header, poly_source, kem_source)
    mutations: list[tuple[str, str, str, str]] = [
        ("params", "#define NTRUPLUS_N 768", "#define NTRUPLUS_N 767", "N parameter"),
        ("params", "#define NTRUPLUS_Q 3457", "#define NTRUPLUS_Q 3456", "q parameter"),
        (
            "header",
            "void poly_triple(poly *r, const poly *a);",
            "void poly_triple(poly *r, poly *a);",
            "triple const ABI",
        ),
        (
            "header",
            "void poly_ntt(poly *r, const poly *a);",
            "void poly_ntt(poly *r, poly *a);",
            "NTT const ABI",
        ),
        (
            "header",
            "int  poly_baseinv(poly *r, const poly *a);",
            "void poly_baseinv(poly *r, const poly *a);",
            "baseinv return ABI",
        ),
        (
            "poly",
            "for(int i = 0; i < NTRUPLUS_N; ++i)\n\t\tr->coeffs[i] = 3*a->coeffs[i];",
            "for(int i = 0; i < NTRUPLUS_N - 1; ++i)\n"
            "\t\tr->coeffs[i] = 3*a->coeffs[i];",
            "triple loop bound",
        ),
        (
            "poly",
            "r->coeffs[i] = 3*a->coeffs[i];",
            "r->coeffs[i] = 2*a->coeffs[i];",
            "triple factor",
        ),
        (
            "poly",
            "r->coeffs[i] = 3*a->coeffs[i];",
            "r->coeffs[i] = 3*a->coeffs[i + 1];",
            "triple source index",
        ),
        (
            "poly",
            "r->coeffs[i] = 3*a->coeffs[i];",
            "r->coeffs[i + 1] = 3*a->coeffs[i];",
            "triple destination index",
        ),
        (
            "kem",
            "poly_triple(f, f);",
            "poly_triple(finv, f);",
            "f triple destination",
        ),
        ("kem", "f->coeffs[0] += 1;", "f->coeffs[1] += 1;", "f constant index"),
        ("kem", "f->coeffs[0] += 1;", "f->coeffs[0] += 2;", "f constant value"),
        ("kem", "poly_ntt(f, f);", "poly_ntt(finv, f);", "f NTT destination"),
        (
            "kem",
            "return poly_baseinv(finv, f);",
            "return poly_baseinv(f, finv);",
            "f inverse order",
        ),
        ("kem", "poly_triple(g, g);", "poly_triple(ginv, g);", "g triple destination"),
        ("kem", "poly_ntt(g, g);", "poly_ntt(ginv, g);", "g NTT destination"),
        (
            "kem",
            "return poly_baseinv(ginv, g);",
            "return poly_baseinv(g, ginv);",
            "g inverse order",
        ),
        ("kem", "poly_cbd1(g, buf);", "poly_cbd1(f, buf);", "g sampler destination"),
    ]

    originals = {
        "params": params,
        "header": header,
        "poly": poly_source,
        "kem": kem_source,
    }
    for target, old, new, label in mutations:
        changed = replace_once(originals[target], old, new, label)
        expect_rejected(
            changed if target == "params" else params,
            changed if target == "header" else header,
            changed if target == "poly" else poly_source,
            changed if target == "kem" else kem_source,
            label,
        )
    return len(mutations)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Check the NTRU+768 keygen sampler-shaping seam"
    )
    parser.add_argument("--params-header", required=True)
    parser.add_argument("--poly-header", required=True)
    parser.add_argument("--poly-source", required=True)
    parser.add_argument("--kem-source", required=True)
    parser.add_argument("--self-check", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        params = Path(args.params_header).read_text(encoding="utf-8")
        header = Path(args.poly_header).read_text(encoding="utf-8")
        poly_source = Path(args.poly_source).read_text(encoding="utf-8")
        kem_source = Path(args.kem_source).read_text(encoding="utf-8")
        if args.self_check:
            count = run_self_check(params, header, poly_source, kem_source)
            print(f"keygen sampler seam self-check passed: {count} mutations rejected")
        else:
            verify_all(params, header, poly_source, kem_source)
            print("keygen sampler seam check passed")
        return 0
    except (OSError, VerificationError) as exc:
        print(f"keygen sampler seam check failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
