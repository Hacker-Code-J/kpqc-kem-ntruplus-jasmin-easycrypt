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
    match = re.search(rf"\b(?:int|void|static inline int16_t)\s+{name}\s*\([^)]*\)", text, flags=re.S)
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


def verify_params_text(text: str) -> None:
    require_single_line(text, r"^\s*#\s*define\s+NTRUPLUS_N\s+768\s*$", "params.h must define NTRUPLUS_N as exactly 768")
    require_single_line(text, r"^\s*#\s*define\s+NTRUPLUS_Q\s+3457\s*$", "params.h must define NTRUPLUS_Q as exactly 3457")


def verify_ntt_header_text(text: str) -> None:
    require_single_line(
        text,
        r"^\s*int\s+baseinv\s*\(\s*int16_t\s+r\s*\[\s*4\s*\]\s*,\s*const\s+int16_t\s+a\s*\[\s*4\s*\]\s*,\s*const\s+int16_t\s+zeta\s*\)\s*;\s*$",
        "ntt.h must declare the exact baseinv ABI",
    )


def verify_poly_header_text(text: str) -> None:
    require_single_line(
        text,
        r"^\s*int\s+poly_baseinv\s*\(\s*poly\s*\*\s*r\s*,\s*const\s+poly\s*\*\s*a\s*\)\s*;\s*$",
        "poly.h must declare the exact poly_baseinv ABI",
    )


def verify_ntt_source_text(text: str) -> None:
    constants = (
        ("NTRUPLUS_R", -147),
        ("NTRUPLUS_RINV", -682),
        ("NTRUPLUS_RSQ", 867),
        ("NTRUPLUS_QINV", 12929),
    )
    for name, value in constants:
        require_single_line(
            text,
            rf"^\s*#\s*define\s+{name}\s+{value}\s*$",
            f"ntt.c must keep {name} = {value}",
        )

    require(
        extract_function_signature(text, "montgomery_reduce") == "static inline int16_t montgomery_reduce(int32_t a)",
        "unexpected montgomery_reduce signature",
    )
    require(
        compact(extract_function_body(text, "montgomery_reduce"))
        == "int16_t t; t = (int16_t)a * NTRUPLUS_QINV; t = (a - (int32_t)t * NTRUPLUS_Q) >> 16; return t;",
        "montgomery_reduce() must keep the exact multiply-subtract-shift body",
    )

    require(
        extract_function_signature(text, "fqmul") == "static inline int16_t fqmul(int16_t a, int16_t b)",
        "unexpected fqmul signature",
    )
    require(
        compact(extract_function_body(text, "fqmul")) == "return montgomery_reduce((int32_t)a * b);",
        "fqmul() must keep the exact Montgomery wrapper body",
    )

    require(
        extract_function_signature(text, "fqinv") == "static inline int16_t fqinv(int16_t a)",
        "unexpected fqinv signature",
    )
    expected_fqinv = compact(
        """
        int16_t t1, t2, t3;
        t1 = fqmul(a, a);
        t2 = fqmul(t1, t1);
        t2 = fqmul(t2, t2);
        t3 = fqmul(t2, t2);
        t1 = fqmul(t1, t2);
        t2 = fqmul(t1, t3);
        t2 = fqmul(t2, t2);
        t2 = fqmul(t2, a);
        t1 = fqmul(t1, t2);
        t2 = fqmul(t2, t2);
        t2 = fqmul(t2, t2);
        t2 = fqmul(t2, t2);
        t2 = fqmul(t2, t2);
        t2 = fqmul(t2, t2);
        t2 = fqmul(t2, t2);
        t2 = fqmul(t2, t1);
        t2 = fqmul(NTRUPLUS_RINV, t2);
        return t2;
        """
    )
    require(compact(extract_function_body(text, "fqinv")) == expected_fqinv, "fqinv() must keep the exact addition chain")

    require(
        extract_function_signature(text, "baseinv") == "int baseinv(int16_t r[4], const int16_t a[4], const int16_t zeta)",
        "unexpected baseinv signature",
    )
    expected_baseinv = compact(
        """
        int16_t t0, t1, t2, t3;
        t0 = montgomery_reduce(a[2]*a[2] - 2*a[1]*a[3]);
        t1 = montgomery_reduce(a[3]*a[3]);
        t0 = montgomery_reduce(a[0]*a[0] + t0*zeta);
        t1 = montgomery_reduce(a[1]*a[1] + t1*zeta - 2*a[0]*a[2]);
        t2 = montgomery_reduce(t1*zeta);
        t3 = montgomery_reduce(t0*t0 - t1*t2);
        if (t3 == 0) return 1;
        r[0] = montgomery_reduce(a[0]*t0 + a[2]*t2);
        r[1] = montgomery_reduce(a[3]*t2 + a[1]*t0);
        r[2] = montgomery_reduce(a[2]*t0 + a[0]*t1);
        r[3] = montgomery_reduce(a[1]*t1 + a[3]*t0);
        t3 = fqinv(t3);
        r[0] = montgomery_reduce(r[0]*t3);
        r[1] = -montgomery_reduce(r[1]*t3);
        r[2] = montgomery_reduce(r[2]*t3);
        r[3] = -montgomery_reduce(r[3]*t3);
        return 0;
        """
    )
    require(compact(extract_function_body(text, "baseinv")) == expected_baseinv, "baseinv() must keep the exact determinant/inversion body")


def verify_poly_source_text(text: str) -> None:
    require(
        extract_function_signature(text, "poly_baseinv") == "int poly_baseinv(poly *r, const poly *a)",
        "unexpected poly_baseinv signature",
    )
    expected = compact(
        """
        for(size_t i = 0; i < NTRUPLUS_N/8; ++i)
        {
            if(baseinv(r->coeffs + 8*i, a->coeffs + 8*i, zetas[96 + i]))
            {
                for (size_t j = 0; j < NTRUPLUS_N; ++j)
                    r->coeffs[j] = 0;
                return 1;
            }
            if(baseinv(r->coeffs + 8*i + 4, a->coeffs + 8*i + 4, -zetas[96 + i]))
            {
                for (size_t j = 0; j < NTRUPLUS_N; ++j)
                    r->coeffs[j] = 0;
                return 1;
            }
        }
        return 0;
        """
    )
    require(compact(extract_function_body(text, "poly_baseinv")) == expected, "poly_baseinv() must keep the exact ±zeta schedule, failure zeroing, and return semantics")


def verify_kem_text(text: str) -> None:
    genf = compact(extract_function_body(text, "genf_derand"))
    geng = compact(extract_function_body(text, "geng_derand"))
    require(
        "poly_ntt(f, f); return poly_baseinv(finv, f);" in genf,
        "genf_derand() must call poly_baseinv(finv, f) after the in-place NTT",
    )
    require(genf.count("return poly_baseinv(finv, f);") == 1, "genf_derand() must call poly_baseinv(finv, f) exactly once")
    require(
        "poly_ntt(g, g); return poly_baseinv(ginv, g);" in geng,
        "geng_derand() must call poly_baseinv(ginv, g) after the in-place NTT",
    )
    require(geng.count("return poly_baseinv(ginv, g);") == 1, "geng_derand() must call poly_baseinv(ginv, g) exactly once")


def verify_all(params_text: str, ntt_header_text: str, poly_header_text: str, ntt_text: str, poly_text: str, kem_text: str) -> None:
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


def expect_rejected(params_text: str, ntt_header_text: str, poly_header_text: str, ntt_text: str, poly_text: str, kem_text: str, label: str) -> None:
    try:
        verify_all(params_text, ntt_header_text, poly_header_text, ntt_text, poly_text, kem_text)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(params_text: str, ntt_header_text: str, poly_header_text: str, ntt_text: str, poly_text: str, kem_text: str) -> int:
    verify_all(params_text, ntt_header_text, poly_header_text, ntt_text, poly_text, kem_text)
    compact_poly = compact(poly_text)
    compact_kem = compact(kem_text)
    baseinv_text = f"{extract_function_signature(ntt_text, 'baseinv')} {{ {extract_function_body(ntt_text, 'baseinv')} }}"
    fqinv_text = f"{extract_function_signature(ntt_text, 'fqinv')} {{ {extract_function_body(ntt_text, 'fqinv')} }}"
    mont_text = f"{extract_function_signature(ntt_text, 'montgomery_reduce')} {{ {extract_function_body(ntt_text, 'montgomery_reduce')} }}"
    fqmul_text = f"{extract_function_signature(ntt_text, 'fqmul')} {{ {extract_function_body(ntt_text, 'fqmul')} }}"
    mutations = [
        ("params", "#define NTRUPLUS_N 768", "#define NTRUPLUS_N 767", "params N"),
        ("params", "#define NTRUPLUS_Q 3457", "#define NTRUPLUS_Q 3456", "params Q"),
        ("ntt_header", "int  baseinv(int16_t r[4], const int16_t a[4], const int16_t zeta);", "int  baseinv(int16_t r[4], const int16_t a[4], int16_t zeta);", "ntt.h zeta const"),
        ("poly_header", "int  poly_baseinv(poly *r, const poly *a);", "void poly_baseinv(poly *r, const poly *a);", "poly.h return type"),
        ("ntt", "#define NTRUPLUS_R            -147", "#define NTRUPLUS_R            -148", "R constant"),
        ("ntt", "#define NTRUPLUS_RINV         -682", "#define NTRUPLUS_RINV         -681", "RINV constant"),
        ("ntt", "#define NTRUPLUS_RSQ           867", "#define NTRUPLUS_RSQ           866", "RSQ constant"),
        ("ntt", "#define NTRUPLUS_QINV        12929", "#define NTRUPLUS_QINV        12928", "QINV constant"),
        ("mont", "t = (int16_t)a * NTRUPLUS_QINV;", "t = (int16_t)a * (NTRUPLUS_QINV - 1);", "montgomery multiplier"),
        ("mont", "t = (a - (int32_t)t * NTRUPLUS_Q) >> 16;", "t = (a + (int32_t)t * NTRUPLUS_Q) >> 16;", "montgomery subtract"),
        ("fqmul", "return montgomery_reduce((int32_t)a * b);", "return montgomery_reduce((int32_t)a + b);", "fqmul operator"),
        ("fqinv", "t2 = fqmul(t2, a);", "t2 = fqmul(t2, t1);", "fqinv chain link"),
        ("fqinv", "t2 = fqmul(NTRUPLUS_RINV, t2);", "t2 = fqmul(NTRUPLUS_RSQ, t2);", "fqinv final scale"),
        ("baseinv", "if (t3 == 0) return 1;", "if (t3 == 0) return 0;", "baseinv failure return"),
        ("baseinv", "r[1] = montgomery_reduce(a[3]*t2 + a[1]*t0);", "r[1] = montgomery_reduce(a[3]*t2 - a[1]*t0);", "baseinv numerator sign"),
        ("baseinv", "r[3] = -montgomery_reduce(r[3]*t3);", "r[3] = montgomery_reduce(r[3]*t3);", "baseinv final sign"),
        ("poly", "baseinv(r->coeffs + 8*i, a->coeffs + 8*i, zetas[96 + i])", "baseinv(r->coeffs + 8*i, a->coeffs + 8*i, zetas[95 + i])", "poly zeta offset"),
        ("poly", "baseinv(r->coeffs + 8*i + 4, a->coeffs + 8*i + 4, -zetas[96 + i])", "baseinv(r->coeffs + 8*i + 4, a->coeffs + 8*i + 4, zetas[96 + i])", "poly negative zeta"),
        ("poly", "return 1;", "return 0;", "poly failure return"),
        ("poly", "r->coeffs[j] = 0;", "r->coeffs[j] = 1;", "poly zeroing value"),
        ("poly", "for (size_t j = 0; j < NTRUPLUS_N; ++j)", "for (size_t j = 0; j < NTRUPLUS_N - 1; ++j)", "poly zeroing bound"),
        ("poly", "return 0;", "return 1;", "poly success return"),
        ("kem", "return poly_baseinv(finv, f);", "return poly_baseinv(f, finv);", "genf inverse order"),
        ("kem", "return poly_baseinv(ginv, g);", "return poly_baseinv(g, ginv);", "geng inverse order"),
    ]
    mutated_count = 0
    for target, old, new, label in mutations:
        target_text = {
            "params": params_text,
            "ntt_header": ntt_header_text,
            "poly_header": poly_header_text,
            "ntt": ntt_text,
            "poly": compact_poly,
            "kem": compact_kem,
            "mont": compact(mont_text),
            "fqmul": compact(fqmul_text),
            "fqinv": compact(fqinv_text),
            "baseinv": compact(baseinv_text),
        }[target]
        changed = replace_once(target_text, old, new, label)
        expect_rejected(
            changed if target == "params" else params_text,
            changed if target == "ntt_header" else ntt_header_text,
            changed if target == "poly_header" else poly_header_text,
            changed if target in {"ntt", "mont", "fqmul", "fqinv", "baseinv"} else ntt_text,
            changed if target == "poly" else poly_text,
            changed if target == "kem" else kem_text,
            label,
        )
        mutated_count += 1
    return mutated_count


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Fail-closed checker for the NTRU+768 baseinv/poly_baseinv seam")
    parser.add_argument("--params-header", required=True)
    parser.add_argument("--ntt-header", required=True)
    parser.add_argument("--poly-header", required=True)
    parser.add_argument("--ntt-source", required=True)
    parser.add_argument("--poly-source", required=True)
    parser.add_argument("--kem-source", required=True)
    parser.add_argument("--self-check", action="store_true")
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
        if args.self_check:
            count = run_self_check(params_text, ntt_header_text, poly_header_text, ntt_text, poly_text, kem_text)
            print(f"baseinv seam self-check passed: {count} mutations rejected")
        else:
            verify_all(params_text, ntt_header_text, poly_header_text, ntt_text, poly_text, kem_text)
            print("baseinv seam check passed")
    except (OSError, VerificationError) as err:
        print(f"FAILED: {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
