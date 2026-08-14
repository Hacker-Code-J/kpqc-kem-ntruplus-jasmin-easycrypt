#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


EXPECTED_EXPORT = "jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3"
MISSING_SOURCE_HINT = (
    "expected Jasmin source implementing inline helper `__crepmod3(reg u16 a) -> reg u16` "
    "and export `jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3` at "
    "ntruplus/jasmin/768/ref/crepmod3.jazz"
)
EXPECTED_JASMIN_TEMPLATE = """param int NTRUPLUS_N = 768;
param int NTRUPLUS_Q = 3457;

inline fn __crepmod3(reg u16 a) -> reg u16
{
  reg u16 t;
  reg u16 mask;
  reg u32 td;

  mask = a;
  mask >>s= 15;
  mask &= NTRUPLUS_Q;
  a += mask;
  a -= (NTRUPLUS_Q + 1) / 2;

  mask = a;
  mask >>s= 15;
  mask &= NTRUPLUS_Q;
  a += mask;
  a -= (NTRUPLUS_Q - 1) / 2;

  td = (32s) a;
  td *= 10923;
  td += 16384;
  td >>s= 15;
  t = td;
  t *= 3;
  a -= t;

  return a;
}

#[safety =
   { requires = is_arr_init(ap,0,2 * NTRUPLUS_N)
   , ensures = is_arr_init(rp,0,2 * NTRUPLUS_N)
   }
]
#[ct = "secret × secret → secret"]
#[sct="
{ ptr: transient, val: secret } ×
{ ptr: transient, val: secret } →
{ ptr: public, val: secret }
"]
export fn jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3(
  reg mut ptr u16[NTRUPLUS_N] rp,
  reg const ptr u16[NTRUPLUS_N] ap) -> reg ptr u16[NTRUPLUS_N]
{
  reg u64 i;

  _ = #init_msf();
  i = 0;
  while (i < NTRUPLUS_N) {
    rp[i] = __crepmod3(ap[i]);
    i += 1;
  }

  return rp;
}
"""


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


def verify_c_text(poly_text: str, kem_text: str) -> None:
    scalar_body = compact(extract_function_body(poly_text, "crepmod3"))
    expected_scalar = (
        "int16_t t; const int16_t v = ((1<<15) + 3/2)/3; "
        "a += (a >> 15) & NTRUPLUS_Q; "
        "a -= (NTRUPLUS_Q+1)/2; "
        "a += (a >> 15) & NTRUPLUS_Q; "
        "a -= (NTRUPLUS_Q-1)/2; "
        "t = ((int32_t)v*a + (1<<14)) >> 15; "
        "t *= 3; "
        "return a - t;"
    )
    require(
        scalar_body == expected_scalar,
        "C crepmod3() no longer matches the verified centered-mod-3 reduction sequence",
    )

    poly_body = compact(extract_function_body(poly_text, "poly_crepmod3"))
    expected_poly = "for(int i = 0; i < NTRUPLUS_N; i++) r->coeffs[i] = crepmod3(a->coeffs[i]);"
    require(
        poly_body == expected_poly,
        "C poly_crepmod3() must keep the exact 768-coefficient scalar-map loop",
    )

    kem_body = compact(extract_function_body(kem_text, "crypto_kem_dec"))
    expected_chain = (
        "poly_basemul(&m1, &c, &f); "
        "poly_invntt(&m1, &m1); "
        "poly_crepmod3(&m1, &m1); "
        "poly_ntt(&m2, &m1); "
        "poly_sub(&c, &c, &m2);"
    )
    require(
        expected_chain in kem_body,
        "crypto_kem_dec() must keep poly_invntt(&m1,&m1) -> poly_crepmod3(&m1,&m1) -> poly_ntt(&m2,&m1)",
    )
    require(
        kem_body.count("poly_crepmod3(&m1, &m1);") == 1,
        "crypto_kem_dec() must contain exactly one poly_crepmod3(&m1, &m1) call",
    )


def verify_export_signature(text: str) -> None:
    signature = re.compile(
        rf"export fn {EXPECTED_EXPORT}\s*\(\s*"
        r"reg mut ptr u16\[NTRUPLUS_N\] rp\s*,\s*"
        r"reg const ptr u16\[NTRUPLUS_N\] ap\s*\)\s*->\s*"
        r"reg ptr u16\[NTRUPLUS_N\]"
    )
    require(signature.search(strip_comments(text)) is not None, MISSING_SOURCE_HINT)


def verify_helper_signature(text: str) -> None:
    signature = re.compile(r"inline fn __crepmod3\s*\(\s*reg u16 a\s*\)\s*->\s*reg u16")
    require(signature.search(strip_comments(text)) is not None, MISSING_SOURCE_HINT)


def verify_jasmin_text(text: str) -> None:
    verify_helper_signature(text)
    verify_export_signature(text)

    helper_body = compact(extract_function_body(text, "__crepmod3"))
    expected_helper = (
        "reg u16 t; reg u16 mask; reg u32 td; "
        "mask = a; mask >>s= 15; mask &= NTRUPLUS_Q; a += mask; a -= (NTRUPLUS_Q + 1) / 2; "
        "mask = a; mask >>s= 15; mask &= NTRUPLUS_Q; a += mask; a -= (NTRUPLUS_Q - 1) / 2; "
        "td = (32s) a; td *= 10923; td += 16384; td >>s= 15; t = td; t *= 3; a -= t; "
        "return a;"
    )
    require(
        helper_body == expected_helper,
        "Jasmin __crepmod3() helper must keep the verified signed-mask and multiply-round-shift reduction",
    )

    export_body = compact(extract_function_body(text, EXPECTED_EXPORT))
    expected_export = (
        "reg u64 i; _ = #init_msf(); i = 0; "
        "while (i < NTRUPLUS_N) { rp[i] = __crepmod3(ap[i]); i += 1; } "
        "return rp;"
    )
    require(
        export_body == expected_export,
        "Jasmin poly_crepmod3 wrapper must keep the exact init_msf + 768-iteration helper loop",
    )


def expect_rejected(check, *args: str, label: str) -> None:
    try:
        check(*args)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(poly_text: str, kem_text: str) -> None:
    verify_c_text(poly_text, kem_text)
    verify_jasmin_text(EXPECTED_JASMIN_TEMPLATE)

    mutated_scalar = poly_text.replace("t *= 3;", "t *= 2;", 1)
    require(mutated_scalar != poly_text, "could not construct C scalar mutation")
    expect_rejected(verify_c_text, mutated_scalar, kem_text, label="C scalar multiplier changed")

    mutated_poly = poly_text.replace(
        "    \tr->coeffs[i] = crepmod3(a->coeffs[i]);",
        "    \tr->coeffs[i] = crepmod3(a->coeffs[i + 1]);",
        1,
    )
    require(mutated_poly != poly_text, "could not construct C poly-map mutation")
    expect_rejected(verify_c_text, mutated_poly, kem_text, label="C poly map stopped using coeff i")

    mutated_kem = kem_text.replace(
        "    poly_crepmod3(&m1, &m1);\n    \n    poly_ntt(&m2, &m1);\n",
        "    poly_ntt(&m2, &m1);\n    poly_crepmod3(&m1, &m1);\n",
        1,
    )
    require(mutated_kem != kem_text, "could not construct kem reorder mutation")
    expect_rejected(verify_c_text, poly_text, mutated_kem, label="kem reordered crepmod3/ntt")

    mutated_kem_alias = kem_text.replace("poly_crepmod3(&m1, &m1);", "poly_crepmod3(&m1, &m2);", 1)
    require(mutated_kem_alias != kem_text, "could not construct kem alias mutation")
    expect_rejected(verify_c_text, poly_text, mutated_kem_alias, label="kem lost exact-alias crepmod3 call")

    mutated_helper = EXPECTED_JASMIN_TEMPLATE.replace("  t *= 3;\n", "  t *= 2;\n", 1)
    require(mutated_helper != EXPECTED_JASMIN_TEMPLATE, "could not construct helper multiplier mutation")
    expect_rejected(verify_jasmin_text, mutated_helper, label="Jasmin helper multiplier changed")

    missing_msf = EXPECTED_JASMIN_TEMPLATE.replace("  _ = #init_msf();\n", "", 1)
    require(missing_msf != EXPECTED_JASMIN_TEMPLATE, "could not construct missing-msf mutation")
    expect_rejected(verify_jasmin_text, missing_msf, label="Jasmin wrapper skipped init_msf")

    widened_loop = EXPECTED_JASMIN_TEMPLATE.replace("while (i < NTRUPLUS_N)", "while (i <= NTRUPLUS_N)", 1)
    require(widened_loop != EXPECTED_JASMIN_TEMPLATE, "could not construct widened-loop mutation")
    expect_rejected(verify_jasmin_text, widened_loop, label="Jasmin wrapper widened loop bound")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--poly-source",
        type=Path,
        default=Path("../../../NTRU+/NTRU+768/poly.c"),
        help="path to the authoritative C poly source",
    )
    parser.add_argument(
        "--kem-source",
        type=Path,
        default=Path("../../../NTRU+/NTRU+768/kem.c"),
        help="path to the authoritative C KEM source",
    )
    parser.add_argument(
        "--jasmin-source",
        type=Path,
        default=Path("../../../ntruplus/jasmin/768/ref/crepmod3.jazz"),
        help="path to the Jasmin wrapper source",
    )
    parser.add_argument(
        "--self-check",
        action="store_true",
        help="exercise the checker against built-in negative mutations",
    )
    args = parser.parse_args()

    try:
        poly_text = args.poly_source.read_text(encoding="utf-8")
        kem_text = args.kem_source.read_text(encoding="utf-8")
        verify_c_text(poly_text, kem_text)
        if args.self_check:
            if args.jasmin_source.exists():
                jasmin_text = args.jasmin_source.read_text(encoding="utf-8")
                verify_jasmin_text(jasmin_text)
            run_self_check(poly_text, kem_text)
            print("crepmod3 checker self-check passed")
            return 0

        jasmin_text = args.jasmin_source.read_text(encoding="utf-8")
        verify_jasmin_text(jasmin_text)
        print("crepmod3 checker passed")
        return 0
    except (OSError, VerificationError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
