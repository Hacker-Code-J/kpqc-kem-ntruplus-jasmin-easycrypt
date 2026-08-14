#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


EXPECTED_EXPORT = "jade_ntruplus_ntruplus768_amd64_ref_poly_sub"
MISSING_SOURCE_HINT = (
    "expected Jasmin source exporting jade_ntruplus_ntruplus768_amd64_ref_poly_sub at "
    "ntruplus/jasmin/768/ref/poly_sub.jazz"
)
EXPECTED_JASMIN_TEMPLATE = """param int NTRUPLUS_N = 768;

#[safety =
   { requires = is_arr_init(ap,0,2 * NTRUPLUS_N) && is_arr_init(bp,0,2 * NTRUPLUS_N)
   , ensures = is_arr_init(rp,0,2 * NTRUPLUS_N)
   }
]
#[ct = "secret × secret × secret → secret"]
#[sct="
{ ptr: transient, val: secret } ×
{ ptr: transient, val: secret } ×
{ ptr: transient, val: secret } →
{ ptr: public, val: secret }
"]
export fn jade_ntruplus_ntruplus768_amd64_ref_poly_sub(
  reg mut ptr u16[NTRUPLUS_N] rp,
  reg const ptr u16[NTRUPLUS_N] ap,
  reg const ptr u16[NTRUPLUS_N] bp) -> reg ptr u16[NTRUPLUS_N]
{
  reg u64 i;
  reg u16 t;

  _ = #init_msf();
  i = 0;
  while (i < NTRUPLUS_N) {
    t = ap[i];
    t -= bp[i];
    rp[i] = t;
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


def extract_function_signature(text: str, name: str) -> str:
    match = re.search(rf"\bvoid\s+{name}\s*\([^)]*\)", text, flags=re.S)
    require(match is not None, f"could not find signature for `{name}`")
    return compact(match.group(0))


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
    ntt_signature = extract_function_signature(poly_text, "poly_ntt")
    require(
        ntt_signature == "void poly_ntt(poly *r, const poly *a)",
        f"unexpected poly_ntt signature: {ntt_signature}",
    )

    ntt_body = compact(extract_function_body(poly_text, "poly_ntt"))
    require(
        ntt_body == "ntt(r->coeffs, a->coeffs);",
        "C poly_ntt() must keep the exact forwarding call into the verified full NTT",
    )

    signature = extract_function_signature(poly_text, "poly_sub")
    require(
        signature == "void poly_sub(poly *r, const poly *a, const poly *b)",
        f"unexpected poly_sub signature: {signature}",
    )

    poly_body = compact(extract_function_body(poly_text, "poly_sub"))
    expected_poly = "for(int i = 0; i < NTRUPLUS_N; ++i) r->coeffs[i] = a->coeffs[i] - b->coeffs[i];"
    require(
        poly_body == expected_poly,
        "C poly_sub() must keep the exact authoritative 768-coefficient subtraction loop",
    )

    kem_body = compact(extract_function_body(kem_text, "crypto_kem_dec"))
    expected_chain = (
        "poly_frombytes(&c, ct); "
        "poly_frombytes(&f, sk); "
        "poly_frombytes(&hinv, sk + NTRUPLUS_POLYBYTES); "
        "poly_basemul(&m1, &c, &f); "
        "poly_invntt(&m1, &m1); "
        "poly_crepmod3(&m1, &m1); "
        "poly_ntt(&m2, &m1); "
        "poly_sub(&c, &c, &m2); "
        "poly_basemul(&r2, &c, &hinv);"
    )
    require(
        expected_chain in kem_body,
        "crypto_kem_dec() must keep the verified decoder -> poly_ntt -> poly_sub seam",
    )
    require(
        kem_body.count("poly_sub(&c, &c, &m2);") == 1,
        "crypto_kem_dec() must contain exactly one poly_sub(&c, &c, &m2) call",
    )


def verify_jasmin_text(text: str) -> None:
    stripped = strip_comments(text)
    signature = re.compile(
        rf"export fn {EXPECTED_EXPORT}\s*\(\s*"
        r"reg mut ptr u16\[NTRUPLUS_N\] rp\s*,\s*"
        r"reg const ptr u16\[NTRUPLUS_N\] ap\s*,\s*"
        r"reg const ptr u16\[NTRUPLUS_N\] bp\s*\)\s*->\s*"
        r"reg ptr u16\[NTRUPLUS_N\]"
    )
    require(signature.search(stripped) is not None, MISSING_SOURCE_HINT)
    require(
        '#[ct = "secret × secret × secret → secret"]' in stripped,
        "Jasmin poly_sub() must keep the constant-time contract annotation",
    )
    require(
        "is_arr_init(ap,0,2 * NTRUPLUS_N) && is_arr_init(bp,0,2 * NTRUPLUS_N)" in stripped,
        "Jasmin poly_sub() must require initialized a/b buffers",
    )
    expected_sct = (
        '{ ptr: transient, val: secret } ×\n'
        '{ ptr: transient, val: secret } ×\n'
        '{ ptr: transient, val: secret } →\n'
        '{ ptr: public, val: secret }'
    )
    require(
        expected_sct in stripped,
        "Jasmin poly_sub() must classify all three pointer arguments in the SCT contract",
    )

    export_body = compact(extract_function_body(text, EXPECTED_EXPORT))
    expected_export = (
        "reg u64 i; reg u16 t; _ = #init_msf(); i = 0; "
        "while (i < NTRUPLUS_N) { t = ap[i]; t -= bp[i]; rp[i] = t; i += 1; } "
        "return rp;"
    )
    require(
        export_body == expected_export,
        "Jasmin poly_sub wrapper must keep the exact init_msf + 768-iteration subtraction loop",
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

    mutated_poly_sig = poly_text.replace(
        "void poly_sub(poly *r, const poly *a, const poly *b)",
        "void poly_sub(poly *r, poly *a, const poly *b)",
        1,
    )
    require(mutated_poly_sig != poly_text, "could not construct C signature mutation")
    expect_rejected(verify_c_text, mutated_poly_sig, kem_text, label="C signature lost const input")

    mutated_poly = poly_text.replace("a->coeffs[i] - b->coeffs[i]", "a->coeffs[i] + b->coeffs[i]", 1)
    require(mutated_poly != poly_text, "could not construct C operator mutation")
    expect_rejected(verify_c_text, mutated_poly, kem_text, label="C subtraction changed to addition")

    mutated_poly_loop = poly_text.replace(
        "for(int i = 0; i < NTRUPLUS_N; ++i)\n\t\tr->coeffs[i] = a->coeffs[i] - b->coeffs[i];",
        "for(int i = 0; i < NTRUPLUS_N; i += 2)\n\t\tr->coeffs[i] = a->coeffs[i] - b->coeffs[i];",
        1,
    )
    require(mutated_poly_loop != poly_text, "could not construct C loop mutation")
    expect_rejected(verify_c_text, mutated_poly_loop, kem_text, label="C loop stride changed")

    mutated_ntt = poly_text.replace(
        "ntt(r->coeffs, a->coeffs);",
        "ntt(a->coeffs, r->coeffs);",
        1,
    )
    require(mutated_ntt != poly_text, "could not construct poly_ntt forwarding mutation")
    expect_rejected(verify_c_text, mutated_ntt, kem_text, label="poly_ntt reversed forwarding buffers")

    mutated_decoder = kem_text.replace("poly_frombytes(&c, ct);", "poly_frombytes(&c, sk);", 1)
    require(mutated_decoder != kem_text, "could not construct ciphertext decoder mutation")
    expect_rejected(verify_c_text, poly_text, mutated_decoder, label="caller changed ciphertext decoder input")

    mutated_kem = kem_text.replace("poly_sub(&c, &c, &m2);", "poly_sub(&c, &m2, &c);", 1)
    require(mutated_kem != kem_text, "could not construct caller alias mutation")
    expect_rejected(verify_c_text, poly_text, mutated_kem, label="caller lost exact poly_sub alias")

    reordered_kem = kem_text.replace(
        "    poly_ntt(&m2, &m1);\n    poly_sub(&c, &c, &m2);\n    poly_basemul(&r2, &c, &hinv);\n",
        "    poly_sub(&c, &c, &m2);\n    poly_ntt(&m2, &m1);\n    poly_basemul(&r2, &c, &hinv);\n",
        1,
    )
    require(reordered_kem != kem_text, "could not construct caller reorder mutation")
    expect_rejected(verify_c_text, poly_text, reordered_kem, label="caller reordered poly_ntt/poly_sub")

    mutated_jasmin = EXPECTED_JASMIN_TEMPLATE.replace("t -= bp[i];", "t += bp[i];", 1)
    require(mutated_jasmin != EXPECTED_JASMIN_TEMPLATE, "could not construct Jasmin operator mutation")
    expect_rejected(verify_jasmin_text, mutated_jasmin, label="Jasmin subtraction changed to addition")

    missing_msf = EXPECTED_JASMIN_TEMPLATE.replace("  _ = #init_msf();\n", "", 1)
    require(missing_msf != EXPECTED_JASMIN_TEMPLATE, "could not construct missing-msf mutation")
    expect_rejected(verify_jasmin_text, missing_msf, label="Jasmin lost init_msf")

    incomplete_sct = EXPECTED_JASMIN_TEMPLATE.replace(
        "{ ptr: transient, val: secret } ×\n{ ptr: transient, val: secret } ×\n",
        "{ ptr: transient, val: secret } ×\n",
        1,
    )
    require(incomplete_sct != EXPECTED_JASMIN_TEMPLATE, "could not construct incomplete SCT mutation")
    expect_rejected(verify_jasmin_text, incomplete_sct, label="Jasmin SCT omitted one pointer input")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fail-closed checker for the NTRU+768 poly_sub decapsulation seam",
    )
    parser.add_argument("--poly-source", required=True, help="path to NTRU+/NTRU+768/poly.c")
    parser.add_argument("--kem-source", required=True, help="path to NTRU+/NTRU+768/kem.c")
    parser.add_argument("--jasmin-source", required=True, help="path to ntruplus/jasmin/768/ref/poly_sub.jazz")
    parser.add_argument("--self-check", action="store_true", help="also require representative bad mutations to be rejected")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        poly_text = Path(args.poly_source).read_text(encoding="utf-8")
        kem_text = Path(args.kem_source).read_text(encoding="utf-8")
        jasmin_text = Path(args.jasmin_source).read_text(encoding="utf-8")
        verify_c_text(poly_text, kem_text)
        verify_jasmin_text(jasmin_text)
        if args.self_check:
            run_self_check(poly_text, kem_text)
    except (OSError, VerificationError) as exc:
        print(f"poly_sub checker failed: {exc}", file=sys.stderr)
        return 1

    print("poly_sub checker passed")
    if args.self_check:
        print("poly_sub checker self-check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
