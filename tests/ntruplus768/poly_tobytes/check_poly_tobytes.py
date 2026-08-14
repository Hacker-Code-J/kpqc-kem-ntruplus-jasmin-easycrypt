#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


EXPECTED_EXPORT = "jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes"
MISSING_SOURCE_HINT = (
    "expected Jasmin source exporting jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes at "
    "ntruplus/jasmin/768/ref/poly_tobytes.jazz"
)
EXPECTED_JASMIN_TEMPLATE = """param int NTRUPLUS_N = 768;
param int NTRUPLUS_Q = 3457;
param int NTRUPLUS_POLYBYTES = 1152;

#[safety =
   { requires = is_arr_init(ap,0,2 * NTRUPLUS_N)
   , ensures = is_arr_init(rp,0,NTRUPLUS_POLYBYTES)
   }
]
#[ct = "secret × secret → secret"]
#[sct="
{ ptr: transient, val: secret } ×
{ ptr: transient, val: secret } →
{ ptr: public, val: secret }
"]
export fn jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(
  reg mut ptr u8[NTRUPLUS_POLYBYTES] rp,
  reg const ptr u16[NTRUPLUS_N] ap) -> reg ptr u8[NTRUPLUS_POLYBYTES]
{
  reg u64 i;
  reg u64 off;
  reg u16 t0;
  reg u16 t1;
  reg u16 t;
  reg u16 mask;

  _ = #init_msf();
  i = 0;
  while (i < NTRUPLUS_N / 2) {
    off = i;
    off <<= 1;
    t0 = ap[2 * i];
    mask = t0;
    mask >>s= 15;
    mask &= NTRUPLUS_Q;
    t0 += mask;

    t1 = ap[2 * i + 1];
    mask = t1;
    mask >>s= 15;
    mask &= NTRUPLUS_Q;
    t1 += mask;

    off += i;
    rp[off] = t0;

    t = t0;
    t >>= 8;
    mask = t1;
    mask <<= 4;
    t |= mask;
    rp[off + 1] = t;

    t = t1;
    t >>= 4;
    rp[off + 2] = t;

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
    match = re.search(rf"\b(?:int|void)\s+{name}\s*\([^)]*\)", text, flags=re.S)
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
    signature = extract_function_signature(poly_text, "poly_tobytes")
    require(
        signature == "void poly_tobytes(uint8_t r[NTRUPLUS_POLYBYTES], const poly *a)",
        f"unexpected poly_tobytes signature: {signature}",
    )

    body = compact(extract_function_body(poly_text, "poly_tobytes"))
    expected_poly = (
        "int16_t t[2]; #pragma GCC unroll 2 "
        "for(size_t i = 0; i < NTRUPLUS_N/2; i++) { "
        "t[0] = a->coeffs[2*i]; "
        "t[0] += (t[0] >> 15) & NTRUPLUS_Q; "
        "t[1] = a->coeffs[2*i+1]; "
        "t[1] += (t[1] >> 15) & NTRUPLUS_Q; "
        "r[3*i+0] = (t[0] >> 0); "
        "r[3*i+1] = (t[0] >> 8) | (t[1] << 4); "
        "r[3*i+2] = (t[1] >> 4); "
        "}"
    )
    require(
        body == expected_poly,
        "C poly_tobytes() must keep the exact authoritative 384-triplet serialization loop",
    )

    keypair_body = compact(extract_function_body(kem_text, "crypto_kem_keypair_derand"))
    expected_keypair_chain = (
        "poly_basemul(&hinv, f, ginv); "
        "poly_tobytes(pk, &h); "
        "poly_tobytes(sk, f); "
        "poly_tobytes(sk + NTRUPLUS_POLYBYTES, &hinv);"
    )
    require(
        expected_keypair_chain in keypair_body,
        "crypto_kem_keypair_derand() must keep the verified hinv serialization seam",
    )
    require(
        keypair_body.count("poly_tobytes(sk + NTRUPLUS_POLYBYTES, &hinv);") == 1,
        "crypto_kem_keypair_derand() must contain exactly one hinv secret-key serialization call",
    )

    decap_body = compact(extract_function_body(kem_text, "crypto_kem_dec"))
    expected_decap = "poly_frombytes(&hinv, sk + NTRUPLUS_POLYBYTES);"
    require(
        expected_decap in decap_body,
        "crypto_kem_dec() must keep the verified hinv deserialization seam",
    )
    require(
        decap_body.count(expected_decap) == 1,
        "crypto_kem_dec() must contain exactly one hinv deserialization call",
    )


def verify_jasmin_text(text: str) -> None:
    stripped = strip_comments(text)
    signature = re.compile(
        rf"export fn {EXPECTED_EXPORT}\s*\(\s*"
        r"reg mut ptr u8\[NTRUPLUS_POLYBYTES\] rp\s*,\s*"
        r"reg const ptr u16\[NTRUPLUS_N\] ap\s*\)\s*->\s*"
        r"reg ptr u8\[NTRUPLUS_POLYBYTES\]"
    )
    require(signature.search(stripped) is not None, MISSING_SOURCE_HINT)
    require(
        '#[ct = "secret × secret → secret"]' in stripped,
        "Jasmin poly_tobytes() must keep the constant-time contract annotation",
    )
    require(
        "is_arr_init(ap,0,2 * NTRUPLUS_N)" in stripped
        and "is_arr_init(rp,0,NTRUPLUS_POLYBYTES)" in stripped,
        "Jasmin poly_tobytes() must keep the exact initialized-buffer contract",
    )
    expected_sct = (
        '{ ptr: transient, val: secret } ×\n'
        '{ ptr: transient, val: secret } →\n'
        '{ ptr: public, val: secret }'
    )
    require(
        expected_sct in stripped,
        "Jasmin poly_tobytes() must classify input/output pointers in the SCT contract",
    )

    export_body = compact(extract_function_body(text, EXPECTED_EXPORT))
    expected_export = compact(EXPECTED_JASMIN_TEMPLATE)
    expected_export = extract_function_body(expected_export, EXPECTED_EXPORT)
    require(
        export_body == compact(expected_export),
        "Jasmin poly_tobytes wrapper must keep the exact sign-fixup and 384-triplet serialization loop",
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

    mutated_sig = poly_text.replace(
        "void poly_tobytes(uint8_t r[NTRUPLUS_POLYBYTES], const poly *a)",
        "void poly_tobytes(unsigned char r[NTRUPLUS_POLYBYTES], const poly *a)",
        1,
    )
    require(mutated_sig != poly_text, "could not construct C signature mutation")
    expect_rejected(verify_c_text, mutated_sig, kem_text, label="C signature type")

    mutated_add = poly_text.replace(
        "t[1] += (t[1] >> 15) & NTRUPLUS_Q;",
        "t[1] -= (t[1] >> 15) & NTRUPLUS_Q;",
        1,
    )
    require(mutated_add != poly_text, "could not construct C canonicalization mutation")
    expect_rejected(verify_c_text, mutated_add, kem_text, label="C canonicalization sign fixup")

    mutated_store = poly_text.replace(
        "r[3*i+1] = (t[0] >> 8) | (t[1] << 4);",
        "r[3*i+1] = (t[0] >> 8) | (t[1] << 3);",
        1,
    )
    require(mutated_store != poly_text, "could not construct C middle-byte mutation")
    expect_rejected(verify_c_text, mutated_store, kem_text, label="C middle-byte packing")

    mutated_keypair = kem_text.replace(
        "poly_tobytes(sk + NTRUPLUS_POLYBYTES, &hinv);",
        "poly_tobytes(sk + NTRUPLUS_POLYBYTES, &h);",
        1,
    )
    require(mutated_keypair != kem_text, "could not construct keypair seam mutation")
    expect_rejected(verify_c_text, poly_text, mutated_keypair, label="keypair hinv serialization target")

    mutated_decap = kem_text.replace(
        "poly_frombytes(&hinv, sk + NTRUPLUS_POLYBYTES);",
        "poly_frombytes(&hinv, sk);",
        1,
    )
    require(mutated_decap != kem_text, "could not construct decap seam mutation")
    expect_rejected(verify_c_text, poly_text, mutated_decap, label="decap hinv source offset")

    mutated_jasmin_body = EXPECTED_JASMIN_TEMPLATE.replace("t1 += mask;", "t1 -= mask;", 1)
    require(
        mutated_jasmin_body != EXPECTED_JASMIN_TEMPLATE,
        "could not construct Jasmin body mutation",
    )
    expect_rejected(
        verify_jasmin_text,
        mutated_jasmin_body,
        label="Jasmin canonicalization body",
    )

    mutated_jasmin_contract = EXPECTED_JASMIN_TEMPLATE.replace(
        "is_arr_init(rp,0,NTRUPLUS_POLYBYTES)",
        "is_arr_init(rp,0,NTRUPLUS_POLYBYTES - 1)",
        1,
    )
    require(
        mutated_jasmin_contract != EXPECTED_JASMIN_TEMPLATE,
        "could not construct Jasmin contract mutation",
    )
    expect_rejected(
        verify_jasmin_text,
        mutated_jasmin_contract,
        label="Jasmin output initialization contract",
    )

    mutated_jasmin_signature = EXPECTED_JASMIN_TEMPLATE.replace(
        "reg const ptr u16[NTRUPLUS_N] ap",
        "reg mut ptr u16[NTRUPLUS_N] ap",
        1,
    )
    require(
        mutated_jasmin_signature != EXPECTED_JASMIN_TEMPLATE,
        "could not construct Jasmin signature mutation",
    )
    expect_rejected(
        verify_jasmin_text,
        mutated_jasmin_signature,
        label="Jasmin input pointer mutability",
    )


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fail-closed checker for the NTRU+768 poly_tobytes and hinv serialization seam",
    )
    parser.add_argument("--poly-source", required=True, help="path to NTRU+/NTRU+768/poly.c")
    parser.add_argument("--kem-source", required=True, help="path to NTRU+/NTRU+768/kem.c")
    parser.add_argument("--jasmin-source", required=True, help="path to ntruplus/jasmin/768/ref/poly_tobytes.jazz")
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
    except VerificationError as exc:
        print(f"poly_tobytes checker failed: {exc}", file=sys.stderr)
        return 1

    print("poly_tobytes checker passed")
    if args.self_check:
        print("poly_tobytes checker self-check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
