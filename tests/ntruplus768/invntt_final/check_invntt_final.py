#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


EXPECTED_EXPORT = "jade_ntruplus_ntruplus768_amd64_ref_invntt_final"
EXPECTED_Q = 3457
EXPECTED_HALF = 384
EXPECTED_ZMINUSZ5INV = -1665
EXPECTED_NINV = -811
EXPECTED_2NINV = -1622
MISSING_SOURCE_HINT = (
    "expected Jasmin source implementing export "
    "`jade_ntruplus_ntruplus768_amd64_ref_invntt_final` at "
    "ntruplus/jasmin/768/ref/invntt_final.jazz with signature "
    "`(reg mut ptr u16[NTRUPLUS_N] rp) -> reg ptr u16[NTRUPLUS_N]`"
)


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


def build_expected_jasmin_source() -> str:
    return "\n".join(
        [
            "param int NTRUPLUS_N = 768;",
            "param int NTRUPLUS_Q = 3457;",
            "param int NTRUPLUS_QINV = 12929;",
            "param int NTRUPLUS_ZMINUSZ5INV = -1665;",
            "param int NTRUPLUS_NINV = -811;",
            "param int NTRUPLUS_2NINV = -1622;",
            "",
            "inline fn __mul_i16(reg u16 a b) -> reg u32",
            "{",
            "  reg u32 ad;",
            "  reg u32 bd;",
            "  reg u32 c;",
            "",
            "  ad = (32s) a;",
            "  bd = (32s) b;",
            "  c = ad * bd;",
            "  return c;",
            "}",
            "",
            "inline fn __montgomery_reduce(reg u32 a) -> reg u16",
            "{",
            "  reg u16 t;",
            "  reg u32 q;",
            "  reg u32 td;",
            "  reg u32 r;",
            "",
            "  q = NTRUPLUS_Q;",
            "  td = (32s) a;",
            "  td *= NTRUPLUS_QINV;",
            "  t = td;",
            "  td = (32s) t;",
            "  r = (32s) a;",
            "  td *= q;",
            "  r -= td;",
            "  r >>s= 16;",
            "  t = r;",
            "  return t;",
            "}",
            "",
            "#[safety =",
            "   { requires = is_arr_init(rp,0,2 * NTRUPLUS_N)",
            "   , ensures = is_arr_init(rp,0,2 * NTRUPLUS_N)",
            "   }",
            "]",
            "#[ct = \"secret → secret\"]",
            "#[sct=\"",
            "{ ptr: transient, val: secret } →",
            "{ ptr: public, val: secret }",
            "\"]",
            f"export fn {EXPECTED_EXPORT}(",
            "  reg mut ptr u16[NTRUPLUS_N] rp) -> reg ptr u16[NTRUPLUS_N]",
            "{",
            "  reg u16 lo;",
            "  reg u16 hi;",
            "  reg u16 t1;",
            "  reg u16 t2;",
            "  reg u16 td;",
            "  reg u32 acc;",
            "  reg u64 i;",
            "",
            "  _ = #init_msf();",
            "  i = 0;",
            "  while (i < NTRUPLUS_N / 2) {",
            "    lo = rp[i];",
            "    hi = rp[i + NTRUPLUS_N / 2];",
            "    t1 = lo;",
            "    t1 += hi;",
            "    td = lo;",
            "    td -= hi;",
            "    acc = __mul_i16(NTRUPLUS_ZMINUSZ5INV, td);",
            "    t2 = __montgomery_reduce(acc);",
            "    td = t1;",
            "    td -= t2;",
            "    acc = __mul_i16(NTRUPLUS_NINV, td);",
            "    rp[i] = __montgomery_reduce(acc);",
            "    acc = __mul_i16(NTRUPLUS_2NINV, t2);",
            "    rp[i + NTRUPLUS_N / 2] = __montgomery_reduce(acc);",
            "    i += 1;",
            "  }",
            "",
            "  return rp;",
            "}",
            "",
        ]
    )


EXPECTED_JASMIN_SOURCE = build_expected_jasmin_source()


def verify_c_text(text: str) -> None:
    for name, value in (
        ("NTRUPLUS_ZMINUSZ5INV", EXPECTED_ZMINUSZ5INV),
        ("NTRUPLUS_NINV", EXPECTED_NINV),
        ("NTRUPLUS_2NINV", EXPECTED_2NINV),
    ):
        require(
            re.search(rf"#define\s+{name}\s+{value}\b", text) is not None,
            f"expected C {name} == {value}",
        )

    body = compact(extract_function_body(text, "invntt"))
    final_stage = re.compile(
        r"for \(int i = 0; i < NTRUPLUS_N/2; i\+\+\) \{ "
        r"t1 = r\[i\] \+ r\[i \+ NTRUPLUS_N/2\]; "
        r"t2 = fqmul\(NTRUPLUS_ZMINUSZ5INV, r\[i\] - r\[i \+ NTRUPLUS_N/2\]\); "
        r"r\[i\] = fqmul\(NTRUPLUS_NINV, t1 - t2\); "
        r"r\[i \+ NTRUPLUS_N/2\] = fqmul\(NTRUPLUS_2NINV, t2\); \}"
    )
    require(
        final_stage.search(body) is not None,
        "C invntt() final pair loop no longer matches the verified half-offset, constants, or arithmetic polarity",
    )
    require(
        re.search(r"for\s*\(\s*int\s+i\s*=\s*0\s*;\s*i\s*<\s*NTRUPLUS_N/2\s*;\s*i\+\+\s*\)", body)
        is not None,
        "C invntt() final pair loop must iterate over exactly NTRUPLUS_N/2 lanes",
    )


def verify_jasmin_text(text: str) -> None:
    source = compact(text)
    for name, value in (
        ("NTRUPLUS_N", 768),
        ("NTRUPLUS_Q", 3457),
        ("NTRUPLUS_QINV", 12929),
        ("NTRUPLUS_ZMINUSZ5INV", -1665),
        ("NTRUPLUS_NINV", -811),
        ("NTRUPLUS_2NINV", -1622),
    ):
        require(
            re.search(rf"param int {name} = {value};", source) is not None,
            f"Jasmin inverse final slice must fix {name} == {value}",
        )

    require(
        re.search(
            rf"export fn {EXPECTED_EXPORT}\(\s*reg mut ptr u16\[NTRUPLUS_N\] rp\s*\) -> reg ptr u16\[NTRUPLUS_N\]",
            text,
            flags=re.S,
        )
        is not None,
        MISSING_SOURCE_HINT,
    )

    mul_body = compact(extract_function_body(text, "__mul_i16"))
    require(
        re.fullmatch(
            r"reg u32 ad; reg u32 bd; reg u32 c; ad = \(32s\) a; bd = \(32s\) b; c = ad \* bd; return c;",
            mul_body,
        )
        is not None,
        "Jasmin signed 16x16 multiply helper no longer matches the verified data flow",
    )

    montgomery_body = compact(extract_function_body(text, "__montgomery_reduce"))
    require(
        re.fullmatch(
            r"reg u16 t; reg u32 q; reg u32 td; reg u32 r; "
            r"q = NTRUPLUS_Q; td = \(32s\) a; td \*= NTRUPLUS_QINV; t = td; "
            r"td = \(32s\) t; r = \(32s\) a; td \*= q; r -= td; r >>s= 16; t = r; return t;",
            montgomery_body,
        )
        is not None,
        "Jasmin Montgomery reducer no longer matches the verified Q/QINV data flow",
    )

    body = compact(extract_function_body(text, EXPECTED_EXPORT))
    stage = re.compile(
        r"reg u16 lo; reg u16 hi; reg u16 t1; reg u16 t2; reg u16 td; reg u32 acc; reg u64 i; "
        r"_ = #init_msf\(\); "
        r"i = 0; while \(i < NTRUPLUS_N / 2\) \{ "
        r"lo = rp\[i\]; hi = rp\[i \+ NTRUPLUS_N / 2\]; "
        r"t1 = lo; t1 \+= hi; "
        r"td = lo; td -= hi; acc = __mul_i16\(NTRUPLUS_ZMINUSZ5INV, td\); t2 = __montgomery_reduce\(acc\); "
        r"td = t1; td -= t2; acc = __mul_i16\(NTRUPLUS_NINV, td\); rp\[i\] = __montgomery_reduce\(acc\); "
        r"acc = __mul_i16\(NTRUPLUS_2NINV, t2\); rp\[i \+ NTRUPLUS_N / 2\] = __montgomery_reduce\(acc\); i \+= 1; \} "
        r"return rp;"
    )
    require(
        stage.search(body) is not None,
        "Jasmin inverse final slice no longer matches the verified half-offset, constants, or arithmetic polarity",
    )


def expect_rejected(check, text: str, label: str) -> None:
    try:
        check(text)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(c_text: str) -> None:
    verify_c_text(c_text)
    verify_jasmin_text(EXPECTED_JASMIN_SOURCE)

    mutated_c_polarity = c_text.replace(
        "t2 = fqmul(NTRUPLUS_ZMINUSZ5INV, r[i] - r[i + NTRUPLUS_N/2]);",
        "t2 = fqmul(NTRUPLUS_ZMINUSZ5INV, r[i + NTRUPLUS_N/2] - r[i]);",
        1,
    )
    require(mutated_c_polarity != c_text, "could not construct C final-stage polarity mutation")
    expect_rejected(verify_c_text, mutated_c_polarity, "C final stage uses wrong difference polarity")

    mutated_c_ninv = c_text.replace(
        "r[i               ] = fqmul(NTRUPLUS_NINV, t1 - t2);",
        "r[i               ] = fqmul(NTRUPLUS_2NINV, t1 - t2);",
        1,
    )
    require(mutated_c_ninv != c_text, "could not construct C final-stage NINV mutation")
    expect_rejected(verify_c_text, mutated_c_ninv, "C final stage uses wrong low-lane scalar")

    mutated_c_high = c_text.replace(
        "r[i + NTRUPLUS_N/2] = fqmul(NTRUPLUS_2NINV, t2);",
        "r[i + NTRUPLUS_N/2] = fqmul(NTRUPLUS_NINV, t2);",
        1,
    )
    require(mutated_c_high != c_text, "could not construct C final-stage high-lane scalar mutation")
    expect_rejected(verify_c_text, mutated_c_high, "C final stage uses wrong high-lane scalar")

    mutated_jasmin_const = EXPECTED_JASMIN_SOURCE.replace(
        "param int NTRUPLUS_ZMINUSZ5INV = -1665;",
        "param int NTRUPLUS_ZMINUSZ5INV = -811;",
        1,
    )
    expect_rejected(verify_jasmin_text, mutated_jasmin_const, "Jasmin wrong final-stage zminusz5inv")

    mutated_jasmin_half = EXPECTED_JASMIN_SOURCE.replace(
        "while (i < NTRUPLUS_N / 2) {",
        "while (i < 256) {",
        1,
    )
    expect_rejected(verify_jasmin_text, mutated_jasmin_half, "Jasmin wrong half-loop bound")

    mutated_jasmin_polarity = EXPECTED_JASMIN_SOURCE.replace(
        "td = lo;\n    td -= hi;",
        "td = hi;\n    td -= lo;",
        1,
    )
    expect_rejected(verify_jasmin_text, mutated_jasmin_polarity, "Jasmin wrong final-stage difference polarity")

    mutated_jasmin_low = EXPECTED_JASMIN_SOURCE.replace(
        "acc = __mul_i16(NTRUPLUS_NINV, td);",
        "acc = __mul_i16(NTRUPLUS_2NINV, td);",
        1,
    )
    expect_rejected(verify_jasmin_text, mutated_jasmin_low, "Jasmin wrong low-lane scalar")

    mutated_jasmin_high = EXPECTED_JASMIN_SOURCE.replace(
        "acc = __mul_i16(NTRUPLUS_2NINV, t2);",
        "acc = __mul_i16(NTRUPLUS_NINV, t2);",
        1,
    )
    expect_rejected(verify_jasmin_text, mutated_jasmin_high, "Jasmin wrong high-lane scalar")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Tie the standalone Jasmin NTRU+768 invntt final slice to the C final pair loop."
    )
    parser.add_argument("--c-source", required=True, help="path to NTRU+/NTRU+768/ntt.c")
    parser.add_argument("--jasmin-source", required=True, help="path to invntt_final.jazz")
    parser.add_argument("--self-check", action="store_true", help="also require representative bad mutations to be rejected")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        c_text = Path(args.c_source).read_text(encoding="utf-8")
        verify_c_text(c_text)

        jasmin_path = Path(args.jasmin_source)
        if jasmin_path.exists():
            jasmin_text = jasmin_path.read_text(encoding="utf-8")
            verify_jasmin_text(jasmin_text)
        elif args.self_check:
            verify_jasmin_text(EXPECTED_JASMIN_SOURCE)
        else:
            raise VerificationError(f"{MISSING_SOURCE_HINT}; missing file `{jasmin_path}`")

        if args.self_check:
            run_self_check(c_text)
    except (OSError, VerificationError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1

    if args.self_check:
        print("PASS: NTRU+768 invntt final checker rejected representative bad mutations")
    print("PASS: NTRU+768 invntt final C/Jasmin source coupling")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
