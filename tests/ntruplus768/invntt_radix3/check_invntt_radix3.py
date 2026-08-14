#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


EXPECTED_ZETAS = [-682, -248, -708, 682]
EXPECTED_OMEGA = -886
EXPECTED_EXPORT = "jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3"
EXPECTED_C_START = 2
EXPECTED_PRE_TAIL_K = 5
EXPECTED_FINAL_K = 1
MISSING_SOURCE_HINT = (
    "expected Jasmin source implementing export "
    "`jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3` at "
    "ntruplus/jasmin/768/ref/invntt_radix3.jazz with signature "
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


def parse_c_zetas(text: str) -> list[int]:
    match = re.search(r"const\s+int16_t\s+zetas\s*\[\s*192\s*\]\s*=\s*\{(.*?)\};", text, flags=re.S)
    require(match is not None, "could not find the 192-entry C zetas table")
    return [int(token) for token in re.findall(r"-?\d+", match.group(1))]


def parse_inv_tail_schedule() -> tuple[int, int, int]:
    step4_blocks = 768 // (2 * 4)
    step8_blocks = 768 // (2 * 8)
    step16_blocks = 768 // (2 * 16)
    step32_blocks = 768 // (2 * 32)
    step64_blocks = 768 // (2 * 64)
    pre_tail_k = 191 - (step4_blocks + step8_blocks + step16_blocks + step32_blocks + step64_blocks)
    block_count = 768 // 384
    start_index = pre_tail_k - ((2 * block_count) - 1)
    final_k = pre_tail_k - (2 * block_count)
    return start_index, pre_tail_k, final_k


def build_expected_jasmin_source() -> str:
    return "\n".join(
        [
            "param int NTRUPLUS_N = 768;",
            "param int NTRUPLUS_Q = 3457;",
            "param int NTRUPLUS_QINV = 12929;",
            "param int NTRUPLUS_OMEGA = -886;",
            "param int NTRUPLUS_ZETA2 = -682;",
            "param int NTRUPLUS_ZETA3 = -248;",
            "param int NTRUPLUS_ZETA4 = -708;",
            "param int NTRUPLUS_ZETA5 = 682;",
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
            "  reg u16 a0;",
            "  reg u16 a1;",
            "  reg u16 a2;",
            "  reg u16 t1;",
            "  reg u16 t2;",
            "  reg u16 t3;",
            "  reg u16 td;",
            "  reg u16 r0;",
            "  reg u32 acc;",
            "  reg u64 i;",
            "",
            "  _ = #init_msf();",
            "  i = 0;",
            "  while (i < 128) {",
            "    a0 = rp[i];",
            "    a1 = rp[i + 128];",
            "    a2 = rp[i + 256];",
            "    td = a1;",
            "    td -= a0;",
            "    acc = __mul_i16(NTRUPLUS_OMEGA, td);",
            "    t1 = __montgomery_reduce(acc);",
            "    td = a2;",
            "    td -= a0;",
            "    td += t1;",
            "    acc = __mul_i16(NTRUPLUS_ZETA4, td);",
            "    t2 = __montgomery_reduce(acc);",
            "    td = a2;",
            "    td -= a1;",
            "    td -= t1;",
            "    acc = __mul_i16(NTRUPLUS_ZETA5, td);",
            "    t3 = __montgomery_reduce(acc);",
            "    r0 = a0;",
            "    r0 += a1;",
            "    r0 += a2;",
            "    rp[i] = r0;",
            "    rp[i + 128] = t2;",
            "    rp[i + 256] = t3;",
            "    i += 1;",
            "  }",
            "  i = 384;",
            "  while (i < 512) {",
            "    a0 = rp[i];",
            "    a1 = rp[i + 128];",
            "    a2 = rp[i + 256];",
            "    td = a1;",
            "    td -= a0;",
            "    acc = __mul_i16(NTRUPLUS_OMEGA, td);",
            "    t1 = __montgomery_reduce(acc);",
            "    td = a2;",
            "    td -= a0;",
            "    td += t1;",
            "    acc = __mul_i16(NTRUPLUS_ZETA2, td);",
            "    t2 = __montgomery_reduce(acc);",
            "    td = a2;",
            "    td -= a1;",
            "    td -= t1;",
            "    acc = __mul_i16(NTRUPLUS_ZETA3, td);",
            "    t3 = __montgomery_reduce(acc);",
            "    r0 = a0;",
            "    r0 += a1;",
            "    r0 += a2;",
            "    rp[i] = r0;",
            "    rp[i + 128] = t2;",
            "    rp[i + 256] = t3;",
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
    zetas = parse_c_zetas(text)
    require(len(zetas) == 192, f"expected 192 C twiddles, found {len(zetas)}")
    require(
        zetas[2:6] == EXPECTED_ZETAS,
        f"expected C zetas[2:6] == {EXPECTED_ZETAS}, found {zetas[2:6]}",
    )
    require(
        re.search(rf"#define\s+NTRUPLUS_OMEGA\s+{EXPECTED_OMEGA}\b", text) is not None,
        f"expected C NTRUPLUS_OMEGA == {EXPECTED_OMEGA}",
    )

    body = compact(extract_function_body(text, "invntt"))
    copy_prefix = re.compile(
        r"int16_t t1, t2, t3; int16_t zeta1, zeta2; int k = 191; "
        r"for \(int i = 0; i < NTRUPLUS_N; i\+\+\) \{ r\[i\] = a\[i\]; \} "
    )
    head_stage = re.compile(
        r"for \(int step = 4; step <= 64; step <<= 1\) \{ "
        r"for \(int start = 0; start < NTRUPLUS_N; start \+= \(step << 1\)\) \{ "
        r"zeta1 = zetas\[k--\]; "
        r"for \(int i = start; i < start \+ step; i\+\+\) \{ "
        r"t1 = r\[i \+ step\]; "
        r"r\[i \+ step\] = fqmul\(zeta1, t1 - r\[i\]\); "
        r"r\[i\] = barrett_reduce\(r\[i\] \+ t1\); \} \} \}"
    )
    tail_stage = re.compile(
        r"for \(int start = 0; start < NTRUPLUS_N; start \+= 384\) \{ "
        r"zeta2 = zetas\[k--\]; zeta1 = zetas\[k--\]; "
        r"for \(int i = start; i < start \+ 128; i\+\+\) \{ "
        r"t1 = fqmul\(NTRUPLUS_OMEGA, r\[i \+ 128\] - r\[i\]\); "
        r"t2 = fqmul\(zeta1, r\[i \+ 256\] - r\[i\] \+ t1\); "
        r"t3 = fqmul\(zeta2, r\[i \+ 256\] - r\[i \+ 128\] - t1\); "
        r"r\[i\] = r\[i\] \+ r\[i \+ 128\] \+ r\[i \+ 256\]; "
        r"r\[i \+ 128\] = t2; r\[i \+ 256\] = t3; \} \}"
    )
    require(copy_prefix.search(body) is not None, "C invntt() no longer copies input into the working output")
    require(head_stage.search(body) is not None, "C invntt() radix-2 head no longer matches the verified step=4->64 schedule")
    require(
        tail_stage.search(body) is not None,
        "C invntt() inverse radix-3 tail no longer matches the verified zeta order, offsets, or arithmetic polarity",
    )

    start_index, pre_tail_k, final_k = parse_inv_tail_schedule()
    require(start_index == EXPECTED_C_START, f"derived C inverse radix-3 zeta start changed from {EXPECTED_C_START} to {start_index}")
    require(pre_tail_k == EXPECTED_PRE_TAIL_K, f"derived C inverse radix-3 entry k changed from {EXPECTED_PRE_TAIL_K} to {pre_tail_k}")
    require(final_k == EXPECTED_FINAL_K, f"derived C inverse radix-3 exit k changed from {EXPECTED_FINAL_K} to {final_k}")


def verify_jasmin_text(text: str) -> None:
    source = compact(text)
    for name, value in (
        ("NTRUPLUS_N", 768),
        ("NTRUPLUS_Q", 3457),
        ("NTRUPLUS_QINV", 12929),
        ("NTRUPLUS_OMEGA", -886),
        ("NTRUPLUS_ZETA2", -682),
        ("NTRUPLUS_ZETA3", -248),
        ("NTRUPLUS_ZETA4", -708),
        ("NTRUPLUS_ZETA5", 682),
    ):
        require(
            re.search(rf"param int {name} = {value};", source) is not None,
            f"Jasmin inverse radix-3 slice must fix {name} == {value}",
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
        r"reg u16 a0; reg u16 a1; reg u16 a2; reg u16 t1; reg u16 t2; reg u16 t3; "
        r"reg u16 td; reg u16 r0; reg u32 acc; reg u64 i; "
        r"_ = #init_msf\(\); "
        r"i = 0; while \(i < 128\) \{ "
        r"a0 = rp\[i\]; a1 = rp\[i \+ 128\]; a2 = rp\[i \+ 256\]; "
        r"td = a1; td -= a0; acc = __mul_i16\(NTRUPLUS_OMEGA, td\); t1 = __montgomery_reduce\(acc\); "
        r"td = a2; td -= a0; td \+= t1; acc = __mul_i16\(NTRUPLUS_ZETA4, td\); t2 = __montgomery_reduce\(acc\); "
        r"td = a2; td -= a1; td -= t1; acc = __mul_i16\(NTRUPLUS_ZETA5, td\); t3 = __montgomery_reduce\(acc\); "
        r"r0 = a0; r0 \+= a1; r0 \+= a2; "
        r"rp\[i\] = r0; rp\[i \+ 128\] = t2; rp\[i \+ 256\] = t3; i \+= 1; \} "
        r"i = 384; while \(i < 512\) \{ "
        r"a0 = rp\[i\]; a1 = rp\[i \+ 128\]; a2 = rp\[i \+ 256\]; "
        r"td = a1; td -= a0; acc = __mul_i16\(NTRUPLUS_OMEGA, td\); t1 = __montgomery_reduce\(acc\); "
        r"td = a2; td -= a0; td \+= t1; acc = __mul_i16\(NTRUPLUS_ZETA2, td\); t2 = __montgomery_reduce\(acc\); "
        r"td = a2; td -= a1; td -= t1; acc = __mul_i16\(NTRUPLUS_ZETA3, td\); t3 = __montgomery_reduce\(acc\); "
        r"r0 = a0; r0 \+= a1; r0 \+= a2; "
        r"rp\[i\] = r0; rp\[i \+ 128\] = t2; rp\[i \+ 256\] = t3; i \+= 1; \} "
        r"return rp;"
    )
    require(
        stage.search(body) is not None,
        "Jasmin inverse radix-3 slice no longer matches the verified explicit blocks, offsets, or arithmetic polarity",
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

    mutated_c_twiddle = c_text.replace("zeta2 = zetas[k--];\n\t\tzeta1 = zetas[k--];", "zeta1 = zetas[k--];\n\t\tzeta2 = zetas[k--];", 1)
    require(mutated_c_twiddle != c_text, "could not construct C inverse radix-3 twiddle-order mutation")
    expect_rejected(verify_c_text, mutated_c_twiddle, "C swapped inverse radix-3 twiddle order")

    mutated_c_omega_input = c_text.replace("t1 = fqmul(NTRUPLUS_OMEGA, r[i + 128] - r[i]);", "t1 = fqmul(NTRUPLUS_OMEGA, r[i] - r[i + 128]);", 1)
    require(mutated_c_omega_input != c_text, "could not construct C inverse radix-3 omega-input mutation")
    expect_rejected(verify_c_text, mutated_c_omega_input, "C inverse radix-3 omega uses wrong polarity")

    mutated_c_t2 = c_text.replace("t2 = fqmul(zeta1, r[i + 256] - r[i]       + t1);", "t2 = fqmul(zeta1, r[i + 256] - r[i]       - t1);", 1)
    require(mutated_c_t2 != c_text, "could not construct C inverse radix-3 t2 mutation")
    expect_rejected(verify_c_text, mutated_c_t2, "C inverse radix-3 t2 uses wrong sign")

    mutated_c_t3 = c_text.replace("t3 = fqmul(zeta2, r[i + 256] - r[i + 128] - t1);", "t3 = fqmul(zeta2, r[i + 256] - r[i + 128] + t1);", 1)
    require(mutated_c_t3 != c_text, "could not construct C inverse radix-3 t3 mutation")
    expect_rejected(verify_c_text, mutated_c_t3, "C inverse radix-3 t3 uses wrong sign")

    mutated_jasmin_zeta = EXPECTED_JASMIN_SOURCE.replace("param int NTRUPLUS_ZETA4 = -708;", "param int NTRUPLUS_ZETA4 = -682;", 1)
    expect_rejected(verify_jasmin_text, mutated_jasmin_zeta, "Jasmin wrong fixed radix-3 twiddle")

    mutated_jasmin_block = EXPECTED_JASMIN_SOURCE.replace("i = 384;", "i = 256;", 1)
    expect_rejected(verify_jasmin_text, mutated_jasmin_block, "Jasmin wrong second inverse radix-3 base")

    mutated_jasmin_offset = EXPECTED_JASMIN_SOURCE.replace("a2 = rp[i + 256];", "a2 = rp[i + 128];", 1)
    expect_rejected(verify_jasmin_text, mutated_jasmin_offset, "Jasmin wrong inverse radix-3 high offset")

    mutated_jasmin_omega = EXPECTED_JASMIN_SOURCE.replace("td = a1;\n    td -= a0;", "td = a0;\n    td -= a1;", 1)
    expect_rejected(verify_jasmin_text, mutated_jasmin_omega, "Jasmin wrong inverse radix-3 omega polarity")

    mutated_jasmin_t2 = EXPECTED_JASMIN_SOURCE.replace("td += t1;", "td -= t1;", 1)
    expect_rejected(verify_jasmin_text, mutated_jasmin_t2, "Jasmin wrong inverse radix-3 t2 sign")

    mutated_jasmin_t3 = EXPECTED_JASMIN_SOURCE.replace("td -= t1;", "td += t1;", 1)
    expect_rejected(verify_jasmin_text, mutated_jasmin_t3, "Jasmin wrong inverse radix-3 t3 sign")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Tie the standalone Jasmin NTRU+768 inverse radix-3 slice to the C inverse tail."
    )
    parser.add_argument("--c-source", required=True, help="path to NTRU+/NTRU+768/ntt.c")
    parser.add_argument("--jasmin-source", required=True, help="path to invntt_radix3.jazz")
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
        print("PASS: NTRU+768 inverse radix-3 checker rejected representative bad mutations")
    print("PASS: NTRU+768 inverse radix-3 C/Jasmin source coupling")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
