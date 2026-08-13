#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


C_WINDOW_ZETAS = [
    1449,
    837,
    901,
    1637,
    -569,
    -1617,
    -1530,
    1199,
    50,
    -830,
    -625,
    4,
    176,
    -156,
    1257,
    -1507,
    -380,
    -606,
    1293,
    661,
    1428,
    -1580,
    -565,
    -992,
    548,
    -800,
    64,
    -371,
    961,
    641,
    87,
    630,
    675,
    -834,
    205,
    54,
    -1081,
    1351,
    1413,
    -1331,
    -1673,
    -1267,
    -1558,
    281,
    -1464,
    -588,
    1015,
    436,
]
EXPECTED_ZETAS = list(reversed(C_WINDOW_ZETAS))
EXPECTED_EXPORT = "jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8"
EXPECTED_HELPER = "__invntt_radix2_8_block"
EXPECTED_BASES = list(range(0, 768, 16))
EXPECTED_OFFSET = 8
EXPECTED_C_START = 95
EXPECTED_PARAM_START = 48
EXPECTED_PARAM_STOP = 95
MISSING_SOURCE_HINT = (
    "expected Jasmin source implementing export "
    "`jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8` at "
    "ntruplus/jasmin/768/ref/invntt_radix2_8.jazz with signature "
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


def parse_inv_tail_schedule() -> tuple[int, int, list[int]]:
    step4_blocks = 768 // (2 * 4)
    step8_blocks = 768 // (2 * EXPECTED_OFFSET)
    start_index = 191 - step4_blocks
    return start_index, step8_blocks, [block * (EXPECTED_OFFSET << 1) for block in range(step8_blocks)]


def build_expected_jasmin_source() -> str:
    header = [
        "param int NTRUPLUS_N = 768;",
        "param int NTRUPLUS_Q = 3457;",
        "param int NTRUPLUS_QINV = 12929;",
        "param int NTRUPLUS_BARRETT_V = 19412;",
        "param int NTRUPLUS_BARRETT_BIAS = 33554432;",
    ]
    zeta_params = [
        f"param int NTRUPLUS_ZETA{index} = {value};"
        for index, value in enumerate(C_WINDOW_ZETAS, start=EXPECTED_PARAM_START)
    ]
    helper_calls = [
        f"  rp = {EXPECTED_HELPER}(rp, {base}, NTRUPLUS_ZETA{index});"
        for index, base in zip(range(EXPECTED_PARAM_STOP, EXPECTED_PARAM_START - 1, -1), EXPECTED_BASES, strict=True)
    ]
    return "\n".join(
        header
        + zeta_params
        + [
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
            "inline fn __barrett_reduce(reg u16 a) -> reg u16",
            "{",
            "  reg u16 t;",
            "  reg u32 td;",
            "  reg u32 v;",
            "  reg u32 q;",
            "",
            "  v = NTRUPLUS_BARRETT_V;",
            "  td = (32s) a;",
            "  td *= v;",
            "  td += NTRUPLUS_BARRETT_BIAS;",
            "  td >>s= 26;",
            "  t = td;",
            "  q = NTRUPLUS_Q;",
            "  td = (32s) t;",
            "  td *= q;",
            "  t = td;",
            "  t = a - t;",
            "  return t;",
            "}",
            "",
            "#[safety =",
            "   { requires = is_arr_init(rp,0,2 * NTRUPLUS_N)",
            "   , ensures = is_arr_init(rp,0,2 * NTRUPLUS_N)",
            "   }",
            "]",
            f"inline fn {EXPECTED_HELPER}(",
            "  reg mut ptr u16[NTRUPLUS_N] rp,",
            "  reg u64 base,",
            "  reg u16 zeta) -> reg ptr u16[NTRUPLUS_N]",
            "{",
            "  reg u16 low;",
            "  reg u16 high;",
            "  reg u16 sum;",
            "  reg u16 diff;",
            "  reg u16 prod;",
            "  reg u32 acc;",
            "  reg u64 i;",
            "  reg u64 stop;",
            "  reg u32 wd;",
            "  reg u32 td;",
            "",
            "  i = base;",
            "  stop = base;",
            "  stop += 8;",
            "  while (i < stop) {",
            "    low = rp[i];",
            "    high = rp[i + 8];",
            "",
            "    wd = (32s) low;",
            "    td = (32s) high;",
            "    wd += td;",
            "    sum = wd;",
            "",
            "    wd = (32s) high;",
            "    td = (32s) low;",
            "    wd -= td;",
            "    diff = wd;",
            "",
            "    sum = __barrett_reduce(sum);",
            "    acc = __mul_i16(zeta, diff);",
            "    prod = __montgomery_reduce(acc);",
            "    rp[i] = sum;",
            "    rp[i + 8] = prod;",
            "    i += 1;",
            "  }",
            "",
            "  return rp;",
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
            "  _ = #init_msf();",
            *helper_calls,
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
        list(reversed(zetas[48:96])) == EXPECTED_ZETAS,
        f"expected reversed C zetas[48:96] == {EXPECTED_ZETAS}, found {list(reversed(zetas[48:96]))}",
    )

    body = compact(extract_function_body(text, "invntt"))
    copy_prefix = re.compile(
        r"int16_t t1, t2, t3; int16_t zeta1, zeta2; int k = 191; "
        r"for \(int i = 0; i < NTRUPLUS_N; i\+\+\) \{ r\[i\] = a\[i\]; \} "
    )
    prefix_match = copy_prefix.search(body)
    require(prefix_match is not None, "C invntt() no longer copies input into the working output before the inverse radix-2 head")

    stage = re.compile(
        r"for \(int step = 4; step <= 64; step <<= 1\) \{ "
        r"for \(int start = 0; start < NTRUPLUS_N; start \+= \(step << 1\)\) \{ "
        r"zeta1 = zetas\[k--\]; "
        r"for \(int i = start; i < start \+ step; i\+\+\) \{ "
        r"t1 = r\[i \+ step\]; "
        r"r\[i \+ step\] = fqmul\(zeta1, t1 - r\[i\]\); "
        r"r\[i\] = barrett_reduce\(r\[i\] \+ t1\); \} \} \}"
    )
    stage_match = stage.search(body)
    require(
        stage_match is not None,
        "C invntt() radix-2 head no longer matches the verified step=4->8->16->32->64 schedule and fqmul/barrett flow",
    )
    require(
        prefix_match.end() <= stage_match.start(),
        "C invntt() no longer executes the copy prefix before the inverse radix-2 head",
    )

    start_index, block_count, bases = parse_inv_tail_schedule()
    require(start_index == EXPECTED_C_START, f"derived C inverse step8 zeta start changed from {EXPECTED_C_START} to {start_index}")
    require(block_count == 48, f"derived C inverse step8 block count changed from 48 to {block_count}")
    require(bases == EXPECTED_BASES, f"derived C inverse step8 bases changed: expected {EXPECTED_BASES}, found {bases}")


def verify_jasmin_text(text: str) -> None:
    source = compact(text)
    for name, value in (
        ("NTRUPLUS_N", 768),
        ("NTRUPLUS_Q", 3457),
        ("NTRUPLUS_QINV", 12929),
        ("NTRUPLUS_BARRETT_V", 19412),
        ("NTRUPLUS_BARRETT_BIAS", 33554432),
    ):
        require(
            re.search(rf"param int {name} = {value};", source) is not None,
            f"Jasmin inverse radix-2 slice must fix {name} == {value}",
        )
    for index, value in enumerate(C_WINDOW_ZETAS, start=EXPECTED_PARAM_START):
        require(
            re.search(rf"param int NTRUPLUS_ZETA{index} = {value};", source) is not None,
            f"Jasmin inverse radix-2 slice must fix NTRUPLUS_ZETA{index} == {value}",
        )

    require(f"export fn {EXPECTED_EXPORT}(" in source, f"missing expected Jasmin export `{EXPECTED_EXPORT}`")
    require(f"inline fn {EXPECTED_HELPER}(" in source, f"missing expected Jasmin helper `{EXPECTED_HELPER}`")
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

    barrett_body = compact(extract_function_body(text, "__barrett_reduce"))
    require(
        re.fullmatch(
            r"reg u16 t; reg u32 td; reg u32 v; reg u32 q; "
            r"v = NTRUPLUS_BARRETT_V; td = \(32s\) a; td \*= v; td \+= NTRUPLUS_BARRETT_BIAS; "
            r"td >>s= 26; t = td; q = NTRUPLUS_Q; td = \(32s\) t; td \*= q; t = td; t = a - t; return t;",
            barrett_body,
        )
        is not None,
        "Jasmin Barrett reducer no longer matches the verified rounding and subtraction data flow",
    )

    helper_body = compact(extract_function_body(text, EXPECTED_HELPER))
    helper_pattern = re.compile(
        r"reg u16 low; reg u16 high; reg u16 sum; reg u16 diff; reg u16 prod; "
        r"reg u32 acc; reg u64 i; reg u64 stop; reg u32 wd; reg u32 td; "
        r"i = base; stop = base; stop \+= 8; while \(i < stop\) \{ "
        r"low = rp\[i\]; high = rp\[i \+ 8\]; "
        r"wd = \(32s\) low; td = \(32s\) high; wd \+= td; sum = wd; "
        r"wd = \(32s\) high; td = \(32s\) low; wd -= td; diff = wd; "
        r"sum = __barrett_reduce\(sum\); "
        r"acc = __mul_i16\(zeta, diff\); prod = __montgomery_reduce\(acc\); "
        r"rp\[i\] = sum; rp\[i \+ 8\] = prod; i \+= 1; \} return rp;"
    )
    require(
        helper_pattern.search(helper_body) is not None,
        "Jasmin inverse radix-2 helper no longer matches the verified in-place step=8 flow",
    )

    export_body = compact(extract_function_body(text, EXPECTED_EXPORT))
    expected_calls = " ".join(
        f"rp = {EXPECTED_HELPER}(rp, {base}, NTRUPLUS_ZETA{index});"
        for index, base in zip(range(EXPECTED_PARAM_STOP, EXPECTED_PARAM_START - 1, -1), EXPECTED_BASES, strict=True)
    )
    call_pattern = re.compile(rf"_ = #init_msf\(\); {re.escape(expected_calls)} return rp;")
    require(
        call_pattern.search(export_body) is not None,
        "Jasmin inverse radix-2 export no longer matches the verified 48-block descending-zeta schedule",
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

    mutated_c_zeta_window = c_text.replace(
        " 1449,   837,   901,  1637,  -569, -1617, -1530,  1199,",
        "  837,  1449,   901,  1637,  -569, -1617, -1530,  1199,",
        1,
    )
    require(mutated_c_zeta_window != c_text, "could not construct C inverse step8 zeta-order mutation")
    expect_rejected(verify_c_text, mutated_c_zeta_window, "C wrong inverse step8 zeta order")

    mutated_c_tail = c_text.replace(
        "for (int step = 4; step <= 64; step <<= 1)",
        "for (int step = 4; step <= 64; step <<= 2)",
        1,
    )
    require(mutated_c_tail != c_text, "could not construct C inverse tail-depth mutation")
    expect_rejected(verify_c_text, mutated_c_tail, "C inverse radix-2 head no longer reaches the verified step8 layer")

    mutated_c_output = c_text.replace(
        "r[i + step] = fqmul(zeta1, t1 - r[i]);",
        "r[i + step] = fqmul(zeta1, r[i] - t1);",
        1,
    )
    require(mutated_c_output != c_text, "could not construct C inverse high-output mutation")
    expect_rejected(verify_c_text, mutated_c_output, "C inverse high output uses wrong fqmul input")

    mutated_jasmin_zeta = EXPECTED_JASMIN_SOURCE.replace("NTRUPLUS_ZETA95 = 436", "NTRUPLUS_ZETA95 = 1015", 1)
    expect_rejected(verify_jasmin_text, mutated_jasmin_zeta, "Jasmin wrong inverse fixed twiddle")

    mutated_jasmin_alias = EXPECTED_JASMIN_SOURCE.replace("low = rp[i];", "low = ap[i];", 1)
    expect_rejected(verify_jasmin_text, mutated_jasmin_alias, "Jasmin inverse helper no longer reads in-place state")

    mutated_jasmin_offset = EXPECTED_JASMIN_SOURCE.replace("high = rp[i + 8];", "high = rp[i + 16];", 1)
    expect_rejected(verify_jasmin_text, mutated_jasmin_offset, "Jasmin inverse helper uses wrong pair offset")

    mutated_jasmin_schedule = EXPECTED_JASMIN_SOURCE.replace(
        f"  rp = {EXPECTED_HELPER}(rp, 0, NTRUPLUS_ZETA95);\n"
        f"  rp = {EXPECTED_HELPER}(rp, 16, NTRUPLUS_ZETA94);",
        f"  rp = {EXPECTED_HELPER}(rp, 16, NTRUPLUS_ZETA94);\n"
        f"  rp = {EXPECTED_HELPER}(rp, 0, NTRUPLUS_ZETA95);",
        1,
    )
    expect_rejected(verify_jasmin_text, mutated_jasmin_schedule, "Jasmin inverse helper-call schedule is permuted")

    stale_two_buffer_copy = EXPECTED_JASMIN_SOURCE.replace(
        f"inline fn {EXPECTED_HELPER}(\n  reg mut ptr u16[NTRUPLUS_N] rp,\n  reg u64 base,",
        f"inline fn {EXPECTED_HELPER}(\n  reg mut ptr u16[NTRUPLUS_N] rp,\n  reg ptr u16[NTRUPLUS_N] ap,\n  reg u64 base,",
        1,
    )
    stale_two_buffer_copy = stale_two_buffer_copy.replace("low = rp[i];", "low = ap[i];", 1)
    stale_two_buffer_copy = stale_two_buffer_copy.replace("high = rp[i + 8];", "high = ap[i + 8];", 1)
    stale_two_buffer_copy = stale_two_buffer_copy.replace(
        f"export fn {EXPECTED_EXPORT}(\n  reg mut ptr u16[NTRUPLUS_N] rp) -> reg ptr u16[NTRUPLUS_N]",
        f"export fn {EXPECTED_EXPORT}(\n  reg mut ptr u16[NTRUPLUS_N] rp,\n  reg ptr u16[NTRUPLUS_N] ap) -> reg ptr u16[NTRUPLUS_N]",
        1,
    )
    stale_two_buffer_copy = stale_two_buffer_copy.replace(
        f"  rp = {EXPECTED_HELPER}(rp, 0, NTRUPLUS_ZETA95);",
        f"  rp = {EXPECTED_HELPER}(rp, ap, 0, NTRUPLUS_ZETA95);",
        1,
    )
    expect_rejected(verify_jasmin_text, stale_two_buffer_copy, "Jasmin accepted stale two-buffer inverse copy")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Tie the standalone Jasmin NTRU+768 inverse radix-2 step8 slice to the C inverse loop."
    )
    parser.add_argument("--c-source", required=True, help="path to NTRU+/NTRU+768/ntt.c")
    parser.add_argument("--jasmin-source", required=True, help="path to invntt_radix2_8.jazz")
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
        print("PASS: NTRU+768 inverse radix-2 step8 checker rejected representative bad mutations")
    print("PASS: NTRU+768 inverse radix-2 step8 C/Jasmin source coupling")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
