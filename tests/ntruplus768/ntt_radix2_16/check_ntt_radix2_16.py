#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


EXPECTED_ZETAS = [
    -455,
    639,
    502,
    655,
    -699,
    541,
    95,
    -1577,
    -1241,
    550,
    -44,
    39,
    -820,
    -216,
    -121,
    -757,
    -348,
    937,
    893,
    387,
    -603,
    1713,
    -1105,
    1058,
]
EXPECTED_EXPORT = "jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16"
EXPECTED_HELPER = "__radix2_16_block"
EXPECTED_BASES = list(range(0, 768, 32))
EXPECTED_OFFSET = 16


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


def parse_tail_schedule() -> tuple[int, int, list[int]]:
    step = EXPECTED_OFFSET
    step64_blocks = 768 // (2 * 64)
    step32_blocks = 768 // (2 * 32)
    step16_blocks = 768 // (2 * step)
    start_index = 6 + step64_blocks + step32_blocks
    return start_index, step16_blocks, [block * (step << 1) for block in range(step16_blocks)]


def verify_c_text(text: str) -> None:
    zetas = parse_c_zetas(text)
    require(len(zetas) == 192, f"expected 192 C twiddles, found {len(zetas)}")
    require(
        zetas[24:48] == EXPECTED_ZETAS,
        f"expected C zetas[24:48] == {EXPECTED_ZETAS}, found {zetas[24:48]}",
    )

    body = compact(extract_function_body(text, "ntt"))
    prefix = re.compile(
        r"int16_t t1, t2, t3; int16_t zeta1, zeta2; int k = 1; "
        r"zeta1 = zetas\[k\+\+\]; "
        r"for \(int i = 0; i < NTRUPLUS_N / 2; i\+\+\) \{ "
        r"t1 = fqmul\(zeta1, a\[i \+ NTRUPLUS_N / 2\]\); "
        r"r\[i \+ NTRUPLUS_N / 2\] = a\[i\] \+ a\[i \+ NTRUPLUS_N / 2\] - t1; "
        r"r\[i\] = a\[i\] \+ t1; \} "
        r"for \(int start = 0; start < NTRUPLUS_N; start \+= 384\) \{ "
        r"zeta1 = zetas\[k\+\+\]; zeta2 = zetas\[k\+\+\]; "
        r"for \(int i = start; i < start \+ 128; i\+\+\) \{ "
        r"t1 = fqmul\(zeta1, r\[i \+ 128\]\); "
        r"t2 = fqmul\(zeta2, r\[i \+ 256\]\); "
        r"t3 = fqmul\(NTRUPLUS_OMEGA, t1 - t2\); "
        r"r\[i \+ 256\] = r\[i\] - t1 - t3; "
        r"r\[i \+ 128\] = r\[i\] - t2 \+ t3; "
        r"r\[i\] = r\[i\] \+ t1 \+ t2; \} \} "
    )
    prefix_match = prefix.search(body)
    require(
        prefix_match is not None,
        "C ntt() prefix no longer proves that the standalone step=16 layer starts after stage1/radix3",
    )

    stage = re.compile(
        r"for \(int step = 64; step >= 4; step >>= 1\) \{ "
        r"for \(int start = 0; start < NTRUPLUS_N; start \+= \(step << 1\)\) \{ "
        r"zeta1 = zetas\[k\+\+\]; "
        r"for \(int i = start; i < start \+ step; i\+\+\) \{ "
        r"t1 = fqmul\(zeta1, r\[i \+ step\]\); "
        r"r\[i \+ step\] = barrett_reduce\(r\[i\] - t1\); "
        r"r\[i\] = barrett_reduce\(r\[i\] \+ t1\); \} \} \}"
    )
    stage_match = stage.search(body)
    require(
        stage_match is not None,
        "C ntt() radix-2 tail no longer matches the verified step=64->32->16->8->4 schedule and Barrett butterfly flow",
    )
    require(
        prefix_match.end() <= stage_match.start(),
        "C ntt() no longer executes the verified stage1/radix3 prefix before the radix-2 tail",
    )

    start_index, block_count, bases = parse_tail_schedule()
    require(start_index == 24, f"derived C step16 zeta start changed from 24 to {start_index}")
    require(block_count == 24, f"derived C step16 block count changed from 24 to {block_count}")
    require(bases == EXPECTED_BASES, f"derived C step16 bases changed: expected {EXPECTED_BASES}, found {bases}")


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
            f"Jasmin radix-2 slice must fix {name} == {value}",
        )
    for index, value in enumerate(EXPECTED_ZETAS, start=24):
        require(
            re.search(rf"param int NTRUPLUS_ZETA{index} = {value};", source) is not None,
            f"Jasmin radix-2 slice must fix NTRUPLUS_ZETA{index} == {value}",
        )
    require(
        f"export fn {EXPECTED_EXPORT}(" in source,
        f"missing expected Jasmin export `{EXPECTED_EXPORT}`",
    )
    require(
        f"inline fn {EXPECTED_HELPER}(" in source,
        f"missing expected Jasmin helper `{EXPECTED_HELPER}`",
    )

    mul_body = compact(extract_function_body(text, "__mul_i16"))
    require(
        re.fullmatch(
            r"reg u32 ad; reg u32 bd; reg u32 c; "
            r"ad = \(32s\) a; bd = \(32s\) b; c = ad \* bd; return c;",
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
            r"td = \(32s\) t; r = \(32s\) a; td \*= q; r -= td; "
            r"r >>s= 16; t = r; return t;",
            montgomery_body,
        )
        is not None,
        "Jasmin Montgomery reducer no longer matches the verified Q/QINV data flow",
    )

    barrett_body = compact(extract_function_body(text, "__barrett_reduce"))
    require(
        re.fullmatch(
            r"reg u16 t; reg u32 td; reg u32 v; reg u32 q; "
            r"v = NTRUPLUS_BARRETT_V; td = \(32s\) a; td \*= v; "
            r"td \+= NTRUPLUS_BARRETT_BIAS; td >>s= 26; t = td; "
            r"q = NTRUPLUS_Q; td = \(32s\) t; td \*= q; t = td; "
            r"t = a - t; return t;",
            barrett_body,
        )
        is not None,
        "Jasmin Barrett reducer no longer matches the verified rounding and subtraction data flow",
    )

    helper_body = compact(extract_function_body(text, EXPECTED_HELPER))
    helper_pattern = re.compile(
        r"reg u16 low; reg u16 high; reg u16 t; reg u16 sum; reg u16 diff; "
        r"reg u32 acc; reg u32 wd; reg u32 td; reg u64 i; reg u64 stop; "
        r"i = base; stop = base; stop \+= 16; while \(i < stop\) \{ "
        r"low = rp\[i\]; high = rp\[i \+ 16\]; "
        r"acc = __mul_i16\(zeta, high\); t = __montgomery_reduce\(acc\); "
        r"wd = \(32s\) low; td = \(32s\) t; wd -= td; diff = wd; "
        r"wd = \(32s\) low; td = \(32s\) t; wd \+= td; sum = wd; "
        r"rp\[i \+ 16\] = __barrett_reduce\(diff\); rp\[i\] = __barrett_reduce\(sum\); "
        r"i \+= 1; \} return rp;"
    )
    require(
        helper_pattern.search(helper_body) is not None,
        "Jasmin radix-2 helper no longer matches the verified step=16 pair offset, multiply, and Barrett flow",
    )

    export_body = compact(extract_function_body(text, EXPECTED_EXPORT))
    expected_calls = " ".join(
        f"rp = {EXPECTED_HELPER}(rp, {base}, NTRUPLUS_ZETA{index});"
        for index, base in enumerate(EXPECTED_BASES, start=24)
    )
    call_pattern = re.compile(rf"_ = #init_msf\(\); {re.escape(expected_calls)} return rp;")
    require(
        call_pattern.search(export_body) is not None,
        "Jasmin radix-2 export no longer matches the verified 24-block step=16 schedule",
    )


def expect_rejected(check, text: str, label: str) -> None:
    try:
        check(text)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(c_text: str, jasmin_text: str) -> None:
    verify_c_text(c_text)
    verify_jasmin_text(jasmin_text)

    mutated_c_zeta_window = c_text.replace("-455,   639,   502,   655,", "639,  -455,   502,   655,", 1)
    require(mutated_c_zeta_window != c_text, "could not construct C step16 zeta-order mutation")
    expect_rejected(verify_c_text, mutated_c_zeta_window, "C wrong step16 zeta order")

    mutated_c_tail = c_text.replace(
        "for (int step = 64; step >= 4; step >>= 1)",
        "for (int step = 32; step >= 4; step >>= 1)",
        1,
    )
    require(mutated_c_tail != c_text, "could not construct C tail-start mutation")
    expect_rejected(verify_c_text, mutated_c_tail, "C radix-2 tail skips the verified step64 prefix")

    mutated_c_output = c_text.replace(
        "r[i + step] = barrett_reduce(r[i] - t1);",
        "r[i + step] = barrett_reduce(r[i] + t1);",
        1,
    )
    require(mutated_c_output != c_text, "could not construct C high-output mutation")
    expect_rejected(verify_c_text, mutated_c_output, "C high output uses wrong Barrett input")

    mutated_jasmin_zeta = jasmin_text.replace("NTRUPLUS_ZETA36 = -820", "NTRUPLUS_ZETA36 = -216", 1)
    require(mutated_jasmin_zeta != jasmin_text, "could not construct Jasmin fixed-zeta mutation")
    expect_rejected(verify_jasmin_text, mutated_jasmin_zeta, "Jasmin wrong fixed twiddle")

    mutated_jasmin_offset = jasmin_text.replace("high = rp[i + 16];", "high = rp[i + 32];", 1)
    require(mutated_jasmin_offset != jasmin_text, "could not construct Jasmin pair-offset mutation")
    expect_rejected(verify_jasmin_text, mutated_jasmin_offset, "Jasmin wrong pair offset")

    mutated_jasmin_barrett = jasmin_text.replace(
        "rp[i + 16] = __barrett_reduce(diff);",
        "rp[i + 16] = __barrett_reduce(sum);",
        1,
    )
    require(mutated_jasmin_barrett != jasmin_text, "could not construct Jasmin Barrett-flow mutation")
    expect_rejected(verify_jasmin_text, mutated_jasmin_barrett, "Jasmin wrong Barrett destination")

    mutated_jasmin_schedule = jasmin_text.replace(
        "rp = __radix2_16_block(rp, 352, NTRUPLUS_ZETA35);\n"
        "  rp = __radix2_16_block(rp, 384, NTRUPLUS_ZETA36);",
        "rp = __radix2_16_block(rp, 384, NTRUPLUS_ZETA36);\n"
        "  rp = __radix2_16_block(rp, 352, NTRUPLUS_ZETA35);",
        1,
    )
    require(mutated_jasmin_schedule != jasmin_text, "could not construct Jasmin block-order mutation")
    expect_rejected(verify_jasmin_text, mutated_jasmin_schedule, "Jasmin wrong helper-call schedule")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Tie the standalone Jasmin NTRU+768 radix-2 step16 slice to the C tail layer."
    )
    parser.add_argument("--c-source", required=True, help="path to NTRU+/NTRU+768/ntt.c")
    parser.add_argument("--jasmin-source", required=True, help="path to ntt_radix2_16.jazz")
    parser.add_argument("--self-check", action="store_true", help="also require representative bad mutations to be rejected")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        c_text = Path(args.c_source).read_text(encoding="utf-8")
        jasmin_text = Path(args.jasmin_source).read_text(encoding="utf-8")
        verify_c_text(c_text)
        verify_jasmin_text(jasmin_text)
        if args.self_check:
            run_self_check(c_text, jasmin_text)
    except (OSError, VerificationError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1

    if args.self_check:
        print("PASS: NTRU+768 NTT radix-2 step16 checker rejected representative bad mutations")
    print("PASS: NTRU+768 NTT radix-2 step16 C/Jasmin source coupling")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
