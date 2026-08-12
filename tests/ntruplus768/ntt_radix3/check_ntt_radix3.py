#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


EXPECTED_ZETAS = [-682, -248, -708, 682]
EXPECTED_OMEGA = -886
EXPECTED_EXPORT = "jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3"


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

    body = compact(extract_function_body(text, "ntt"))
    stage = re.compile(
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
        r"r\[i\] = r\[i\] \+ t1 \+ t2; \} \}"
    )
    require(
        stage.search(body) is not None,
        "C ntt() radix-3 prefix no longer matches the verified stage1->radix3 twiddle order and data flow",
    )


def verify_jasmin_text(text: str) -> None:
    source = compact(text)
    require(
        re.search(rf"param int NTRUPLUS_OMEGA = {EXPECTED_OMEGA};", source) is not None,
        f"Jasmin radix-3 slice must fix NTRUPLUS_OMEGA == {EXPECTED_OMEGA}",
    )
    for index, value in enumerate(EXPECTED_ZETAS, start=2):
        require(
            re.search(rf"param int NTRUPLUS_ZETA{index} = {value};", source) is not None,
            f"Jasmin radix-3 slice must fix NTRUPLUS_ZETA{index} == {value}",
        )
    require(
        re.search(rf"export fn {EXPECTED_EXPORT}\s*\(", source) is not None,
        f"missing expected Jasmin export `{EXPECTED_EXPORT}`",
    )

    body = compact(extract_function_body(text, EXPECTED_EXPORT))
    stage = re.compile(
        r"reg u16 a0; reg u16 a1; reg u16 a2; reg u16 t1; reg u16 t2; reg u16 t3; "
        r"reg u16 td; reg u16 r0; reg u16 r1; reg u16 r2; reg u32 acc; reg u64 i; "
        r"_ = #init_msf\(\); "
        r"i = 0; while \(i < 128\) \{ "
        r"a0 = rp\[i\]; a1 = rp\[i \+ 128\]; a2 = rp\[i \+ 256\]; "
        r"acc = __mul_i16\(NTRUPLUS_ZETA2, a1\); t1 = __montgomery_reduce\(acc\); "
        r"acc = __mul_i16\(NTRUPLUS_ZETA3, a2\); t2 = __montgomery_reduce\(acc\); "
        r"td = t1; td -= t2; acc = __mul_i16\(NTRUPLUS_OMEGA, td\); t3 = __montgomery_reduce\(acc\); "
        r"r0 = a0; r0 \+= t1; r0 \+= t2; "
        r"r1 = a0; r1 -= t2; r1 \+= t3; "
        r"r2 = a0; r2 -= t1; r2 -= t3; "
        r"rp\[i\] = r0; rp\[i \+ 128\] = r1; rp\[i \+ 256\] = r2; i \+= 1; \} "
        r"i = 384; while \(i < 512\) \{ "
        r"a0 = rp\[i\]; a1 = rp\[i \+ 128\]; a2 = rp\[i \+ 256\]; "
        r"acc = __mul_i16\(NTRUPLUS_ZETA4, a1\); t1 = __montgomery_reduce\(acc\); "
        r"acc = __mul_i16\(NTRUPLUS_ZETA5, a2\); t2 = __montgomery_reduce\(acc\); "
        r"td = t1; td -= t2; acc = __mul_i16\(NTRUPLUS_OMEGA, td\); t3 = __montgomery_reduce\(acc\); "
        r"r0 = a0; r0 \+= t1; r0 \+= t2; "
        r"r1 = a0; r1 -= t2; r1 \+= t3; "
        r"r2 = a0; r2 -= t1; r2 -= t3; "
        r"rp\[i\] = r0; rp\[i \+ 128\] = r1; rp\[i \+ 256\] = r2; i \+= 1; \} "
        r"return rp;"
    )
    require(
        stage.search(body) is not None,
        "Jasmin radix-3 slice no longer matches the verified explicit blocks, offsets, or load/compute/store flow",
    )


def expect_rejected(check, text: str, label: str) -> None:
    try:
        check(text)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(c_text: str, jasmin_text: str) -> None:
    mutated_c_twiddle = c_text.replace("zeta1 = zetas[k++];\n\t\tzeta2 = zetas[k++];", "zeta2 = zetas[k++];\n\t\tzeta1 = zetas[k++];", 1)
    require(mutated_c_twiddle != c_text, "could not construct C twiddle-order mutation")
    expect_rejected(verify_c_text, mutated_c_twiddle, "C swapped radix-3 twiddle order")

    mutated_c_omega = c_text.replace("t3 = fqmul(NTRUPLUS_OMEGA, t1 - t2);", "t3 = fqmul(zeta1, t1 - t2);", 1)
    require(mutated_c_omega != c_text, "could not construct C omega mutation")
    expect_rejected(verify_c_text, mutated_c_omega, "C wrong radix-3 omega source")

    mutated_c_omega_input = c_text.replace(
        "t3 = fqmul(NTRUPLUS_OMEGA, t1 - t2);",
        "t3 = fqmul(NTRUPLUS_OMEGA, t1 + t2);",
        1,
    )
    require(mutated_c_omega_input != c_text, "could not construct C omega-input mutation")
    expect_rejected(verify_c_text, mutated_c_omega_input, "C omega multiplies the wrong combination")

    mutated_c_output = c_text.replace("r[i      ] = r[i] + t1 + t2;", "r[i      ] = r[i] + t1 - t2;", 1)
    require(mutated_c_output != c_text, "could not construct C output-sign mutation")
    expect_rejected(verify_c_text, mutated_c_output, "C low output uses wrong sign")

    mutated_jasmin_twiddle = jasmin_text.replace("NTRUPLUS_ZETA3 = -248", "NTRUPLUS_ZETA3 = -708", 1)
    require(mutated_jasmin_twiddle != jasmin_text, "could not construct Jasmin twiddle mutation")
    expect_rejected(verify_jasmin_text, mutated_jasmin_twiddle, "Jasmin wrong fixed twiddle")

    mutated_jasmin_boundary = jasmin_text.replace("while (i < 512)", "while (i < 513)", 1)
    require(mutated_jasmin_boundary != jasmin_text, "could not construct Jasmin block-boundary mutation")
    expect_rejected(verify_jasmin_text, mutated_jasmin_boundary, "Jasmin wrong second-block boundary")

    mutated_jasmin_omega = jasmin_text.replace("acc = __mul_i16(NTRUPLUS_OMEGA, td);", "acc = __mul_i16(NTRUPLUS_ZETA4, td);", 1)
    require(mutated_jasmin_omega != jasmin_text, "could not construct Jasmin omega mutation")
    expect_rejected(verify_jasmin_text, mutated_jasmin_omega, "Jasmin wrong omega multiply")

    mutated_jasmin_omega_input = jasmin_text.replace("td -= t2;", "td += t2;", 1)
    require(mutated_jasmin_omega_input != jasmin_text, "could not construct Jasmin omega-input mutation")
    expect_rejected(verify_jasmin_text, mutated_jasmin_omega_input, "Jasmin omega multiplies the wrong combination")

    mutated_jasmin_output = jasmin_text.replace("r2 -= t3;", "r2 += t3;", 1)
    require(mutated_jasmin_output != jasmin_text, "could not construct Jasmin output-sign mutation")
    expect_rejected(verify_jasmin_text, mutated_jasmin_output, "Jasmin high output uses wrong sign")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Tie the standalone Jasmin NTRU+768 radix-3 slice to the C stage1->radix3 prefix."
    )
    parser.add_argument("--c-source", required=True, help="path to NTRU+/NTRU+768/ntt.c")
    parser.add_argument("--jasmin-source", required=True, help="path to ntt_radix3.jazz")
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
        print("PASS: NTRU+768 NTT radix-3 checker rejected representative bad mutations")
    print("PASS: NTRU+768 NTT radix-3 C/Jasmin source coupling")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
