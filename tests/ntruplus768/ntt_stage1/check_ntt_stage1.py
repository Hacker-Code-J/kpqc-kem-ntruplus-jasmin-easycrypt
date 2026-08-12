#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


EXPECTED_ZETA = -1033
EXPECTED_SLICE = "jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1"


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


def parse_zetas(text: str) -> list[int]:
    match = re.search(r"const\s+int16_t\s+zetas\s*\[\s*192\s*\]\s*=\s*\{(.*?)\};", text, flags=re.S)
    require(match is not None, "could not find the 192-entry C zetas table")
    return [int(token) for token in re.findall(r"-?\d+", match.group(1))]


def verify_c_text(text: str) -> None:
    zetas = parse_zetas(text)
    require(len(zetas) == 192, f"expected 192 C twiddles, found {len(zetas)}")
    require(zetas[1] == EXPECTED_ZETA, f"expected zetas[1] == {EXPECTED_ZETA}, found {zetas[1]}")

    body = compact(extract_function_body(text, "ntt"))
    stage = re.compile(
        r"int k = 1; zeta1 = zetas\[k\+\+\]; "
        r"for \(int i = 0; i < NTRUPLUS_N / 2; i\+\+\) \{ "
        r"t1 = fqmul\(zeta1, a\[i \+ NTRUPLUS_N / 2\]\); "
        r"r\[i \+ NTRUPLUS_N / 2\] = a\[i\] \+ a\[i \+ NTRUPLUS_N / 2\] - t1; "
        r"r\[i\] = a\[i\] \+ t1; \}"
    )
    require(stage.search(body) is not None, "C ntt() initial split no longer matches the verified stage-1 data flow")


def verify_jasmin_text(text: str) -> None:
    source = compact(text)
    require(
        re.search(rf"param int NTRUPLUS_STAGE1_ZETA = {EXPECTED_ZETA};", source) is not None,
        f"Jasmin stage must fix the C twiddle zetas[1] == {EXPECTED_ZETA}",
    )
    require(
        re.search(rf"export fn {EXPECTED_SLICE}\s*\(", source) is not None,
        f"missing expected Jasmin export `{EXPECTED_SLICE}`",
    )

    body = compact(extract_function_body(text, EXPECTED_SLICE))
    stage = re.compile(
        r"i = 0; while \(i < NTRUPLUS_N / 2\) \{ "
        r"a0 = ap\[i\]; a1 = ap\[i \+ NTRUPLUS_N / 2\]; "
        r"acc = __mul_i16\(NTRUPLUS_STAGE1_ZETA, a1\); "
        r"t = __montgomery_reduce\(acc\); "
        r"lo = a0; lo \+= t; hi = a0; hi \+= a1; hi -= t; "
        r"rp\[i\] = lo; rp\[i \+ NTRUPLUS_N / 2\] = hi; i \+= 1; \}"
    )
    require(stage.search(body) is not None, "Jasmin stage-1 loop no longer matches the C initial-split data flow")


def expect_rejected(check, text: str, label: str) -> None:
    try:
        check(text)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(c_text: str, jasmin_text: str) -> None:
    mutated_c_zeta = c_text.replace("zeta1 = zetas[k++];", "zeta1 = zetas[++k];", 1)
    require(mutated_c_zeta != c_text, "could not construct C zeta-index mutation")
    expect_rejected(verify_c_text, mutated_c_zeta, "C pre-incremented zeta index")

    mutated_c_add = c_text.replace("r[i                 ] = a[i]                         + t1;", "r[i                 ] = a[i]                         - t1;", 1)
    require(mutated_c_add != c_text, "could not construct C butterfly-sign mutation")
    expect_rejected(verify_c_text, mutated_c_add, "C low-output subtraction")

    mutated_jasmin_zeta = jasmin_text.replace(
        f"NTRUPLUS_STAGE1_ZETA = {EXPECTED_ZETA}",
        "NTRUPLUS_STAGE1_ZETA = -682",
        1,
    )
    require(mutated_jasmin_zeta != jasmin_text, "could not construct Jasmin zeta mutation")
    expect_rejected(verify_jasmin_text, mutated_jasmin_zeta, "Jasmin wrong fixed twiddle")

    mutated_jasmin_add = jasmin_text.replace("lo += t;", "lo -= t;", 1)
    require(mutated_jasmin_add != jasmin_text, "could not construct Jasmin butterfly-sign mutation")
    expect_rejected(verify_jasmin_text, mutated_jasmin_add, "Jasmin low-output subtraction")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Tie the standalone Jasmin NTRU+768 initial NTT split to the C prefix.")
    parser.add_argument("--c-source", required=True, help="path to NTRU+/NTRU+768/ntt.c")
    parser.add_argument("--jasmin-source", required=True, help="path to ntt_stage1.jazz")
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
        print("PASS: NTRU+768 NTT stage-1 checker rejected representative bad mutations")
    print("PASS: NTRU+768 NTT stage-1 C/Jasmin source coupling")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
