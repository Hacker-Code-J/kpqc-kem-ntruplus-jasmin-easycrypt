#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


EXPECTED_EXPORT = "jade_ntruplus_ntruplus768_amd64_ref_invntt"
EXPECTED_NAMESPACE_REQUIRES = [
    ("Radix2_4", "invntt_radix2_4.jazz"),
    ("Radix2_8", "invntt_radix2_8.jazz"),
    ("Radix2_16", "invntt_radix2_16.jazz"),
    ("Radix2_32", "invntt_radix2_32.jazz"),
    ("Radix2_64", "invntt_radix2_64.jazz"),
    ("Radix3", "invntt_radix3.jazz"),
    ("Final", "invntt_final.jazz"),
]
EXPECTED_CALLS = [
    ("Radix2_4::jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4", "rp"),
    ("Radix2_8::jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8", "rp"),
    ("Radix2_16::jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16", "rp"),
    ("Radix2_32::jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32", "rp"),
    ("Radix2_64::jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64", "rp"),
    ("Radix3::jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3", "rp"),
    ("Final::jade_ntruplus_ntruplus768_amd64_ref_invntt_final", "rp"),
]
MISSING_SOURCE_HINT = (
    "expected Jasmin source implementing export "
    "`jade_ntruplus_ntruplus768_amd64_ref_invntt` at "
    "ntruplus/jasmin/768/ref/invntt.jazz with signature "
    "`(reg mut ptr u16[NTRUPLUS_N] rp, reg const ptr u16[NTRUPLUS_N] ap) -> reg ptr u16[NTRUPLUS_N]`"
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


def verify_c_text(text: str) -> None:
    body = compact(extract_function_body(text, "invntt"))

    require(re.search(r"\bint k = 191;", body) is not None, "invntt() must initialize k to 191")
    copy_loop = re.search(
        r"for \(int i = 0; i < NTRUPLUS_N; i\+\+\) \{ r\[i\] = a\[i\]; \}",
        body,
    )
    require(copy_loop is not None, "C invntt() must begin with an exact full copy from a[] into r[]")

    radix2_tail = re.compile(
        r"for \(int step = 4; step <= 64; step <<= 1\) \{ "
        r"for \(int start = 0; start < NTRUPLUS_N; start \+= \(step << 1\)\) \{ "
        r"zeta1 = zetas\[k--\]; "
        r"for \(int i = start; i < start \+ step; i\+\+\) \{ "
        r"t1 = r\[i \+ step\]; "
        r"r\[i \+ step\] = fqmul\(zeta1, t1 - r\[i\]\); "
        r"r\[i\] = barrett_reduce\(r\[i\] \+ t1\); \} \} \}"
    )
    radix2_match = radix2_tail.search(body)
    require(
        radix2_match is not None,
        "C invntt() radix-2 prefix no longer matches the verified step=4->8->16->32->64 schedule",
    )

    radix3_stage = re.compile(
        r"for \(int start = 0; start < NTRUPLUS_N; start \+= 384\) \{ "
        r"zeta2 = zetas\[k--\]; zeta1 = zetas\[k--\]; "
        r"for \(int i = start; i < start \+ 128; i\+\+\) \{ "
        r"t1 = fqmul\(NTRUPLUS_OMEGA, r\[i \+ 128\] - r\[i\]\); "
        r"t2 = fqmul\(zeta1, r\[i \+ 256\] - r\[i\] \+ t1\); "
        r"t3 = fqmul\(zeta2, r\[i \+ 256\] - r\[i \+ 128\] - t1\); "
        r"r\[i\] = r\[i\] \+ r\[i \+ 128\] \+ r\[i \+ 256\]; "
        r"r\[i \+ 128\] = t2; r\[i \+ 256\] = t3; \} \}"
    )
    radix3_match = radix3_stage.search(body)
    require(
        radix3_match is not None,
        "C invntt() radix-3 stage no longer matches the verified twiddle order or arithmetic polarity",
    )

    final_stage = re.compile(
        r"for \(int i = 0; i < NTRUPLUS_N/2; i\+\+\) \{ "
        r"t1 = r\[i\] \+ r\[i \+ NTRUPLUS_N/2\]; "
        r"t2 = fqmul\(NTRUPLUS_ZMINUSZ5INV, r\[i\] - r\[i \+ NTRUPLUS_N/2\]\); "
        r"r\[i\] = fqmul\(NTRUPLUS_NINV, t1 - t2\); "
        r"r\[i \+ NTRUPLUS_N/2\] = fqmul\(NTRUPLUS_2NINV, t2\); \}"
    )
    final_match = final_stage.search(body)
    require(
        final_match is not None,
        "C invntt() final stage no longer matches the verified half-offset, constants, or arithmetic polarity",
    )

    require(
        copy_loop.end() <= radix2_match.start() <= radix3_match.start() <= final_match.start(),
        "C invntt() no longer executes copy -> radix2 -> radix3 -> final in the verified order",
    )

    loads = re.findall(r"\b(zeta[12])\s*=\s*zetas\s*\[\s*(k--)\s*\]\s*;", body)
    require(
        loads == [("zeta1", "k--"), ("zeta2", "k--"), ("zeta1", "k--")],
        "invntt() must keep the verified textual zeta1/zeta2 load order",
    )


def parse_namespace_requires(text: str) -> list[tuple[str, str]]:
    stripped = strip_comments(text)
    return re.findall(
        r'namespace\s+([A-Za-z0-9_]+)\s*\{\s*require\s+"([^"]+)"\s*\}',
        stripped,
        flags=re.S,
    )


def verify_export_signature(text: str) -> None:
    signature = re.compile(
        rf"export fn {EXPECTED_EXPORT}\s*\(\s*"
        r"reg mut ptr u16\[NTRUPLUS_N\] rp\s*,\s*"
        r"reg const ptr u16\[NTRUPLUS_N\] ap\s*\)\s*->\s*"
        r"reg ptr u16\[NTRUPLUS_N\]"
    )
    require(signature.search(strip_comments(text)) is not None, MISSING_SOURCE_HINT)


def verify_copy_helper(text: str) -> None:
    signature = re.compile(
        r"fn __invntt_copy\s*\(\s*"
        r"reg mut ptr u16\[NTRUPLUS_N\] rp\s*,\s*"
        r"reg const ptr u16\[NTRUPLUS_N\] ap\s*\)\s*->\s*"
        r"reg ptr u16\[NTRUPLUS_N\]"
    )
    require(
        signature.search(strip_comments(text)) is not None,
        "wrapper must keep the private two-buffer copy helper",
    )

    body = compact(extract_function_body(text, "__invntt_copy"))
    expected_body = (
        "reg u64 i; _ = #init_msf(); i = 0; while (i < NTRUPLUS_N) { "
        "rp[i] = ap[i]; i += 1; } return rp;"
    )
    require(
        body == expected_body,
        "copy helper must initialize the speculation mask, copy exactly ap[0..767] to rp[0..767], and return rp",
    )


def verify_jasmin_text(text: str) -> None:
    requires = parse_namespace_requires(text)
    require(
        requires == EXPECTED_NAMESPACE_REQUIRES,
        f"wrapper namespace/require list changed: expected {EXPECTED_NAMESPACE_REQUIRES}, found {requires}",
    )

    verify_export_signature(text)
    verify_copy_helper(text)
    body = compact(extract_function_body(text, EXPECTED_EXPORT))

    expected_body = (
        "rp = __invntt_copy(rp, ap); "
        "rp = Radix2_4::jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4(rp); "
        "rp = Radix2_8::jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8(rp); "
        "rp = Radix2_16::jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16(rp); "
        "rp = Radix2_32::jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32(rp); "
        "rp = Radix2_64::jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64(rp); "
        "rp = Radix3::jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3(rp); "
        "rp = Final::jade_ntruplus_ntruplus768_amd64_ref_invntt_final(rp); "
        "return rp;"
    )
    require(
        body == expected_body,
        "wrapper body no longer matches copy -> radix2 -> radix3 -> final composition",
    )

    calls = re.findall(
        r"rp = ((?:Radix2_4|Radix2_8|Radix2_16|Radix2_32|Radix2_64|Radix3|Final)::jade_ntruplus_ntruplus768_amd64_ref_(?:invntt_radix2_4|invntt_radix2_8|invntt_radix2_16|invntt_radix2_32|invntt_radix2_64|invntt_radix3|invntt_final))\(([^)]*)\);",
        body,
    )
    require(calls == EXPECTED_CALLS, f"wrapper call sequence changed: expected {EXPECTED_CALLS}, found {calls}")


def expect_rejected(check, text: str, label: str) -> None:
    try:
        check(text)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(c_text: str, jasmin_text: str) -> None:
    verify_c_text(c_text)
    verify_jasmin_text(jasmin_text)

    mutated_c_k = c_text.replace("int k = 191;", "int k = 190;", 1)
    require(mutated_c_k != c_text, "could not construct C initial-k mutation")
    expect_rejected(verify_c_text, mutated_c_k, "C wrong initial zeta index")

    mutated_c_copy = c_text.replace("r[i] = a[i];", "r[i] = 0;", 1)
    require(mutated_c_copy != c_text, "could not construct C copy-loop mutation")
    expect_rejected(verify_c_text, mutated_c_copy, "C lost exact input copy")

    broken_copy = jasmin_text.replace("    rp[i] = ap[i];", "    rp[i] = 0;", 1)
    require(broken_copy != jasmin_text, "could not construct broken-copy mutation")
    expect_rejected(verify_jasmin_text, broken_copy, "copy loop lost the input value")

    missing_msf = jasmin_text.replace("  _ = #init_msf();\n", "", 1)
    require(missing_msf != jasmin_text, "could not construct missing-msf mutation")
    expect_rejected(verify_jasmin_text, missing_msf, "copy helper skipped speculation-mask initialization")

    missing_copy = jasmin_text.replace(
        "  rp = __invntt_copy(rp, ap);\n",
        "",
        1,
    )
    require(missing_copy != jasmin_text, "could not construct missing-copy mutation")
    expect_rejected(verify_jasmin_text, missing_copy, "wrapper skipped input copy")

    reordered_calls = jasmin_text.replace(
        "  rp = Radix2_64::jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64(rp);\n"
        "  rp = Radix3::jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3(rp);\n",
        "  rp = Radix3::jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3(rp);\n"
        "  rp = Radix2_64::jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64(rp);\n",
        1,
    )
    require(reordered_calls != jasmin_text, "could not construct reordered-call mutation")
    expect_rejected(verify_jasmin_text, reordered_calls, "wrapper reordered radix2_64/radix3 calls")

    missing_final = jasmin_text.replace(
        "  rp = Final::jade_ntruplus_ntruplus768_amd64_ref_invntt_final(rp);\n",
        "",
        1,
    )
    require(missing_final != jasmin_text, "could not construct missing-final mutation")
    expect_rejected(verify_jasmin_text, missing_final, "wrapper missing final stage")

    one_buffer_signature = jasmin_text.replace(
        f"export fn {EXPECTED_EXPORT}(\n"
        "  reg mut ptr u16[NTRUPLUS_N] rp,\n"
        "  reg const ptr u16[NTRUPLUS_N] ap) -> reg ptr u16[NTRUPLUS_N]",
        f"export fn {EXPECTED_EXPORT}(\n"
        "  reg mut ptr u16[NTRUPLUS_N] rp) -> reg ptr u16[NTRUPLUS_N]",
        1,
    )
    require(one_buffer_signature != jasmin_text, "could not construct one-buffer signature mutation")
    expect_rejected(verify_jasmin_text, one_buffer_signature, "wrapper regressed to one-buffer signature")

    wrong_require = jasmin_text.replace('namespace Final', 'namespace Finish', 1)
    require(wrong_require != jasmin_text, "could not construct wrong-require mutation")
    expect_rejected(verify_jasmin_text, wrong_require, "wrapper wrong namespace")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Tie the composed NTRU+768 inverse-NTT Jasmin wrapper to the authoritative C full schedule.",
    )
    parser.add_argument("--c-source", required=True, help="path to NTRU+/NTRU+768/ntt.c")
    parser.add_argument("--jasmin-source", required=True, help="path to ntruplus/jasmin/768/ref/invntt.jazz")
    parser.add_argument("--self-check", action="store_true", help="also require representative bad mutations to be rejected")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        c_text = Path(args.c_source).read_text(encoding="utf-8")
        jasmin_path = Path(args.jasmin_source)
        if not jasmin_path.exists():
            raise VerificationError(MISSING_SOURCE_HINT)
        jasmin_text = jasmin_path.read_text(encoding="utf-8")
        verify_c_text(c_text)
        verify_jasmin_text(jasmin_text)
        if args.self_check:
            run_self_check(c_text, jasmin_text)
    except (OSError, VerificationError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1

    if args.self_check:
        print("PASS: NTRU+768 composed inverse-NTT checker rejected representative bad mutations")
    print("PASS: NTRU+768 composed inverse-NTT C/Jasmin source coupling")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
