#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


EXPECTED_ZETAS = [
    -147, -1033, -682, -248, -708, 682, 1, -722, -723, -257, -1124, -867,
    -256, 1484, 1262, -1590, 1611, 222, 1164, -1346, 1716, -1521, -357, 395,
    -455, 639, 502, 655, -699, 541, 95, -1577, -1241, 550, -44, 39, -820,
    -216, -121, -757, -348, 937, 893, 387, -603, 1713, -1105, 1058, 1449,
    837, 901, 1637, -569, -1617, -1530, 1199, 50, -830, -625, 4, 176, -156,
    1257, -1507, -380, -606, 1293, 661, 1428, -1580, -565, -992, 548, -800,
    64, -371, 961, 641, 87, 630, 675, -834, 205, 54, -1081, 1351, 1413,
    -1331, -1673, -1267, -1558, 281, -1464, -588, 1015, 436, 223, 1138,
    -1059, -397, -183, 1655, 559, -1674, 277, 933, 1723, 437, -1514, 242,
    1640, 432, -1583, 696, 774, 1671, 927, 514, 512, 489, 297, 601, 1473,
    1130, 1322, 871, 760, 1212, -312, -352, 443, 943, 8, 1250, -100, 1660,
    -31, 1206, -1341, -1247, 444, 235, 1364, -1209, 361, 230, 673, 582, 1409,
    1501, 1401, 251, 1022, -1063, 1053, 1188, 417, -1391, -27, -1626, 1685,
    -315, 1408, -1248, 400, 274, -1543, 32, -1550, 1531, -1367, -124, 1458,
    1379, -940, -1681, 22, 1709, -275, 1108, 354, -1728, -968, 858, 1221,
    -218, 294, -732, -1095, 892, 1588, -779,
]
EXPECTED_EXPORT = "jade_ntruplus_ntruplus768_amd64_ref_ntt"
EXPECTED_NAMESPACE_REQUIRES = [
    ("Stage1", "ntt_stage1.jazz"),
    ("Radix3", "ntt_radix3.jazz"),
    ("Radix2_64", "ntt_radix2_64.jazz"),
    ("Radix2_32", "ntt_radix2_32.jazz"),
    ("Radix2_16", "ntt_radix2_16.jazz"),
    ("Radix2_8", "ntt_radix2_8.jazz"),
    ("Radix2_4", "ntt_radix2_4.jazz"),
]
EXPECTED_CALLS = [
    ("Stage1::jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1", "rp, ap"),
    ("Radix3::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3", "rp"),
    ("Radix2_64::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64", "rp"),
    ("Radix2_32::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32", "rp"),
    ("Radix2_16::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16", "rp"),
    ("Radix2_8::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8", "rp"),
    ("Radix2_4::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4", "rp"),
]


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
    require(zetas == EXPECTED_ZETAS, "C zetas[192] no longer match the authoritative NTRU+768 schedule")

    body = compact(extract_function_body(text, "ntt"))
    require(re.search(r"\bint k = 1;", body) is not None, "ntt() must initialize k to 1")

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
    require(prefix_match is not None, "C ntt() prefix no longer matches the verified stage1/radix3 schedule")

    tail = re.compile(
        r"for \(int step = 64; step >= 4; step >>= 1\) \{ "
        r"for \(int start = 0; start < NTRUPLUS_N; start \+= \(step << 1\)\) \{ "
        r"zeta1 = zetas\[k\+\+\]; "
        r"for \(int i = start; i < start \+ step; i\+\+\) \{ "
        r"t1 = fqmul\(zeta1, r\[i \+ step\]\); "
        r"r\[i \+ step\] = barrett_reduce\(r\[i\] - t1\); "
        r"r\[i\] = barrett_reduce\(r\[i\] \+ t1\); \} \} \}"
    )
    tail_match = tail.search(body)
    require(
        tail_match is not None,
        "C ntt() radix-2 tail no longer matches the verified step=64->32->16->8->4 Barrett schedule",
    )
    require(
        prefix_match.end() <= tail_match.start(),
        "C ntt() no longer executes the verified prefix before the radix-2 tail",
    )

    loads = re.findall(r"\b(zeta[12])\s*=\s*zetas\s*\[\s*(k\+\+|k--)\s*\]\s*;", body)
    require(
        loads == [("zeta1", "k++"), ("zeta1", "k++"), ("zeta2", "k++"), ("zeta1", "k++")],
        "ntt() must keep the verified zeta1/zeta2 textual load order",
    )
    radix3_reads = (768 // 384) * 2
    radix2_reads = sum(768 // (2 * step) for step in (64, 32, 16, 8, 4))
    total_reads = 1 + radix3_reads + radix2_reads
    require(total_reads == 191, f"derived ntt() zeta-read count changed: expected 191, found {total_reads}")
    require(body.count("for (int step = 64; step >= 4; step >>= 1)") == 1, "ntt() must keep a single radix-2 tail loop")
    require(body.count("for (int start = 0; start < NTRUPLUS_N; start += 384)") == 1, "ntt() must keep a single radix-3 outer loop")


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
    require(
        signature.search(strip_comments(text)) is not None,
        "wrapper export must keep the two-buffer `(rp, ap) -> rp` signature",
    )


def verify_jasmin_text(text: str) -> None:
    requires = parse_namespace_requires(text)
    require(
        requires == EXPECTED_NAMESPACE_REQUIRES,
        f"wrapper namespace/require list changed: expected {EXPECTED_NAMESPACE_REQUIRES}, found {requires}",
    )

    verify_export_signature(text)
    body = compact(extract_function_body(text, EXPECTED_EXPORT))

    expected_body = (
        "rp = Stage1::jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1(rp, ap); "
        "rp = Radix3::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3(rp); "
        "rp = Radix2_64::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64(rp); "
        "rp = Radix2_32::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32(rp); "
        "rp = Radix2_16::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16(rp); "
        "rp = Radix2_8::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8(rp); "
        "rp = Radix2_4::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4(rp); "
        "return rp;"
    )
    require(body == expected_body, "wrapper body no longer matches the verified seven-call composition order")

    calls = re.findall(
        r"rp = ((?:Stage1|Radix3|Radix2_64|Radix2_32|Radix2_16|Radix2_8|Radix2_4)::jade_ntruplus_ntruplus768_amd64_ref_ntt(?:_stage1|_radix3|_radix2_64|_radix2_32|_radix2_16|_radix2_8|_radix2_4))\(([^)]*)\);",
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

    mutated_c_index = c_text.replace("int k = 1;", "int k = 0;", 1)
    require(mutated_c_index != c_text, "could not construct C initial-k mutation")
    expect_rejected(verify_c_text, mutated_c_index, "C wrong initial zeta index")

    mutated_c_zeta = c_text.replace("-779", "-778", 1)
    require(mutated_c_zeta != c_text, "could not construct C zeta-table mutation")
    expect_rejected(verify_c_text, mutated_c_zeta, "C wrong terminal zeta")

    missing_call = jasmin_text.replace(
        '  rp = Radix2_8::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8(rp);\n',
        "",
        1,
    )
    require(missing_call != jasmin_text, "could not construct missing-call mutation")
    expect_rejected(verify_jasmin_text, missing_call, "wrapper missing radix2_8 call")

    reordered_calls = jasmin_text.replace(
        "  rp = Radix2_32::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32(rp);\n"
        "  rp = Radix2_16::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16(rp);\n",
        "  rp = Radix2_16::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16(rp);\n"
        "  rp = Radix2_32::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32(rp);\n",
        1,
    )
    require(reordered_calls != jasmin_text, "could not construct reordered-call mutation")
    expect_rejected(verify_jasmin_text, reordered_calls, "wrapper reordered radix2_32/radix2_16 calls")

    duplicated_call = jasmin_text.replace(
        "  rp = Radix2_16::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16(rp);\n",
        "  rp = Radix2_16::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16(rp);\n"
        "  rp = Radix2_16::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16(rp);\n",
        1,
    )
    require(duplicated_call != jasmin_text, "could not construct duplicated-call mutation")
    expect_rejected(verify_jasmin_text, duplicated_call, "wrapper duplicated radix2_16 call")

    wrong_require = jasmin_text.replace('namespace Radix2_8', 'namespace Radix2_8_Partial', 1)
    require(wrong_require != jasmin_text, "could not construct wrong-require mutation")
    expect_rejected(verify_jasmin_text, wrong_require, "wrapper wrong namespace")

    aliased_signature = jasmin_text.replace(
        "  reg const ptr u16[NTRUPLUS_N] ap) -> reg ptr u16[NTRUPLUS_N]",
        "  reg mut ptr u16[NTRUPLUS_N] rp_alias) -> reg ptr u16[NTRUPLUS_N]",
        1,
    )
    require(aliased_signature != jasmin_text, "could not construct signature-alias mutation")
    expect_rejected(verify_jasmin_text, aliased_signature, "wrapper signature alias regression")

    stale_partial = jasmin_text.replace(
        "  rp = Radix2_8::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8(rp);\n"
        "  rp = Radix2_4::jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4(rp);\n"
        "\n"
        "  return rp;\n",
        "  return rp;\n",
        1,
    )
    require(stale_partial != jasmin_text, "could not construct stale-partial mutation")
    expect_rejected(verify_jasmin_text, stale_partial, "wrapper stale partial composition")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Tie the composed NTRU+768 forward-NTT Jasmin wrapper to the authoritative C full schedule.",
    )
    parser.add_argument("--c-source", required=True, help="path to NTRU+/NTRU+768/ntt.c")
    parser.add_argument("--jasmin-source", required=True, help="path to ntruplus/jasmin/768/ref/ntt.jazz")
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
        print("PASS: NTRU+768 composed forward-NTT checker rejected representative bad mutations")
    print("PASS: NTRU+768 composed forward-NTT C/Jasmin source coupling")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
