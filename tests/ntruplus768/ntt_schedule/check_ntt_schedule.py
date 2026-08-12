#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


EXPECTED_N = 768
EXPECTED_Q = 3457
EXPECTED_D = 4
EXPECTED_ROOT = 22
MONT_R = 1 << 16
PROOF_POLY = (192, 96)


class VerificationError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def center(value: int, modulus: int) -> int:
    return ((value + modulus // 2) % modulus) - modulus // 2


def mod_inverse(value: int, modulus: int) -> int:
    return pow(value, -1, modulus)


def strip_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    return re.sub(r"//.*", "", text)


def parse_define_map(text: str) -> dict[str, int]:
    defines: dict[str, int] = {}
    for name, value in re.findall(r"^\s*#define\s+([A-Za-z0-9_]+)\s+(-?\d+)\b", text, flags=re.M):
        defines[name] = int(value)
    return defines


def parse_array(text: str, name: str) -> tuple[int, list[int]]:
    pattern = rf"const\s+int16_t\s+{re.escape(name)}\s*\[(\d+)\]\s*=\s*\{{(.*?)\}};"
    match = re.search(pattern, text, flags=re.S)
    require(match is not None, f"could not find int16_t array `{name}`")
    declared_len = int(match.group(1))
    values = [int(token) for token in re.findall(r"-?\d+", match.group(2))]
    return declared_len, values


def extract_function_body(text: str, name: str) -> str:
    match = re.search(rf"\b{name}\s*\([^)]*\)\s*\{{", text)
    require(match is not None, f"could not find function `{name}`")
    start = match.end() - 1
    depth = 0
    for index in range(start, len(text)):
        char = text[index]
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1 : index]
    raise VerificationError(f"unterminated body for function `{name}`")


def parse_params(params_path: Path) -> tuple[int, int]:
    params_text = params_path.read_text(encoding="utf-8")
    defines = parse_define_map(params_text)
    require("NTRUPLUS_N" in defines, f"missing NTRUPLUS_N in {params_path}")
    require("NTRUPLUS_Q" in defines, f"missing NTRUPLUS_Q in {params_path}")
    return defines["NTRUPLUS_N"], defines["NTRUPLUS_Q"]


def factor_counts(value: int) -> tuple[int, int]:
    radix2 = 0
    radix3 = 0
    while value % 2 == 0:
        value //= 2
        radix2 += 1
    while value % 3 == 0:
        value //= 3
        radix3 += 1
    require(value == 1, "n/d must factor completely into powers of 2 and 3")
    require(radix2 >= 1, "cyclotomic-trinomial split requires at least one radix-2 factor")
    return radix2, radix3


def build_schedule(n_value: int, d_value: int, w_order: int) -> tuple[list[int], list[int]]:
    radix2, radix3 = factor_counts(n_value // d_value)
    rows: list[list[int]] = [[w_order]]
    schedule = [0]

    rows.append([w_order // 6, 5 * w_order // 6])
    schedule.append(rows[1][0] % w_order)

    for _ in range(radix3):
        previous = rows[-1]
        current: list[int] = []
        for entry in previous:
            base = entry // 3
            current.extend([base, base + w_order // 3, base + 2 * w_order // 3])
            schedule.extend([base % w_order, (2 * base) % w_order])
        rows.append(current)

    for _ in range(radix2 - 1):
        previous = rows[-1]
        current = []
        for entry in previous:
            base = entry // 2
            current.extend([base, base + w_order // 2])
            schedule.append(base % w_order)
        rows.append(current)

    leaves = [entry % w_order for entry in rows[-1]]
    require(len(schedule) == n_value // d_value, "internal Figure-22 schedule generator produced the wrong length")
    require(len(leaves) == n_value // d_value, "terminal factor generator produced the wrong length")
    return schedule, leaves


def decode_montgomery(value: int, q_value: int, r_inverse_mod_q: int) -> int:
    return (value % q_value) * r_inverse_mod_q % q_value


def discrete_log_table(root: int, order: int, modulus: int) -> dict[int, int]:
    table = {}
    value = 1
    for exponent in range(order):
        require(value not in table, f"root {root} does not have exact order {order}")
        table[value] = exponent
        value = (value * root) % modulus
    require(value == 1, f"root {root} failed to wrap after {order} steps")
    return table


def verify_root_and_constants(defines: dict[str, int], q_value: int, n_value: int) -> tuple[int, int]:
    r_mod_q = MONT_R % q_value
    r_inverse_mod_q = mod_inverse(r_mod_q, q_value)
    w_order = 3 * n_value // EXPECTED_D

    require(pow(EXPECTED_ROOT, w_order, q_value) == 1, "zeta=22 does not satisfy zeta^576 = 1 mod q")
    for divisor in (2, 3):
        require(
            pow(EXPECTED_ROOT, w_order // divisor, q_value) != 1,
            f"zeta=22 does not have exact order {w_order}",
        )

    expected_constants = {
        "NTRUPLUS_R": center(r_mod_q, q_value),
        "NTRUPLUS_RINV": center(r_inverse_mod_q, q_value),
        "NTRUPLUS_RSQ": center((r_mod_q * r_mod_q) % q_value, q_value),
        "NTRUPLUS_QINV": mod_inverse(q_value, MONT_R),
        "NTRUPLUS_OMEGA": center(pow(EXPECTED_ROOT, w_order // 3, q_value) * r_mod_q, q_value),
        "NTRUPLUS_ZMINUSZ5INV": center(
            mod_inverse(
                (
                    pow(EXPECTED_ROOT, w_order // 6, q_value)
                    - pow(pow(EXPECTED_ROOT, w_order // 6, q_value), 5, q_value)
                )
                % q_value,
                q_value,
            )
            * r_mod_q,
            q_value,
        ),
        "NTRUPLUS_NINV": center(mod_inverse(n_value // EXPECTED_D, q_value) * r_mod_q, q_value),
        "NTRUPLUS_2NINV": center(2 * mod_inverse(n_value // EXPECTED_D, q_value) * r_mod_q, q_value),
    }

    for name, expected in expected_constants.items():
        actual = defines.get(name)
        require(actual == expected, f"{name} mismatch: expected {expected}, found {actual}")

    return w_order, r_inverse_mod_q


def verify_schedule_table(
    zetas: list[int],
    q_value: int,
    w_order: int,
    r_inverse_mod_q: int,
) -> None:
    expected_exponents, leaves = build_schedule(EXPECTED_N, EXPECTED_D, w_order)
    require(len(zetas) == len(expected_exponents), "zetas table length does not match the Figure-22 schedule")

    log_table = discrete_log_table(EXPECTED_ROOT, w_order, q_value)
    expected_values = [center(pow(EXPECTED_ROOT, exponent, q_value) * (MONT_R % q_value), q_value) for exponent in expected_exponents]
    require(
        zetas == expected_values,
        "zetas table values do not equal centered Montgomery zeta^exp values from Figure 22",
    )

    decoded_exponents = []
    for index, value in enumerate(zetas):
        decoded = decode_montgomery(value, q_value, r_inverse_mod_q)
        exponent = log_table.get(decoded)
        require(exponent is not None, f"zetas[{index}] decodes to a value outside <22>")
        decoded_exponents.append(exponent)

    require(
        decoded_exponents == expected_exponents,
        "decoded zetas exponents deviate from the official Figure-22 NTRU+768 schedule",
    )

    require(len(set(leaves)) == len(leaves), "terminal factor exponents are not all distinct")
    for pair_index in range(0, len(leaves), 2):
        lhs = leaves[pair_index]
        rhs = leaves[pair_index + 1]
        require(
            (rhs - lhs) % w_order == w_order // 2,
            f"terminal factor pair {pair_index // 2} does not interleave +/- siblings",
        )

    degree_hi, degree_lo = PROOF_POLY
    for index, exponent in enumerate(leaves):
        root = pow(EXPECTED_ROOT, exponent, q_value)
        value = (pow(root, degree_hi, q_value) - pow(root, degree_lo, q_value) + 1) % q_value
        require(value == 0, f"terminal root {index} does not satisfy y^{degree_hi}-y^{degree_lo}+1 = 0")


def verify_ntt_loops(body: str, n_value: int) -> None:
    normalized = strip_comments(body)
    require(re.search(r"\bint\s+k\s*=\s*1\s*;", normalized) is not None, "ntt() must initialize k to 1")
    loads = re.findall(r"\b(zeta[12])\s*=\s*zetas\s*\[\s*(k\+\+|k--)\s*\]\s*;", normalized)
    require(
        loads == [("zeta1", "k++"), ("zeta1", "k++"), ("zeta2", "k++"), ("zeta1", "k++")],
        "ntt() must load zetas[k++] exactly four times in the expected zeta1/zeta2 order",
    )
    require(
        re.search(
            r"\bzeta1\s*=\s*zetas\s*\[\s*k\+\+\s*\]\s*;\s*for\s*\(\s*int\s+i\s*=\s*0\s*;\s*i\s*<\s*NTRUPLUS_N\s*/\s*2\s*;\s*i\+\+\s*\)",
            normalized,
        )
        is not None,
        "ntt() initial zeta load must occur immediately before the first half-size loop",
    )
    require(
        re.search(
            r"for\s*\(\s*int\s+start\s*=\s*0\s*;\s*start\s*<\s*NTRUPLUS_N\s*;\s*start\s*\+=\s*384\s*\)\s*\{\s*"
            r"zeta1\s*=\s*zetas\s*\[\s*k\+\+\s*\]\s*;\s*"
            r"zeta2\s*=\s*zetas\s*\[\s*k\+\+\s*\]\s*;\s*"
            r"for\s*\(\s*int\s+i\s*=\s*start\s*;\s*i\s*<\s*start\s*\+\s*128\s*;\s*i\+\+\s*\)",
            normalized,
        )
        is not None,
        "ntt() radix-3 loop must load zeta1 then zeta2 before the 128-point inner loop",
    )
    require(
        re.search(
            r"for\s*\(\s*int\s+step\s*=\s*64\s*;\s*step\s*>=\s*4\s*;\s*step\s*>>=\s*1\s*\)\s*\{\s*"
            r"for\s*\(\s*int\s+start\s*=\s*0\s*;\s*start\s*<\s*NTRUPLUS_N\s*;\s*start\s*\+=\s*\(step\s*<<\s*1\)\s*\)\s*\{\s*"
            r"zeta1\s*=\s*zetas\s*\[\s*k\+\+\s*\]\s*;\s*"
            r"for\s*\(\s*int\s+i\s*=\s*start\s*;\s*i\s*<\s*start\s*\+\s*step\s*;\s*i\+\+\s*\)",
            normalized,
        )
        is not None,
        "ntt() radix-2 loop must load zeta1 inside each start block before the butterfly loop",
    )

    radix3_reads = (n_value // 384) * 2
    radix2_reads = sum(n_value // (2 * step) for step in (64, 32, 16, 8, 4))
    total_reads = 1 + radix3_reads + radix2_reads
    require(total_reads == 191, f"ntt() should consume 191 table entries, not {total_reads}")
    require(1 + total_reads - 1 == 191, "ntt() table bounds should end at zetas[191]")


def verify_invntt_loops(body: str, n_value: int) -> None:
    normalized = strip_comments(body)
    require(re.search(r"\bint\s+k\s*=\s*191\s*;", normalized) is not None, "invntt() must initialize k to 191")
    loads = re.findall(r"\b(zeta[12])\s*=\s*zetas\s*\[\s*(k\+\+|k--)\s*\]\s*;", normalized)
    require(
        loads == [("zeta1", "k--"), ("zeta2", "k--"), ("zeta1", "k--")],
        "invntt() must load zetas[k--] exactly three times in the expected reverse order",
    )
    require(
        re.search(
            r"for\s*\(\s*int\s+step\s*=\s*4\s*;\s*step\s*<=\s*64\s*;\s*step\s*<<=\s*1\s*\)\s*\{\s*"
            r"for\s*\(\s*int\s+start\s*=\s*0\s*;\s*start\s*<\s*NTRUPLUS_N\s*;\s*start\s*\+=\s*\(step\s*<<\s*1\)\s*\)\s*\{\s*"
            r"zeta1\s*=\s*zetas\s*\[\s*k--\s*\]\s*;\s*"
            r"for\s*\(\s*int\s+i\s*=\s*start\s*;\s*i\s*<\s*start\s*\+\s*step\s*;\s*i\+\+\s*\)",
            normalized,
        )
        is not None,
        "invntt() radix-2 loop must load zeta1 inside each start block before the butterfly loop",
    )
    require(
        re.search(
            r"for\s*\(\s*int\s+start\s*=\s*0\s*;\s*start\s*<\s*NTRUPLUS_N\s*;\s*start\s*\+=\s*384\s*\)\s*\{\s*"
            r"zeta2\s*=\s*zetas\s*\[\s*k--\s*\]\s*;\s*"
            r"zeta1\s*=\s*zetas\s*\[\s*k--\s*\]\s*;\s*"
            r"for\s*\(\s*int\s+i\s*=\s*start\s*;\s*i\s*<\s*start\s*\+\s*128\s*;\s*i\+\+\s*\)",
            normalized,
        )
        is not None,
        "invntt() radix-3 loop must load zeta2 then zeta1 before the 128-point inner loop",
    )
    require(
        re.search(
            r"t2\s*=\s*fqmul\s*\(\s*NTRUPLUS_ZMINUSZ5INV\s*,\s*r\[i\]\s*-\s*r\[i\s*\+\s*NTRUPLUS_N\s*/\s*2\]\s*\)",
            normalized,
        )
        is not None,
        "invntt() final cyclotomic-trinomial recombination changed",
    )

    radix2_reads = sum(n_value // (2 * step) for step in (4, 8, 16, 32, 64))
    radix3_reads = (n_value // 384) * 2
    total_reads = radix2_reads + radix3_reads
    require(total_reads == 190, f"invntt() should consume 190 table entries, not {total_reads}")
    require(191 - total_reads == 1, "invntt() should stop with k == 1 after the reverse walk")


def run_self_check() -> None:
    w_order = 3 * EXPECTED_N // EXPECTED_D
    schedule, leaves = build_schedule(EXPECTED_N, EXPECTED_D, w_order)
    require(schedule[:6] == [0, 96, 32, 64, 160, 320], "self-check prefix mismatch for Figure-22 schedule")
    require(leaves[:8] == [1, 289, 145, 433, 73, 361, 217, 505], "self-check terminal factor prefix mismatch")
    require(center((MONT_R % EXPECTED_Q), EXPECTED_Q) == -147, "self-check Montgomery R mismatch")
    require(pow(EXPECTED_ROOT, w_order, EXPECTED_Q) == 1, "self-check root order mismatch")


def verify_source(source_path: Path) -> None:
    source_text = source_path.read_text(encoding="utf-8")
    defines = parse_define_map(source_text)
    params_path = source_path.with_name("params.h")
    n_value, q_value = parse_params(params_path)
    require(n_value == EXPECTED_N, f"expected NTRUPLUS_N == {EXPECTED_N}, found {n_value}")
    require(q_value == EXPECTED_Q, f"expected NTRUPLUS_Q == {EXPECTED_Q}, found {q_value}")

    declared_len, zetas = parse_array(source_text, "zetas")
    require(declared_len == 192, f"zetas declaration length must be 192, found {declared_len}")
    require(len(zetas) == 192, f"zetas table must contain 192 entries, found {len(zetas)}")

    w_order, r_inverse_mod_q = verify_root_and_constants(defines, q_value, n_value)
    verify_schedule_table(zetas, q_value, w_order, r_inverse_mod_q)
    verify_ntt_loops(extract_function_body(source_text, "ntt"), n_value)
    verify_invntt_loops(extract_function_body(source_text, "invntt"), n_value)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Verify the NTRU+768 NTT schedule, constants, and loop/table coupling.",
    )
    parser.add_argument(
        "source",
        nargs="?",
        default="NTRU+/NTRU+768/ntt.c",
        help="path to NTRU+/NTRU+768/ntt.c",
    )
    parser.add_argument(
        "--self-check",
        action="store_true",
        help="run internal checker invariants before verifying the source",
    )
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        if args.self_check:
            run_self_check()
        verify_source(Path(args.source))
    except (OSError, VerificationError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1

    if args.self_check:
        print("PASS: NTRU+768 NTT checker self-check")
    print(f"PASS: NTRU+768 NTT schedule verification ({args.source})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
