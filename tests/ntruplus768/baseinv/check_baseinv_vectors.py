#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path


NTRUPLUS_N = 768
NTRUPLUS_Q = 3457
NTRUPLUS_RINV = 2775
SCALAR_CASES = 24
POLY_CASES = 17


def mod_q(value: int) -> int:
    reduced = value % NTRUPLUS_Q
    return reduced if reduced >= 0 else reduced + NTRUPLUS_Q


def centered_mod_q(value: int) -> int:
    reduced = mod_q(value)
    return reduced - NTRUPLUS_Q if reduced > NTRUPLUS_Q // 2 else reduced


def parse_zetas(ntt_source: Path) -> list[int]:
    text = ntt_source.read_text(encoding="utf-8")
    match = re.search(r"const\s+int16_t\s+zetas\[192\]\s*=\s*\{(.*?)\};", text, flags=re.S)
    if match is None:
        raise RuntimeError("could not locate zetas[192]")
    zetas = [int(token) for token in re.findall(r"-?\d+", match.group(1))]
    if len(zetas) != 192:
        raise RuntimeError(f"expected 192 zetas, found {len(zetas)}")
    return zetas


def zeta_to_math(zeta_word: int) -> int:
    return mod_q(zeta_word * NTRUPLUS_RINV)


def quartic_mul(a: list[int], b: list[int], zeta_word: int) -> list[int]:
    zeta = zeta_to_math(zeta_word)
    return [
        mod_q(a[0] * b[0] + zeta * (a[1] * b[3] + a[2] * b[2] + a[3] * b[1])),
        mod_q(a[0] * b[1] + a[1] * b[0] + zeta * (a[2] * b[3] + a[3] * b[2])),
        mod_q(a[0] * b[2] + a[1] * b[1] + a[2] * b[0] + zeta * a[3] * b[3]),
        mod_q(a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0]),
    ]


def multiplication_matrix(a: list[int], zeta_word: int) -> list[list[int]]:
    columns = []
    for basis_index in range(4):
        basis = [0, 0, 0, 0]
        basis[basis_index] = 1
        columns.append(quartic_mul(a, basis, zeta_word))
    return [[columns[col][row] for col in range(4)] for row in range(4)]


def determinant_and_inverse(a: list[int], zeta_word: int) -> tuple[int, list[int] | None]:
    matrix = multiplication_matrix(a, zeta_word)
    aug = [row[:] + [1 if idx == 0 else 0] for idx, row in enumerate(matrix)]
    determinant = 1
    sign = 1
    pivot_row = 0

    for col in range(4):
        pivot = None
        for row in range(pivot_row, 4):
            if aug[row][col] % NTRUPLUS_Q != 0:
                pivot = row
                break
        if pivot is None:
            return 0, None
        if pivot != pivot_row:
            aug[pivot_row], aug[pivot] = aug[pivot], aug[pivot_row]
            sign = -sign
        pivot_value = mod_q(aug[pivot_row][col])
        determinant = mod_q(determinant * pivot_value)
        inv_pivot = pow(pivot_value, -1, NTRUPLUS_Q)
        aug[pivot_row] = [mod_q(value * inv_pivot) for value in aug[pivot_row]]
        for row in range(4):
            if row == pivot_row:
                continue
            factor = aug[row][col] % NTRUPLUS_Q
            if factor == 0:
                continue
            aug[row] = [
                mod_q(aug[row][idx] - factor * aug[pivot_row][idx])
                for idx in range(5)
            ]
        pivot_row += 1

    if sign < 0:
        determinant = mod_q(-determinant)
    inverse = [centered_mod_q(aug[idx][4]) for idx in range(4)]
    return determinant, inverse


def parse_driver_output(text: str) -> tuple[dict[int, tuple[int, int, list[int], list[int]]], dict[int, tuple[int, list[int], list[int]]], dict[int, int]]:
    scalar_cases: dict[int, tuple[int, int, list[int], list[int]]] = {}
    poly_cases: dict[int, tuple[int, list[int], list[int]]] = {}
    fqinv_table: dict[int, int] = {}
    for line in text.splitlines():
        parts = line.strip().split()
        if not parts:
            continue
        if parts[0] == "SCALAR":
            if len(parts) != 12:
                raise RuntimeError(f"unexpected scalar line: {line}")
            case_index = int(parts[1])
            scalar_cases[case_index] = (
                int(parts[2]),
                int(parts[3]),
                [int(value) for value in parts[4:8]],
                [int(value) for value in parts[8:12]],
            )
        elif parts[0] == "POLY":
            if len(parts) != 2 + 1 + 2 * NTRUPLUS_N:
                raise RuntimeError(f"unexpected poly line length: {len(parts)}")
            case_index = int(parts[1])
            poly_cases[case_index] = (
                int(parts[2]),
                [int(value) for value in parts[3 : 3 + NTRUPLUS_N]],
                [int(value) for value in parts[3 + NTRUPLUS_N :]],
            )
        elif parts[0] == "FQINV":
            if len(parts) != 3:
                raise RuntimeError(f"unexpected fqinv line: {line}")
            fqinv_table[int(parts[1])] = int(parts[2])
        else:
            raise RuntimeError(f"unexpected driver tag: {parts[0]}")
    return scalar_cases, poly_cases, fqinv_table


def verify_scalar_cases(scalar_cases: dict[int, tuple[int, int, list[int], list[int]]]) -> None:
    if len(scalar_cases) != SCALAR_CASES:
        raise RuntimeError(f"expected {SCALAR_CASES} scalar cases, found {len(scalar_cases)}")
    for case_index in range(SCALAR_CASES):
        zeta_word, status, a, r = scalar_cases[case_index]
        determinant, oracle_inv = determinant_and_inverse(a, zeta_word)
        expected_status = 1 if determinant == 0 else 0
        if status != expected_status:
            raise RuntimeError(
                f"scalar case {case_index} status mismatch: driver={status} oracle={expected_status}"
            )
        if status == 0:
            if oracle_inv is None:
                raise RuntimeError(f"scalar case {case_index} unexpectedly missing inverse")
            for value in r:
                if value < -NTRUPLUS_Q or value >= NTRUPLUS_Q:
                    raise RuntimeError(f"scalar case {case_index} out-of-range output {value}")
            if [mod_q(value) for value in r] != [mod_q(value) for value in oracle_inv]:
                raise RuntimeError(f"scalar case {case_index} inverse mismatch")
            if quartic_mul(a, r, zeta_word) != [1, 0, 0, 0]:
                raise RuntimeError(f"scalar case {case_index} does not multiply to the identity")


def verify_poly_cases(poly_cases: dict[int, tuple[int, list[int], list[int]]], zetas: list[int]) -> None:
    if len(poly_cases) != POLY_CASES:
        raise RuntimeError(f"expected {POLY_CASES} poly cases, found {len(poly_cases)}")
    for case_index in range(POLY_CASES):
        status, a, r = poly_cases[case_index]
        failed = False
        for block in range(NTRUPLUS_N // 4):
            zeta_word = zetas[96 + block // 2] if (block & 1) == 0 else -zetas[96 + block // 2]
            coeffs = a[4 * block : 4 * block + 4]
            determinant, oracle_inv = determinant_and_inverse(coeffs, zeta_word)
            if determinant == 0:
                failed = True
                break
            if oracle_inv is None:
                raise RuntimeError(f"poly case {case_index} block {block} missing inverse")
            if status == 0:
                out_block = r[4 * block : 4 * block + 4]
                if [mod_q(value) for value in out_block] != [mod_q(value) for value in oracle_inv]:
                    raise RuntimeError(f"poly case {case_index} block {block} inverse mismatch")
                if quartic_mul(coeffs, out_block, zeta_word) != [1, 0, 0, 0]:
                    raise RuntimeError(f"poly case {case_index} block {block} identity mismatch")
                for value in out_block:
                    if value < -NTRUPLUS_Q or value >= NTRUPLUS_Q:
                        raise RuntimeError(f"poly case {case_index} block {block} out-of-range output {value}")
        expected_status = 1 if failed else 0
        if status != expected_status:
            raise RuntimeError(
                f"poly case {case_index} status mismatch: driver={status} oracle={expected_status}"
            )
        if status == 1 and any(value != 0 for value in r):
            raise RuntimeError(f"poly case {case_index} failure output was not all zero")


def verify_fqinv_table(fqinv_table: dict[int, int]) -> None:
    if len(fqinv_table) != NTRUPLUS_Q:
        raise RuntimeError(f"expected {NTRUPLUS_Q} fqinv outputs, found {len(fqinv_table)}")
    for residue in range(1, NTRUPLUS_Q):
        inv_value = fqinv_table[residue]
        if mod_q(residue * inv_value) != 1:
            raise RuntimeError(f"fqinv({residue}) failed the multiplicative identity check")


def run_driver(driver: Path) -> tuple[dict[int, tuple[int, int, list[int], list[int]]], dict[int, tuple[int, list[int], list[int]]], dict[int, int]]:
    completed = subprocess.run([str(driver)], check=True, capture_output=True, text=True)
    return parse_driver_output(completed.stdout)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Independent oracle checks for the NTRU+768 baseinv/poly_baseinv milestone")
    parser.add_argument("--driver", required=True)
    parser.add_argument("--ntt-source", required=True)
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        scalar_cases, poly_cases, fqinv_table = run_driver(Path(args.driver))
        zetas = parse_zetas(Path(args.ntt_source))
        verify_scalar_cases(scalar_cases)
        verify_poly_cases(poly_cases, zetas)
        verify_fqinv_table(fqinv_table)
    except (OSError, RuntimeError, subprocess.CalledProcessError) as err:
        print(f"FAILED: {err}", file=sys.stderr)
        return 1

    print("baseinv vectors verified: 24 scalar, 17 poly, 3456 nonzero fqinv residues")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
