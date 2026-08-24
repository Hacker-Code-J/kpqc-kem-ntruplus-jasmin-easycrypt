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
NTT_CENTERED_BOUND = 1728
CASES_BOUNDARY = 6
CASES_RANDOM = 16
CASES_TOTAL = CASES_BOUNDARY + CASES_RANDOM


def next_u32(state: int) -> tuple[int, int]:
    x = state & 0xFFFFFFFF
    x ^= (x << 13) & 0xFFFFFFFF
    x ^= x >> 17
    x ^= (x << 5) & 0xFFFFFFFF
    return x & 0xFFFFFFFF, x & 0xFFFFFFFF


def sample_mod_q(state: int) -> tuple[int, int]:
    state, value = next_u32(state)
    return state, int(value % (2 * NTRUPLUS_Q)) - NTRUPLUS_Q


def sample_centered(state: int) -> tuple[int, int]:
    state, value = next_u32(state)
    return state, int(value % (2 * NTT_CENTERED_BOUND + 1)) - NTT_CENTERED_BOUND


def fill_constant(value: int) -> list[int]:
    return [value] * NTRUPLUS_N


def fill_alternating(even_value: int, odd_value: int) -> list[int]:
    return [even_value if (idx & 1) == 0 else odd_value for idx in range(NTRUPLUS_N)]


def fill_staircase(start: int, step: int) -> list[int]:
    out: list[int] = []
    value = start
    for _ in range(NTRUPLUS_N):
        out.append(value)
        value += step
        if value >= NTRUPLUS_Q:
            value = -NTRUPLUS_Q
        elif value < -NTRUPLUS_Q:
            value = NTRUPLUS_Q - 1
    return out


def fill_centered_staircase(start: int, step: int) -> list[int]:
    out: list[int] = []
    value = start
    for _ in range(NTRUPLUS_N):
        out.append(value)
        value += step
        if value > NTT_CENTERED_BOUND:
            value = -NTT_CENTERED_BOUND
        elif value < -NTT_CENTERED_BOUND:
            value = NTT_CENTERED_BOUND
    return out


def init_case(idx: int) -> tuple[list[int], list[int], list[int]]:
    if idx == 0:
        return fill_constant(0), fill_constant(0), fill_constant(0)
    if idx == 1:
        return (
            fill_constant(NTRUPLUS_Q - 1),
            fill_constant(NTRUPLUS_Q - 1),
            fill_constant(NTT_CENTERED_BOUND),
        )
    if idx == 2:
        return (
            fill_constant(-NTRUPLUS_Q),
            fill_constant(-NTRUPLUS_Q),
            fill_constant(-NTT_CENTERED_BOUND),
        )
    if idx == 3:
        return (
            fill_alternating(NTRUPLUS_Q - 1, -NTRUPLUS_Q),
            fill_alternating(-NTRUPLUS_Q, NTRUPLUS_Q - 1),
            fill_alternating(NTT_CENTERED_BOUND, -NTT_CENTERED_BOUND),
        )
    if idx == 4:
        return (
            fill_staircase(-NTRUPLUS_Q, 17),
            fill_staircase(NTRUPLUS_Q, -19),
            fill_centered_staircase(-NTT_CENTERED_BOUND, 29),
        )
    if idx == 5:
        h = [0] * NTRUPLUS_N
        r = [0] * NTRUPLUS_N
        m = [0] * NTRUPLUS_N
        for block in range(NTRUPLUS_N // 8):
            off = 8 * block
            left = NTRUPLUS_Q - 1 if (block & 1) == 0 else -NTRUPLUS_Q
            right = NTRUPLUS_Q - 1 if (block % 3) == 0 else 1 - NTRUPLUS_Q

            h[off + 0] = left
            h[off + 1] = right
            h[off + 2] = -right
            h[off + 3] = -left
            h[off + 4] = right
            h[off + 5] = left
            h[off + 6] = -left
            h[off + 7] = -right

            r[off + 0] = right
            r[off + 1] = left
            r[off + 2] = -left
            r[off + 3] = -right
            r[off + 4] = left
            r[off + 5] = right
            r[off + 6] = -right
            r[off + 7] = -left

            m[off + 0] = block % NTRUPLUS_Q
            m[off + 1] = -(block % NTRUPLUS_Q)
            m[off + 2] = (3 * block) % NTRUPLUS_Q
            m[off + 3] = -((5 * block) % NTRUPLUS_Q)
            m[off + 4] = (7 * block) % NTRUPLUS_Q
            m[off + 5] = -((11 * block) % NTRUPLUS_Q)
            m[off + 6] = (13 * block) % NTRUPLUS_Q
            m[off + 7] = -((17 * block) % NTRUPLUS_Q)
        return h, r, m

    state = (0x45D9F3B + 0x9E3779B9 * idx) & 0xFFFFFFFF
    h: list[int] = []
    r: list[int] = []
    m: list[int] = []
    for _ in range(NTRUPLUS_N):
        state, sample = sample_mod_q(state)
        h.append(sample)
    for _ in range(NTRUPLUS_N):
        state, sample = sample_mod_q(state)
        r.append(sample)
    for _ in range(NTRUPLUS_N):
        state, sample = sample_centered(state)
        m.append(sample)
    return h, r, m


def mod_q(value: int) -> int:
    reduced = value % NTRUPLUS_Q
    return reduced if reduced >= 0 else reduced + NTRUPLUS_Q


def load_zetas(ntt_source: Path) -> list[int]:
    text = ntt_source.read_text(encoding="utf-8")
    match = re.search(r"const\s+int16_t\s+zetas\[192\]\s*=\s*\{(.*?)\};", text, flags=re.S)
    if match is None:
        raise RuntimeError("could not locate zetas[192] table in ntt.c")
    zetas = [int(token) for token in re.findall(r"-?\d+", match.group(1))]
    if len(zetas) != 192:
        raise RuntimeError(f"expected 192 zetas, found {len(zetas)}")
    return zetas


def oracle_poly_basemul_add(h: list[int], r: list[int], m: list[int], zetas: list[int]) -> list[int]:
    out = [0] * NTRUPLUS_N
    for block in range(NTRUPLUS_N // 4):
        off = 4 * block
        zeta_word = zetas[96 + block // 2] if (block & 1) == 0 else -zetas[96 + block // 2]
        zeta_math = mod_q(zeta_word * NTRUPLUS_RINV)

        out[off + 0] = mod_q(
            h[off + 0] * r[off + 0]
            + zeta_math * (h[off + 1] * r[off + 3] + h[off + 2] * r[off + 2] + h[off + 3] * r[off + 1])
            + m[off + 0]
        )
        out[off + 1] = mod_q(
            h[off + 0] * r[off + 1]
            + h[off + 1] * r[off + 0]
            + zeta_math * (h[off + 2] * r[off + 3] + h[off + 3] * r[off + 2])
            + m[off + 1]
        )
        out[off + 2] = mod_q(
            h[off + 0] * r[off + 2]
            + h[off + 1] * r[off + 1]
            + h[off + 2] * r[off + 0]
            + zeta_math * h[off + 3] * r[off + 3]
            + m[off + 2]
        )
        out[off + 3] = mod_q(
            h[off + 0] * r[off + 3]
            + h[off + 1] * r[off + 2]
            + h[off + 2] * r[off + 1]
            + h[off + 3] * r[off + 0]
            + m[off + 3]
        )
    return out


def parse_driver_output(text: str) -> dict[tuple[str, int], list[int]]:
    parsed: dict[tuple[str, int], list[int]] = {}
    for line in text.splitlines():
        parts = line.strip().split()
        if not parts:
            continue
        if parts[0] not in {"ADD", "MUL", "MSG"}:
            raise RuntimeError(f"unexpected driver line: {line}")
        if len(parts) != NTRUPLUS_N + 2:
            raise RuntimeError(f"unexpected coefficient count in line: {parts[0]} {parts[1]}")
        parsed[(parts[0], int(parts[1]))] = [int(value) for value in parts[2:]]
    return parsed


def run_driver(driver: Path) -> dict[tuple[str, int], list[int]]:
    completed = subprocess.run(
        [str(driver)],
        check=True,
        capture_output=True,
        text=True,
    )
    return parse_driver_output(completed.stdout)


def verify_driver_vectors(parsed: dict[tuple[str, int], list[int]], zetas: list[int]) -> None:
    for idx in range(CASES_TOTAL):
        h, r, m = init_case(idx)
        oracle = oracle_poly_basemul_add(h, r, m, zetas)
        add = parsed[("ADD", idx)]
        mul = parsed[("MUL", idx)]
        msg = parsed[("MSG", idx)]

        if msg != m:
            raise RuntimeError(f"driver MSG payload mismatch in case {idx}")

        for coeff_idx, value in enumerate(add):
            if not (-NTRUPLUS_Q <= value < NTRUPLUS_Q):
                raise RuntimeError(f"ADD range violation in case {idx} coeff {coeff_idx}: {value}")
            if mod_q(value) != oracle[coeff_idx]:
                raise RuntimeError(
                    f"oracle mismatch in case {idx} coeff {coeff_idx}: "
                    f"driver={mod_q(value)} oracle={oracle[coeff_idx]}"
                )
            if mod_q(value) != mod_q(mul[coeff_idx] + m[coeff_idx]):
                raise RuntimeError(
                    f"poly_basemul + m relation mismatch in case {idx} coeff {coeff_idx}: "
                    f"add={mod_q(value)} mul_plus_m={mod_q(mul[coeff_idx] + m[coeff_idx])}"
                )


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Independent q-ring oracle check for NTRU+768 poly_basemul_add encapsulation vectors",
    )
    parser.add_argument("--driver", required=True, help="path to compiled encap_poly_basemul_add driver")
    parser.add_argument("--ntt-source", required=True, help="path to NTRU+/NTRU+768/ntt.c")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        parsed = run_driver(Path(args.driver))
        verify_driver_vectors(parsed, load_zetas(Path(args.ntt_source)))
    except (OSError, subprocess.CalledProcessError, RuntimeError) as err:
        print(f"FAILED: {err}", file=sys.stderr)
        return 1

    print(f"encap poly_basemul_add vectors verified across {CASES_TOTAL} cases")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
