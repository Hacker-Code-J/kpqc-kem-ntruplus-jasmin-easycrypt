#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import random
import subprocess
import sys
from pathlib import Path


TAIL_BYTES = 192
POLY_DEGREE = 768


class VerificationError(RuntimeError):
    pass


def cbd1_oracle(tail: bytes) -> list[int]:
    if len(tail) != TAIL_BYTES:
        raise VerificationError(f"tail must be {TAIL_BYTES} bytes")
    coeffs: list[int] = []
    half = POLY_DEGREE // 8
    for index in range(half):
        t1 = tail[index]
        t2 = tail[index + half]
        for _ in range(8):
            coeffs.append((t1 & 0x1) - (t2 & 0x1))
            t1 >>= 1
            t2 >>= 1
    if len(coeffs) != POLY_DEGREE:
        raise VerificationError("oracle produced the wrong coefficient count")
    return coeffs


def deterministic_vectors() -> list[tuple[str, bytes]]:
    half = TAIL_BYTES // 2
    zero_half = bytes(half)
    ff_half = bytes([0xFF]) * half
    vectors = [
        ("all-zero", bytes(TAIL_BYTES)),
        ("all-ff", bytes([0xFF]) * TAIL_BYTES),
        ("all-positive", ff_half + zero_half),
        ("all-negative", zero_half + ff_half),
        ("first-positive-bit", b"\x01" + bytes(TAIL_BYTES - 1)),
        ("last-positive-bit", bytes(half - 1) + b"\x80" + zero_half),
        ("first-negative-bit", zero_half + b"\x01" + bytes(half - 1)),
        ("last-negative-bit", bytes(TAIL_BYTES - 1) + b"\x80"),
        ("alternating-halves", bytes([0x55]) * half + bytes([0xAA]) * half),
        ("inverse-alternating-halves", bytes([0xAA]) * half + bytes([0x55]) * half),
        ("ascending", bytes(index & 0xFF for index in range(TAIL_BYTES))),
        ("descending", bytes(0xFF - (index & 0xFF) for index in range(TAIL_BYTES))),
    ]
    return vectors


def randomized_vectors() -> list[tuple[str, bytes]]:
    vectors: list[tuple[str, bytes]] = []
    for seed in range(32):
        rng = random.Random(seed)
        vectors.append((f"random-{seed:02d}", bytes(rng.getrandbits(8) for _ in range(TAIL_BYTES))))
    return vectors


def test_vectors() -> list[tuple[str, bytes]]:
    return deterministic_vectors() + randomized_vectors()


def run_driver(binary: Path, tail: bytes) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        [str(binary)],
        input=tail,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def decode_driver_output(data: bytes) -> list[int]:
    try:
        payload = json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise VerificationError(f"driver returned invalid JSON: {exc}") from exc
    if not isinstance(payload, list) or len(payload) != POLY_DEGREE:
        raise VerificationError(f"driver returned {len(payload) if isinstance(payload, list) else 'non-list'} coefficients")
    coeffs: list[int] = []
    for index, value in enumerate(payload):
        if not isinstance(value, int):
            raise VerificationError(f"driver coefficient {index} is not an integer")
        if value not in (-1, 0, 1):
            raise VerificationError(f"driver coefficient {index}={value} is outside [-1, 1]")
        coeffs.append(value)
    return coeffs


def verify(binary: Path) -> None:
    if not binary.is_file():
        raise VerificationError(f"missing poly_cbd1 driver: {binary}")

    for label, tail in test_vectors():
        expected_coeffs = cbd1_oracle(tail)

        completed = run_driver(binary, tail)
        if completed.returncode != 0:
            detail = completed.stderr.decode("utf-8", errors="replace").strip()
            raise VerificationError(f"driver failed for {label} with exit {completed.returncode}: {detail}")
        coeffs = decode_driver_output(completed.stdout)
        if coeffs != expected_coeffs:
            raise VerificationError(f"poly_cbd1 differential mismatch for {label}")

        repeated = run_driver(binary, tail)
        if repeated.returncode != 0:
            detail = repeated.stderr.decode("utf-8", errors="replace").strip()
            raise VerificationError(f"driver repeat failed for {label} with exit {repeated.returncode}: {detail}")
        if repeated.stdout != completed.stdout:
            raise VerificationError(f"driver output changed across repeated runs for {label}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compare NTRU+768 poly_cbd1 against an independent 192-byte-tail oracle",
    )
    parser.add_argument("--binary", required=True)
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        verify(Path(args.binary).resolve())
    except (OSError, VerificationError) as exc:
        print(f"poly_cbd1 differential test failed: {exc}", file=sys.stderr)
        return 1

    print(f"poly_cbd1 differential test passed ({len(test_vectors())} vectors)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
