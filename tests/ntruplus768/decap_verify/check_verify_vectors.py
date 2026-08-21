#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path


POLY_BYTES = 1152


class VerificationError(RuntimeError):
    pass


def lcg_bytes(seed: int, length: int) -> bytes:
    state = seed & 0xFFFFFFFF
    result = bytearray(length)
    for index in range(length):
        state = (1664525 * state + 1013904223) & 0xFFFFFFFF
        result[index] = state >> 24
    return bytes(result)


def pair_vectors() -> list[tuple[str, bytes, bytes, int]]:
    base = bytes(POLY_BYTES)
    first = bytearray(base)
    first[0] = 1
    middle = bytearray(base)
    middle[POLY_BYTES // 2] = 0x80
    last = bytearray(base)
    last[-1] = 0xFF
    sparse = bytearray(base)
    for index in (3, 97, 511, 900, 1151):
        sparse[index] = (index * 17) & 0xFF
    multi = bytearray(base)
    for index, value in ((0, 0xAA), (1, 0x55), (100, 0x11), (700, 0x22), (1151, 0x33)):
        multi[index] = value

    vectors = [
        ("equal-zero", base, base, 0),
        ("equal-random", lcg_bytes(123, POLY_BYTES), lcg_bytes(123, POLY_BYTES), 0),
        ("first-mismatch", base, bytes(first), 1),
        ("middle-mismatch", base, bytes(middle), 1),
        ("last-mismatch", base, bytes(last), 1),
        ("sparse-mismatch", base, bytes(sparse), 1),
        ("multiple-mismatch", base, bytes(multi), 1),
    ]
    for seed in range(24):
        left = lcg_bytes(seed, POLY_BYTES)
        right = bytearray(left)
        if seed & 1:
            right[(37 * seed) % POLY_BYTES] ^= 0x5A
            expected = 1
        else:
            expected = 0
        vectors.append((f"lcg-{seed:02d}", left, bytes(right), expected))
    return vectors


def run_driver(binary: Path, left: bytes, right: bytes) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        [str(binary)],
        input=left + right,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def decode_output(data: bytes) -> dict[str, int]:
    try:
        payload = json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise VerificationError(f"driver returned invalid JSON: {exc}") from exc
    if not isinstance(payload, dict):
        raise VerificationError("driver returned non-object JSON")
    result = payload.get("result")
    if not isinstance(result, int):
        raise VerificationError("driver field `result` is missing or non-int")
    return payload


def verify(binary: Path) -> None:
    if not binary.is_file():
        raise VerificationError(f"missing verify driver: {binary}")

    for label, left, right, expected in pair_vectors():
        left_before = bytes(left)
        right_before = bytes(right)
        completed = run_driver(binary, left, right)
        if completed.returncode != 0:
            detail = completed.stderr.decode("utf-8", errors="replace").strip()
            raise VerificationError(f"driver failed for {label} with exit {completed.returncode}: {detail}")
        payload = decode_output(completed.stdout)
        if payload["result"] != expected:
            raise VerificationError(f"verify() mismatch for {label}: expected {expected}, got {payload['result']}")
        if payload["result"] not in (0, 1):
            raise VerificationError(f"verify() escaped boolean range for {label}: {payload['result']}")
        if left != left_before or right != right_before:
            raise VerificationError(f"test harness mutated inputs for {label}")

        repeated = run_driver(binary, left, right)
        if repeated.returncode != 0:
            detail = repeated.stderr.decode("utf-8", errors="replace").strip()
            raise VerificationError(f"driver repeat failed for {label} with exit {repeated.returncode}: {detail}")
        if repeated.stdout != completed.stdout:
            raise VerificationError(f"driver output changed across repeated runs for {label}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compare NTRU+768 verify() against an independent equality oracle",
    )
    parser.add_argument("--binary", required=True)
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        verify(Path(args.binary).resolve())
    except (OSError, VerificationError) as exc:
        print(f"verify differential test failed: {exc}", file=sys.stderr)
        return 1

    print(f"verify differential test passed ({len(pair_vectors())} vectors)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
