#!/usr/bin/env python3

from __future__ import annotations

import argparse
import hashlib
import subprocess
import sys
from pathlib import Path


INPUT_BYTES = 1152
OUTPUT_BYTES = 32
DOMAIN_BYTE = b"\x00"


class VerificationError(RuntimeError):
    pass


def lcg_bytes(seed: int, length: int) -> bytes:
    state = seed & 0xFFFFFFFF
    result = bytearray(length)
    for index in range(length):
        state = (1664525 * state + 1013904223) & 0xFFFFFFFF
        result[index] = state >> 24
    return bytes(result)


def test_vectors() -> list[tuple[str, bytes]]:
    vectors = [
        ("all-zero", bytes(INPUT_BYTES)),
        ("all-ff", bytes([0xFF]) * INPUT_BYTES),
        ("ascending", bytes(index & 0xFF for index in range(INPUT_BYTES))),
        (
            "descending",
            bytes(0xFF - (index & 0xFF) for index in range(INPUT_BYTES)),
        ),
        ("first-bit", b"\x01" + bytes(INPUT_BYTES - 1)),
        (
            "middle-bit",
            bytes(INPUT_BYTES // 2) + b"\x80" + bytes(INPUT_BYTES // 2 - 1),
        ),
        ("last-bit", bytes(INPUT_BYTES - 1) + b"\x01"),
    ]
    vectors.extend(
        (f"lcg-{seed:02d}", lcg_bytes(seed, INPUT_BYTES))
        for seed in range(24)
    )
    return vectors


def run_driver(binary: Path, message: bytes) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        [str(binary)],
        input=message,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def verify(binary: Path) -> None:
    if not binary.is_file():
        raise VerificationError(f"missing hash_f driver: {binary}")

    for label, message in test_vectors():
        expected = hashlib.shake_256(DOMAIN_BYTE + message).digest(OUTPUT_BYTES)
        original = bytes(message)
        completed = run_driver(binary, message)
        if completed.returncode != 0:
            detail = completed.stderr.decode("utf-8", errors="replace").strip()
            raise VerificationError(
                f"driver failed for {label} with exit "
                f"{completed.returncode}: {detail}",
            )
        if completed.stdout != expected:
            raise VerificationError(f"SHAKE256 differential mismatch for {label}")
        if len(completed.stdout) != OUTPUT_BYTES:
            raise VerificationError(
                f"driver returned {len(completed.stdout)} bytes "
                f"for {label}; expected {OUTPUT_BYTES}",
            )
        if message != original:
            raise VerificationError(f"test harness mutated input for {label}")

        repeated = run_driver(binary, message)
        if repeated.returncode != 0:
            detail = repeated.stderr.decode("utf-8", errors="replace").strip()
            raise VerificationError(
                f"driver repeat failed for {label} with exit "
                f"{repeated.returncode}: {detail}",
            )
        if repeated.stdout != completed.stdout:
            raise VerificationError(
                f"driver output changed across repeated runs for {label}",
            )


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Compare NTRU+768 hash_f against Python's independent SHAKE256 "
            "oracle"
        ),
    )
    parser.add_argument("--binary", required=True)
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        verify(Path(args.binary).resolve())
    except (OSError, VerificationError) as exc:
        print(f"hash_f differential test failed: {exc}", file=sys.stderr)
        return 1

    print(f"hash_f differential test passed ({len(test_vectors())} vectors)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
