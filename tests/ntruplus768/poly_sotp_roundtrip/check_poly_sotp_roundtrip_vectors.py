#!/usr/bin/env python3

from __future__ import annotations

import argparse
import random
import subprocess
import sys
from pathlib import Path


PAD_BYTES = 192
MSG_BYTES = 96
OUTPUT_BYTES = 1 + MSG_BYTES


class VerificationError(RuntimeError):
    pass


def lcg_bytes(seed: int, length: int) -> bytes:
    state = seed & 0xFFFFFFFF
    result = bytearray(length)
    for index in range(length):
        state = (1664525 * state + 1013904223) & 0xFFFFFFFF
        result[index] = state >> 24
    return bytes(result)


def test_vectors() -> list[tuple[str, bytes, bytes]]:
    vectors = [
        ("zero-zero", bytes(MSG_BYTES), bytes(PAD_BYTES)),
        ("ff-zero", bytes([0xFF]) * MSG_BYTES, bytes(PAD_BYTES)),
        ("zero-ff", bytes(MSG_BYTES), bytes([0xFF]) * PAD_BYTES),
        (
            "ascending",
            bytes(index & 0xFF for index in range(MSG_BYTES)),
            bytes(index & 0xFF for index in range(PAD_BYTES)),
        ),
        (
            "descending",
            bytes(0xFF - (index & 0xFF) for index in range(MSG_BYTES)),
            bytes(0xFF - (index & 0xFF) for index in range(PAD_BYTES)),
        ),
        ("first-bit", b"\x01" + bytes(MSG_BYTES - 1), b"\x01" + bytes(PAD_BYTES - 1)),
        (
            "last-bit",
            bytes(MSG_BYTES - 1) + b"\x80",
            bytes(PAD_BYTES - 1) + b"\x80",
        ),
    ]
    for seed in range(32):
        vectors.append(
            (
                f"lcg-{seed:02d}",
                lcg_bytes(seed, MSG_BYTES),
                lcg_bytes(seed ^ 0xA5A5A5A5, PAD_BYTES),
            ),
        )

    rng = random.Random(768)
    for seed in range(16):
        vectors.append(
            (
                f"random-{seed:02d}",
                bytes(rng.getrandbits(8) for _ in range(MSG_BYTES)),
                bytes(rng.getrandbits(8) for _ in range(PAD_BYTES)),
            ),
        )
    return vectors


def run_driver(binary: Path, msg: bytes, pad: bytes) -> tuple[int, bytes]:
    completed = subprocess.run(
        [str(binary)],
        input=msg + pad,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise VerificationError(
            f"{binary.name} failed with exit {completed.returncode}: {detail}",
        )
    if len(completed.stdout) != OUTPUT_BYTES:
        raise VerificationError(
            f"{binary.name} returned {len(completed.stdout)} bytes; "
            f"expected {OUTPUT_BYTES}",
        )
    return completed.stdout[0], completed.stdout[1:]


def verify(binary: Path, jasmin_binary: Path | None) -> None:
    if not binary.is_file():
        raise VerificationError(f"missing roundtrip driver: {binary}")
    if jasmin_binary is not None and not jasmin_binary.is_file():
        raise VerificationError(f"missing comparison binary: {jasmin_binary}")

    for label, msg, pad in test_vectors():
        msg_before = bytes(msg)
        pad_before = bytes(pad)
        fail, decoded = run_driver(binary, msg, pad)
        if fail != 0:
            raise VerificationError(f"{label}: expected fail=0, got {fail}")
        if decoded != msg:
            raise VerificationError(f"{label}: decoded message mismatch")
        if msg != msg_before or pad != pad_before:
            raise VerificationError(f"{label}: test harness mutated input")

        repeated_fail, repeated_decoded = run_driver(binary, msg, pad)
        if repeated_fail != fail or repeated_decoded != decoded:
            raise VerificationError(f"{label}: driver output changed across runs")

        if jasmin_binary is not None:
            j_fail, j_decoded = run_driver(jasmin_binary, msg, pad)
            if j_fail != fail:
                raise VerificationError(f"{label}: Jasmin fail mismatch")
            if j_decoded != decoded:
                raise VerificationError(f"{label}: Jasmin decoded mismatch")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Check NTRU+768 poly_sotp_encode/decode roundtrip against "
            "production and Jasmin decode"
        ),
    )
    parser.add_argument("--binary", required=True)
    parser.add_argument("--jasmin-binary")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        jasmin_binary = (
            Path(args.jasmin_binary).resolve() if args.jasmin_binary else None
        )
        verify(Path(args.binary).resolve(), jasmin_binary)
    except (OSError, VerificationError) as exc:
        print(f"poly_sotp_roundtrip differential test failed: {exc}", file=sys.stderr)
        return 1

    print(
        "poly_sotp_roundtrip differential test passed "
        f"({len(test_vectors())} vectors)",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
