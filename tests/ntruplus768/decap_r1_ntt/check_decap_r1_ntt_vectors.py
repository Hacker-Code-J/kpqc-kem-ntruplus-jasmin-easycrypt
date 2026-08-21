#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import random
import subprocess
import sys
from pathlib import Path


TAIL_BYTES = 192
POLY_BYTES = 1152
POLY_DEGREE = 768


class VerificationError(RuntimeError):
    pass


def cbd1_oracle(tail: bytes) -> list[int]:
    if len(tail) != TAIL_BYTES:
        raise VerificationError(f"tail must be {TAIL_BYTES} bytes")
    coeffs: list[int] = []
    half = TAIL_BYTES // 2
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
    sparse = bytearray(TAIL_BYTES)
    sparse[0] = 0x01
    sparse[half - 1] = 0x80
    sparse[half] = 0x01
    sparse[-1] = 0x80
    return [
        ("all-zero", bytes(TAIL_BYTES)),
        ("all-ff", bytes([0xFF]) * TAIL_BYTES),
        ("all-positive", ff_half + zero_half),
        ("all-negative", zero_half + ff_half),
        ("positive-leading-bit", b"\x01" + bytes(TAIL_BYTES - 1)),
        ("positive-trailing-bit", bytes(half - 1) + b"\x80" + zero_half),
        ("negative-leading-bit", zero_half + b"\x01" + bytes(half - 1)),
        ("negative-trailing-bit", bytes(TAIL_BYTES - 1) + b"\x80"),
        ("alternating-halves", bytes([0x55]) * half + bytes([0xAA]) * half),
        ("inverse-alternating-halves", bytes([0xAA]) * half + bytes([0x55]) * half),
        ("ascending", bytes(index & 0xFF for index in range(TAIL_BYTES))),
        ("descending", bytes(0xFF - (index & 0xFF) for index in range(TAIL_BYTES))),
        ("sparse-edges", bytes(sparse)),
    ]


def randomized_vectors() -> list[tuple[str, bytes]]:
    vectors: list[tuple[str, bytes]] = []
    for seed in range(48):
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


def decode_driver_output(data: bytes) -> dict[str, str]:
    try:
        payload = json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise VerificationError(f"driver returned invalid JSON: {exc}") from exc
    if not isinstance(payload, dict):
        raise VerificationError("driver returned non-object JSON")
    for key in ("target_hex", "oracle_hex"):
        value = payload.get(key)
        if not isinstance(value, str):
            raise VerificationError(f"driver field `{key}` is missing or non-string")
        if len(value) != 2 * POLY_BYTES:
            raise VerificationError(f"driver field `{key}` has wrong hex length {len(value)}")
    sampled_hex = payload.get("sampled_hex")
    if not isinstance(sampled_hex, str):
        raise VerificationError("driver field `sampled_hex` is missing or non-string")
    if len(sampled_hex) != 4 * POLY_DEGREE:
        raise VerificationError(
            f"driver field `sampled_hex` has wrong hex length {len(sampled_hex)}",
        )
    return payload


def encode_coeffs(coeffs: list[int]) -> str:
    return b"".join((value & 0xFFFF).to_bytes(2, "little") for value in coeffs).hex()


def verify(binary: Path) -> None:
    if not binary.is_file():
        raise VerificationError(f"missing decap-r1 driver: {binary}")

    for label, tail in test_vectors():
        expected_sampled = encode_coeffs(cbd1_oracle(tail))

        completed = run_driver(binary, tail)
        if completed.returncode != 0:
            detail = completed.stderr.decode("utf-8", errors="replace").strip()
            raise VerificationError(f"driver failed for {label} with exit {completed.returncode}: {detail}")
        payload = decode_driver_output(completed.stdout)
        if payload["sampled_hex"] != expected_sampled:
            raise VerificationError(f"poly_cbd1/Python mismatch for {label}")
        if payload["target_hex"] != payload["oracle_hex"]:
            raise VerificationError(f"target/oracle mismatch for {label}")

        repeated = run_driver(binary, tail)
        if repeated.returncode != 0:
            detail = repeated.stderr.decode("utf-8", errors="replace").strip()
            raise VerificationError(f"driver repeat failed for {label} with exit {repeated.returncode}: {detail}")
        if repeated.stdout != completed.stdout:
            raise VerificationError(f"driver output changed across repeated runs for {label}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compare decap-r1 cbd1 -> in-place ntt -> tobytes against an independent cbd1 oracle plus verified Jasmin NTT",
    )
    parser.add_argument("--binary", required=True)
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        verify(Path(args.binary).resolve())
    except (OSError, VerificationError) as exc:
        print(f"decap-r1 ntt differential test failed: {exc}", file=sys.stderr)
        return 1

    print(f"decap-r1 ntt differential test passed ({len(test_vectors())} vectors)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
