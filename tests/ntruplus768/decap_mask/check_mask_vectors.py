#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path


SS_BYTES = 32


class VerificationError(RuntimeError):
    pass


def lcg_bytes(seed: int, length: int) -> bytes:
    state = seed & 0xFFFFFFFF
    result = bytearray(length)
    for index in range(length):
        state = (1664525 * state + 1013904223) & 0xFFFFFFFF
        result[index] = state >> 24
    return bytes(result)


def test_vectors() -> list[tuple[str, int, bytes]]:
    vectors = [
        ("zero-prefix", 0, bytes(SS_BYTES)),
        ("ff-prefix", 0, bytes([0xFF]) * SS_BYTES),
        ("ascending", 0, bytes(range(SS_BYTES))),
        ("descending", 0, bytes(0xFF - i for i in range(SS_BYTES))),
        ("first-bit", 0, b"\x01" + bytes(SS_BYTES - 1)),
        ("last-bit", 0, bytes(SS_BYTES - 1) + b"\x80"),
        ("mask-zero-zero", 1, bytes(SS_BYTES)),
        ("mask-zero-random", 1, lcg_bytes(77, SS_BYTES)),
    ]
    for seed in range(24):
        vectors.append((f"lcg-copy-{seed:02d}", 0, lcg_bytes(seed, SS_BYTES)))
        vectors.append((f"lcg-zero-{seed:02d}", 1, lcg_bytes(100 + seed, SS_BYTES)))
    return vectors


def run_driver(binary: Path, fail: int, prefix: bytes) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        [str(binary)],
        input=bytes([fail]) + prefix,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def decode_output(data: bytes) -> dict[str, object]:
    try:
        payload = json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise VerificationError(f"driver returned invalid JSON: {exc}") from exc
    if not isinstance(payload, dict):
        raise VerificationError("driver returned non-object JSON")
    if not isinstance(payload.get("return_fail"), int):
        raise VerificationError("driver field `return_fail` is missing or non-int")
    if not isinstance(payload.get("ss_hex"), str):
        raise VerificationError("driver field `ss_hex` is missing or non-string")
    if len(payload["ss_hex"]) != 2 * SS_BYTES:
        raise VerificationError(f"driver field `ss_hex` has wrong length {len(payload['ss_hex'])}")
    return payload


def verify(binary: Path) -> None:
    if not binary.is_file():
        raise VerificationError(f"missing decap-mask driver: {binary}")

    for label, fail, prefix in test_vectors():
        prefix_before = bytes(prefix)
        completed = run_driver(binary, fail, prefix)
        if completed.returncode != 0:
            detail = completed.stderr.decode("utf-8", errors="replace").strip()
            raise VerificationError(f"driver failed for {label} with exit {completed.returncode}: {detail}")
        payload = decode_output(completed.stdout)
        expected = prefix if fail == 0 else bytes(SS_BYTES)
        if payload["ss_hex"] != expected.hex():
            raise VerificationError(f"masked output mismatch for {label}")
        if payload["return_fail"] != fail:
            raise VerificationError(f"return preservation mismatch for {label}: expected {fail}, got {payload['return_fail']}")
        if payload["return_fail"] not in (0, 1):
            raise VerificationError(f"return escaped boolean range for {label}")
        if prefix != prefix_before:
            raise VerificationError(f"test harness mutated input for {label}")

        repeated = run_driver(binary, fail, prefix)
        if repeated.returncode != 0:
            detail = repeated.stderr.decode("utf-8", errors="replace").strip()
            raise VerificationError(f"driver repeat failed for {label} with exit {repeated.returncode}: {detail}")
        if repeated.stdout != completed.stdout:
            raise VerificationError(f"driver output changed across repeated runs for {label}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compare the NTRU+768 post-verify ss mask loop against an independent oracle",
    )
    parser.add_argument("--binary", required=True)
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        verify(Path(args.binary).resolve())
    except (OSError, VerificationError) as exc:
        print(f"decap-mask differential test failed: {exc}", file=sys.stderr)
        return 1

    print(f"decap-mask differential test passed ({len(test_vectors())} vectors)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
