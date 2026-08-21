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


def case_vectors() -> list[tuple[str, int, bytes, bytes, int]]:
    zero = bytes(POLY_BYTES)
    first = bytearray(zero)
    first[0] = 1
    middle = bytearray(zero)
    middle[POLY_BYTES // 2] = 0x80
    last = bytearray(zero)
    last[-1] = 0xFF
    multi = bytearray(zero)
    for index, value in ((0, 0xAA), (21, 0x11), (400, 0x22), (1151, 0x33)):
        multi[index] = value

    vectors = [
        ("truth-00", 0, zero, zero, 0),
        ("truth-01", 0, zero, bytes(first), 1),
        ("truth-10", 1, zero, zero, 1),
        ("truth-11", 1, zero, bytes(first), 1),
        ("first-mismatch", 0, zero, bytes(first), 1),
        ("middle-mismatch", 0, zero, bytes(middle), 1),
        ("last-mismatch", 0, zero, bytes(last), 1),
        ("multiple-mismatch", 0, zero, bytes(multi), 1),
    ]
    for seed in range(24):
        left = lcg_bytes(seed, POLY_BYTES)
        right = bytearray(left)
        decode_fail = seed & 1
        if seed % 3:
            right[(53 * seed + 7) % POLY_BYTES] ^= 0x5A
            verify_fail = 1
        else:
            verify_fail = 0
        vectors.append((f"lcg-{seed:02d}", decode_fail, left, bytes(right), decode_fail | verify_fail))
    return vectors


def run_driver(binary: Path, decode_fail: int, left: bytes, right: bytes) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        [str(binary)],
        input=bytes([decode_fail]) + left + right,
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
    for key in ("verify_result", "fail_result"):
        value = payload.get(key)
        if not isinstance(value, int):
            raise VerificationError(f"driver field `{key}` is missing or non-int")
    return payload


def verify(binary: Path) -> None:
    if not binary.is_file():
        raise VerificationError(f"missing fail driver: {binary}")

    for label, decode_fail, left, right, expected_fail in case_vectors():
        left_before = bytes(left)
        right_before = bytes(right)
        completed = run_driver(binary, decode_fail, left, right)
        if completed.returncode != 0:
            detail = completed.stderr.decode("utf-8", errors="replace").strip()
            raise VerificationError(f"driver failed for {label} with exit {completed.returncode}: {detail}")
        payload = decode_output(completed.stdout)
        expected_verify = 0 if left == right else 1
        if payload["verify_result"] != expected_verify:
            raise VerificationError(f"verify_result mismatch for {label}: expected {expected_verify}, got {payload['verify_result']}")
        if payload["fail_result"] != expected_fail:
            raise VerificationError(f"fail_result mismatch for {label}: expected {expected_fail}, got {payload['fail_result']}")
        if payload["verify_result"] not in (0, 1) or payload["fail_result"] not in (0, 1):
            raise VerificationError(f"result escaped boolean range for {label}")
        if left != left_before or right != right_before:
            raise VerificationError(f"test harness mutated inputs for {label}")

        repeated = run_driver(binary, decode_fail, left, right)
        if repeated.returncode != 0:
            detail = repeated.stderr.decode("utf-8", errors="replace").strip()
            raise VerificationError(f"driver repeat failed for {label} with exit {repeated.returncode}: {detail}")
        if repeated.stdout != completed.stdout:
            raise VerificationError(f"driver output changed across repeated runs for {label}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compare the NTRU+768 decapsulation fail-flag combination against an independent boolean oracle",
    )
    parser.add_argument("--binary", required=True)
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        verify(Path(args.binary).resolve())
    except (OSError, VerificationError) as exc:
        print(f"decap-fail differential test failed: {exc}", file=sys.stderr)
        return 1

    print(f"decap-fail differential test passed ({len(case_vectors())} vectors)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
