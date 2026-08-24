#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path


POLY_BYTES = 1152
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


def case_vectors() -> list[tuple[str, int, bytes, bytes, bytes]]:
    zero_poly = bytes(POLY_BYTES)
    first = bytearray(zero_poly)
    first[0] = 1
    middle = bytearray(zero_poly)
    middle[POLY_BYTES // 2] = 0x80
    last = bytearray(zero_poly)
    last[-1] = 0xFF
    multi = bytearray(zero_poly)
    for index, value in ((0, 0xAA), (11, 0x11), (511, 0x22), (900, 0x33), (1151, 0x44)):
        multi[index] = value

    vectors = [
        ("truth-00", 0, bytes(range(SS_BYTES)), zero_poly, zero_poly),
        ("truth-01", 0, bytes(reversed(range(SS_BYTES))), zero_poly, bytes(first)),
        ("truth-10", 1, lcg_bytes(7, SS_BYTES), zero_poly, zero_poly),
        ("truth-11", 1, lcg_bytes(8, SS_BYTES), zero_poly, bytes(first)),
        ("first-mismatch", 0, lcg_bytes(9, SS_BYTES), zero_poly, bytes(first)),
        ("middle-mismatch", 0, lcg_bytes(10, SS_BYTES), zero_poly, bytes(middle)),
        ("last-mismatch", 0, lcg_bytes(11, SS_BYTES), zero_poly, bytes(last)),
        ("multiple-mismatch", 0, lcg_bytes(12, SS_BYTES), zero_poly, bytes(multi)),
    ]

    for seed in range(24):
        candidate = lcg_bytes(100 + seed, SS_BYTES)
        left = lcg_bytes(seed, POLY_BYTES)
        right = bytearray(left)
        if seed % 3:
            right[(41 * seed + 5) % POLY_BYTES] ^= 0x5A
        decode_fail = seed & 1
        vectors.append((f"lcg-{seed:02d}", decode_fail, candidate, left, bytes(right)))

    return vectors


def run_driver(binary: Path, decode_fail: int, candidate: bytes, left: bytes, right: bytes) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        [str(binary)],
        input=bytes([decode_fail]) + candidate + left + right,
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
    for key in ("verify_result", "return_fail"):
        if not isinstance(payload.get(key), int):
            raise VerificationError(f"driver field `{key}` is missing or non-int")
    if not isinstance(payload.get("ss_hex"), str):
        raise VerificationError("driver field `ss_hex` is missing or non-string")
    if len(payload["ss_hex"]) != 2 * SS_BYTES:
        raise VerificationError(f"driver field `ss_hex` has wrong length {len(payload['ss_hex'])}")
    return payload


def verify(binary: Path) -> None:
    if not binary.is_file():
        raise VerificationError(f"missing decap-terminal driver: {binary}")

    for label, decode_fail, candidate, left, right in case_vectors():
        candidate_before = bytes(candidate)
        left_before = bytes(left)
        right_before = bytes(right)

        completed = run_driver(binary, decode_fail, candidate, left, right)
        if completed.returncode != 0:
            detail = completed.stderr.decode("utf-8", errors="replace").strip()
            raise VerificationError(f"driver failed for {label} with exit {completed.returncode}: {detail}")

        payload = decode_output(completed.stdout)
        expected_verify = 0 if left == right else 1
        expected_fail = decode_fail | expected_verify
        expected_ss = candidate if expected_fail == 0 else bytes(SS_BYTES)

        if payload["verify_result"] != expected_verify:
            raise VerificationError(f"verify_result mismatch for {label}: expected {expected_verify}, got {payload['verify_result']}")
        if payload["return_fail"] != expected_fail:
            raise VerificationError(f"return_fail mismatch for {label}: expected {expected_fail}, got {payload['return_fail']}")
        if payload["ss_hex"] != expected_ss.hex():
            raise VerificationError(f"masked shared-secret mismatch for {label}")
        if payload["verify_result"] not in (0, 1) or payload["return_fail"] not in (0, 1):
            raise VerificationError(f"result escaped boolean range for {label}")
        if candidate != candidate_before or left != left_before or right != right_before:
            raise VerificationError(f"test harness mutated inputs for {label}")

        repeated = run_driver(binary, decode_fail, candidate, left, right)
        if repeated.returncode != 0:
            detail = repeated.stderr.decode("utf-8", errors="replace").strip()
            raise VerificationError(f"driver repeat failed for {label} with exit {repeated.returncode}: {detail}")
        if repeated.stdout != completed.stdout:
            raise VerificationError(f"driver output changed across repeated runs for {label}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Integration oracle for the NTRU+768 terminal verify/fail/mask seam",
    )
    parser.add_argument("--binary", required=True)
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        verify(Path(args.binary).resolve())
    except (OSError, VerificationError) as exc:
        print(f"decap-terminal differential test failed: {exc}", file=sys.stderr)
        return 1

    print(f"decap-terminal differential test passed ({len(case_vectors())} vectors)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
