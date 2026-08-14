#!/usr/bin/env python3

from __future__ import annotations

import argparse
import random
import struct
import subprocess
import sys
from pathlib import Path


BUF_BYTES = 192
MSG_BYTES = 96
COEFF_COUNT = 768
COEFF_BYTES = COEFF_COUNT * 2
INPUT_BYTES = BUF_BYTES + COEFF_BYTES
OUTPUT_BYTES = 1 + MSG_BYTES


class VerificationError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def bit(byte: int, offset: int) -> int:
    return (byte >> offset) & 1


def encode_coeffs(msg: bytes, buf: bytes) -> list[int]:
    coeffs: list[int] = []
    for i in range(MSG_BYTES):
        head = buf[i]
        tail = buf[i + MSG_BYTES]
        for j in range(8):
            coeffs.append((bit(head, j) ^ bit(msg[i], j)) - bit(tail, j))
    require(len(coeffs) == COEFF_COUNT, "oracle built the wrong coefficient count")
    return coeffs


def oracle_decode(coeffs: list[int], buf: bytes) -> tuple[int, bytes]:
    require(len(coeffs) == COEFF_COUNT, "unexpected coefficient count")
    require(len(buf) == BUF_BYTES, "unexpected buffer length")
    output = bytearray(MSG_BYTES)
    fail = 0
    for i in range(MSG_BYTES):
        t1 = buf[i]
        t2 = buf[i + MSG_BYTES]
        acc = 0
        for j in range(8):
            t4 = (t2 & 1) + coeffs[8 * i + j]
            if t4 not in (0, 1):
                fail = 1
            acc ^= ((t4 ^ t1) & 1) << j
            t1 >>= 1
            t2 >>= 1
        output[i] = acc
    if fail:
        return 1, bytes(MSG_BYTES)
    return 0, bytes(output)


def lcg_bytes(seed: int, length: int) -> bytes:
    state = seed & 0xFFFFFFFF
    result = bytearray(length)
    for index in range(length):
        state = (1664525 * state + 1013904223) & 0xFFFFFFFF
        result[index] = state >> 24
    return bytes(result)


def candidate_index(buf: bytes, want_tail_bit: int) -> int:
    for coeff_index in range(COEFF_COUNT):
        tail_byte = buf[MSG_BYTES + coeff_index // 8]
        if bit(tail_byte, coeff_index % 8) == want_tail_bit:
            return coeff_index
    raise VerificationError(f"could not find coefficient with tail bit {want_tail_bit}")


def pack_case(buf: bytes, coeffs: list[int]) -> bytes:
    require(len(buf) == BUF_BYTES, "unexpected buffer length while packing")
    require(len(coeffs) == COEFF_COUNT, "unexpected coefficient count while packing")
    return buf + b"".join(struct.pack("<h", value) for value in coeffs)


def run_driver(binary: Path, payload: bytes) -> tuple[int, bytes]:
    completed = subprocess.run(
        [str(binary)],
        input=payload,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise VerificationError(
            f"{binary.name} failed with exit {completed.returncode}: {detail}",
        )
    require(
        len(completed.stdout) == OUTPUT_BYTES,
        f"{binary.name} returned {len(completed.stdout)} bytes; expected {OUTPUT_BYTES}",
    )
    return completed.stdout[0], completed.stdout[1:]


def test_vectors() -> list[tuple[str, bytes, list[int]]]:
    vectors: list[tuple[str, bytes, list[int]]] = []

    success_cases = [
        ("success-zero", bytes(BUF_BYTES), bytes(MSG_BYTES)),
        ("success-all-ff", bytes([0xFF]) * BUF_BYTES, bytes([0xFF]) * MSG_BYTES),
        (
            "success-alternating",
            bytes(0xAA if index & 1 else 0x55 for index in range(BUF_BYTES)),
            bytes(0x3C if index & 1 else 0xC3 for index in range(MSG_BYTES)),
        ),
        (
            "success-ascending",
            bytes(index & 0xFF for index in range(BUF_BYTES)),
            bytes((3 * index + 1) & 0xFF for index in range(MSG_BYTES)),
        ),
    ]
    for seed in range(32):
        success_cases.append(
            (
                f"success-lcg-{seed:02d}",
                lcg_bytes(seed, BUF_BYTES),
                lcg_bytes(seed ^ 0xA5A5A5A5, MSG_BYTES),
            )
        )

    for label, buf, msg in success_cases:
        vectors.append((label, buf, encode_coeffs(msg, buf)))

    buf_tail_zero = bytes(MSG_BYTES) + bytes(MSG_BYTES)
    coeffs_tail_zero = encode_coeffs(bytes(MSG_BYTES), buf_tail_zero)
    idx_tail_zero = candidate_index(buf_tail_zero, 0)
    coeffs_tail_zero[idx_tail_zero] = -1
    vectors.append(("invalid-minus-one-with-zero-tail-bit", buf_tail_zero, coeffs_tail_zero))

    buf_tail_one = bytes(MSG_BYTES) + bytes([0xFF]) * MSG_BYTES
    coeffs_tail_one = encode_coeffs(bytes(MSG_BYTES), buf_tail_one)
    idx_tail_one = candidate_index(buf_tail_one, 1)
    coeffs_tail_one[idx_tail_one] = 1
    vectors.append(("invalid-plus-one-with-one-tail-bit", buf_tail_one, coeffs_tail_one))

    buf_pos_mag = lcg_bytes(77, BUF_BYTES)
    coeffs_pos_mag = encode_coeffs(lcg_bytes(11, MSG_BYTES), buf_pos_mag)
    coeffs_pos_mag[17] = 2
    vectors.append(("invalid-positive-magnitude", buf_pos_mag, coeffs_pos_mag))

    buf_neg_mag = lcg_bytes(91, BUF_BYTES)
    coeffs_neg_mag = encode_coeffs(lcg_bytes(23, MSG_BYTES), buf_neg_mag)
    coeffs_neg_mag[31] = -2
    vectors.append(("invalid-negative-magnitude", buf_neg_mag, coeffs_neg_mag))

    rng = random.Random(768)
    for seed in range(16):
        buf = bytes(rng.getrandbits(8) for _ in range(BUF_BYTES))
        msg = bytes(rng.getrandbits(8) for _ in range(MSG_BYTES))
        vectors.append((f"success-random-{seed:02d}", buf, encode_coeffs(msg, buf)))

    return vectors


def verify(binary: Path, jasmin_binary: Path | None) -> None:
    require(binary.is_file(), f"missing poly_sotp_decode driver: {binary}")
    if jasmin_binary is not None:
        require(jasmin_binary.is_file(), f"missing comparison binary: {jasmin_binary}")

    for label, buf, coeffs in test_vectors():
        payload = pack_case(buf, coeffs)
        expected_fail, expected_msg = oracle_decode(coeffs, buf)
        fail, msg = run_driver(binary, payload)
        require(fail == expected_fail, f"{label}: fail mismatch {fail} != {expected_fail}")
        require(msg == expected_msg, f"{label}: decoded message mismatch")

        if expected_fail:
            require(msg == bytes(MSG_BYTES), f"{label}: failure path must zero the message")

        if jasmin_binary is not None:
            j_fail, j_msg = run_driver(jasmin_binary, payload)
            require(j_fail == fail, f"{label}: Jasmin fail mismatch")
            require(j_msg == msg, f"{label}: Jasmin message mismatch")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compare NTRU+768 poly_sotp_decode against an independent Python oracle",
    )
    parser.add_argument("--binary", required=True)
    parser.add_argument("--jasmin-binary")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        jasmin_binary = Path(args.jasmin_binary).resolve() if args.jasmin_binary else None
        verify(Path(args.binary).resolve(), jasmin_binary)
    except (OSError, VerificationError) as exc:
        print(f"poly_sotp_decode differential test failed: {exc}", file=sys.stderr)
        return 1

    print(f"poly_sotp_decode differential test passed ({len(test_vectors())} vectors)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
