#!/usr/bin/env python3

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


PK_BYTES = 1152
MSG_BYTES = 128
TAIL_OFFSET = 96
TAIL_BYTES = 32
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


def test_vectors() -> list[tuple[str, bytes, bytes]]:
    vectors = [
        ("zero-pk-zero-msg", bytes(PK_BYTES), bytes(MSG_BYTES)),
        ("ff-pk-ff-msg", bytes([0xFF]) * PK_BYTES, bytes([0xFF]) * MSG_BYTES),
        (
            "ascending-pk",
            bytes(index & 0xFF for index in range(PK_BYTES)),
            lcg_bytes(77, MSG_BYTES),
        ),
        (
            "descending-pk",
            bytes(0xFF - (index & 0xFF) for index in range(PK_BYTES)),
            lcg_bytes(78, MSG_BYTES),
        ),
    ]
    vectors.extend(
        (
            f"lcg-{seed:02d}",
            lcg_bytes(seed, PK_BYTES),
            lcg_bytes(100 + seed, MSG_BYTES),
        )
        for seed in range(24)
    )
    return vectors


def run_driver(
    binary: Path,
    pk: bytes,
    msg: bytes,
) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        [str(binary)],
        input=pk + msg,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def decode_output(data: bytes) -> dict[str, str]:
    try:
        payload = json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise VerificationError(f"driver returned invalid JSON: {exc}") from exc
    if not isinstance(payload, dict):
        raise VerificationError("driver returned non-object JSON")
    for key in ("suffix_hex", "msg_tail_hex"):
        value = payload.get(key)
        if not isinstance(value, str):
            raise VerificationError(f"driver field `{key}` is missing or non-string")
        if len(value) != 2 * TAIL_BYTES:
            raise VerificationError(
                f"driver field `{key}` has wrong hex length {len(value)}",
            )
    return payload


def verify(binary: Path) -> None:
    if not binary.is_file():
        raise VerificationError(f"missing keygen_hash_f layout driver: {binary}")

    for label, pk, msg in test_vectors():
        pk_before = bytes(pk)
        msg_before = bytes(msg)
        expected_suffix = hashlib.shake_256(DOMAIN_BYTE + pk).digest(TAIL_BYTES)

        completed = run_driver(binary, pk, msg)
        if completed.returncode != 0:
            detail = completed.stderr.decode("utf-8", errors="replace").strip()
            raise VerificationError(
                f"driver failed for {label} with exit "
                f"{completed.returncode}: {detail}",
            )
        payload = decode_output(completed.stdout)
        if payload["suffix_hex"] != expected_suffix.hex():
            raise VerificationError(f"suffix hash mismatch for {label}")
        if payload["msg_tail_hex"] != expected_suffix.hex():
            raise VerificationError(f"msg tail copy mismatch for {label}")
        if pk != pk_before or msg != msg_before:
            raise VerificationError(f"test harness mutated inputs for {label}")

        repeated = run_driver(binary, pk, msg)
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
            "Verify the NTRU+768 hash_f secret-key suffix layout and "
            "decap copy seam"
        ),
    )
    parser.add_argument("--binary", required=True)
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        verify(Path(args.binary).resolve())
    except (OSError, VerificationError) as exc:
        print(f"keygen_hash_f layout test failed: {exc}", file=sys.stderr)
        return 1

    print(f"keygen_hash_f layout test passed ({len(test_vectors())} vectors)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
