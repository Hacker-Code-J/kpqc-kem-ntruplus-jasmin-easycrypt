#!/usr/bin/env python3

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


PK_BYTES = 1152
COINS_PREFIX_BYTES = 96
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


def test_vectors() -> list[tuple[str, bytes, bytes, bytes]]:
    vectors = [
        (
            "zero-pk-zero-prefix",
            bytes(PK_BYTES),
            bytes(COINS_PREFIX_BYTES),
            bytes(COINS_PREFIX_BYTES),
        ),
        (
            "ff-pk-ff-prefix",
            bytes([0xFF]) * PK_BYTES,
            bytes([0xFF]) * COINS_PREFIX_BYTES,
            bytes([0xAA]) * COINS_PREFIX_BYTES,
        ),
        (
            "ascending-pk",
            bytes(index & 0xFF for index in range(PK_BYTES)),
            lcg_bytes(77, COINS_PREFIX_BYTES),
            lcg_bytes(78, COINS_PREFIX_BYTES),
        ),
        (
            "descending-pk",
            bytes(0xFF - (index & 0xFF) for index in range(PK_BYTES)),
            lcg_bytes(79, COINS_PREFIX_BYTES),
            lcg_bytes(80, COINS_PREFIX_BYTES),
        ),
    ]
    vectors.extend(
        (
            f"lcg-{seed:02d}",
            lcg_bytes(seed, PK_BYTES),
            lcg_bytes(100 + seed, COINS_PREFIX_BYTES),
            lcg_bytes(200 + seed, COINS_PREFIX_BYTES),
        )
        for seed in range(24)
    )
    return vectors


def run_driver(
    binary: Path,
    pk: bytes,
    encap_prefix: bytes,
    decap_prefix: bytes,
) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        [str(binary)],
        input=pk + encap_prefix + decap_prefix,
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
    for key in ("suffix_hex", "encap_tail_hex", "decap_tail_hex"):
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
        raise VerificationError(
            f"missing encap_hash_f_agreement layout driver: {binary}",
        )

    for label, pk, encap_prefix, decap_prefix in test_vectors():
        pk_before = bytes(pk)
        encap_before = bytes(encap_prefix)
        decap_before = bytes(decap_prefix)
        expected_suffix = hashlib.shake_256(DOMAIN_BYTE + pk).digest(TAIL_BYTES)

        completed = run_driver(binary, pk, encap_prefix, decap_prefix)
        if completed.returncode != 0:
            detail = completed.stderr.decode("utf-8", errors="replace").strip()
            raise VerificationError(
                f"driver failed for {label} with exit "
                f"{completed.returncode}: {detail}",
            )
        payload = decode_output(completed.stdout)
        expected_hex = expected_suffix.hex()
        if payload["suffix_hex"] != expected_hex:
            raise VerificationError(f"suffix hash mismatch for {label}")
        if payload["encap_tail_hex"] != expected_hex:
            raise VerificationError(f"encap tail mismatch for {label}")
        if payload["decap_tail_hex"] != expected_hex:
            raise VerificationError(f"decap tail mismatch for {label}")
        if pk != pk_before:
            raise VerificationError(f"pk mutated for {label}")
        if encap_prefix != encap_before:
            raise VerificationError(f"encap prefix mutated for {label}")
        if decap_prefix != decap_before:
            raise VerificationError(f"decap prefix mutated for {label}")

        repeated = run_driver(binary, pk, encap_prefix, decap_prefix)
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
            "Verify the NTRU+768 encap hash_f agreement among keygen, "
            "encap, and decap layouts"
        ),
    )
    parser.add_argument("--binary", required=True)
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        verify(Path(args.binary).resolve())
    except (OSError, VerificationError) as exc:
        print(f"encap_hash_f agreement layout test failed: {exc}", file=sys.stderr)
        return 1

    print(
        "encap_hash_f agreement layout test passed "
        f"({len(test_vectors())} vectors)",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
