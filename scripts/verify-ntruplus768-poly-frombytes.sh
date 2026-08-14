#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/poly_frombytes"
PROOF="$PROOF_DIR/NTRUPlus768PolyFromBytesAlgebra.ec"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/poly_frombytes"
DOWNSTREAM_VERIFIER="$REPO_ROOT/scripts/verify-ntruplus768-poly-basemul-invntt.sh"
BASEMUL_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/basemul"
BASEMUL_EXTRACTED="$BASEMUL_PROOF/extracted"
POLY_BASEMUL_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/poly_basemul"
POLY_BASEMUL_EXTRACTED="$POLY_BASEMUL_PROOF/extracted"
POLY_BASEMUL_INVNTT_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/poly_basemul_invntt"
NTT_SCHEDULE_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/ntt_schedule"
NTT_RADIX2_64_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/ntt_radix2_64"
NTT_RADIX2_64_EXTRACTED="$NTT_RADIX2_64_PROOF/extracted"
INVNTT_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt"
INVNTT_EXTRACTED="$INVNTT_PROOF/extracted"
INVNTT_RADIX2_4_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_4"
INVNTT_RADIX2_4_EXTRACTED="$INVNTT_RADIX2_4_PROOF/extracted"
INVNTT_RADIX2_8_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_8"
INVNTT_RADIX2_8_EXTRACTED="$INVNTT_RADIX2_8_PROOF/extracted"
INVNTT_RADIX2_16_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_16"
INVNTT_RADIX2_16_EXTRACTED="$INVNTT_RADIX2_16_PROOF/extracted"
INVNTT_RADIX2_32_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_32"
INVNTT_RADIX2_32_EXTRACTED="$INVNTT_RADIX2_32_PROOF/extracted"
INVNTT_RADIX2_64_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_64"
INVNTT_RADIX2_64_EXTRACTED="$INVNTT_RADIX2_64_PROOF/extracted"
INVNTT_RADIX3_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix3"
INVNTT_RADIX3_EXTRACTED="$INVNTT_RADIX3_PROOF/extracted"
INVNTT_FINAL_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt_final"
INVNTT_FINAL_EXTRACTED="$INVNTT_FINAL_PROOF/extracted"
FORMOSA_ARRAYS="$REPO_ROOT/external/formosa-mlkem/crypto-specs/arrays"
FORMOSA_ECLIB="$REPO_ROOT/external/formosa-mlkem/proof/eclib"
FORMOSA_COMMON="$REPO_ROOT/external/formosa-mlkem/crypto-specs/common"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-poly-frombytes.XXXXXX")
WHY3_PID=
WHY3SERVER_BIN=

cleanup() {
  if [[ -n "$WHY3_PID" ]]; then
    kill "$WHY3_PID" 2>/dev/null || true
    wait "$WHY3_PID" 2>/dev/null || true
  fi
  rm -rf "$WORKDIR"
}
trap cleanup EXIT INT TERM

fail() {
  printf 'FAIL: %s\n' "$1" >&2
  exit 1
}

require_command() {
  command -v "$1" >/dev/null 2>&1 || fail "missing required command: $1"
}

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status_code

  if grep -ERni --include='*.ec' \
    '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
    "$PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "poly_frombytes EasyCrypt proof contains a proof-hole keyword"
  else
    status_code=$?
    [[ $status_code -eq 1 ]] || fail "could not scan the poly_frombytes proof for holes"
  fi
}

compile_easycrypt() {
  local socket="$WORKDIR/w3.sock"
  local server_log="$WORKDIR/why3.log"
  local attempt
  local launch
  local ready=0

  : >"$server_log"
  for ((launch = 1; launch <= 3; ++launch)); do
    rm -f "$socket"
    "$WHY3SERVER_BIN" --socket "$socket" --single-client -j1 \
      >>"$server_log" 2>&1 &
    WHY3_PID=$!

    for ((attempt = 0; attempt < 200; ++attempt)); do
      if [[ -S "$socket" ]]; then
        ready=1
        break
      fi
      sleep 0.05
    done
    [[ $ready -eq 1 ]] && break

    kill "$WHY3_PID" 2>/dev/null || true
    wait "$WHY3_PID" 2>/dev/null || true
    WHY3_PID=
    sleep 0.1
  done

  if [[ $ready -ne 1 ]]; then
    sed -n '1,120p' "$server_log" >&2 || true
    fail "Why3 server did not accept the poly_frombytes proof after three attempts"
  fi

  if ! easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
    -server "$socket" \
    -I "$PROOF_DIR" \
    -I "$BASEMUL_PROOF" \
    -I "$BASEMUL_EXTRACTED" \
    -I "$POLY_BASEMUL_PROOF" \
    -I "$POLY_BASEMUL_EXTRACTED" \
    -I "$POLY_BASEMUL_INVNTT_PROOF" \
    -I "$NTT_SCHEDULE_PROOF" \
    -I "$NTT_RADIX2_64_PROOF" \
    -I "$NTT_RADIX2_64_EXTRACTED" \
    -I "$INVNTT_PROOF" \
    -I "$INVNTT_EXTRACTED" \
    -I "$INVNTT_RADIX2_4_PROOF" \
    -I "$INVNTT_RADIX2_4_EXTRACTED" \
    -I "$INVNTT_RADIX2_8_PROOF" \
    -I "$INVNTT_RADIX2_8_EXTRACTED" \
    -I "$INVNTT_RADIX2_16_PROOF" \
    -I "$INVNTT_RADIX2_16_EXTRACTED" \
    -I "$INVNTT_RADIX2_32_PROOF" \
    -I "$INVNTT_RADIX2_32_EXTRACTED" \
    -I "$INVNTT_RADIX2_64_PROOF" \
    -I "$INVNTT_RADIX2_64_EXTRACTED" \
    -I "$INVNTT_RADIX3_PROOF" \
    -I "$INVNTT_RADIX3_EXTRACTED" \
    -I "$INVNTT_FINAL_PROOF" \
    -I "$INVNTT_FINAL_EXTRACTED" \
    -I "$FORMOSA_ARRAYS" \
    -I "$FORMOSA_ECLIB" \
    -I "$FORMOSA_COMMON" \
    "$PROOF"; then
    kill "$WHY3_PID" 2>/dev/null || true
    wait "$WHY3_PID" 2>/dev/null || true
    WHY3_PID=
    sed -n '1,120p' "$server_log" >&2 || true
    fail "EasyCrypt poly_frombytes range/caller bridge failed"
  fi

  kill "$WHY3_PID" 2>/dev/null || true
  wait "$WHY3_PID" 2>/dev/null || true
  WHY3_PID=
}

main() {
  local easycrypt_bin
  local easycrypt_bindir

  require_command bash
  require_command easycrypt
  require_command grep
  require_command make
  require_command python3
  require_command "${CC:-cc}"

  bash -n "$0"

  easycrypt_bin=$(command -v easycrypt)
  easycrypt_bindir=$(cd -- "$(dirname -- "$easycrypt_bin")" && pwd)
  WHY3SERVER_BIN="$easycrypt_bindir/../lib/why3/why3server"
  [[ -x "$WHY3SERVER_BIN" ]] ||
    fail "missing Why3 server next to the EasyCrypt installation: $WHY3SERVER_BIN"

  [[ -f "$PROOF" ]] || fail "missing poly_frombytes EasyCrypt proof"
  [[ -f "$TEST_DIR/Makefile" ]] || fail "missing poly_frombytes test Makefile"
  [[ -f "$TEST_DIR/check_poly_frombytes.py" ]] || fail "missing authoritative-C checker"
  [[ -f "$TEST_DIR/poly_frombytes_diff.c" ]] || fail "missing C/oracle differential test"
  [[ -x "$DOWNSTREAM_VERIFIER" ]] || fail "missing executable downstream bridge verifier"
  [[ -f "$FORMOSA_ARRAYS/Array1152.ec" ]] ||
    fail "missing Array1152 EasyCrypt dependency"

  reject_proof_holes
  compile_easycrypt

  make -C "$TEST_DIR" OUTDIR="$WORKDIR/test" selfcheck run ubsan
  "$DOWNSTREAM_VERIFIER"

  printf 'PASS: verify-ntruplus768-poly-frombytes.sh syntax check\n'
  printf 'PASS: NTRU+768 poly_frombytes proof-hole scan\n'
  printf 'PASS: NTRU+768 byte-decoder range and poly_basemul->invntt-ready proof\n'
  printf 'PASS: NTRU+768 authoritative C decoder/caller self-check and differential/UBSan tests\n'
  printf 'PASS: NTRU+768 downstream poly_basemul->invntt bridge regression\n'
}

main "$@"
