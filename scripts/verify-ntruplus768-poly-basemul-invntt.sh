#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
TEST_DIR="$REPO_ROOT/tests/ntruplus768/poly_basemul"
BRIDGE_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/poly_basemul_invntt"
BRIDGE_PROOF="$BRIDGE_PROOF_DIR/NTRUPlus768PolyBasemulInvNTTAlgebra.ec"
POLY_BASEMUL_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/poly_basemul"
POLY_BASEMUL_EXTRACTED="$POLY_BASEMUL_PROOF/extracted"
BASEMUL_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/basemul"
BASEMUL_EXTRACTED="$BASEMUL_PROOF/extracted"
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
FORMOSA_ECLIB="$REPO_ROOT/external/formosa-mlkem/proof/eclib"
FORMOSA_COMMON="$REPO_ROOT/external/formosa-mlkem/crypto-specs/common"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-poly-basemul-invntt.XXXXXX")
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

require_stage() {
  local proof_dir=$1
  local proof_name=$2
  local extracted_dir=$3
  local label=$4

  [[ -f "$proof_dir/$proof_name" ]] || fail "missing dependent $label proof tree"
  [[ -d "$extracted_dir" ]] || fail "missing dependent $label extraction tree"
}

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status_code

  if grep -ERni --include='*.ec' \
    '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
    "$BRIDGE_PROOF_DIR" \
    "$POLY_BASEMUL_PROOF" \
    "$BASEMUL_PROOF" \
    "$NTT_SCHEDULE_PROOF" \
    "$NTT_RADIX2_64_PROOF" \
    "$INVNTT_PROOF" \
    "$INVNTT_RADIX2_4_PROOF" \
    "$INVNTT_RADIX2_8_PROOF" \
    "$INVNTT_RADIX2_16_PROOF" \
    "$INVNTT_RADIX2_32_PROOF" \
    "$INVNTT_RADIX2_64_PROOF" \
    "$INVNTT_RADIX3_PROOF" \
    "$INVNTT_FINAL_PROOF" \
    >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "EasyCrypt proof trees contain a proof-hole keyword"
  else
    status_code=$?
    [[ $status_code -eq 1 ]] || fail "could not scan the EasyCrypt proof trees for holes"
  fi
}

compile_easycrypt() {
  local proof=$1
  local tag=$2
  local socket="$WORKDIR/w3.sock"
  local server_log="$WORKDIR/why3-$tag.log"
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
    fail "Why3 server did not accept the $tag proof after three attempts"
  fi

  if ! easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
    -server "$socket" \
    -I "$BRIDGE_PROOF_DIR" \
    -I "$POLY_BASEMUL_PROOF" \
    -I "$POLY_BASEMUL_EXTRACTED" \
    -I "$BASEMUL_PROOF" \
    -I "$BASEMUL_EXTRACTED" \
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
    -I "$FORMOSA_ECLIB" \
    -I "$FORMOSA_COMMON" \
    "$proof"; then
    kill "$WHY3_PID" 2>/dev/null || true
    wait "$WHY3_PID" 2>/dev/null || true
    WHY3_PID=
    sed -n '1,120p' "$server_log" >&2 || true
    fail "EasyCrypt $tag proof failed"
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
  require_command jasminc
  require_command make
  require_command "${CC:-cc}"

  bash -n "$0"

  easycrypt_bin=$(command -v easycrypt)
  easycrypt_bindir=$(cd -- "$(dirname -- "$easycrypt_bin")" && pwd)
  WHY3SERVER_BIN="$easycrypt_bindir/../lib/why3/why3server"
  [[ -x "$WHY3SERVER_BIN" ]] ||
    fail "missing Why3 server next to the EasyCrypt installation: $WHY3SERVER_BIN"

  [[ -f "$TEST_DIR/Makefile" ]] || fail "missing poly_basemul test Makefile"
  [[ -f "$TEST_DIR/poly_basemul_diff.c" ]] || fail "missing poly_basemul differential test"
  [[ -d "$BRIDGE_PROOF_DIR" ]] || fail "missing poly_basemul->invntt bridge proof tree"
  [[ -f "$BRIDGE_PROOF" ]] || fail "missing poly_basemul->invntt bridge theory"
  [[ -f "$POLY_BASEMUL_PROOF/NTRUPlus768PolyBasemulProof.ec" ]] ||
    fail "missing poly_basemul word-level proof"
  [[ -f "$POLY_BASEMUL_PROOF/NTRUPlus768PolyBasemulAlgebra.ec" ]] ||
    fail "missing poly_basemul algebra proof"
  [[ -d "$POLY_BASEMUL_EXTRACTED" ]] ||
    fail "missing tracked poly_basemul extraction tree: $POLY_BASEMUL_EXTRACTED"
  [[ -f "$BASEMUL_PROOF/NTRUPlus768BasemulAlgebra.ec" ]] ||
    fail "missing dependent basemul proof tree"
  [[ -d "$BASEMUL_EXTRACTED" ]] || fail "missing dependent basemul extraction tree"
  [[ -f "$NTT_SCHEDULE_PROOF/NTRUPlus768NTTSchedule.ec" ]] ||
    fail "missing dependent NTT schedule proof tree"
  [[ -f "$NTT_RADIX2_64_PROOF/NTRUPlus768NTTRadix2_64Proof.ec" ]] ||
    fail "missing dependent forward radix-2 step64 word-level proof"
  [[ -f "$INVNTT_PROOF/NTRUPlus768InvNTTProof.ec" ]] ||
    fail "missing composed inverse NTT word-level proof"
  [[ -f "$INVNTT_PROOF/NTRUPlus768InvNTTAlgebra.ec" ]] ||
    fail "missing composed inverse NTT algebra proof"
  [[ -d "$INVNTT_EXTRACTED" ]] ||
    fail "missing composed inverse NTT extraction tree: $INVNTT_EXTRACTED"
  [[ -f "$FORMOSA_ECLIB/W16extra.ec" ]] ||
    fail "Formosa proof dependency is missing; initialize recursive submodules"
  [[ -f "$FORMOSA_COMMON/JWord_extra.ec" ]] ||
    fail "Formosa crypto-specs dependency is missing; initialize recursive submodules"

  require_stage "$NTT_RADIX2_64_PROOF" \
    NTRUPlus768NTTRadix2_64Algebra.ec "$NTT_RADIX2_64_EXTRACTED" \
    "forward radix-2 step64"
  require_stage "$INVNTT_RADIX2_4_PROOF" \
    NTRUPlus768InvNTTRadix2_4Algebra.ec "$INVNTT_RADIX2_4_EXTRACTED" \
    "inverse radix-2 step4"
  require_stage "$INVNTT_RADIX2_8_PROOF" \
    NTRUPlus768InvNTTRadix2_8Algebra.ec "$INVNTT_RADIX2_8_EXTRACTED" \
    "inverse radix-2 step8"
  require_stage "$INVNTT_RADIX2_16_PROOF" \
    NTRUPlus768InvNTTRadix2_16Algebra.ec "$INVNTT_RADIX2_16_EXTRACTED" \
    "inverse radix-2 step16"
  require_stage "$INVNTT_RADIX2_32_PROOF" \
    NTRUPlus768InvNTTRadix2_32Algebra.ec "$INVNTT_RADIX2_32_EXTRACTED" \
    "inverse radix-2 step32"
  require_stage "$INVNTT_RADIX2_64_PROOF" \
    NTRUPlus768InvNTTRadix2_64Algebra.ec "$INVNTT_RADIX2_64_EXTRACTED" \
    "inverse radix-2 step64"
  require_stage "$INVNTT_RADIX3_PROOF" \
    NTRUPlus768InvNTTRadix3Algebra.ec "$INVNTT_RADIX3_EXTRACTED" \
    "inverse radix-3"
  require_stage "$INVNTT_FINAL_PROOF" \
    NTRUPlus768InvNTTFinalAlgebra.ec "$INVNTT_FINAL_EXTRACTED" \
    "inverse final"

  reject_proof_holes
  compile_easycrypt "$BRIDGE_PROOF" poly-basemul-invntt-bridge

  make -C "$TEST_DIR" OUTDIR="$WORKDIR/test" run ubsan

  printf 'PASS: verify-ntruplus768-poly-basemul-invntt.sh syntax check\n'
  printf 'PASS: NTRU+768 poly_basemul->invntt bridge proof-hole scan\n'
  printf 'PASS: NTRU+768 poly_basemul->invntt EasyCrypt range/algebra bridge\n'
  printf 'PASS: NTRU+768 poly_basemul signed12/qrange differential and UBSan tests\n'
}

main "$@"
