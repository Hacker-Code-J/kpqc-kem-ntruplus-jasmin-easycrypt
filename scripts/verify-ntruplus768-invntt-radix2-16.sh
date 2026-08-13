#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
JASMIN_SOURCE="$REPO_ROOT/ntruplus/jasmin/768/ref/invntt_radix2_16.jazz"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/invntt_radix2_16"
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_16"
TRACKED_EXTRACTED="$PROOF_DIR/extracted"
BASEMUL_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/basemul"
BASEMUL_EXTRACTED="$BASEMUL_PROOF/extracted"
RADIX2_64_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/ntt_radix2_64"
RADIX2_64_EXTRACTED="$RADIX2_64_PROOF/extracted"
NTT_SCHEDULE_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/ntt_schedule"
INVNTT_RADIX2_8_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_8"
INVNTT_RADIX2_8_EXTRACTED="$INVNTT_RADIX2_8_PROOF/extracted"
INVNTT_RADIX2_4_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_4"
INVNTT_RADIX2_4_EXTRACTED="$INVNTT_RADIX2_4_PROOF/extracted"
FORMOSA_ECLIB="$REPO_ROOT/external/formosa-mlkem/proof/eclib"
FORMOSA_COMMON="$REPO_ROOT/external/formosa-mlkem/crypto-specs/common"
SLICE=jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-invntt-radix2-16.XXXXXX")
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
    "$PROOF_DIR" "$BASEMUL_PROOF" "$RADIX2_64_PROOF" "$NTT_SCHEDULE_PROOF" \
    "$INVNTT_RADIX2_8_PROOF" "$INVNTT_RADIX2_4_PROOF" \
    >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "EasyCrypt proof trees contain a proof-hole keyword"
  else
    status_code=$?
    [[ $status_code -eq 1 ]] || fail "could not scan the EasyCrypt proof trees for holes"
  fi
}

start_why3_server() {
  local socket=$1
  local server_log=$2
  local attempt
  local launch
  local ready=0

  : >"$server_log"
  for ((launch = 1; launch <= 3; ++launch)); do
    rm -f "$socket"
    "$WHY3SERVER_BIN" --socket "$socket" --single-client -j1 >>"$server_log" 2>&1 &
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
    fail "Why3 server did not become ready after three attempts"
  fi
}

compile_easycrypt() {
  local proof=$1
  local tag=$2
  local socket="$WORKDIR/why3-$tag.sock"
  local server_log="$WORKDIR/why3-$tag.log"

  start_why3_server "$socket" "$server_log"

  if ! easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
    -server "$socket" \
    -I "$GENERATED_DIR" \
    -I "$PROOF_DIR" \
    -I "$BASEMUL_PROOF" \
    -I "$BASEMUL_EXTRACTED" \
    -I "$RADIX2_64_PROOF" \
    -I "$RADIX2_64_EXTRACTED" \
    -I "$NTT_SCHEDULE_PROOF" \
    -I "$INVNTT_RADIX2_8_PROOF" \
    -I "$INVNTT_RADIX2_8_EXTRACTED" \
    -I "$INVNTT_RADIX2_4_PROOF" \
    -I "$INVNTT_RADIX2_4_EXTRACTED" \
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

compare_extraction() {
  local generated_dir=$1
  local expected_list="$WORKDIR/expected-extracted.txt"
  local generated_list="$WORKDIR/generated-extracted.txt"
  local name

  printf '%s\n' \
    Array768.ec \
    NTRUPlus768InvNTTRadix2_16.ec \
    WArray1536.ec >"$expected_list"
  find "$generated_dir" -maxdepth 1 -type f -name '*.ec' -printf '%f\n' | sort >"$generated_list"

  if ! cmp -s "$expected_list" "$generated_list"; then
    diff -u "$expected_list" "$generated_list" >&2 || true
    fail "generated extraction file set does not match expected inverse radix-2 step16 extraction"
  fi

  while IFS= read -r name; do
    if ! cmp -s "$generated_dir/$name" "$TRACKED_EXTRACTED/$name"; then
      diff -u "$TRACKED_EXTRACTED/$name" "$generated_dir/$name" | sed -n '1,120p' >&2 || true
      fail "tracked inverse radix-2 step16 EasyCrypt extraction is stale: $name"
    fi
  done <"$expected_list"
}

main() {
  local easycrypt_bin
  local easycrypt_bindir
  local generated_dir="$WORKDIR/extracted"
  local asm_dir="$WORKDIR/asm"

  require_command bash
  require_command easycrypt
  require_command grep
  require_command jasmin-ct
  require_command jasmin2ec
  require_command jasminc
  require_command make
  require_command python3
  require_command "${CC:-cc}"

  easycrypt_bin=$(command -v easycrypt)
  easycrypt_bindir=$(cd -- "$(dirname -- "$easycrypt_bin")" && pwd)
  WHY3SERVER_BIN="$easycrypt_bindir/../lib/why3/why3server"
  [[ -x "$WHY3SERVER_BIN" ]] ||
    fail "missing Why3 server next to the EasyCrypt installation: $WHY3SERVER_BIN"

  [[ -f "$JASMIN_SOURCE" ]] || fail "missing Jasmin source: $JASMIN_SOURCE"
  [[ -d "$TEST_DIR" ]] || fail "missing inverse radix-2 step16 test tree: $TEST_DIR"
  [[ -f "$PROOF_DIR/NTRUPlus768InvNTTRadix2_16Proof.ec" ]] ||
    fail "missing inverse radix-2 step16 word-level proof"
  [[ -f "$PROOF_DIR/NTRUPlus768InvNTTRadix2_16Algebra.ec" ]] ||
    fail "missing inverse radix-2 step16 algebra proof"
  [[ -d "$TRACKED_EXTRACTED" ]] ||
    fail "missing tracked inverse radix-2 step16 extraction tree: $TRACKED_EXTRACTED"
  [[ -f "$FORMOSA_ECLIB/W16extra.ec" ]] ||
    fail "Formosa proof dependency is missing; initialize recursive submodules"
  [[ -f "$FORMOSA_COMMON/JWord_extra.ec" ]] ||
    fail "Formosa crypto-specs dependency is missing; initialize recursive submodules"
  [[ -f "$BASEMUL_PROOF/NTRUPlus768BasemulAlgebra.ec" ]] ||
    fail "missing dependent basemul proof tree"
  [[ -f "$RADIX2_64_PROOF/NTRUPlus768NTTRadix2_64Algebra.ec" ]] ||
    fail "missing dependent radix-2 step64 algebra tree"
  [[ -d "$RADIX2_64_EXTRACTED" ]] ||
    fail "missing dependent radix-2 step64 extraction tree"
  [[ -f "$NTT_SCHEDULE_PROOF/NTRUPlus768NTTSchedule.ec" ]] ||
    fail "missing dependent NTT schedule proof tree"
  [[ -f "$INVNTT_RADIX2_8_PROOF/NTRUPlus768InvNTTRadix2_8Algebra.ec" ]] ||
    fail "missing dependent inverse radix-2 step8 algebra proof tree"
  [[ -d "$INVNTT_RADIX2_8_EXTRACTED" ]] ||
    fail "missing dependent inverse radix-2 step8 extraction tree"
  [[ -f "$INVNTT_RADIX2_4_PROOF/NTRUPlus768InvNTTRadix2_4Algebra.ec" ]] ||
    fail "missing dependent inverse radix-2 step4 algebra proof tree"
  [[ -d "$INVNTT_RADIX2_4_EXTRACTED" ]] ||
    fail "missing dependent inverse radix-2 step4 extraction tree"

  bash -n "$0"
  mkdir -p "$asm_dir" "$generated_dir"
  GENERATED_DIR=$generated_dir

  jasmin2ec "$JASMIN_SOURCE" --array-model=old \
    -o "$generated_dir/NTRUPlus768InvNTTRadix2_16.ec" -f "$SLICE"
  compare_extraction "$generated_dir"
  reject_proof_holes

  compile_easycrypt "$PROOF_DIR/NTRUPlus768InvNTTRadix2_16Proof.ec" word-level
  compile_easycrypt "$PROOF_DIR/NTRUPlus768InvNTTRadix2_16Algebra.ec" algebra

  jasminc -arch x86-64 -call-conv linux -system linux \
    -slice "$SLICE" -o "$asm_dir/invntt_radix2_16.s" "$JASMIN_SOURCE"
  jasminc -arch x86-64 -call-conv linux -system linux -checksafety \
    -slice "$SLICE" -o "$asm_dir/invntt_radix2_16-safety.s" "$JASMIN_SOURCE"
  jasmin-ct --slice="$SLICE" "$JASMIN_SOURCE"
  jasmin-ct --slice="$SLICE" --sct "$JASMIN_SOURCE"

  make -C "$TEST_DIR" OUTDIR="$WORKDIR/test" selfcheck run ubsan

  printf 'PASS: verify-ntruplus768-invntt-radix2-16.sh syntax check\n'
  printf 'PASS: NTRU+768 inverse radix-2 step16 C/Jasmin coupling and checker self-check\n'
  printf 'PASS: NTRU+768 inverse radix-2 step16 Jasmin build, safety, CT, and SCT checks\n'
  printf 'PASS: NTRU+768 inverse radix-2 step16 differential and UBSan tests\n'
  printf 'PASS: NTRU+768 inverse radix-2 step16 fresh extraction matches tracked EasyCrypt model\n'
  printf 'PASS: NTRU+768 inverse radix-2 step16 EasyCrypt word-level functional proof\n'
  printf 'PASS: NTRU+768 inverse radix-2 step16 reverse-schedule, range, and algebra bridge\n'
}

main "$@"
