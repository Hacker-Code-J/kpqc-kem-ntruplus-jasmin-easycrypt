#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_ROOT="$REPO_ROOT/ntruplus/proof/768/ref"
PROOF_DIR="$PROOF_ROOT/decap_mask"
MASK_PROOF="$PROOF_DIR/NTRUPlus768DecapMaskProof.ec"
BRIDGE_PROOF="$PROOF_DIR/NTRUPlus768DecapMaskBridge.ec"
SOURCE_BRIDGE="$PROOF_DIR/NTRUPlus768DecapMaskSourceBridge.ec"
HASH_DIR="$PROOF_ROOT/decap_hash_h"
HASH_BRIDGE="$HASH_DIR/NTRUPlus768DecapHashHBridge.ec"
FAIL_DIR="$PROOF_ROOT/decap_fail"
FAIL_PROOF="$FAIL_DIR/NTRUPlus768DecapFailProof.ec"
FAIL_BRIDGE="$FAIL_DIR/NTRUPlus768DecapFailBridge.ec"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/decap_mask"
HASH_TEST_DIR="$REPO_ROOT/tests/ntruplus768/decap_hash_h"
NTRU_ROOT="$REPO_ROOT/NTRU+/NTRU+768"
PARAMS_SOURCE="$NTRU_ROOT/params.h"
KEM_SOURCE="$NTRU_ROOT/kem.c"
FAIL_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-decap-fail.sh"
FULL_HASH_H=${NTRUPLUS768_FULL_HASH_H:-0}

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-decap-mask.XXXXXX")
WHY3_PID=
WHY3SERVER_BIN=
WHY3_SOCKET="$WORKDIR/why3.sock"
CC_BIN=

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

require_file() {
  [[ -f "$1" ]] || fail "missing required file: $1"
}

resolve_compiler() {
  if [[ -n "${CC:-}" ]]; then
    command -v "$CC" >/dev/null 2>&1 ||
      fail "configured C compiler is unavailable: $CC"
    CC_BIN=$(command -v "$CC")
  elif command -v gcc >/dev/null 2>&1; then
    CC_BIN=$(command -v gcc)
  elif command -v cc >/dev/null 2>&1; then
    CC_BIN=$(command -v cc)
  else
    fail "missing required C compiler: set CC or install gcc/cc"
  fi
}

require_lemma() {
  local file=$1
  local lemma=$2

  grep -Eq "^lemma[[:space:]]+$lemma([[:space:](]|$)" "$file" ||
    fail "missing required EasyCrypt lemma: $lemma"
}

require_pattern() {
  local file=$1
  local pattern=$2
  local label=$3

  grep -Eq "$pattern" "$file" || fail "missing required $label"
}

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
      '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
      "$PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "decap mask theories contain a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan decap mask theories for proof holes"
  fi

  if grep -Eni \
      '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
      "$HASH_BRIDGE" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "hash_h bridge contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan hash_h bridge for proof holes"
  fi
}

start_why3_server() {
  local server_log=$1
  local attempt
  local launch
  local ready=0

  : >"$server_log"
  for ((launch = 1; launch <= 3; ++launch)); do
    rm -f "$WHY3_SOCKET"
    "$WHY3SERVER_BIN" --socket "$WHY3_SOCKET" --single-client -j1 \
      >>"$server_log" 2>&1 &
    WHY3_PID=$!

    for ((attempt = 0; attempt < 200; ++attempt)); do
      if [[ -S "$WHY3_SOCKET" ]]; then
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

  [[ $ready -eq 1 ]]
}

stop_why3_server() {
  if [[ -n "$WHY3_PID" ]]; then
    kill "$WHY3_PID" 2>/dev/null || true
    wait "$WHY3_PID" 2>/dev/null || true
    WHY3_PID=
  fi
}

compile_easycrypt_target() {
  local workdir=$1
  local proof=$2
  local label=$3
  local server_log="$WORKDIR/$(basename -- "$proof").why3.log"

  if start_why3_server "$server_log"; then
    if ! (
      cd "$workdir"
      easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
        -server "$WHY3_SOCKET" "$proof"
    ); then
      sed -n '1,120p' "$server_log" >&2 || true
      fail "EasyCrypt $label failed"
    fi
  else
    if ! (
      cd "$workdir"
      easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 "$proof"
    ); then
      sed -n '1,120p' "$server_log" >&2 || true
      fail "EasyCrypt $label failed without Why3 server fallback"
    fi
  fi
  stop_why3_server
}

main() {
  local easycrypt_bin
  local easycrypt_bindir

  require_command bash
  require_command easycrypt
  require_command grep
  require_command make
  require_command python3
  resolve_compiler

  easycrypt_bin=$(command -v easycrypt)
  easycrypt_bindir=$(cd -- "$(dirname -- "$easycrypt_bin")" && pwd)
  WHY3SERVER_BIN="$easycrypt_bindir/../lib/why3/why3server"
  [[ -x "$WHY3SERVER_BIN" ]] ||
    fail "missing Why3 server next to the EasyCrypt installation: $WHY3SERVER_BIN"

  require_file "$MASK_PROOF"
  require_file "$BRIDGE_PROOF"
  require_file "$SOURCE_BRIDGE"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$PROOF_DIR/Makefile"
  require_file "$HASH_BRIDGE"
  require_file "$HASH_DIR/easycrypt.project"
  require_file "$FAIL_PROOF"
  require_file "$FAIL_BRIDGE"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_decap_mask.py"
  require_file "$TEST_DIR/check_mask_vectors.py"
  require_file "$TEST_DIR/mask_driver.c"
  require_file "$HASH_TEST_DIR/Makefile"
  require_file "$HASH_TEST_DIR/check_decap_hash_h.py"
  require_file "$HASH_TEST_DIR/check_hash_h_vectors.py"
  require_file "$HASH_TEST_DIR/hash_h_driver.c"
  require_file "$PARAMS_SOURCE"
  require_file "$KEM_SOURCE"
  require_file "$FAIL_VERIFIER"
  [[ "$FULL_HASH_H" == 0 || "$FULL_HASH_H" == 1 ]] ||
    fail "NTRUPLUS768_FULL_HASH_H must be 0 or 1"

  require_pattern "$MASK_PROOF" \
    'invw[[:space:]]*\(-[[:space:]]*MOVSX_u32s8[[:space:]]+failv\)' \
    'signed int8-to-W32 promotion and complement mask'
  require_pattern "$MASK_PROOF" \
    'zeroextu32[[:space:]]+src[[:space:]]*`&`[[:space:]]*decap_mask_word32' \
    'promoted uint8 source AND mask'
  require_pattern "$BRIDGE_PROOF" \
    'ss_source_frontier[[:space:]]*:[[:space:]]*W8\.t[[:space:]]+Array32\.t[[:space:]]*->[[:space:]]*bool' \
    'typed hash_h shared-secret source frontier'
  require_pattern "$KEM_SOURCE" \
    'ss\[i\][[:space:]]*=[[:space:]]*buf3\[i\][[:space:]]*&[[:space:]]*~\(-fail\);' \
    'shared-secret mask assignment'

  require_lemma "$MASK_PROOF" movsx_u32s8_fail_false
  require_lemma "$MASK_PROOF" movsx_u32s8_fail_true
  require_lemma "$MASK_PROOF" decap_mask_word32_fail_false
  require_lemma "$MASK_PROOF" decap_mask_word32_fail_true
  require_lemma "$MASK_PROOF" decap_masked_byte_copy
  require_lemma "$MASK_PROOF" decap_masked_byte_zero
  require_lemma "$MASK_PROOF" decap_mask_ss_copy
  require_lemma "$MASK_PROOF" decap_mask_ss_zero
  require_lemma "$MASK_PROOF" decap_mask_ss_select
  require_lemma "$MASK_PROOF" decap_mask_functional
  require_lemma "$MASK_PROOF" decap_mask_selection_h
  require_lemma "$MASK_PROOF" decap_mask_ll
  require_lemma "$MASK_PROOF" decap_mask_correct
  require_lemma "$BRIDGE_PROOF" decap_mask_value_flow_intro
  require_lemma "$BRIDGE_PROOF" decap_mask_value_flow_from_hash_frontier
  require_lemma "$BRIDGE_PROOF" decap_mask_value_flow_fail_range
  require_lemma "$BRIDGE_PROOF" decap_mask_value_flow_fail_zero_iff
  require_lemma "$BRIDGE_PROOF" decap_mask_value_flow_fail_one_iff
  require_lemma "$BRIDGE_PROOF" decap_mask_value_flow_selection
  require_lemma "$BRIDGE_PROOF" decap_mask_value_flow_copy
  require_lemma "$BRIDGE_PROOF" decap_mask_value_flow_zero
  require_lemma "$BRIDGE_PROOF" decap_mask_value_flow_byte_selection
  require_lemma "$BRIDGE_PROOF" decap_mask_procedure_functional
  require_lemma "$BRIDGE_PROOF" decap_mask_procedure_correct
  require_lemma "$SOURCE_BRIDGE" decap_mask_ss_source_byte
  require_lemma "$SOURCE_BRIDGE" decap_mask_source_value_flow_intro
  require_lemma "$SOURCE_BRIDGE" decap_mask_source_value_flow_exact
  require_lemma "$SOURCE_BRIDGE" decap_mask_source_value_flow_byte
  require_lemma "$SOURCE_BRIDGE" projected_ss_source_frontier_intro
  require_lemma "$HASH_BRIDGE" decap_hash_h_value_flow_ss_source
  require_lemma "$FAIL_PROOF" decap_fail_spec_range
  require_lemma "$FAIL_BRIDGE" decap_fail_value_flow_result_range
  require_lemma "$FAIL_BRIDGE" decap_fail_value_flow_combined_fail

  bash -n "$0"
  reject_proof_holes
  compile_easycrypt_target "$PROOF_DIR" "$MASK_PROOF" \
    "standalone shared-secret mask proof"
  compile_easycrypt_target "$PROOF_DIR" "$BRIDGE_PROOF" \
    "typed decapsulation mask bridge"
  compile_easycrypt_target "$PROOF_DIR" "$SOURCE_BRIDGE" \
    "lightweight hash_h shared-secret source projection"
  make -C "$TEST_DIR" CC="$CC_BIN" OUTDIR="$WORKDIR/mask-test" all
  if [[ "$FULL_HASH_H" == 1 ]]; then
    compile_easycrypt_target "$HASH_DIR" "$HASH_BRIDGE" \
      "full hash_h shared-secret projection frontier"
  fi
  make -C "$HASH_TEST_DIR" CC="$CC_BIN" OUTDIR="$WORKDIR/hash-test" all
  "$FAIL_VERIFIER"

  printf 'PASS: NTRU+768 W32 shadow of int8_t ~(-fail) masking for normalized 0/1 inputs\n'
  printf 'PASS: NTRU+768 32-byte shared secret copies hash_h prefix on success and zeroes on failure\n'
  printf 'PASS: NTRU+768 typed hash_h-source and final-failure frontier composition\n'
  printf 'PASS: NTRU+768 exact verify -> mask loop -> return fail source seam and mutation checks\n'
  printf 'PASS: NTRU+768 56-vector target-ABI differential and UBSan checks\n'
  printf 'PASS: NTRU+768 lightweight hash_h projection and decap-fail predecessor regressions\n'
  if [[ "$FULL_HASH_H" == 0 ]]; then
    printf '%s\n' \
      'INFO: set NTRUPLUS768_FULL_HASH_H=1 to recompile the full hash_h/Keccak bridge in this run'
  fi
  printf '%s\n' \
    'SCOPE: byte-observable 32-byte copy/zero result for normalized fail values with an x86 W32 promotion shadow; no formal ISO C integer-representation, C memory/pointer/binary equivalence, formal C int-return theorem, API-level shared-secret agreement, or full-KEM correctness'
}

main "$@"
