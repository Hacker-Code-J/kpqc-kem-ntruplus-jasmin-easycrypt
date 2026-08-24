#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/decap_terminal"
TERMINAL_PROOF="$PROOF_DIR/NTRUPlus768DecapTerminalProof.ec"
BRIDGE_PROOF="$PROOF_DIR/NTRUPlus768DecapTerminalBridge.ec"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/decap_terminal"
MASK_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-decap-mask.sh"
NTRU_ROOT="$REPO_ROOT/NTRU+/NTRU+768"
PARAMS_SOURCE="$NTRU_ROOT/params.h"
KEM_SOURCE="$NTRU_ROOT/kem.c"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-decap-terminal.XXXXXX")
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

reject_pattern() {
  local file=$1
  local pattern=$2
  local label=$3

  if grep -Eq "$pattern" "$file"; then
    fail "unexpected $label"
  fi
}

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
      '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
      "$PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "decap terminal theories contain a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan decap terminal theories for proof holes"
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
  local proof=$1
  local label=$2
  local server_log="$WORKDIR/$(basename -- "$proof").why3.log"

  if start_why3_server "$server_log"; then
    if ! (
      cd "$PROOF_DIR"
      easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
        -server "$WHY3_SOCKET" -I . -I ../decap_fail -I ../decap_mask "$proof"
    ); then
      sed -n '1,120p' "$server_log" >&2 || true
      fail "EasyCrypt $label failed"
    fi
  else
    if ! (
      cd "$PROOF_DIR"
      easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
        -I . -I ../decap_fail -I ../decap_mask "$proof"
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

  require_file "$TERMINAL_PROOF"
  require_file "$BRIDGE_PROOF"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$PROOF_DIR/Makefile"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_terminal_vectors.py"
  require_file "$TEST_DIR/terminal_driver.c"
  require_file "$MASK_VERIFIER"
  require_file "$PARAMS_SOURCE"
  require_file "$KEM_SOURCE"

  require_pattern "$BRIDGE_PROOF" \
    'decap_terminal_correlated_hash_frontier' \
    'correlated hash frontier'
  require_pattern "$BRIDGE_PROOF" \
    'W8\.t[[:space:]]+Array1152\.t[[:space:]]*->[[:space:]]*$' \
    'shared buf1 hash-frontier parameter'
  require_pattern "$BRIDGE_PROOF" \
    'W8\.t[[:space:]]+Array96\.t[[:space:]]*->[[:space:]]*$' \
    'shared decoded-msg hash-frontier parameter'
  require_pattern "$BRIDGE_PROOF" \
    'ret_fail[[:space:]]*=[[:space:]]*failv' \
    'returned W8 failure-byte preservation'
  reject_pattern "$BRIDGE_PROOF" \
    'NTRUPlus768DecapHashHBridge' \
    'full hash_h/Keccak import in the lightweight terminal bridge'

  require_lemma "$TERMINAL_PROOF" finish_functional
  require_lemma "$TERMINAL_PROOF" finish_ll
  require_lemma "$TERMINAL_PROOF" finish_correct
  require_lemma "$BRIDGE_PROOF" decap_terminal_fail_frontier_intro
  require_lemma "$BRIDGE_PROOF" decap_terminal_value_flow_intro
  require_lemma "$BRIDGE_PROOF" decap_terminal_correlated_value_flow_intro
  require_lemma "$BRIDGE_PROOF" decap_terminal_value_flow_source_exact
  require_lemma "$BRIDGE_PROOF" decap_terminal_value_flow_failed_iff
  require_lemma "$BRIDGE_PROOF" decap_terminal_value_flow_return_range
  require_lemma "$BRIDGE_PROOF" decap_terminal_value_flow_return_zero_iff
  require_lemma "$BRIDGE_PROOF" decap_terminal_value_flow_return_one_iff
  require_lemma "$BRIDGE_PROOF" decap_terminal_value_flow_selection
  require_lemma "$BRIDGE_PROOF" decap_terminal_value_flow_selection_from_prefix
  require_lemma "$BRIDGE_PROOF" decap_terminal_correlated_outcome
  require_lemma "$BRIDGE_PROOF" decap_terminal_value_flow_byte_selection
  require_lemma "$BRIDGE_PROOF" decap_terminal_value_flow_success_pair
  require_lemma "$BRIDGE_PROOF" decap_terminal_value_flow_failure_pair
  require_lemma "$BRIDGE_PROOF" finish_functional_from_value_flow
  require_lemma "$BRIDGE_PROOF" finish_correct_from_value_flow

  bash -n "$0"
  reject_proof_holes
  compile_easycrypt_target "$TERMINAL_PROOF" "terminal finish wrapper"
  compile_easycrypt_target "$BRIDGE_PROOF" "correlated decapsulation terminal bridge"
  make -C "$TEST_DIR" CC="$CC_BIN" OUTDIR="$WORKDIR/terminal-test" all
  "$MASK_VERIFIER"

  printf 'PASS: NTRU+768 correlated hash/fail/mask terminal value-flow proof\n'
  printf 'PASS: NTRU+768 returned W8 byte is 0 iff decode succeeds and buf1 equals buf2\n'
  printf 'PASS: NTRU+768 returned W8 byte is 1 iff decode fails or buf1 differs from buf2\n'
  printf 'PASS: NTRU+768 final ss copies the same projected hash source on success and is zero32 on failure\n'
  printf 'PASS: NTRU+768 exact verify/OR/mask/return integration over 32 normal and UBSan vectors\n'
  printf 'PASS: NTRU+768 fail-closed source seam and full mask predecessor regressions\n'
  printf '%s\n' \
    'SCOPE: correlated fixed-array terminal `(ss, W8 fail)` value theorem over typed predecessors; no formal C int-return conversion, C memory/pointer/binary equivalence, concrete full crypto_kem_dec procedure equivalence, API shared-secret agreement, or full-KEM correctness'
}

main "$@"
