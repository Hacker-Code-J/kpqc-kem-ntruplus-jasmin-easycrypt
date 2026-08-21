#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_ROOT="$REPO_ROOT/ntruplus/proof/768/ref"
PROOF_DIR="$PROOF_ROOT/decap_fail"
FAIL_PROOF="$PROOF_DIR/NTRUPlus768DecapFailProof.ec"
BRIDGE_PROOF="$PROOF_DIR/NTRUPlus768DecapFailBridge.ec"
DECODE_DIR="$PROOF_ROOT/poly_sotp_decode"
DECODE_ALGEBRA="$DECODE_DIR/NTRUPlus768PolySOTPDecodeAlgebra.ec"
DECODE_BRIDGE="$DECODE_DIR/NTRUPlus768PolySOTPDecodeDecapBridge.ec"
VERIFY_DIR="$PROOF_ROOT/decap_verify"
VERIFY_PROOF="$VERIFY_DIR/NTRUPlus768VerifyProof.ec"
VERIFY_BRIDGE="$VERIFY_DIR/NTRUPlus768DecapVerifyBridge.ec"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/decap_fail"
DECODE_TEST_DIR="$REPO_ROOT/tests/ntruplus768/poly_sotp_decode"
VERIFY_TEST_DIR="$REPO_ROOT/tests/ntruplus768/decap_verify"
NTRU_ROOT="$REPO_ROOT/NTRU+/NTRU+768"
PARAMS_SOURCE="$NTRU_ROOT/params.h"
POLY_SOURCE="$NTRU_ROOT/poly.c"
KEM_SOURCE="$NTRU_ROOT/kem.c"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-decap-fail.XXXXXX")
WHY3_PID=
WHY3SERVER_BIN=
WHY3_SOCKET="$WORKDIR/why3.sock"
CC_BIN=
JASMINC_BIN=

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

resolve_tools() {
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

  require_command jasminc
  JASMINC_BIN=$(command -v jasminc)
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

  if grep -ERni --include='*.ec' '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' "$PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "decap fail theories contain a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] ||
      fail "could not scan the decap fail theories for proof holes"
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
    "$WHY3SERVER_BIN" --socket "$WHY3_SOCKET" --single-client -j1 >>"$server_log" 2>&1 &
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
      easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 -server "$WHY3_SOCKET" "$proof"
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
  resolve_tools

  easycrypt_bin=$(command -v easycrypt)
  easycrypt_bindir=$(cd -- "$(dirname -- "$easycrypt_bin")" && pwd)
  WHY3SERVER_BIN="$easycrypt_bindir/../lib/why3/why3server"
  [[ -x "$WHY3SERVER_BIN" ]] ||
    fail "missing Why3 server next to the EasyCrypt installation: $WHY3SERVER_BIN"

  require_file "$FAIL_PROOF"
  require_file "$BRIDGE_PROOF"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$PROOF_DIR/Makefile"
  require_file "$DECODE_ALGEBRA"
  require_file "$DECODE_BRIDGE"
  require_file "$DECODE_DIR/easycrypt.project"
  require_file "$VERIFY_PROOF"
  require_file "$VERIFY_BRIDGE"
  require_file "$VERIFY_DIR/easycrypt.project"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_decap_fail.py"
  require_file "$TEST_DIR/check_fail_vectors.py"
  require_file "$TEST_DIR/fail_driver.c"
  require_file "$DECODE_TEST_DIR/Makefile"
  require_file "$DECODE_TEST_DIR/check_poly_sotp_decode.py"
  require_file "$DECODE_TEST_DIR/check_poly_sotp_decode_vectors.py"
  require_file "$DECODE_TEST_DIR/poly_sotp_decode_driver.c"
  require_file "$VERIFY_TEST_DIR/Makefile"
  require_file "$VERIFY_TEST_DIR/check_decap_verify.py"
  require_file "$VERIFY_TEST_DIR/check_verify_vectors.py"
  require_file "$VERIFY_TEST_DIR/verify_driver.c"
  require_file "$PARAMS_SOURCE"
  require_file "$POLY_SOURCE"
  require_file "$KEM_SOURCE"

  require_pattern "$FAIL_PROOF" 'truncateu8[[:space:]]*\(\(zeroextu64[[:space:]]+decode_fail_byte\)' 'promoted OR and int8 truncation model'
  require_pattern "$BRIDGE_PROOF" 'compare_failed[[:space:]]*=[[:space:]]*\(buf1[[:space:]]*<>[[:space:]]*buf2\)' 'serialized-buffer mismatch relation'
  require_pattern "$DECODE_ALGEBRA" 'op[[:space:]]+poly_sotp_decode_fail_spec' 'boolean decode-failure specification'
  require_pattern "$VERIFY_PROOF" 'if[[:space:]]+buf1[[:space:]]*=[[:space:]]*buf2[[:space:]]+then[[:space:]]+W64\.of_int[[:space:]]+0' 'zero-on-equality verify specification'
  require_pattern "$KEM_SOURCE" 'fail[[:space:]]*=.*poly_sotp_decode\(msg,[[:space:]]*&m1,[[:space:]]*buf2\);' 'decode fail assignment'
  require_pattern "$KEM_SOURCE" 'fail[[:space:]]*\|=[[:space:]]*verify\(buf1,[[:space:]]*buf2,[[:space:]]*NTRUPLUS_POLYBYTES\);' 'verify failure OR update'

  require_lemma "$FAIL_PROOF" zeroextu64_fail_byte
  require_lemma "$FAIL_PROOF" fail_word_or
  require_lemma "$FAIL_PROOF" decap_fail_word_spec_bool
  require_lemma "$FAIL_PROOF" decap_fail_spec_range
  require_lemma "$FAIL_PROOF" decap_fail_spec_zero_iff
  require_lemma "$FAIL_PROOF" decap_fail_spec_one_iff
  require_lemma "$FAIL_PROOF" decap_fail_functional
  require_lemma "$FAIL_PROOF" decap_fail_correct_h
  require_lemma "$FAIL_PROOF" decap_fail_ll
  require_lemma "$FAIL_PROOF" decap_fail_correct
  require_lemma "$BRIDGE_PROOF" decap_fail_value_flow_intro
  require_lemma "$BRIDGE_PROOF" decap_fail_value_flow_decode_range
  require_lemma "$BRIDGE_PROOF" decap_fail_value_flow_compare_range
  require_lemma "$BRIDGE_PROOF" decap_fail_value_flow_result_range
  require_lemma "$BRIDGE_PROOF" decap_fail_value_flow_zero_iff
  require_lemma "$BRIDGE_PROOF" decap_fail_value_flow_one_iff
  require_lemma "$BRIDGE_PROOF" decap_fail_procedure_functional
  require_lemma "$BRIDGE_PROOF" decap_fail_procedure_correct
  require_lemma "$DECODE_ALGEBRA" poly_sotp_decode_fail_spec_iff
  require_lemma "$DECODE_BRIDGE" decap_terminal_poly_sotp_decode_value_flow
  require_lemma "$VERIFY_PROOF" verify_spec_eq_iff
  require_lemma "$VERIFY_PROOF" verify_spec_neq_iff
  require_lemma "$VERIFY_BRIDGE" decap_verify_value_flow_equal_iff
  require_lemma "$VERIFY_BRIDGE" decap_verify_value_flow_mismatch_iff

  bash -n "$0"
  reject_proof_holes
  compile_easycrypt_target "$PROOF_DIR" "$FAIL_PROOF" "standalone fail-OR proof"
  compile_easycrypt_target "$PROOF_DIR" "$BRIDGE_PROOF" "typed decapsulation fail bridge"
  make -C "$TEST_DIR" CC="$CC_BIN" OUTDIR="$WORKDIR/fail-test" all
  compile_easycrypt_target "$DECODE_DIR" "$DECODE_ALGEBRA" "decode-failure algebra"
  compile_easycrypt_target "$DECODE_DIR" "$DECODE_BRIDGE" "decode-failure frontier bridge"
  make -C "$DECODE_TEST_DIR" CC="$CC_BIN" JASMINC="$JASMINC_BIN" OUTDIR="$WORKDIR/decode-test" all
  compile_easycrypt_target "$VERIFY_DIR" "$VERIFY_PROOF" "verify-result proof"
  compile_easycrypt_target "$VERIFY_DIR" "$VERIFY_BRIDGE" "verify-result frontier bridge"
  make -C "$VERIFY_TEST_DIR" CC="$CC_BIN" OUTDIR="$WORKDIR/verify-test" all

  printf 'PASS: NTRU+768 promoted 0/1 decode/verify OR and int8 truncation proof\n'
  printf 'PASS: NTRU+768 final failure byte is 0 iff decode succeeds and buf1 equals buf2\n'
  printf 'PASS: NTRU+768 final failure byte is 1 iff decode fails or buf1 differs from buf2\n'
  printf 'PASS: NTRU+768 exact fail assignment/OR caller seam and mutation checks\n'
  printf 'PASS: NTRU+768 32-vector truth-table differential and UBSan checks\n'
  printf 'PASS: NTRU+768 decode and verify frontier proofs/focused regressions\n'
  printf '%s\n' 'SCOPE: exact 0/1 failure-byte composition through fail |= verify; no formal general C integer-promotion theorem, C/pointer/binary equivalence, shared-secret mask/fallback selection, or full-KEM correctness'
}

main "$@"
