#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_ROOT="$REPO_ROOT/ntruplus/proof/768/ref"
PROOF_DIR="$PROOF_ROOT/decap_verify"
VERIFY_PROOF="$PROOF_DIR/NTRUPlus768VerifyProof.ec"
BRIDGE_PROOF="$PROOF_DIR/NTRUPlus768DecapVerifyBridge.ec"
R2_DIR="$PROOF_ROOT/decap_r2_tobytes"
R1_DIR="$PROOF_ROOT/decap_r1_tobytes"
R2_BRIDGE="$R2_DIR/NTRUPlus768DecapR2ToBytesBridge.ec"
R1_BRIDGE="$R1_DIR/NTRUPlus768DecapR1ToBytesBridge.ec"
R2_TEST_DIR="$REPO_ROOT/tests/ntruplus768/decap_r2_tobytes"
R1_TEST_DIR="$REPO_ROOT/tests/ntruplus768/decap_r1_tobytes"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/decap_verify"
NTRU_ROOT="$REPO_ROOT/NTRU+/NTRU+768"
PARAMS_SOURCE="$NTRU_ROOT/params.h"
KEM_SOURCE="$NTRU_ROOT/kem.c"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-decap-verify.XXXXXX")
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
    fail "decap verify theories contain a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] ||
      fail "could not scan the decap verify theories for proof holes"
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

  require_file "$VERIFY_PROOF"
  require_file "$BRIDGE_PROOF"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$PROOF_DIR/Makefile"
  require_file "$R2_BRIDGE"
  require_file "$R1_BRIDGE"
  require_file "$R2_DIR/easycrypt.project"
  require_file "$R1_DIR/easycrypt.project"
  require_file "$R2_TEST_DIR/Makefile"
  require_file "$R2_TEST_DIR/check_decap_r2_tobytes.py"
  require_file "$R1_TEST_DIR/Makefile"
  require_file "$R1_TEST_DIR/check_decap_r1_tobytes.py"
  require_file "$R1_TEST_DIR/check_decap_r1_tobytes_vectors.py"
  require_file "$R1_TEST_DIR/decap_r1_tobytes_driver.c"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_decap_verify.py"
  require_file "$TEST_DIR/check_verify_vectors.py"
  require_file "$TEST_DIR/verify_driver.c"
  require_file "$PARAMS_SOURCE"
  require_file "$KEM_SOURCE"

  require_pattern "$VERIFY_PROOF" 'acc[[:space:]]*<-[[:space:]]*W8\.zero' 'uint8 zero accumulator model'
  require_pattern "$VERIFY_PROOF" 'zeroextu64[[:space:]]+acc' 'uint8-to-uint64 extension'
  require_pattern "$VERIFY_PROOF" 'W8\.of_int[[:space:]]+63' '63-bit normalization shift'
  require_pattern "$BRIDGE_PROOF" 'buf1_flow[[:space:]]+buf2_flow[[:space:]]*:[[:space:]]*W8\.t[[:space:]]+Array1152\.t[[:space:]]*->[[:space:]]*bool' 'typed serialized-frontier predicates'
  require_pattern "$R2_BRIDGE" 'buf1[[:space:]]*=[[:space:]]*NTRUPlus768PolyToBytesProof\.poly_tobytes_spec[[:space:]]+r2_output' 'r2 serialized buf1 value'
  require_pattern "$R1_BRIDGE" 'buf2[[:space:]]*=[[:space:]]*NTRUPlus768PolyToBytesProof\.poly_tobytes_spec[[:space:]]+r1_post' 'r1 serialized buf2 value'

  require_lemma "$VERIFY_PROOF" verify_prefix_eq_full
  require_lemma "$VERIFY_PROOF" array1152_neq_exists_mismatch
  require_lemma "$VERIFY_PROOF" normalize_nonzero_byte
  require_lemma "$VERIFY_PROOF" verify_spec_range
  require_lemma "$VERIFY_PROOF" verify_spec_eq_iff
  require_lemma "$VERIFY_PROOF" verify_spec_neq_iff
  require_lemma "$VERIFY_PROOF" verify_spec_mismatch_iff
  require_lemma "$VERIFY_PROOF" verify_correct_h
  require_lemma "$VERIFY_PROOF" verify_functional
  require_lemma "$VERIFY_PROOF" verify_ll
  require_lemma "$VERIFY_PROOF" verify_correct
  require_lemma "$BRIDGE_PROOF" decap_verify_value_flow_intro
  require_lemma "$BRIDGE_PROOF" decap_verify_value_flow_result_range
  require_lemma "$BRIDGE_PROOF" decap_verify_value_flow_equal_iff
  require_lemma "$BRIDGE_PROOF" decap_verify_value_flow_mismatch_iff
  require_lemma "$BRIDGE_PROOF" decap_verify_value_flow_mismatch_exists
  require_lemma "$BRIDGE_PROOF" decap_verify_procedure_functional
  require_lemma "$BRIDGE_PROOF" decap_verify_procedure_correct
  require_lemma "$R2_BRIDGE" decap_r2_serialized_value_flow
  require_lemma "$R1_BRIDGE" decap_terminal_r1_tobytes_value_flow

  bash -n "$0"
  reject_proof_holes
  compile_easycrypt_target "$PROOF_DIR" "$VERIFY_PROOF" "standalone verify procedure proof"
  compile_easycrypt_target "$PROOF_DIR" "$BRIDGE_PROOF" "typed decapsulation verify bridge"
  make -C "$TEST_DIR" CC="$CC_BIN" OUTDIR="$WORKDIR/test" all
  compile_easycrypt_target "$R2_DIR" "$R2_BRIDGE" "r2 serialized-frontier proof"
  make -C "$R2_TEST_DIR" check selfcheck
  compile_easycrypt_target "$R1_DIR" "$R1_BRIDGE" "r1 serialized-frontier proof"
  make -C "$R1_TEST_DIR" CC="$CC_BIN" JASMINC="$JASMINC_BIN" \
    OUTDIR="$WORKDIR/r1-tobytes-test" all

  printf 'PASS: NTRU+768 verify uint8 XOR/OR accumulator and uint64 normalization proof\n'
  printf 'PASS: NTRU+768 verify result is 0 iff equal and 1 iff a byte differs\n'
  printf 'PASS: NTRU+768 typed buf1/buf2 serialization-frontier comparison bridge\n'
  printf 'PASS: NTRU+768 exact production verify helper and decapsulation call-seam mutation checks\n'
  printf 'PASS: NTRU+768 31-vector normal and UBSan differential checks\n'
  printf 'PASS: NTRU+768 r2-tobytes and r1-tobytes frontier proofs/focused regressions\n'
  printf '%s\n' 'SCOPE: exact fixed-array verify semantics over established serialized frontiers; no formal C/pointer/binary equivalence, constant-time theorem, fail |= composition, shared-secret mask/fallback selection, or full-KEM correctness'
}

main "$@"
