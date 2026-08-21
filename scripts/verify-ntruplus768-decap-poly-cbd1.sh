#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_ROOT="$REPO_ROOT/ntruplus/proof/768/ref"
BRIDGE_DIR="$PROOF_ROOT/decap_poly_cbd1"
ALGEBRA_PROOF="$BRIDGE_DIR/NTRUPlus768PolyCBD1Algebra.ec"
BRIDGE_PROOF="$BRIDGE_DIR/NTRUPlus768DecapPolyCBD1Bridge.ec"
HASH_H_PROOF="$PROOF_ROOT/decap_hash_h/NTRUPlus768DecapHashHBridge.ec"
SOTP_ALGEBRA="$PROOF_ROOT/poly_sotp_decode/NTRUPlus768PolySOTPDecodeAlgebra.ec"
NTT_STAGE1_ALGEBRA="$PROOF_ROOT/ntt_stage1/NTRUPlus768NTTStage1Algebra.ec"
BASE_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-decap-hash-h.sh"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/decap_poly_cbd1"
HASH_H_TEST_DIR="$REPO_ROOT/tests/ntruplus768/decap_hash_h"
NTRU_ROOT="$REPO_ROOT/NTRU+/NTRU+768"
FULL_PREDECESSOR=${NTRUPLUS768_FULL_PREDECESSOR:-0}

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-decap-poly-cbd1.XXXXXX")
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

  grep -Eq "^(hoare|phoare|lemma)[[:space:]]+$lemma([[:space:](]|$)" "$file" ||
    fail "missing required EasyCrypt result: $lemma"
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
    "$BRIDGE_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "decap poly_cbd1 proofs contain a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the decap poly_cbd1 proofs for holes"
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

  if [[ $ready -ne 1 ]]; then
    sed -n '1,120p' "$server_log" >&2 || true
    fail "Why3 server did not become ready after three attempts"
  fi
}

stop_why3_server() {
  if [[ -n "$WHY3_PID" ]]; then
    kill "$WHY3_PID" 2>/dev/null || true
    wait "$WHY3_PID" 2>/dev/null || true
    WHY3_PID=
  fi
}

compile_bridge() {
  local server_log="$WORKDIR/why3.log"

  start_why3_server "$server_log"
  if ! (
    cd "$BRIDGE_DIR"
    easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
      -server "$WHY3_SOCKET" "$BRIDGE_PROOF"
  ); then
    sed -n '1,120p' "$server_log" >&2 || true
    fail "EasyCrypt decap poly_cbd1 bridge proof failed"
  fi
  stop_why3_server
}

verify_predecessor() {
  case "$FULL_PREDECESSOR" in
    0)
      make -C "$HASH_H_TEST_DIR" CC="$CC_BIN" \
        OUTDIR="$WORKDIR/hash-h-test" all
      ;;
    1)
      "$BASE_VERIFIER"
      ;;
    *)
      fail "NTRUPLUS768_FULL_PREDECESSOR must be 0 or 1"
      ;;
  esac
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

  require_file "$ALGEBRA_PROOF"
  require_file "$BRIDGE_PROOF"
  require_file "$BRIDGE_DIR/easycrypt.project"
  require_file "$BRIDGE_DIR/Makefile"
  require_file "$HASH_H_PROOF"
  require_file "$SOTP_ALGEBRA"
  require_file "$NTT_STAGE1_ALGEBRA"
  require_file "$BASE_VERIFIER"
  require_file "$HASH_H_TEST_DIR/Makefile"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_decap_poly_cbd1.py"
  require_file "$TEST_DIR/check_poly_cbd1_vectors.py"
  require_file "$TEST_DIR/poly_cbd1_driver.c"
  require_file "$NTRU_ROOT/params.h"
  require_file "$NTRU_ROOT/poly.h"
  require_file "$NTRU_ROOT/poly.c"
  require_file "$NTRU_ROOT/kem.c"

  require_pattern "$ALGEBRA_PROOF" \
    'poly_sotp_bit[[:space:]]+b[[:space:]]+j' \
    'reused byte-bit specification'
  require_pattern "$ALGEBRA_PROOF" \
    'buf\.\[96[[:space:]]*\+[[:space:]]*i\]' \
    'second 96-byte half'
  require_pattern "$ALGEBRA_PROOF" \
    'poly_cbd1_head_bit.*-[[:space:]]*$' \
    'head-minus-tail coefficient order'
  require_pattern "$HASH_H_PROOF" \
    'Array192\.init[[:space:]]*\(fun[[:space:]]+i[[:space:]]*=>[[:space:]]*\(hash_h_spec[[:space:]]+msg[[:space:]]+suffix\)\.\[32[[:space:]]*\+[[:space:]]*i\]\)' \
    '32-byte hash_h tail projection'
  require_pattern "$BRIDGE_PROOF" \
    'Array192\.init[[:space:]]*\(fun[[:space:]]+i[[:space:]]*=>[[:space:]]*buf3_prefix\.\[32[[:space:]]*\+[[:space:]]*i\]\)' \
    'Keccak-free 224-byte-prefix tail projection'
  require_pattern "$BRIDGE_PROOF" \
    'predecessor_flow[[:space:]]+buf3_prefix[[:space:]]*/\\' \
    'parameterized predecessor-flow preservation'

  require_lemma "$SOTP_ALGEBRA" poly_sotp_bit_bound
  require_lemma "$HASH_H_PROOF" decap_terminal_hash_h_value_flow
  require_lemma "$HASH_H_PROOF" decap_hash_h_failure_zero
  require_lemma "$ALGEBRA_PROOF" poly_cbd1_bit_bound
  require_lemma "$ALGEBRA_PROOF" poly_cbd1_coeff_int_range
  require_lemma "$ALGEBRA_PROOF" poly_cbd1_spec_word
  require_lemma "$ALGEBRA_PROOF" poly_cbd1_spec_coeff
  require_lemma "$ALGEBRA_PROOF" poly_cbd1_coeff_layout
  require_lemma "$ALGEBRA_PROOF" poly_cbd1_spec_trit_output
  require_lemma "$ALGEBRA_PROOF" poly_cbd1_spec_sotp_trit_input
  require_lemma "$ALGEBRA_PROOF" poly_cbd1_spec_input_qrange
  require_lemma "$BRIDGE_PROOF" hash_h_cbd1_input_is_tail
  require_lemma "$BRIDGE_PROOF" hash_h_cbd1_input_first
  require_lemma "$BRIDGE_PROOF" hash_h_cbd1_input_last
  require_lemma "$BRIDGE_PROOF" hash_h_output_to_poly_cbd1_value_flow
  require_lemma "$BRIDGE_PROOF" decap_terminal_poly_cbd1_value_flow
  require_lemma "$BRIDGE_PROOF" decap_poly_cbd1_r1_trit_output
  require_lemma "$BRIDGE_PROOF" decap_poly_cbd1_r1_input_qrange
  require_lemma "$BRIDGE_PROOF" poly_cbd1_preserves_hash_output_equality

  bash -n "$0"
  reject_proof_holes
  compile_bridge
  make -C "$TEST_DIR" CC="$CC_BIN" OUTDIR="$WORKDIR/test" all
  verify_predecessor

  printf 'PASS: NTRU+768 decap hash_h-tail to poly_cbd1 array-value bridge and proof-hole checks\n'
  printf 'PASS: NTRU+768 exact buf3[32..223] projection and paired 96-byte bit sampler\n'
  printf 'PASS: NTRU+768 poly_cbd1 coefficient {-1,0,1} and next-NTT input-range theorems\n'
  printf 'PASS: NTRU+768 poly_cbd1 C body/caller source checks and negative mutations\n'
  printf 'PASS: NTRU+768 poly_cbd1 44-vector differential and UBSan checks\n'
  if [[ "$FULL_PREDECESSOR" == 1 ]]; then
    printf 'PASS: NTRU+768 full predecessor hash_h, poly_sotp_decode, hash_g, and arithmetic regressions\n'
  else
    printf 'PASS: NTRU+768 predecessor hash_h source, SHAKE256 differential, and UBSan regressions\n'
    printf 'NOTE: set NTRUPLUS768_FULL_PREDECESSOR=1 to replay the memory-intensive full predecessor proof chain\n'
  fi
  printf '%s\n' \
    'SCOPE: Keccak-free exact Array224-tail value bridge parameterized by the established predecessor flow, plus source-shape and differential checks; no in-file concrete SHAKE256 instantiation, formal C/Jasmin equivalence, C pointer/alias model, formal hash_f suffix provenance, poly_ntt procedure composition, reencryption, comparison, fallback selection, or full-KEM correctness'
}

main "$@"
