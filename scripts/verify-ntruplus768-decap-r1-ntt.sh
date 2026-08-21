#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_ROOT="$REPO_ROOT/ntruplus/proof/768/ref"
BRIDGE_DIR="$PROOF_ROOT/decap_r1_ntt"
BRIDGE_PROOF="$BRIDGE_DIR/NTRUPlus768DecapR1NTTBridge.ec"
CBD_DIR="$PROOF_ROOT/decap_poly_cbd1"
CBD_BRIDGE="$CBD_DIR/NTRUPlus768DecapPolyCBD1Bridge.ec"
CBD_ALGEBRA="$CBD_DIR/NTRUPlus768PolyCBD1Algebra.ec"
NTT_DIR="$PROOF_ROOT/ntt"
NTT_PROOF="$NTT_DIR/NTRUPlus768NTTProof.ec"
NTT_ALGEBRA="$NTT_DIR/NTRUPlus768NTTAlgebra.ec"
TOBYTES_ALGEBRA="$PROOF_ROOT/poly_tobytes/NTRUPlus768PolyToBytesAlgebra.ec"
CBD_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-decap-poly-cbd1.sh"
NTT_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-ntt.sh"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/decap_r1_ntt"
NTRU_ROOT="$REPO_ROOT/NTRU+/NTRU+768"
JASMIN_SOURCE="$REPO_ROOT/ntruplus/jasmin/768/ref/ntt.jazz"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-decap-r1-ntt.XXXXXX")
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

  grep -Eq "^(hoare|phoare|equiv|lemma)[[:space:]]+$lemma([[:space:](]|$)" "$file" ||
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
    fail "decap r1 NTT bridge contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the decap r1 NTT bridge for holes"
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
    fail "EasyCrypt decap r1 NTT bridge proof failed"
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

  require_file "$BRIDGE_PROOF"
  require_file "$BRIDGE_DIR/easycrypt.project"
  require_file "$BRIDGE_DIR/Makefile"
  require_file "$CBD_BRIDGE"
  require_file "$CBD_ALGEBRA"
  require_file "$NTT_PROOF"
  require_file "$NTT_ALGEBRA"
  require_file "$TOBYTES_ALGEBRA"
  require_file "$CBD_VERIFIER"
  require_file "$NTT_VERIFIER"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_decap_r1_ntt.py"
  require_file "$TEST_DIR/check_decap_r1_ntt_vectors.py"
  require_file "$TEST_DIR/decap_r1_ntt_driver.c"
  require_file "$NTRU_ROOT/params.h"
  require_file "$NTRU_ROOT/poly.h"
  require_file "$NTRU_ROOT/poly.c"
  require_file "$NTRU_ROOT/ntt.c"
  require_file "$NTRU_ROOT/kem.c"
  require_file "$JASMIN_SOURCE"

  require_pattern "$BRIDGE_PROOF" \
    'predecessor_flow[[:space:]]*:[[:space:]]*W8\.t[[:space:]]+Array224\.t[[:space:]]*->[[:space:]]*bool' \
    'typed predecessor predicate'
  require_pattern "$BRIDGE_PROOF" \
    'r1_post[[:space:]]*=[[:space:]]*NTRUPlus768NTTProof\.ntt_spec[[:space:]]+r1_pre' \
    'exact NTT output value'
  require_pattern "$BRIDGE_PROOF" \
    'rp[[:space:]]*=[[:space:]]*r1_pre[[:space:]]*/\\[[:space:]]*ap[[:space:]]*=[[:space:]]*r1_pre' \
    'equal-value in-place procedure specialization'
  require_pattern "$BRIDGE_PROOF" \
    'poly_tobytes_input_qrange[[:space:]]+r1_post' \
    'poly_tobytes successor readiness'

  require_lemma "$CBD_BRIDGE" decap_poly_cbd1_r1_input_qrange
  require_lemma "$NTT_PROOF" ntt_functional
  require_lemma "$NTT_PROOF" ntt_lossless
  require_lemma "$NTT_PROOF" ntt_correct
  require_lemma "$NTT_ALGEBRA" ntt_specE
  require_lemma "$NTT_ALGEBRA" forward_ntt_spec_algebra
  require_lemma "$NTT_ALGEBRA" forward_ntt_centered_coeff_range
  require_lemma "$BRIDGE_PROOF" decap_poly_cbd1_to_r1_ntt_value_flow
  require_lemma "$BRIDGE_PROOF" decap_terminal_r1_ntt_value_flow
  require_lemma "$BRIDGE_PROOF" decap_r1_ntt_input_qrange
  require_lemma "$BRIDGE_PROOF" decap_r1_ntt_inplace_functional
  require_lemma "$BRIDGE_PROOF" decap_r1_ntt_inplace_lossless
  require_lemma "$BRIDGE_PROOF" decap_r1_ntt_inplace_correct
  require_lemma "$BRIDGE_PROOF" decap_r1_ntt_value_flow_inplace_functional
  require_lemma "$BRIDGE_PROOF" decap_r1_ntt_value_flow_inplace_correct
  require_lemma "$BRIDGE_PROOF" decap_r1_ntt_algebra
  require_lemma "$BRIDGE_PROOF" decap_r1_ntt_centered_output
  require_lemma "$BRIDGE_PROOF" decap_r1_ntt_poly_tobytes_ready

  bash -n "$0"
  reject_proof_holes
  compile_bridge
  make -C "$TEST_DIR" CC="$CC_BIN" JASMINC="$JASMINC_BIN" \
    OUTDIR="$WORKDIR/test" all
  "$NTT_VERIFIER"
  "$CBD_VERIFIER"

  printf 'PASS: NTRU+768 decap r1 CBD-to-NTT value and procedure bridge\n'
  printf 'PASS: NTRU+768 exact ntt_spec output, algebra chain, and centered range\n'
  printf 'PASS: NTRU+768 poly_tobytes successor input-range theorem\n'
  printf 'PASS: NTRU+768 C in-place caller/wrapper source checks and negative mutations\n'
  printf 'PASS: NTRU+768 61-vector CBD/Python plus C/Jasmin NTT differential and UBSan checks\n'
  printf 'PASS: NTRU+768 full composed NTT and focused CBD/hash_h predecessor regressions\n'
  printf '%s\n' \
    'SCOPE: Keccak-free typed value-flow plus verified old-array Jasmin procedure specialization and exact C/Jasmin runtime checks; no formal C pointer-alias/shared-memory theorem, concrete Keccak instantiation in this file, poly_tobytes procedure composition, reencryption, comparison, fallback selection, or full-KEM correctness'
}

main "$@"
