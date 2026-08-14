#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_ROOT="$REPO_ROOT/ntruplus/proof/768/ref"
BRIDGE_DIR="$PROOF_ROOT/decap_r2"
BRIDGE_PROOF="$BRIDGE_DIR/NTRUPlus768DecapR2Bridge.ec"
BASEMUL_ALGEBRA="$PROOF_ROOT/basemul/NTRUPlus768BasemulAlgebra.ec"
POLY_BASEMUL_ALGEBRA="$PROOF_ROOT/poly_basemul/NTRUPlus768PolyBasemulAlgebra.ec"
POLY_TOBYTES_ALGEBRA="$PROOF_ROOT/poly_tobytes/NTRUPlus768PolyToBytesAlgebra.ec"
POLY_TOBYTES_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-poly-tobytes.sh"
POLY_BASEMUL_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-poly-basemul.sh"
POLY_SUB_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-poly-sub.sh"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-decap-r2.XXXXXX")
WHY3_PID=
WHY3SERVER_BIN=
WHY3_SOCKET="$WORKDIR/why3.sock"

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
    "$BRIDGE_DIR" "$PROOF_ROOT/poly_tobytes" \
    "$PROOF_ROOT/basemul" "$PROOF_ROOT/poly_basemul" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "decap-r2 proof closure contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the decap-r2 proof closure for holes"
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
    fail "EasyCrypt decap-r2 bridge proof failed"
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
  [[ -x /usr/bin/gcc ]] || fail "missing required GCC compiler: /usr/bin/gcc"

  easycrypt_bin=$(command -v easycrypt)
  easycrypt_bindir=$(cd -- "$(dirname -- "$easycrypt_bin")" && pwd)
  WHY3SERVER_BIN="$easycrypt_bindir/../lib/why3/why3server"
  [[ -x "$WHY3SERVER_BIN" ]] ||
    fail "missing Why3 server next to the EasyCrypt installation: $WHY3SERVER_BIN"

  require_file "$BRIDGE_PROOF"
  require_file "$BRIDGE_DIR/easycrypt.project"
  require_file "$BASEMUL_ALGEBRA"
  require_file "$POLY_BASEMUL_ALGEBRA"
  require_file "$POLY_TOBYTES_ALGEBRA"
  require_file "$POLY_TOBYTES_VERIFIER"
  require_file "$POLY_BASEMUL_VERIFIER"
  require_file "$POLY_SUB_VERIFIER"

  require_pattern "$BASEMUL_ALGEBRA" \
    '^op[[:space:]]+asym_bound_hi[[:space:]]*:[[:space:]]*int[[:space:]]*=[[:space:]]*7552\.' \
    'asymmetric subtraction upper bound'
  require_lemma "$BASEMUL_ALGEBRA" basemul_spec_algebra_asym
  require_lemma "$POLY_BASEMUL_ALGEBRA" poly_basemul_word_to_qring_asym
  require_lemma "$POLY_BASEMUL_ALGEBRA" poly_basemul_correct_qring_asym
  require_lemma "$POLY_TOBYTES_ALGEBRA" poly_tobytes_roundtrip_correct
  require_lemma "$BRIDGE_PROOF" keygen_hinv_poly_basemul_roundtrip_provenance
  require_lemma "$BRIDGE_PROOF" valid_hinv_decap_r2_value_flow
  require_lemma "$BRIDGE_PROOF" valid_hinv_decap_r2_poly_basemul_correct
  require_lemma "$BRIDGE_PROOF" \
    poly_frombytes_two_decoder_specs_keygen_hinv_decap_r2_poly_basemul_correct
  require_lemma "$BRIDGE_PROOF" \
    poly_frombytes_two_decoder_specs_keygen_hinv_decap_r2_value_flow

  bash -n "$0"
  reject_proof_holes
  compile_bridge

  "$POLY_TOBYTES_VERIFIER"
  "$POLY_BASEMUL_VERIFIER"
  "$POLY_SUB_VERIFIER"

  printf 'PASS: NTRU+768 decap-r2 bridge proof-hole and required-theorem checks\n'
  printf 'PASS: NTRU+768 q-range key-generation hinv serialization/decoding provenance\n'
  printf 'PASS: NTRU+768 asymmetric poly_sub-output x canonical-hinv poly_basemul proof\n'
  printf 'PASS: NTRU+768 concrete decapsulation value flow through poly_basemul(&r2,&c,&hinv)\n'
  printf 'PASS: NTRU+768 poly_tobytes, poly_basemul, and poly_sub regression verifiers\n'
  printf '%s\n' \
    'SCOPE: old-array value/procedure theorems and exact-source/differential checks; no sampler/inversion provenance, pointer-overlap model, C-AST equivalence, downstream r2 serialization/hash, or full-KEM theorem'
}

main "$@"
