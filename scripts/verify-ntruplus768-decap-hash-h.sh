#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_ROOT="$REPO_ROOT/ntruplus/proof/768/ref"
BRIDGE_DIR="$PROOF_ROOT/decap_hash_h"
BRIDGE_PROOF="$BRIDGE_DIR/NTRUPlus768DecapHashHBridge.ec"
SOTP_DIR="$PROOF_ROOT/poly_sotp_decode"
SOTP_ALGEBRA="$SOTP_DIR/NTRUPlus768PolySOTPDecodeAlgebra.ec"
SOTP_BRIDGE="$SOTP_DIR/NTRUPlus768PolySOTPDecodeDecapBridge.ec"
FIPS202_SPEC="$REPO_ROOT/external/formosa-mlkem/crypto-specs/fips202/properties/Keccak1600_Spec.ec"
BASE_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-decap-sotp-decode.sh"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/decap_hash_h"
NTRU_ROOT="$REPO_ROOT/NTRU+/NTRU+768"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-decap-hash-h.XXXXXX")
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
    fail "decap hash_h bridge contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the decap hash_h bridge for holes"
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
    fail "EasyCrypt decap hash_h bridge proof failed"
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

  require_file "$BRIDGE_PROOF"
  require_file "$BRIDGE_DIR/easycrypt.project"
  require_file "$BRIDGE_DIR/Makefile"
  require_file "$SOTP_ALGEBRA"
  require_file "$SOTP_BRIDGE"
  require_file "$FIPS202_SPEC"
  require_file "$BASE_VERIFIER"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_decap_hash_h.py"
  require_file "$TEST_DIR/check_hash_h_vectors.py"
  require_file "$TEST_DIR/hash_h_driver.c"
  require_file "$NTRU_ROOT/params.h"
  require_file "$NTRU_ROOT/symmetric.c"
  require_file "$NTRU_ROOT/symmetric.h"
  require_file "$NTRU_ROOT/fips202/fips202.c"
  require_file "$NTRU_ROOT/fips202/fips202.h"
  require_file "$NTRU_ROOT/kem.c"

  require_pattern "$BRIDGE_PROOF" \
    '\[W8\.of_int[[:space:]]+2\][[:space:]]*\+\+' \
    '0x02-prefixed hash input'
  require_pattern "$BRIDGE_PROOF" \
    'SHAKE256[[:space:]]*\(hash_h_input[[:space:]]+msg[[:space:]]+suffix\)[[:space:]]+224' \
    '224-byte SHAKE256 functional specification'
  require_pattern "$BRIDGE_PROOF" \
    'Keccak1600Bytes\.shake256\(hash_h_input[[:space:]]+msg[[:space:]]+suffix,[[:space:]]*224\)' \
    'FIPS202 byte-procedure call'

  require_lemma "$FIPS202_SPEC" SHAKE256_h
  require_lemma "$FIPS202_SPEC" SHAKE256_ph
  require_lemma "$SOTP_ALGEBRA" poly_sotp_decode_failure_zero
  require_lemma "$SOTP_BRIDGE" decap_terminal_poly_sotp_decode_value_flow
  require_lemma "$BRIDGE_PROOF" hash_h_payload_size
  require_lemma "$BRIDGE_PROOF" hash_h_input_size
  require_lemma "$BRIDGE_PROOF" hash_h_input_domain
  require_lemma "$BRIDGE_PROOF" hash_h_input_payload
  require_lemma "$BRIDGE_PROOF" hash_h_output_list_size
  require_lemma "$BRIDGE_PROOF" hash_h_spec_to_list
  require_lemma "$BRIDGE_PROOF" hash_h_h
  require_lemma "$BRIDGE_PROOF" hash_h_ll
  require_lemma "$BRIDGE_PROOF" hash_h_abstract_correct
  require_lemma "$BRIDGE_PROOF" decap_terminal_hash_h_value_flow
  require_lemma "$BRIDGE_PROOF" decap_hash_h_failure_zero
  require_lemma "$BRIDGE_PROOF" decap_hash_h_correct

  bash -n "$0"
  reject_proof_holes
  compile_bridge
  make -C "$TEST_DIR" CC="$CC_BIN" OUTDIR="$WORKDIR/test" all
  "$BASE_VERIFIER"

  printf 'PASS: NTRU+768 decap hash_h FIPS202 value/procedure bridge and proof-hole checks\n'
  printf 'PASS: NTRU+768 exact 0x02 || decoded-prefix || secret-key-suffix input and 224-byte SHAKE256 output\n'
  printf 'PASS: NTRU+768 hash_h failure-zero value theorem with suffix preservation\n'
  printf 'PASS: NTRU+768 hash_h C wrapper/caller/key-layout source checks and negative mutations\n'
  printf 'PASS: NTRU+768 hash_h differential and UBSan checks against Python hashlib SHAKE256\n'
  printf 'PASS: NTRU+768 predecessor poly_sotp_decode, hash_g, and arithmetic regressions\n'
  printf '%s\n' \
    'SCOPE: FIPS202 abstract byte-procedure/value bridge plus exact-source and differential checks; the suffix is an arbitrary formal Array32 value and the keygen hash_f/decap offset relation is source-checked only; no formal C/Jasmin equivalence, heap-failure or pointer-alias model, formal hash_f provenance, poly_cbd1, reencryption, comparison, fallback selection, or full-KEM correctness'
}

main "$@"
