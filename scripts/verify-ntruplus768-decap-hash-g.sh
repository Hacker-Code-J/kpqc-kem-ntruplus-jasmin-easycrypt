#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_ROOT="$REPO_ROOT/ntruplus/proof/768/ref"
BRIDGE_DIR="$PROOF_ROOT/decap_hash_g"
BRIDGE_PROOF="$BRIDGE_DIR/NTRUPlus768DecapHashGBridge.ec"
BASE_BRIDGE="$PROOF_ROOT/decap_r2_tobytes/NTRUPlus768DecapR2ToBytesBridge.ec"
FIPS202_SPEC="$REPO_ROOT/external/formosa-mlkem/crypto-specs/fips202/properties/Keccak1600_Spec.ec"
BASE_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-decap-r2-tobytes.sh"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/decap_hash_g"
NTRU_ROOT="$REPO_ROOT/NTRU+/NTRU+768"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-decap-hash-g.XXXXXX")
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
    fail "decap hash_g bridge contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the decap hash_g bridge for holes"
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
    fail "EasyCrypt decap hash_g bridge proof failed"
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
  require_file "$BASE_BRIDGE"
  require_file "$FIPS202_SPEC"
  require_file "$BASE_VERIFIER"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_decap_hash_g.py"
  require_file "$TEST_DIR/check_hash_g_vectors.py"
  require_file "$TEST_DIR/hash_g_driver.c"
  require_file "$NTRU_ROOT/params.h"
  require_file "$NTRU_ROOT/symmetric.c"
  require_file "$NTRU_ROOT/symmetric.h"
  require_file "$NTRU_ROOT/fips202/fips202.c"
  require_file "$NTRU_ROOT/fips202/fips202.h"
  require_file "$NTRU_ROOT/kem.c"

  require_pattern "$BRIDGE_PROOF" \
    '\[W8\.of_int[[:space:]]+1\][[:space:]]*\+\+[[:space:]]*to_list[[:space:]]+buf1' \
    '0x01-prefixed 1152-byte hash input'
  require_pattern "$BRIDGE_PROOF" \
    'SHAKE256[[:space:]]*\(hash_g_input[[:space:]]+buf1\)[[:space:]]+192' \
    '192-byte SHAKE256 functional specification'
  require_pattern "$BRIDGE_PROOF" \
    'Keccak1600Bytes\.shake256\(hash_g_input[[:space:]]+buf1,[[:space:]]*192\)' \
    'FIPS202 byte-procedure call'

  require_lemma "$FIPS202_SPEC" SHAKE256_h
  require_lemma "$FIPS202_SPEC" SHAKE256_ph
  require_lemma "$BASE_BRIDGE" decap_r2_serialized_value_flow
  require_lemma "$BRIDGE_PROOF" hash_g_input_size
  require_lemma "$BRIDGE_PROOF" hash_g_input_domain
  require_lemma "$BRIDGE_PROOF" hash_g_input_payload
  require_lemma "$BRIDGE_PROOF" hash_g_output_list_size
  require_lemma "$BRIDGE_PROOF" hash_g_spec_to_list
  require_lemma "$BRIDGE_PROOF" hash_g_h
  require_lemma "$BRIDGE_PROOF" hash_g_abstract_correct
  require_lemma "$BRIDGE_PROOF" decap_r2_hash_g_value_flow
  require_lemma "$BRIDGE_PROOF" decap_hash_g_correct

  bash -n "$0"
  reject_proof_holes
  compile_bridge
  make -C "$TEST_DIR" CC="$CC_BIN" OUTDIR="$WORKDIR/test" all
  "$BASE_VERIFIER"

  printf 'PASS: NTRU+768 decap hash_g FIPS202 value/procedure bridge and proof-hole checks\n'
  printf 'PASS: NTRU+768 exact 0x01 || poly_tobytes(r2) input and 192-byte SHAKE256 output\n'
  printf 'PASS: NTRU+768 hash_g C wrapper/caller source checks and negative mutations\n'
  printf 'PASS: NTRU+768 hash_g differential and UBSan checks against Python hashlib SHAKE256\n'
  printf 'PASS: NTRU+768 predecessor decap-r2 serialization and arithmetic regressions\n'
  printf '%s\n' \
    'SCOPE: FIPS202 abstract byte-procedure/value bridge plus exact-source and differential checks; no formal C/Jasmin equivalence, heap-failure or pointer-alias model, SOTP theorem, bytes buf2[192..1151], reencryption, fallback selection, or full-KEM correctness'
}

main "$@"
