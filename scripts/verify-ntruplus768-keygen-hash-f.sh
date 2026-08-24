#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/keygen_hash_f"
HASH_F_PROOF="$PROOF_DIR/NTRUPlus768HashFProof.ec"
PROVENANCE_BRIDGE="$PROOF_DIR/NTRUPlus768KeygenHashFBridge.ec"
CONCRETE_BRIDGE="$PROOF_DIR/NTRUPlus768KeygenHashFConcrete.ec"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/keygen_hash_f"
TERMINAL_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-decap-terminal.sh"
NTRU_ROOT="$REPO_ROOT/NTRU+/NTRU+768"
PARAMS_SOURCE="$NTRU_ROOT/params.h"
SYMMETRIC_SOURCE="$NTRU_ROOT/symmetric.c"
KEM_SOURCE="$NTRU_ROOT/kem.c"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-keygen-hash-f.XXXXXX")
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
    fail "keygen hash_f theories contain a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan keygen hash_f theories for proof holes"
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
        -server "$WHY3_SOCKET" "$proof"
    ); then
      sed -n '1,120p' "$server_log" >&2 || true
      fail "EasyCrypt $label failed"
    fi
  else
    if ! (
      cd "$PROOF_DIR"
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

  require_file "$HASH_F_PROOF"
  require_file "$PROVENANCE_BRIDGE"
  require_file "$CONCRETE_BRIDGE"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$PROOF_DIR/Makefile"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_keygen_hash_f.py"
  require_file "$TEST_DIR/check_hash_f_vectors.py"
  require_file "$TEST_DIR/check_keygen_hash_f_layout_vectors.py"
  require_file "$TEST_DIR/hash_f_driver.c"
  require_file "$TEST_DIR/keygen_hash_f_layout_driver.c"
  require_file "$TERMINAL_VERIFIER"
  require_file "$PARAMS_SOURCE"
  require_file "$SYMMETRIC_SOURCE"
  require_file "$KEM_SOURCE"

  require_pattern "$HASH_F_PROOF" \
    '\[W8\.of_int[[:space:]]+0\][[:space:]]*\+\+' \
    '0x00-prefixed hash_f input'
  require_pattern "$HASH_F_PROOF" \
    'SHAKE256[[:space:]]*\(hash_f_input[[:space:]]+pk\)[[:space:]]+32' \
    '32-byte hash_f SHAKE256 specification'
  require_pattern "$PROVENANCE_BRIDGE" \
    '2304[[:space:]]*\+[[:space:]]*i' \
    'secret-key suffix offset projection'
  require_pattern "$PROVENANCE_BRIDGE" \
    '96[[:space:]]*\+[[:space:]]*i' \
    'decapsulation message suffix projection'
  require_pattern "$CONCRETE_BRIDGE" \
    'suffix[[:space:]]*=[[:space:]]*hash_f_spec[[:space:]]+pk' \
    'concrete hash_f suffix frontier'
  reject_pattern "$PROVENANCE_BRIDGE" \
    'Keccak1600_Spec|NTRUPlus768DecapTerminalBridge' \
    'heavy Keccak or terminal import in the lightweight provenance bridge'

  require_lemma "$HASH_F_PROOF" hash_f_payload_size
  require_lemma "$HASH_F_PROOF" hash_f_input_size
  require_lemma "$HASH_F_PROOF" hash_f_input_domain
  require_lemma "$HASH_F_PROOF" hash_f_input_payload
  require_lemma "$HASH_F_PROOF" hash_f_output_list_size
  require_lemma "$HASH_F_PROOF" hash_f_spec_to_list
  require_pattern "$HASH_F_PROOF" \
    '^hoare[[:space:]]+hash_f_h([[:space:](]|$)' \
    'EasyCrypt Hoare theorem: hash_f_h'
  require_lemma "$HASH_F_PROOF" hash_f_ll
  require_lemma "$HASH_F_PROOF" hash_f_correct
  require_lemma "$PROVENANCE_BRIDGE" keygen_hash_f_secret_suffix_byte
  require_lemma "$PROVENANCE_BRIDGE" keygen_hash_f_secret_suffix_exact
  require_lemma "$PROVENANCE_BRIDGE" keygen_hash_f_msg_payload_prefix_byte
  require_lemma "$PROVENANCE_BRIDGE" keygen_hash_f_msg_payload_suffix_byte
  require_lemma "$PROVENANCE_BRIDGE" keygen_hash_f_msg_suffix_exact
  require_lemma "$PROVENANCE_BRIDGE" keygen_hash_f_suffix_value_flow_intro
  require_lemma "$PROVENANCE_BRIDGE" keygen_hash_f_correlated_suffix_value_flow_intro
  require_lemma "$PROVENANCE_BRIDGE" keygen_hash_f_correlated_hash_closure_intro
  require_lemma "$PROVENANCE_BRIDGE" keygen_hash_f_correlated_suffix_outcome
  require_lemma "$PROVENANCE_BRIDGE" keygen_hash_f_correlated_hash_closure_outcome
  require_lemma "$CONCRETE_BRIDGE" hash_f_exact_frontier_intro
  require_lemma "$CONCRETE_BRIDGE" keygen_hash_f_concrete_suffix_value_flow_intro
  require_lemma "$CONCRETE_BRIDGE" keygen_hash_f_concrete_hash_closure_intro

  bash -n "$0"
  reject_proof_holes
  compile_easycrypt_target "$HASH_F_PROOF" "standalone FIPS202 hash_f proof"
  compile_easycrypt_target "$PROVENANCE_BRIDGE" "lightweight keygen/decap suffix provenance bridge"
  compile_easycrypt_target "$CONCRETE_BRIDGE" "concrete hash_f_spec provenance adapter"
  make -C "$TEST_DIR" CC="$CC_BIN" OUTDIR="$WORKDIR/test" all
  "$TERMINAL_VERIFIER"

  printf 'PASS: NTRU+768 hash_f is SHAKE256(0x00 || pk[0..1151], 32)\n'
  printf 'PASS: NTRU+768 keygen suffix is the concrete Array32 hash_f_spec(pk) value\n'
  printf 'PASS: NTRU+768 split Array2304/Array32 layout projects suffix at offset 2304\n'
  printf 'PASS: NTRU+768 decapsulation copies the same suffix into msg[96..127] before hash_h\n'
  printf 'PASS: NTRU+768 hash_f/hash_h typed closure shares one suffix without equating pk and decap buf1\n'
  printf 'PASS: NTRU+768 31 hash_f and 28 layout/copy normal and UBSan vectors\n'
  printf 'PASS: NTRU+768 correlated terminal and full mask/fail predecessor regressions\n'
  printf '%s\n' \
    'SCOPE: exact hash_f FIPS202 value/procedure proof plus split-layout suffix provenance and source/runtime offset anchoring; no flat C secret-key memory theorem, full keypair/decapsulation procedure equivalence, encapsulation-side hash_f agreement, API shared-secret agreement, or full-KEM correctness'
}

main "$@"
