#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/encap_hash_f_agreement"
AGREEMENT_PROOF="$PROOF_DIR/NTRUPlus768EncapHashFAgreement.ec"
CONCRETE_PROOF="$PROOF_DIR/NTRUPlus768EncapHashFConcrete.ec"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/encap_hash_f_agreement"
KEYGEN_TEST_DIR="$REPO_ROOT/tests/ntruplus768/keygen_hash_f"
PREDECESSOR_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-keygen-hash-f.sh"
NTRU_ROOT="$REPO_ROOT/NTRU+/NTRU+768"
PARAMS_SOURCE="$NTRU_ROOT/params.h"
SYMMETRIC_SOURCE="$NTRU_ROOT/symmetric.c"
KEM_SOURCE="$NTRU_ROOT/kem.c"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-encap-hash-f.XXXXXX")
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
    fail "encap hash_f agreement theories contain a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] ||
      fail "could not scan encap hash_f agreement theories for proof holes"
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
        -server "$WHY3_SOCKET" -I . -I ../keygen_hash_f "$proof"
    ); then
      sed -n '1,120p' "$server_log" >&2 || true
      fail "EasyCrypt $label failed"
    fi
  else
    if ! (
      cd "$PROOF_DIR"
      easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
        -I . -I ../keygen_hash_f "$proof"
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

  require_file "$AGREEMENT_PROOF"
  require_file "$CONCRETE_PROOF"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$PROOF_DIR/Makefile"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_encap_hash_f_agreement.py"
  require_file "$TEST_DIR/check_encap_hash_f_agreement_layout_vectors.py"
  require_file "$TEST_DIR/encap_hash_f_agreement_layout_driver.c"
  require_file "$KEYGEN_TEST_DIR/check_hash_f_vectors.py"
  require_file "$KEYGEN_TEST_DIR/hash_f_driver.c"
  require_file "$PREDECESSOR_VERIFIER"
  require_file "$PARAMS_SOURCE"
  require_file "$SYMMETRIC_SOURCE"
  require_file "$KEM_SOURCE"

  require_pattern "$AGREEMENT_PROOF" \
    '96[[:space:]]*\+[[:space:]]*i' \
    'encapsulation/decapsulation suffix byte offset'
  require_pattern "$AGREEMENT_PROOF" \
    'keygen_hash_f_secret_suffix' \
    'keygen secret-key suffix projection'
  require_pattern "$CONCRETE_PROOF" \
    'hash_f_spec[[:space:]]+pk' \
    'concrete hash_f_spec public-key suffix'
  reject_pattern "$AGREEMENT_PROOF" \
    'Keccak1600_Spec|NTRUPlus768HashFProof|NTRUPlus768DecapHashHBridge|NTRUPlus768DecapTerminalBridge' \
    'heavy Keccak/hash/terminal import in the lightweight agreement bridge'
  reject_pattern "$AGREEMENT_PROOF" \
    'encap_msg_prefix[[:space:]]*=[[:space:]]*decap_msg_prefix|decap_msg_prefix[[:space:]]*=[[:space:]]*encap_msg_prefix' \
    'equality between independent encapsulation and decapsulation prefixes'
  reject_pattern "$AGREEMENT_PROOF" \
    'pk[[:space:]]*=[[:space:]]*buf1|buf1[[:space:]]*=[[:space:]]*pk' \
    'public-key/decapsulation-buffer equality'

  require_lemma "$AGREEMENT_PROOF" encap_hash_f_agreement_value_flow_intro
  require_lemma "$AGREEMENT_PROOF" encap_hash_f_encap_suffix_exact
  require_lemma "$AGREEMENT_PROOF" encap_hash_f_encap_suffix_byte
  require_lemma "$AGREEMENT_PROOF" encap_hash_f_keygen_suffix_exact
  require_lemma "$AGREEMENT_PROOF" encap_hash_f_decap_suffix_exact
  require_lemma "$AGREEMENT_PROOF" encap_hash_f_decap_suffix_byte
  require_lemma "$AGREEMENT_PROOF" encap_hash_f_suffix_agreement
  require_lemma "$AGREEMENT_PROOF" encap_hash_f_agreement_outcome
  require_lemma "$CONCRETE_PROOF" encap_hash_f_concrete_agreement_intro
  require_lemma "$CONCRETE_PROOF" encap_hash_f_concrete_agreement_outcome

  bash -n "$0"
  reject_proof_holes
  compile_easycrypt_target "$AGREEMENT_PROOF" \
    "lightweight encapsulation/keygen/decapsulation suffix agreement"
  compile_easycrypt_target "$CONCRETE_PROOF" \
    "concrete hash_f_spec encapsulation agreement adapter"
  make -C "$TEST_DIR" CC="$CC_BIN" OUTDIR="$WORKDIR/test" all
  "$PREDECESSOR_VERIFIER"

  printf 'PASS: NTRU+768 encapsulation writes hash_f_spec(pk) to msg[96..127]\n'
  printf 'PASS: NTRU+768 keygen, encapsulation, and decapsulation share one 32-byte suffix\n'
  printf 'PASS: NTRU+768 encap/decap suffix equality requires no equality between their 96-byte prefixes\n'
  printf 'PASS: NTRU+768 exact encap hash_f-before-hash_h source seam and 17 negative mutations\n'
  printf 'PASS: NTRU+768 31 hash_f and 28 three-layout normal and UBSan vectors\n'
  printf 'PASS: NTRU+768 keygen hash_f provenance and full correlated terminal predecessor regressions\n'
  printf '%s\n' \
    'SCOPE: concrete hash_f_spec(pk) agreement for keygen sk[2304..2335], encapsulation msg[96..127], and decapsulation msg[96..127]; no equality of the independent 96-byte prefixes, full 128-byte message/hash_h/shared-secret agreement, flat C memory or full procedure equivalence, API agreement, or full-KEM correctness'
}

main "$@"
