#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/keygen_h"
PROOF="$PROOF_DIR/NTRUPlus768KeygenHBridge.ec"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/keygen_h"
KEYGEN_INVERSE_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-keygen-inverse.sh"
POLY_BASEMUL_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-poly-basemul.sh"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-keygen-h.XXXXXX")
WHY3_SOCKET="$WORKDIR/why3.sock"
WHY3_PID=
WHY3SERVER_BIN=
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

require_lemma() {
  local lemma=$1

  grep -Eq "^lemma[[:space:]]+$lemma([[:space:](]|$)" "$PROOF" ||
    fail "missing required EasyCrypt lemma: $lemma"
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

start_why3_server() {
  local log=$1
  local launch
  local attempt

  : >"$log"
  for ((launch = 1; launch <= 3; ++launch)); do
    rm -f "$WHY3_SOCKET"
    "$WHY3SERVER_BIN" --socket "$WHY3_SOCKET" --single-client -j1 \
      >>"$log" 2>&1 &
    WHY3_PID=$!
    for ((attempt = 0; attempt < 200; ++attempt)); do
      [[ -S "$WHY3_SOCKET" ]] && return 0
      sleep 0.05
    done
    kill "$WHY3_PID" 2>/dev/null || true
    wait "$WHY3_PID" 2>/dev/null || true
    WHY3_PID=
    sleep 0.1
  done
  return 1
}

compile_proof() {
  local log="$WORKDIR/why3.log"

  start_why3_server "$log" || {
    sed -n '1,120p' "$log" >&2 || true
    fail "could not start the dedicated Why3 server"
  }
  if ! (
    cd "$PROOF_DIR"
    easycrypt compile -no-eco -p Z3 -timeout 30 -max-provers 1 \
      -server "$WHY3_SOCKET" "$PROOF"
  ); then
    sed -n '1,120p' "$log" >&2 || true
    fail "strict EasyCrypt keygen h bridge failed"
  fi
  kill "$WHY3_PID" 2>/dev/null || true
  wait "$WHY3_PID" 2>/dev/null || true
  WHY3_PID=
}

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
      '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry|abort)([^[:alnum:]_]|$)' \
      "$PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "keygen h proof contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the keygen h proof"
  fi
}

reject_overclaims() {
  local findings="$WORKDIR/overclaims.txt"
  local pattern='^lemma[[:space:]]+.*(retry|probability|production_c|c_equiv|serialization|hash|ntt_homomorphism|full_kem|_ct|_sct)'

  if grep -En "$pattern" "$PROOF" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "keygen h proof contains an out-of-scope claim"
  fi
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
  WHY3SERVER_BIN=$(cd -- "$easycrypt_bindir/../lib/why3" && pwd)/why3server
  [[ -x "$WHY3SERVER_BIN" ]] ||
    fail "missing Why3 server next to the EasyCrypt installation"

  require_file "$PROOF"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$PROOF_DIR/Makefile"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_keygen_h.py"
  require_file "$TEST_DIR/keygen_h_driver.c"
  [[ -x "$KEYGEN_INVERSE_VERIFIER" ]] ||
    fail "missing executable keygen inverse predecessor verifier"
  [[ -x "$POLY_BASEMUL_VERIFIER" ]] ||
    fail "missing executable poly_basemul predecessor verifier"

  bash -n "$0"
  reject_proof_holes
  reject_overclaims
  grep -Fq 'production-C semantics or C/Jasmin equivalence' "$PROOF" ||
    fail "missing production-C scope disclaimer"
  grep -Fq 'random-retry' "$PROOF" ||
    fail "missing retry scope disclaimer"
  grep -Fq 'public/secret-key serialization' "$PROOF" ||
    fail "missing serialization scope disclaimer"
  grep -Fq 'high-level NTT/InvNTT ring homomorphism' "$PROOF" ||
    fail "missing high-level transform scope disclaimer"

  require_lemma nested0_swap_first_two
  require_lemma nested1_swap_first_two
  require_lemma nested2_swap_first_two
  require_lemma nested3_swap_first_two
  require_lemma block_inverse_product_cancel
  require_lemma poly_inverse_product_cancel
  require_lemma keygen_h_f_equals_g
  require_lemma keygen_hinv_g_equals_f
  require_lemma keygen_h_poly_basemul_ready
  require_lemma keygen_hinv_poly_basemul_ready
  require_lemma keygen_keypair_ntt_relation_intro
  require_lemma keypair_products_jasmin_calls_word_correct
  require_lemma keypair_products_word_post_implies_relation
  require_lemma keypair_products_jasmin_calls_correct
  require_lemma keygen_sampled_keypair_jasmin_calls_correct

  compile_proof
  OUTDIR="$WORKDIR/tests" CC="$CC_BIN" make -C "$TEST_DIR" all
  "$KEYGEN_INVERSE_VERIFIER"
  "$POLY_BASEMUL_VERIFIER"

  printf 'PASS: terminal four-coefficient quotient-ring commutativity, associativity, identity, and inverse cancellation\n'
  printf 'PASS: successful finv/ginv contracts imply h*f=g and hinv*g=f over all 192 terminal blocks\n'
  printf 'PASS: keygen h/hinv inputs satisfy the verified Jasmin poly_basemul q-range preconditions\n'
  printf 'PASS: the two exact Jasmin poly_basemul calls compose to the sampled-keygen NTT relation\n'
  printf 'PASS: strict single-Z3 keygen h proof completed through a dedicated Why3 server\n'
  printf 'PASS: keypair product checker rejected 15 representative mutations\n'
  printf 'PASS: 31 successful deterministic keypairs satisfy both identities under normal and UBSan builds\n'
  printf 'PASS: complete keygen inverse and poly_basemul predecessor verifier chains\n'
  printf '%s\n' \
    'SCOPE: proof-level NTT terminal-block keypair products plus exact-source and executable C/Jasmin anchoring; no random retry termination or probability, formal production-C semantics or C/Jasmin equivalence, high-level NTT/InvNTT ring homomorphism, public/secret-key serialization, hash provenance, aggregate CT/SCT claim, or full-KEM correctness'
}

main "$@"
