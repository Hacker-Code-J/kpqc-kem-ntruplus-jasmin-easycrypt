#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/keygen_public_key"
PROOF="$PROOF_DIR/NTRUPlus768KeygenPublicKeyBridge.ec"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/keygen_public_key"
KEYGEN_H_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-keygen-h.sh"
POLY_TOBYTES_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-poly-tobytes.sh"
POLY_FROMBYTES_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-poly-frombytes.sh"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-keygen-public-key.XXXXXX")
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
    fail "strict EasyCrypt keygen public-key bridge failed"
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
    fail "keygen public-key proof contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the keygen public-key proof"
  fi
}

reject_overclaims() {
  local findings="$WORKDIR/overclaims.txt"
  local pattern='^lemma[[:space:]]+.*(retry|probability|production_c|c_equiv|secret_key|hash|ntt_homomorphism|full_kem|_ct|_sct)'

  if grep -En "$pattern" "$PROOF" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "keygen public-key proof contains an out-of-scope claim"
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
  require_file "$TEST_DIR/check_keygen_public_key.py"
  require_file "$TEST_DIR/keygen_public_key_driver.c"
  [[ -x "$KEYGEN_H_VERIFIER" ]] ||
    fail "missing executable keygen h predecessor verifier"
  [[ -x "$POLY_TOBYTES_VERIFIER" ]] ||
    fail "missing executable poly_tobytes predecessor verifier"
  [[ -x "$POLY_FROMBYTES_VERIFIER" ]] ||
    fail "missing executable poly_frombytes predecessor verifier"

  bash -n "$0"
  reject_proof_holes
  reject_overclaims
  grep -Fq 'production-C semantics or C/Jasmin equivalence' "$PROOF" ||
    fail "missing production-C scope disclaimer"
  grep -Fq 'random retry' "$PROOF" ||
    fail "missing retry scope disclaimer"
  grep -Fq 'high-level NTT/InvNTT homomorphism' "$PROOF" ||
    fail "missing high-level transform scope disclaimer"
  grep -Fq 'secret-key' "$PROOF" ||
    fail "missing secret-key serialization scope disclaimer"
  grep -Fq 'hash provenance' "$PROOF" ||
    fail "missing hash scope disclaimer"
  grep -Fq 'aggregate CT/SCT' "$PROOF" ||
    fail "missing aggregate CT/SCT scope disclaimer"
  grep -Fq 'full-KEM correctness' "$PROOF" ||
    fail "missing full-KEM scope disclaimer"

  require_lemma poly_frombytes_specsE
  require_lemma keygen_public_key_bytes_procedure_specE
  require_lemma poly_basemul_qring_output_in_qrange768
  require_lemma in_qrange768_poly_tobytes_input_qrange
  require_lemma keygen_public_h_qrange
  require_lemma keygen_public_h_tobytes_input_qrange
  require_lemma keygen_decoded_public_key_roundtrip
  require_lemma keygen_decoded_public_key_coeff_range
  require_lemma keygen_decoded_public_key_canonical_range
  require_lemma keygen_decoded_public_key_mod_q
  require_lemma coeff0_left_mod_q_congr
  require_lemma coeff1_left_mod_q_congr
  require_lemma coeff2_left_mod_q_congr
  require_lemma coeff3_left_mod_q_congr
  require_lemma poly_coeff_eq_mod_q_block4
  require_lemma poly_basemul_qring_left_mod_q_congr
  require_lemma keygen_decoded_h_f_equals_g
  require_lemma keygen_public_key_serialization_relation_intro
  require_lemma keygen_public_key_procedure_result_implies_relation
  require_lemma keygen_public_key_jasmin_tobytes_functional
  require_lemma keygen_public_key_jasmin_tobytes_correct
  require_lemma keygen_sampled_public_key_jasmin_tobytes_functional
  require_lemma keygen_sampled_public_key_jasmin_tobytes_correct
  require_lemma keygen_public_key_serialization_relation_outcome

  compile_proof
  OUTDIR="$WORKDIR/tests" CC="$CC_BIN" make -C "$TEST_DIR" all
  "$KEYGEN_H_VERIFIER"
  "$POLY_TOBYTES_VERIFIER"
  "$POLY_FROMBYTES_VERIFIER"

  printf 'PASS: keygen h is a verified q-range input to the exact Jasmin poly_tobytes call\n'
  printf 'PASS: public-key bytes equal poly_tobytes_spec(h) and decode to the canonical representative\n'
  printf 'PASS: decoded public-key coefficients preserve h modulo q and satisfy decoded_h*f=g\n'
  printf 'PASS: strict single-Z3 keygen public-key proof completed through a dedicated Why3 server\n'
  printf 'PASS: fail-closed checker, deterministic differential tests, and UBSan tests completed\n'
  printf 'PASS: complete keygen h, poly_tobytes, and poly_frombytes predecessor verifier chains\n'
  printf '%s\n' \
    'SCOPE: proof-facing public-key serialization and canonical decode provenance plus exact-source and executable C/Jasmin anchoring; no random retry termination or probability, formal production-C semantics or C/Jasmin equivalence, high-level NTT/InvNTT homomorphism, secret-key serialization, hash provenance, aggregate CT/SCT claim, or full-KEM correctness'
}

main "$@"
