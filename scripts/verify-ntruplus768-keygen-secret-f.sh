#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/keygen_secret_f"
PROOF="$PROOF_DIR/NTRUPlus768KeygenSecretFBridge.ec"
VALID_KEY_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/ring_semantics/NTRUPlus768ValidKeyDecapM1Semantics.ec"
README_FILE="$REPO_ROOT/README.md"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/keygen_secret_f"
KEYGEN_PUBLIC_KEY_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-keygen-public-key.sh"
VALID_KEY_M1_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-valid-key-decap-m1-semantics.sh"
DECAP_M1_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-decap-m1.sh"
FULL_PREDECESSOR=${NTRUPLUS768_FULL_PREDECESSOR:-0}

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-keygen-secret-f.XXXXXX")
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

require_operation() {
  local operation=$1

  grep -Eq "^op[[:space:]]+$operation([[:space:](]|$)" "$PROOF" ||
    fail "missing required EasyCrypt operation: $operation"
}

require_lemma() {
  local lemma=$1

  grep -Eq "^lemma[[:space:]]+$lemma([[:space:](]|$)" "$PROOF" ||
    fail "missing required EasyCrypt lemma: $lemma"
}

require_valid_key_lemma() {
  local lemma=$1

  grep -Eq "^lemma[[:space:]]+$lemma([[:space:](]|$)" "$VALID_KEY_PROOF" ||
    fail "missing required valid-key semantics lemma: $lemma"
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

stop_why3_server() {
  if [[ -n "$WHY3_PID" ]]; then
    kill "$WHY3_PID" 2>/dev/null || true
    wait "$WHY3_PID" 2>/dev/null || true
    WHY3_PID=
  fi
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
    fail "strict EasyCrypt keygen secret-f bridge failed"
  fi
  stop_why3_server
}

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
      '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry|abort)([^[:alnum:]_]|$)' \
      "$PROOF_DIR" "$VALID_KEY_PROOF" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "keygen secret-f proof contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the keygen secret-f proof"
  fi
}

reject_semantic_overclaims() {
  local stripped="$WORKDIR/proof-without-comments.ec"
  local findings="$WORKDIR/overclaims.txt"
  local pattern='NTRUPlus768Crepmod3|poly_crepmod3|crepmod3_(int|word|spec)|no_wrap|m1_exact|encoded_m|production_c|c_equiv|full_kem'

  python3 -c \
    'import re, sys; print("\n".join(re.sub(r"\(\*.*?\*\)", "", open(path, encoding="utf-8").read(), flags=re.S) for path in sys.argv[1:]))' \
    "$PROOF" "$VALID_KEY_PROOF" >"$stripped"

  if grep -En "$pattern" "$stripped" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "keygen secret-f proof tree contains an out-of-scope semantic claim"
  fi
}

check_readme_scope() {
  local section="$WORKDIR/readme-secret-f-section.md"

  if ! python3 -c \
      'from pathlib import Path; import sys; text = Path(sys.argv[1]).read_text(encoding="utf-8"); heading = "## Secret-key `f` serialization provenance"; start = text.find(heading); assert start >= 0; end = text.find("\n## ", start + len(heading)); print(text[start:] if end < 0 else text[start:end])' \
      "$README_FILE" >"$section"; then
    fail "README is missing the secret-f serialization section"
  fi
  grep -Fq 'centered-noise/no-q-wrap theorem' "$section" ||
    fail "README secret-f section must retain the no-wrap scope boundary"
  grep -Fq 'formal production-C semantics or C/Jasmin equivalence' "$section" ||
    fail "README secret-f section must retain the production-C scope boundary"
  grep -Fq 'or full-KEM correctness.' "$section" ||
    fail "README secret-f section must retain the full-KEM scope boundary"
}

verify_full_predecessor_setting() {
  case "$FULL_PREDECESSOR" in
    0|1) ;;
    *) fail "NTRUPLUS768_FULL_PREDECESSOR must be 0 or 1" ;;
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
  verify_full_predecessor_setting

  easycrypt_bin=$(command -v easycrypt)
  easycrypt_bindir=$(cd -- "$(dirname -- "$easycrypt_bin")" && pwd)
  WHY3SERVER_BIN=$(cd -- "$easycrypt_bindir/../lib/why3" && pwd)/why3server
  [[ -x "$WHY3SERVER_BIN" ]] ||
    fail "missing Why3 server next to the EasyCrypt installation"

  require_file "$PROOF"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$PROOF_DIR/Makefile"
  require_file "$VALID_KEY_PROOF"
  require_file "$README_FILE"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_keygen_secret_f.py"
  require_file "$TEST_DIR/keygen_secret_f_driver.c"
  [[ -x "$KEYGEN_PUBLIC_KEY_VERIFIER" ]] ||
    fail "missing executable keygen public-key predecessor verifier"
  [[ -x "$VALID_KEY_M1_VERIFIER" ]] ||
    fail "missing executable valid-key m1 semantics verifier"
  [[ -x "$DECAP_M1_VERIFIER" ]] ||
    fail "missing executable decap-m1 predecessor verifier"

  bash -n "$0"
  reject_proof_holes
  reject_semantic_overclaims
  grep -Fq 'first 1152 secret-key bytes' "$PROOF" ||
    fail "missing first-secret-key-block scope"
  grep -Fq 'hinv/hash suffix' "$PROOF" ||
    fail "missing remaining-secret-key scope disclaimer"
  grep -Fq 'no-wrap' "$PROOF" ||
    fail "missing no-wrap scope disclaimer"
  grep -Fq 'production-C' "$PROOF" ||
    fail "missing production-C scope disclaimer"
  check_readme_scope

  require_operation keygen_secret_f_bytes
  require_operation keygen_decoded_secret_f
  require_operation keygen_secret_f_serialization_relation
  require_lemma keygen_secret_f_bytes_procedure_specE
  require_lemma keygen_secret_f_tobytes_input_qrange
  require_lemma keygen_decoded_secret_f_roundtrip
  require_lemma keygen_decoded_secret_f_coeff_range
  require_lemma keygen_decoded_secret_f_canonical_range
  require_lemma keygen_decoded_secret_f_mod_q
  require_lemma poly_coeff_eq_mod_q_block_poly
  require_lemma terminal_represents_mod_q_replacement
  require_lemma poly_basemul_qring_right_mod_q_congr
  require_lemma keygen_secret_f_qrange
  require_lemma keygen_decoded_h_decoded_f_equals_g
  require_lemma keygen_sampled_secret_f_tobytes_input_qrange
  require_lemma keygen_sampled_secret_f_terminal_represents
  require_lemma keygen_sampled_decoded_secret_f_terminal_represents
  require_lemma keygen_secret_f_serialization_relation_intro
  require_lemma keygen_sampled_secret_f_serialization_relation_intro
  require_lemma keygen_secret_f_serialization_relation_outcome
  require_lemma keygen_secret_f_valid_key_m1_spec_semantics
  require_lemma keygen_secret_f_jasmin_tobytes_functional
  require_lemma keygen_secret_f_jasmin_tobytes_correct
  require_valid_key_lemma terminal_valid_key_decap_product_local
  require_valid_key_lemma valid_key_decap_m1_local_spec_semantics

  compile_proof
  OUTDIR="$WORKDIR/tests" CC="$CC_BIN" make -C "$TEST_DIR" all

  if [[ "$FULL_PREDECESSOR" == 1 ]]; then
    "$KEYGEN_PUBLIC_KEY_VERIFIER"
    "$VALID_KEY_M1_VERIFIER"
    "$DECAP_M1_VERIFIER"
  else
    printf 'NOTE: set NTRUPLUS768_FULL_PREDECESSOR=1 to replay the complete keygen/valid-key/decap predecessor chains\n'
  fi

  printf 'PASS: keygen sk[0..1151] equals poly_tobytes_spec(f) and decap decodes the same block\n'
  printf 'PASS: decoded_f is canonical, coefficientwise equal modulo q, and preserves terminal representation\n'
  printf 'PASS: decoded_h*decoded_f=g holds in every terminal quotient ring\n'
  printf 'PASS: valid-key m1 composition no longer requires a global polynomial representative for h\n'
  printf 'PASS: exact Jasmin poly_tobytes functional and probability-one contracts cover secret f\n'
  printf 'PASS: fail-closed source checker and 10,256 normal/UBSan runtime cases completed\n'
  printf '%s\n' \
    'SCOPE: proof-facing and executable provenance for the first 1152-byte secret-f block through canonical decode; no hinv/hash suffix provenance, centered-noise/no-wrap theorem, exact post-crepmod3 m1 recovery, formal production-C semantics or C/Jasmin equivalence, or full-KEM correctness'
}

main "$@"
