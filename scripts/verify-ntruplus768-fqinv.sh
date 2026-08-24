#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/fqinv"
PRIME_PROOF="$PROOF_DIR/NTRUPlus768FqInvPrime.ec"
ALGEBRA_PROOF="$PROOF_DIR/NTRUPlus768FqInvAlgebra.ec"
BRIDGE_PROOF="$PROOF_DIR/NTRUPlus768FqInvBaseInvBridge.ec"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/baseinv"
BASEINV_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-baseinv.sh"
NTT_SOURCE="$REPO_ROOT/NTRU+/NTRU+768/ntt.c"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-fqinv.XXXXXX")

cleanup() {
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
      "$PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "fqinv theories contain a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan fqinv theories for proof holes"
  fi
}

reject_overclaims() {
  local findings="$WORKDIR/overclaims.txt"
  local pattern='^lemma[[:space:]]+.*(c_fqinv|jasmin_fqinv|baseinv_return|poly_baseinv_return|keygen_inverse|h_f|valid_key|m1|r2|no_wrap)'

  if grep -En "$pattern" "$PRIME_PROOF" "$ALGEBRA_PROOF" "$BRIDGE_PROOF" \
      >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "fqinv proof contains a C/Jasmin, keygen, or recovery overclaim"
  fi
}

compile_easycrypt_target() {
  local proof=$1
  local label=$2

  if ! (
    cd "$PROOF_DIR"
    easycrypt compile -no-eco -p Z3 -timeout 10 -max-provers 1 "$proof"
  ); then
    fail "EasyCrypt $label failed"
  fi
}

main() {
  require_command bash
  require_command easycrypt
  require_command grep

  require_file "$PRIME_PROOF"
  require_file "$ALGEBRA_PROOF"
  require_file "$BRIDGE_PROOF"
  require_file "$PROOF_DIR/Makefile"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_baseinv.py"
  require_file "$TEST_DIR/check_baseinv_vectors.py"
  require_file "$TEST_DIR/baseinv_driver.c"
  require_file "$TEST_DIR/fqinv_wrapper.c"
  require_file "$NTT_SOURCE"
  [[ -x "$BASEINV_VERIFIER" ]] || fail "missing executable baseinv predecessor verifier"

  bash -n "$0"
  reject_proof_holes
  reject_overclaims
  require_pattern "$ALGEBRA_PROOF" \
    'no C/Jasmin procedure equivalence' 'word-spec scope disclaimer'
  require_pattern "$BRIDGE_PROOF" \
    'does not connect the current C' 'baseinv bridge scope disclaimer'
  require_pattern "$NTT_SOURCE" \
    't3[[:space:]]*=[[:space:]]*fqinv\(t3\);[[:space:]]*//[[:space:]]*R\^3' \
    'correct final fqinv Montgomery scale annotation'

  require_lemma "$PRIME_PROOF" q_prime
  require_lemma "$PRIME_PROOF" exp3455_inverse
  require_lemma "$PRIME_PROOF" exp3456_one
  require_lemma "$PRIME_PROOF" pow_qminus2_inverse
  require_lemma "$PRIME_PROOF" pow_qminus1_one
  require_lemma "$PRIME_PROOF" inverse_times_unit_power
  require_lemma "$PRIME_PROOF" inverse_output_congr
  require_lemma "$ALGEBRA_PROOF" fqmul_word_spec_algebra
  require_lemma "$ALGEBRA_PROOF" fqinv_exponent_schedule
  require_lemma "$ALGEBRA_PROOF" fqinv_word_spec_power_relation_generic
  require_lemma "$ALGEBRA_PROOF" fqinv_word_spec_power_relation
  require_lemma "$ALGEBRA_PROOF" fqinv_word_spec_inverse
  require_lemma "$ALGEBRA_PROOF" fqinv_word_spec_rminus3_scaling
  require_lemma "$BRIDGE_PROOF" determinant_power_witness
  require_lemma "$BRIDGE_PROOF" baseinv_math_spec_nonzero_block_inverse

  compile_easycrypt_target "$PRIME_PROOF" "prime-field foundation"
  compile_easycrypt_target "$ALGEBRA_PROOF" "exact fqinv word chain"
  compile_easycrypt_target "$BRIDGE_PROOF" "nonzero determinant bridge"

  "$BASEINV_VERIFIER"

  printf 'PASS: axiom-free primality of q=3457 and finite-field exponent laws\n'
  printf 'PASS: exact 17-step fqinv word trace and Montgomery power accounting\n'
  printf 'PASS: every exact trace output for a nonzero q-range input is a q-range multiplicative inverse\n'
  printf 'PASS: an R^-3 determinant encoding yields its inverse with R^3 scaling\n'
  printf 'PASS: nonzero determinants instantiate the conditional quartic inverse algebra\n'
  printf 'PASS: all 3456 nonzero fqinv residues under normal and UBSan builds\n'
  printf 'PASS: complete conditional baseinv, poly_basemul, keygen, functional, and KAT regressions\n'
  printf '%s\n' \
    'SCOPE: pure exact word-trace and prime-field fqinv algebra plus fail-closed source and exhaustive executable anchoring; no formal C/Jasmin fqinv/baseinv/poly_baseinv equivalence, no theorem that the current C trace satisfies the EasyCrypt relation, no theorem that C t3 is the encoded determinant or that return 0 supplies an inverse witness, no fqinv(0) contract, universal C arithmetic-safety theorem, keygen retry/success distribution, h*f=g, serialization provenance, NTT/InvNTT high-level ring semantics, no-wrap/noise theorem, m1/r2 recovery, or full-KEM proof'
}

main "$@"
