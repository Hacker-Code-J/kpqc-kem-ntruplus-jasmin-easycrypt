#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/fqinv"
WORD_PROOF="$PROOF_DIR/NTRUPlus768BaseInvWordAlgebra.ec"
FQINV_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-fqinv.sh"
BASEINV_TEST_DIR="$REPO_ROOT/tests/ntruplus768/baseinv"
BASEINV_SOURCE="$REPO_ROOT/NTRU+/NTRU+768/ntt.c"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-baseinv-word.XXXXXX")

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
      '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry|abort)([^[:alnum:]_]|$)' \
      "$PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "fqinv/baseinv-word theories contain a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan theories for proof holes"
  fi
}

reject_overclaims() {
  local findings="$WORKDIR/overclaims.txt"
  local pattern='^lemma[[:space:]]+.*(c_baseinv|jasmin_baseinv|baseinv_return|poly_baseinv|keygen|decap_m1|decap_r2|m1_recovery|r2_recovery|no_wrap|determinant_zero_implies_trace5_zero|trace5_zero_iff|trace5_iff)'

  if grep -En "$pattern" "$WORD_PROOF" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "baseinv word proof contains a C/Jasmin, return-code, converse, or downstream overclaim"
  fi
}

compile_easycrypt_target() {
  if ! (
    cd "$PROOF_DIR"
    easycrypt compile -no-eco -p Z3 -timeout 10 -max-provers 1 \
      "$WORD_PROOF"
  ); then
    fail "EasyCrypt scalar baseinv word trace failed"
  fi
}

main() {
  require_command bash
  require_command easycrypt
  require_command grep

  require_file "$WORD_PROOF"
  require_file "$PROOF_DIR/Makefile"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$BASEINV_TEST_DIR/Makefile"
  require_file "$BASEINV_TEST_DIR/check_baseinv.py"
  require_file "$BASEINV_TEST_DIR/check_baseinv_vectors.py"
  require_file "$BASEINV_SOURCE"
  [[ -x "$FQINV_VERIFIER" ]] || fail "missing executable fqinv predecessor verifier"

  bash -n "$0"
  reject_proof_holes
  reject_overclaims

  require_pattern "$WORD_PROOF" \
    'pure relational word spec' 'pure-word scope disclaimer'
  require_pattern "$WORD_PROOF" \
    'no formal C/Jasmin procedure equivalence' 'C/Jasmin scope disclaimer'
  require_pattern "$WORD_PROOF" \
    'return-code theorem' 'return-code scope disclaimer'
  require_pattern "$WORD_PROOF" \
    'not the converse' 'one-way failure scope disclaimer'
  require_pattern "$WORD_PROOF" \
    'strict q-range.*explicit premise' 'explicit final q-range premise disclaimer'
  require_pattern "$WORD_PROOF" \
    '4 \* q \* q < R %/ 2 \* q' 'four-q-squared Montgomery bound'
  require_pattern "$WORD_PROOF" \
    'inverse_determinant a z \* exp Rinv 3' 'R^-3 determinant encoding'

  require_lemma "$WORD_PROOF" mred_word_spec_algebra
  require_lemma "$WORD_PROOF" square_minus_double_product_bound
  require_lemma "$WORD_PROOF" square_plus_product_minus_double_product_bound
  require_lemma "$WORD_PROOF" baseinv_trace0
  require_lemma "$WORD_PROOF" baseinv_trace1
  require_lemma "$WORD_PROOF" baseinv_trace2
  require_lemma "$WORD_PROOF" baseinv_trace3
  require_lemma "$WORD_PROOF" baseinv_trace4
  require_lemma "$WORD_PROOF" baseinv_trace5
  require_lemma "$WORD_PROOF" determinant_nonzero_implies_trace5_nonzero
  require_lemma "$WORD_PROOF" trace5_zero_implies_determinant_zero
  require_lemma "$WORD_PROOF" baseinv_trace6789
  require_lemma "$WORD_PROOF" baseinv_word_trace_inverse_relation
  require_lemma "$WORD_PROOF" baseinv_word_trace_block_inverse

  compile_easycrypt_target
  "$FQINV_VERIFIER"

  printf 'PASS: exact pure 14-reduction scalar baseinv word trace and Montgomery scale accounting\n'
  printf 'PASS: every scalar reduction input is bounded by 4*q^2 and fits its verified precondition\n'
  printf 'PASS: raw determinant-word zero implies mathematical determinant zero modulo q\n'
  printf 'PASS: nonzero determinant plus the exact fqinv trace yields the quartic block inverse\n'
  printf 'PASS: exhaustive fqinv, conditional baseinv, UBSan, functional, and KAT predecessors\n'
  printf '%s\n' \
    'SCOPE: pure relational word specification matching the seam-checked scalar source body, with final strict q-range explicit; no formal C/Jasmin baseinv realization, no current C return-code theorem, no converse from determinant residue zero to raw trace5 zero, no full poly_baseinv correctness, keygen retry/success distribution, h*f=g, serialization provenance, NTT/InvNTT high-level ring semantics, no-wrap/noise theorem, m1/r2 recovery, or full-KEM proof'
}

main "$@"
