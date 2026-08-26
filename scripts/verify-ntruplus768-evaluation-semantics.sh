#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ring_semantics"
PROOF_FILE="$PROOF_DIR/NTRUPlus768EvaluationSemantics.ec"
POLY_BASEMUL_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/poly_basemul"
BASEMUL_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/basemul"
SCHEDULE_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_schedule"
FQINV_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/fqinv"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-evaluation-semantics.XXXXXX")

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

require_lemma() {
  local lemma=$1

  grep -Eq "^lemma[[:space:]]+$lemma([[:space:](]|$)" "$PROOF_FILE" ||
    fail "missing required EasyCrypt lemma: $lemma"
}

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
    '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
    "$PROOF_DIR" "$POLY_BASEMUL_PROOF_DIR" "$BASEMUL_PROOF_DIR" \
    "$SCHEDULE_PROOF_DIR" "$FQINV_PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "evaluation-semantics proof tree contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the proof tree for holes"
  fi
}

compile_easycrypt_via_makefile() {
  local easycrypt_bin

  easycrypt_bin=$(command -v easycrypt)
  if ! make -C "$PROOF_DIR" evaluation EASYCRYPT="$easycrypt_bin"; then
    fail "EasyCrypt terminal quotient-ring semantics proof failed"
  fi
}

main() {
  require_command bash
  require_command easycrypt
  require_command grep
  require_command make

  [[ -f "$PROOF_FILE" ]] || fail "missing EasyCrypt proof: $PROOF_FILE"
  [[ -f "$PROOF_DIR/Makefile" ]] || fail "missing proof Makefile"

  bash -n "$0"
  require_lemma eqm4_refl
  require_lemma eqm4_sym
  require_lemma eqm4_trans
  require_lemma eqm4_add
  require_lemma eqm4_mul
  require_lemma terminal_quartic_product_global
  require_lemma quartic_modulus_divides_global
  require_lemma global_modulus_eqm4_zero
  require_lemma block_product_split
  require_lemma reduced_block_poly_split
  require_lemma reduced_product_factor
  require_lemma poly_basemul_qring_block_eqm4
  require_lemma poly_basemul_qring_all_blocks_eqm4
  reject_proof_holes

  "$REPO_ROOT/scripts/verify-ntruplus768-poly-basemul.sh"
  "$REPO_ROOT/scripts/verify-ntruplus768-cyclotomic-factorization.sh"
  compile_easycrypt_via_makefile

  printf 'PASS: terminal quotient relation is an additive and multiplicative congruence\n'
  printf 'PASS: every terminal quartic divides the global NTRU+768 modulus\n'
  printf 'PASS: verified poly_basemul coefficient contracts lift to all 192 quotient rings\n'
  printf 'PASS: EasyCrypt NTRU+768 terminal evaluation semantics\n'
}

main "$@"
