#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ring_semantics"
PROOF_FILE="$PROOF_DIR/NTRUPlus768ForwardNTTStage1Semantics.ec"
NTT_STAGE1_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_stage1"
POLY_BASEMUL_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/poly_basemul"
BASEMUL_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/basemul"
SCHEDULE_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_schedule"
FQINV_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/fqinv"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-forward-ntt-stage1-semantics.XXXXXX")

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
    "$PROOF_DIR" "$NTT_STAGE1_PROOF_DIR" "$POLY_BASEMUL_PROOF_DIR" \
    "$BASEMUL_PROOF_DIR" "$SCHEDULE_PROOF_DIR" "$FQINV_PROOF_DIR" \
    >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "forward-NTT stage1 semantics proof tree contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the proof tree for holes"
  fi
}

compile_easycrypt_via_makefile() {
  local easycrypt_bin

  easycrypt_bin=$(command -v easycrypt)
  if ! make -C "$PROOF_DIR" forward-stage1 EASYCRYPT="$easycrypt_bin"; then
    fail "EasyCrypt forward-NTT stage1 semantics proof failed"
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
  require_lemma factor_eqm_refl
  require_lemma factor_eqm_sym
  require_lemma factor_eqm_trans
  require_lemma factor_eqm_add
  require_lemma factor_eqm_mul
  require_lemma stage1_root_field_96
  require_lemma stage1_other_root_field_480
  require_lemma stage1_factor_moduli_global
  require_lemma stage1_remainder_polyE
  require_lemma stage1_low_segment_polyE
  require_lemma stage1_high_segment_polyE
  require_lemma stage1_remainder_factor_eqm
  require_lemma stage1_low_factor_eqm
  require_lemma stage1_high_factor_eqm
  require_lemma stage1_algebra_implies_semantics
  require_lemma stage1_spec_semantics
  require_lemma ntt_stage1_semantics_functional
  require_lemma ntt_stage1_correct_semantics
  reject_proof_holes

  "$REPO_ROOT/scripts/verify-ntruplus768-terminal-representation.sh"
  "$REPO_ROOT/scripts/verify-ntruplus768-ntt-stage1.sh"
  compile_easycrypt_via_makefile

  printf 'PASS: the two stage1 factor moduli multiply to the global modulus\n'
  printf 'PASS: both 384-coefficient output halves represent the input polynomial\n'
  printf 'PASS: executable Jasmin stage1 satisfies the polynomial split semantics\n'
  printf 'PASS: EasyCrypt NTRU+768 forward-NTT stage1 semantics\n'
}

main "$@"
