#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ring_semantics"
PROOF_FILE="$PROOF_DIR/NTRUPlus768InverseNTTRadix2_4Semantics.ec"
RECOMBINATION_FILE="$PROOF_DIR/NTRUPlus768InverseNTTRadix2_4Recombination.ec"
PROOF_CACHE="${PROOF_FILE%.ec}.eco"
RECOMBINATION_CACHE="${RECOMBINATION_FILE%.ec}.eco"
INVNTT_RADIX2_4_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_4"
NTT_RADIX2_4_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_radix2_4"
NTT_RADIX2_8_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_radix2_8"
NTT_RADIX2_16_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_radix2_16"
NTT_RADIX2_32_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_radix2_32"
NTT_RADIX2_64_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_radix2_64"
NTT_RADIX3_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_radix3"
NTT_STAGE1_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_stage1"
POLY_BASEMUL_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/poly_basemul"
BASEMUL_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/basemul"
SCHEDULE_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_schedule"
FQINV_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/fqinv"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-invntt-radix2-4-semantics.XXXXXX")

cleanup() {
  rm -f "$PROOF_CACHE" "$RECOMBINATION_CACHE"
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

  grep -Eq "^lemma[[:space:]]+$lemma([[:space:](]|$)" \
    "$RECOMBINATION_FILE" "$PROOF_FILE" ||
    fail "missing required EasyCrypt lemma: $lemma"
}

require_operation() {
  local operation=$1

  grep -Eq "^op[[:space:]]+$operation([[:space:](]|$)" \
    "$RECOMBINATION_FILE" "$PROOF_FILE" ||
    fail "missing required EasyCrypt operation: $operation"
}

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
    '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
    "$PROOF_DIR" "$INVNTT_RADIX2_4_PROOF_DIR" "$NTT_RADIX2_4_PROOF_DIR" \
    "$NTT_RADIX2_8_PROOF_DIR" "$NTT_RADIX2_16_PROOF_DIR" \
    "$NTT_RADIX2_32_PROOF_DIR" "$NTT_RADIX2_64_PROOF_DIR" \
    "$NTT_RADIX3_PROOF_DIR" "$NTT_STAGE1_PROOF_DIR" \
    "$POLY_BASEMUL_PROOF_DIR" "$BASEMUL_PROOF_DIR" \
    "$SCHEDULE_PROOF_DIR" "$FQINV_PROOF_DIR" \
    >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "inverse-NTT radix2_4 semantics proof tree contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the proof tree for holes"
  fi
}

compile_easycrypt_via_makefile() {
  local easycrypt_bin

  easycrypt_bin=$(command -v easycrypt)
  if ! make -C "$PROOF_DIR" inverse-radix2-4 EASYCRYPT="$easycrypt_bin"; then
    fail "EasyCrypt inverse-NTT radix2_4 semantics proof failed"
  fi
}

main() {
  require_command bash
  require_command easycrypt
  require_command grep
  require_command make

  [[ -f "$PROOF_FILE" ]] || fail "missing EasyCrypt proof: $PROOF_FILE"
  [[ -f "$RECOMBINATION_FILE" ]] ||
    fail "missing EasyCrypt proof: $RECOMBINATION_FILE"
  [[ -f "$PROOF_DIR/Makefile" ]] || fail "missing proof Makefile"

  rm -f "$PROOF_CACHE" "$RECOMBINATION_CACHE"

  bash -n "$0"
  require_lemma invntt_radix2_4_schedule_expE
  require_lemma terminal_exp_reverse_sum_288
  require_lemma invntt_radix2_4_schedule_sumE
  require_lemma invntt_radix2_4_schedule_nonneg
  require_lemma invntt_radix2_4_root_cancelE
  require_lemma terminal_represents_factor_eqm_left
  require_lemma terminal_represents_factor_eqm_right
  require_lemma invntt_radix2_4_segment_leftE
  require_operation invntt_radix2_4_scaled_diff_poly
  require_lemma invntt_radix2_4_scaled_diff_polyE
  require_lemma segment_poly_scaled_diffE
  require_lemma invntt_radix2_4_segment_rightE
  require_lemma invntt_radix2_4_output_segmentE
  require_lemma invntt_radix2_4_interpolation_identity
  require_lemma invntt_radix2_4_abstract_recombine
  require_lemma invntt_radix2_4_recombine_factor_eqm
  require_operation invntt_radix2_4_semantics
  require_lemma invntt_radix2_4_algebra_refines_terminal_representation
  require_lemma invntt_radix2_4_spec_semantics
  require_lemma invntt_radix2_4_semantics_functional
  require_lemma invntt_radix2_4_correct_semantics
  reject_proof_holes

  "$REPO_ROOT/scripts/verify-ntruplus768-terminal-representation.sh"
  "$REPO_ROOT/scripts/verify-ntruplus768-invntt-radix2-4.sh"
  compile_easycrypt_via_makefile

  printf 'PASS: reverse schedule identifies each inverse twiddle with the complementary terminal exponent\n'
  printf 'PASS: each inverse radix2_4 block recombines two quartic terminal residues into one degree-8 residue of 2p\n'
  printf 'PASS: executable Jasmin inverse radix2_4 establishes the first inverse ring-semantics milestone\n'
  printf 'PASS: EasyCrypt NTRU+768 inverse radix2_4 polynomial semantics\n'
}

main "$@"
