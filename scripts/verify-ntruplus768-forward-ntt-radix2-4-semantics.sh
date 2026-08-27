#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ring_semantics"
PROOF_FILE="$PROOF_DIR/NTRUPlus768ForwardNTTRadix2_4Semantics.ec"
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
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-forward-ntt-radix2-4-semantics.XXXXXX")

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

require_operation() {
  local operation=$1

  grep -Eq "^op[[:space:]]+$operation([[:space:](]|$)" "$PROOF_FILE" ||
    fail "missing required EasyCrypt operation: $operation"
}

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
    '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
    "$PROOF_DIR" "$NTT_RADIX2_4_PROOF_DIR" "$NTT_RADIX2_8_PROOF_DIR" \
    "$NTT_RADIX2_16_PROOF_DIR" "$NTT_RADIX2_32_PROOF_DIR" \
    "$NTT_RADIX2_64_PROOF_DIR" "$NTT_RADIX3_PROOF_DIR" \
    "$NTT_STAGE1_PROOF_DIR" "$POLY_BASEMUL_PROOF_DIR" \
    "$BASEMUL_PROOF_DIR" "$SCHEDULE_PROOF_DIR" "$FQINV_PROOF_DIR" \
    >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "forward-NTT radix2_4 semantics proof tree contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the proof tree for holes"
  fi
}

compile_easycrypt_via_makefile() {
  local easycrypt_bin

  easycrypt_bin=$(command -v easycrypt)
  if ! make -C "$PROOF_DIR" forward-radix2-4 EASYCRYPT="$easycrypt_bin"; then
    fail "EasyCrypt forward-NTT radix2_4 semantics proof failed"
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
  require_lemma segment_poly_split2_4
  require_lemma radix2_4_eval_factor_eqm
  require_lemma schedule_modulus_split2_4
  require_lemma factor_eqm_split2_4_left
  require_lemma factor_eqm_split2_4_right
  require_lemma radix2_4_pair_child0_eqm
  require_lemma radix2_4_pair_child1_eqm
  require_lemma linear2_4_remainder_polyE
  require_lemma segment_poly_radix2_4_evalE
  require_lemma radix2_4_schedule_expsE
  require_lemma radix2_4_schedule_expE
  require_lemma radix2_4_schedule_exp_terminalE
  require_lemma radix2_4_schedule_exp_nonneg
  require_lemma radix2_4_zeta_scheduleE
  require_lemma radix2_4_segment_left_evalE
  require_lemma radix2_4_segment_right_evalE
  require_lemma radix2_4_segment_factor_eqm
  require_lemma radix2_4_refine_left
  require_lemma radix2_4_refine_right
  require_lemma radix2_4_refine_block_pair
  require_lemma radix2_4_parent_expsE
  require_lemma radix2_4_parent_scheduleE
  require_lemma radix2_8_semantics_parent_at
  require_operation radix2_4_semantics
  require_lemma radix2_4_algebra_refines_radix2_8_semantics
  require_lemma radix2_4_spec_semantics
  require_lemma ntt_radix2_4_semantics_functional
  require_lemma ntt_radix2_4_correct_semantics
  require_lemma segment_poly4_block_polyE
  require_lemma factor_eqm_terminal_eqm4
  require_lemma radix2_4_semantics_terminal_represents
  require_lemma radix2_4_algebra_refines_terminal_representation
  require_lemma radix2_4_spec_terminal_represents
  require_lemma ntt_radix2_4_terminal_represents_functional
  require_lemma ntt_radix2_4_correct_terminal_represents
  reject_proof_holes

  "$REPO_ROOT/scripts/verify-ntruplus768-forward-ntt-radix2-8-semantics.sh"
  "$REPO_ROOT/scripts/verify-ntruplus768-ntt-radix2-4.sh"
  compile_easycrypt_via_makefile

  printf 'PASS: ninety-six degree-8 factors split into 192 degree-4 factors\n'
  printf 'PASS: all 192 terminal blocks represent the original input polynomial\n'
  printf 'PASS: executable Jasmin radix2_4 establishes terminal_represents\n'
  printf 'PASS: EasyCrypt NTRU+768 final-layer forward-NTT polynomial semantics\n'
}

main "$@"
