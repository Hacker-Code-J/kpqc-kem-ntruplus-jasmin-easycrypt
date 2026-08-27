#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ring_semantics"
PROOF_FILE="$PROOF_DIR/NTRUPlus768ForwardNTTRadix3Semantics.ec"
NTT_RADIX3_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_radix3"
NTT_STAGE1_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_stage1"
POLY_BASEMUL_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/poly_basemul"
BASEMUL_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/basemul"
SCHEDULE_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_schedule"
FQINV_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/fqinv"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-forward-ntt-radix3-semantics.XXXXXX")

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
    "$PROOF_DIR" "$NTT_RADIX3_PROOF_DIR" "$NTT_STAGE1_PROOF_DIR" \
    "$POLY_BASEMUL_PROOF_DIR" "$BASEMUL_PROOF_DIR" \
    "$SCHEDULE_PROOF_DIR" "$FQINV_PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "forward-NTT radix-3 semantics proof tree contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the proof tree for holes"
  fi
}

compile_easycrypt_via_makefile() {
  local easycrypt_bin

  easycrypt_bin=$(command -v easycrypt)
  if ! make -C "$PROOF_DIR" forward-radix3 EASYCRYPT="$easycrypt_bin"; then
    fail "EasyCrypt forward-NTT radix-3 semantics proof failed"
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
  require_lemma segment_poly_split3
  require_lemma radix3_eval_factor_eqm
  require_lemma stage1_low_modulus_split3
  require_lemma stage1_high_modulus_split3
  require_lemma radix3_first_child0_eqm
  require_lemma radix3_first_child1_eqm
  require_lemma radix3_first_child2_eqm
  require_lemma radix3_second_child0_eqm
  require_lemma radix3_second_child1_eqm
  require_lemma radix3_second_child2_eqm
  require_lemma linear3_remainder_radix3_evalE
  require_lemma radix3_segment_0_evalE
  require_lemma radix3_segment_128_evalE
  require_lemma radix3_segment_256_evalE
  require_lemma radix3_segment_384_evalE
  require_lemma radix3_segment_512_evalE
  require_lemma radix3_segment_640_evalE
  require_lemma radix3_algebra_refines_stage1_semantics
  require_lemma radix3_spec_semantics
  require_lemma ntt_radix3_semantics_functional
  require_lemma ntt_radix3_correct_semantics
  reject_proof_holes

  "$REPO_ROOT/scripts/verify-ntruplus768-forward-ntt-stage1-semantics.sh"
  "$REPO_ROOT/scripts/verify-ntruplus768-ntt-radix3.sh"
  compile_easycrypt_via_makefile

  printf 'PASS: both degree-384 stage1 factors split into three degree-128 factors\n'
  printf 'PASS: all six radix-3 output segments represent the input polynomial\n'
  printf 'PASS: executable Jasmin radix-3 preserves the refined polynomial semantics\n'
  printf 'PASS: EasyCrypt NTRU+768 forward-NTT radix-3 semantics\n'
}

main "$@"
