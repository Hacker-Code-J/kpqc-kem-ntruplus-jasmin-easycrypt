#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ring_semantics"
PROOF_FILE="$PROOF_DIR/NTRUPlus768InverseNTTFinalSemantics.ec"
RECOMBINATION_FILE="$PROOF_DIR/NTRUPlus768InverseNTTFinalRecombination.ec"
INTERPOLATION_FILE="$PROOF_DIR/NTRUPlus768InverseNTTFinalInterpolation.ec"
RADIX3_PROOF_FILE="$PROOF_DIR/NTRUPlus768InverseNTTRadix3Semantics.ec"
RADIX3_RECOMBINATION_FILE="$PROOF_DIR/NTRUPlus768InverseNTTRadix3Recombination.ec"
RADIX3_INTERPOLATION_FILE="$PROOF_DIR/NTRUPlus768InverseNTTRadix3Interpolation.ec"
STEP64_PROOF_FILE="$PROOF_DIR/NTRUPlus768InverseNTTRadix2_64Semantics.ec"
STEP64_RECOMBINATION_FILE="$PROOF_DIR/NTRUPlus768InverseNTTRadix2_64Recombination.ec"
STEP32_PROOF_FILE="$PROOF_DIR/NTRUPlus768InverseNTTRadix2_32Semantics.ec"
STEP32_RECOMBINATION_FILE="$PROOF_DIR/NTRUPlus768InverseNTTRadix2_32Recombination.ec"
STEP16_PROOF_FILE="$PROOF_DIR/NTRUPlus768InverseNTTRadix2_16Semantics.ec"
STEP16_RECOMBINATION_FILE="$PROOF_DIR/NTRUPlus768InverseNTTRadix2_16Recombination.ec"
STEP8_PROOF_FILE="$PROOF_DIR/NTRUPlus768InverseNTTRadix2_8Semantics.ec"
STEP8_RECOMBINATION_FILE="$PROOF_DIR/NTRUPlus768InverseNTTRadix2_8Recombination.ec"
STEP4_PROOF_FILE="$PROOF_DIR/NTRUPlus768InverseNTTRadix2_4Semantics.ec"
STEP4_RECOMBINATION_FILE="$PROOF_DIR/NTRUPlus768InverseNTTRadix2_4Recombination.ec"
FINAL_PROOF_CACHE="${PROOF_FILE%.ec}.eco"
FINAL_RECOMBINATION_CACHE="${RECOMBINATION_FILE%.ec}.eco"
FINAL_INTERPOLATION_CACHE="${INTERPOLATION_FILE%.ec}.eco"
RADIX3_PROOF_CACHE="${RADIX3_PROOF_FILE%.ec}.eco"
RADIX3_RECOMBINATION_CACHE="${RADIX3_RECOMBINATION_FILE%.ec}.eco"
RADIX3_INTERPOLATION_CACHE="${RADIX3_INTERPOLATION_FILE%.ec}.eco"
STEP64_PROOF_CACHE="${STEP64_PROOF_FILE%.ec}.eco"
STEP64_RECOMBINATION_CACHE="${STEP64_RECOMBINATION_FILE%.ec}.eco"
STEP32_PROOF_CACHE="${STEP32_PROOF_FILE%.ec}.eco"
STEP32_RECOMBINATION_CACHE="${STEP32_RECOMBINATION_FILE%.ec}.eco"
STEP16_PROOF_CACHE="${STEP16_PROOF_FILE%.ec}.eco"
STEP16_RECOMBINATION_CACHE="${STEP16_RECOMBINATION_FILE%.ec}.eco"
STEP8_PROOF_CACHE="${STEP8_PROOF_FILE%.ec}.eco"
STEP8_RECOMBINATION_CACHE="${STEP8_RECOMBINATION_FILE%.ec}.eco"
STEP4_PROOF_CACHE="${STEP4_PROOF_FILE%.ec}.eco"
STEP4_RECOMBINATION_CACHE="${STEP4_RECOMBINATION_FILE%.ec}.eco"
INVNTT_RADIX2_4_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_4"
INVNTT_RADIX2_8_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_8"
INVNTT_RADIX2_16_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_16"
INVNTT_RADIX2_32_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_32"
INVNTT_RADIX2_64_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_64"
INVNTT_RADIX3_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix3"
INVNTT_FINAL_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt_final"
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
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-invntt-final-semantics.XXXXXX")

cleanup() {
  rm -f "$FINAL_PROOF_CACHE" "$FINAL_RECOMBINATION_CACHE" \
    "$FINAL_INTERPOLATION_CACHE" \
    "$RADIX3_PROOF_CACHE" "$RADIX3_RECOMBINATION_CACHE" \
    "$RADIX3_INTERPOLATION_CACHE" \
    "$STEP64_PROOF_CACHE" "$STEP64_RECOMBINATION_CACHE" \
    "$STEP32_PROOF_CACHE" "$STEP32_RECOMBINATION_CACHE" \
    "$STEP16_PROOF_CACHE" "$STEP16_RECOMBINATION_CACHE" \
    "$STEP8_PROOF_CACHE" "$STEP8_RECOMBINATION_CACHE" \
    "$STEP4_PROOF_CACHE" "$STEP4_RECOMBINATION_CACHE"
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
    "$RECOMBINATION_FILE" "$INTERPOLATION_FILE" "$PROOF_FILE" ||
    fail "missing required EasyCrypt lemma: $lemma"
}

require_operation() {
  local operation=$1

  grep -Eq "^op[[:space:]]+$operation([[:space:](]|$)" \
    "$RECOMBINATION_FILE" "$INTERPOLATION_FILE" "$PROOF_FILE" ||
    fail "missing required EasyCrypt operation: $operation"
}

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
    '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
    "$PROOF_DIR" "$INVNTT_RADIX2_4_PROOF_DIR" "$INVNTT_RADIX2_8_PROOF_DIR" \
    "$INVNTT_RADIX2_16_PROOF_DIR" "$INVNTT_RADIX2_32_PROOF_DIR" \
    "$INVNTT_RADIX2_64_PROOF_DIR" "$INVNTT_RADIX3_PROOF_DIR" \
    "$INVNTT_FINAL_PROOF_DIR" "$NTT_RADIX2_8_PROOF_DIR" \
    "$NTT_RADIX2_16_PROOF_DIR" "$NTT_RADIX2_32_PROOF_DIR" \
    "$NTT_RADIX2_64_PROOF_DIR" "$NTT_RADIX3_PROOF_DIR" \
    "$NTT_STAGE1_PROOF_DIR" "$POLY_BASEMUL_PROOF_DIR" "$BASEMUL_PROOF_DIR" \
    "$SCHEDULE_PROOF_DIR" "$FQINV_PROOF_DIR" \
    >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "inverse-NTT final semantics proof tree contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the proof tree for holes"
  fi
}

compile_easycrypt_via_makefile() {
  local easycrypt_bin

  easycrypt_bin=$(command -v easycrypt)
  if ! make -C "$PROOF_DIR" inverse-final EASYCRYPT="$easycrypt_bin"; then
    fail "EasyCrypt inverse-NTT final semantics proof failed"
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
  [[ -f "$INTERPOLATION_FILE" ]] ||
    fail "missing EasyCrypt proof: $INTERPOLATION_FILE"
  [[ -f "$RADIX3_PROOF_FILE" ]] ||
    fail "missing predecessor EasyCrypt proof: $RADIX3_PROOF_FILE"
  [[ -f "$PROOF_DIR/Makefile" ]] || fail "missing proof Makefile"

  rm -f "$FINAL_PROOF_CACHE" "$FINAL_RECOMBINATION_CACHE" \
    "$FINAL_INTERPOLATION_CACHE" \
    "$RADIX3_PROOF_CACHE" "$RADIX3_RECOMBINATION_CACHE" \
    "$RADIX3_INTERPOLATION_CACHE" \
    "$STEP64_PROOF_CACHE" "$STEP64_RECOMBINATION_CACHE" \
    "$STEP32_PROOF_CACHE" "$STEP32_RECOMBINATION_CACHE" \
    "$STEP16_PROOF_CACHE" "$STEP16_RECOMBINATION_CACHE" \
    "$STEP8_PROOF_CACHE" "$STEP8_RECOMBINATION_CACHE" \
    "$STEP4_PROOF_CACHE" "$STEP4_RECOMBINATION_CACHE"

  bash -n "$0"
  require_operation invntt_final_semantics
  require_lemma invntt_final_algebra_refines_invntt_radix3_semantics
  require_lemma invntt_final_spec_semantics
  require_lemma invntt_final_semantics_functional
  require_lemma invntt_final_correct_semantics
  reject_proof_holes

  # The implementation verifier is intentionally a separate top-level command.
  # This Make dependency chain recompiles the inverse semantic theories through
  # the final layer without rerunning the implementation checks.
  compile_easycrypt_via_makefile

  printf 'PASS: inverse step4, step8, step16, step32, step64, radix3, and final semantic dependencies recompile before the final layer\n'
  printf 'PASS: inverse final combines the two degree-384 residues at exponents 96 and 480\n'
  printf 'PASS: inverse final cancels factor96 and recovers eqm_global p (input_poly output)\n'
  printf 'PASS: semantic endpoints typecheck against the inverse final Jasmin proof\n'
  printf 'PASS: EasyCrypt NTRU+768 inverse final polynomial semantics\n'
}

main "$@"
