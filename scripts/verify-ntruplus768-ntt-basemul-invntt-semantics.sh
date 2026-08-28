#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ring_semantics"
HEADLINE_PROOF_FILE="$PROOF_DIR/NTRUPlus768NTTBasemulInvNTTSemantics.ec"
ROUNDTRIP_PROOF_FILE="$PROOF_DIR/NTRUPlus768NTTRoundtripSemantics.ec"
INVERSE_PROOF_FILE="$PROOF_DIR/NTRUPlus768InverseNTTSemantics.ec"
FORWARD_PROOF_FILE="$PROOF_DIR/NTRUPlus768ForwardNTTSemantics.ec"
FINAL_PROOF_FILE="$PROOF_DIR/NTRUPlus768InverseNTTFinalSemantics.ec"
FINAL_RECOMBINATION_FILE="$PROOF_DIR/NTRUPlus768InverseNTTFinalRecombination.ec"
FINAL_INTERPOLATION_FILE="$PROOF_DIR/NTRUPlus768InverseNTTFinalInterpolation.ec"
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

NTT_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt"
INVNTT_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt"
INVNTT_RADIX2_4_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_4"
INVNTT_RADIX2_8_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_8"
INVNTT_RADIX2_16_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_16"
INVNTT_RADIX2_32_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_32"
INVNTT_RADIX2_64_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_64"
INVNTT_RADIX3_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix3"
INVNTT_FINAL_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt_final"
NTT_RADIX2_4_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_radix2_4"
NTT_RADIX2_8_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_radix2_8"
NTT_RADIX2_16_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_radix2_16"
NTT_RADIX2_32_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_radix2_32"
NTT_RADIX2_64_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_radix2_64"
NTT_RADIX3_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_radix3"
NTT_STAGE1_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_stage1"
POLY_BASEMUL_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/poly_basemul"
POLY_BASEMUL_INVNTT_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/poly_basemul_invntt"
BASEMUL_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/basemul"
SCHEDULE_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_schedule"
FQINV_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/fqinv"

CACHE_FILES=(
  "${HEADLINE_PROOF_FILE%.ec}.eco"
  "${ROUNDTRIP_PROOF_FILE%.ec}.eco"
  "${INVERSE_PROOF_FILE%.ec}.eco"
  "${FORWARD_PROOF_FILE%.ec}.eco"
  "${FINAL_PROOF_FILE%.ec}.eco"
  "${FINAL_RECOMBINATION_FILE%.ec}.eco"
  "${FINAL_INTERPOLATION_FILE%.ec}.eco"
  "${RADIX3_PROOF_FILE%.ec}.eco"
  "${RADIX3_RECOMBINATION_FILE%.ec}.eco"
  "${RADIX3_INTERPOLATION_FILE%.ec}.eco"
  "${STEP64_PROOF_FILE%.ec}.eco"
  "${STEP64_RECOMBINATION_FILE%.ec}.eco"
  "${STEP32_PROOF_FILE%.ec}.eco"
  "${STEP32_RECOMBINATION_FILE%.ec}.eco"
  "${STEP16_PROOF_FILE%.ec}.eco"
  "${STEP16_RECOMBINATION_FILE%.ec}.eco"
  "${STEP8_PROOF_FILE%.ec}.eco"
  "${STEP8_RECOMBINATION_FILE%.ec}.eco"
  "${STEP4_PROOF_FILE%.ec}.eco"
  "${STEP4_RECOMBINATION_FILE%.ec}.eco"
)

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-ntt-basemul-invntt.XXXXXX")

cleanup() {
  rm -f "${CACHE_FILES[@]}"
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

  grep -Eq "^lemma[[:space:]]+$lemma([[:space:](]|$)" "$HEADLINE_PROOF_FILE" ||
    fail "missing required EasyCrypt lemma: $lemma"
}

require_operation() {
  local operation=$1

  grep -Eq "^op[[:space:]]+$operation([[:space:](]|$)" "$HEADLINE_PROOF_FILE" ||
    fail "missing required EasyCrypt operation: $operation"
}

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
    '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
    "$PROOF_DIR" "$NTT_PROOF_DIR" "$INVNTT_PROOF_DIR" \
    "$INVNTT_RADIX2_4_PROOF_DIR" "$INVNTT_RADIX2_8_PROOF_DIR" \
    "$INVNTT_RADIX2_16_PROOF_DIR" "$INVNTT_RADIX2_32_PROOF_DIR" \
    "$INVNTT_RADIX2_64_PROOF_DIR" "$INVNTT_RADIX3_PROOF_DIR" \
    "$INVNTT_FINAL_PROOF_DIR" "$NTT_RADIX2_4_PROOF_DIR" \
    "$NTT_RADIX2_8_PROOF_DIR" "$NTT_RADIX2_16_PROOF_DIR" \
    "$NTT_RADIX2_32_PROOF_DIR" "$NTT_RADIX2_64_PROOF_DIR" \
    "$NTT_RADIX3_PROOF_DIR" "$NTT_STAGE1_PROOF_DIR" \
    "$POLY_BASEMUL_PROOF_DIR" "$POLY_BASEMUL_INVNTT_PROOF_DIR" \
    "$BASEMUL_PROOF_DIR" "$SCHEDULE_PROOF_DIR" "$FQINV_PROOF_DIR" \
    >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "NTT/Basemul/InvNTT semantics proof tree contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the proof tree for holes"
  fi
}

compile_easycrypt_via_makefile() {
  local easycrypt_bin

  easycrypt_bin=$(command -v easycrypt)
  if ! make -C "$PROOF_DIR" ntt-basemul-invntt EASYCRYPT="$easycrypt_bin"; then
    fail "EasyCrypt NTT/Basemul/InvNTT semantics proof failed"
  fi
}

main() {
  require_command bash
  require_command easycrypt
  require_command grep
  require_command make

  [[ -f "$HEADLINE_PROOF_FILE" ]] ||
    fail "missing EasyCrypt proof: $HEADLINE_PROOF_FILE"
  [[ -f "$PROOF_DIR/Makefile" ]] || fail "missing proof Makefile"

  rm -f "${CACHE_FILES[@]}"

  bash -n "$0"
  require_operation ntt_basemul_invntt_semantics
  require_lemma forward_ntt_spec_poly_basemul_input_shape
  require_lemma terminal_product_inverse_spec_semantics
  require_lemma ntt_basemul_invntt_spec_product
  reject_proof_holes

  # Implementation checks remain separate top-level commands. This target
  # rebuilds the complete polynomial-semantics dependency chain once.
  compile_easycrypt_via_makefile

  printf 'PASS: both forward NTT specifications satisfy the poly_basemul q-range contract\n'
  printf 'PASS: exact poly_basemul words refine the terminal quotient-ring product\n'
  printf 'PASS: inverse NTT reconstructs the represented product modulo X^768-X^384+1\n'
  printf 'PASS: InvNTT(Basemul(NTT(a),NTT(b))) recovers a*b in the global quotient ring\n'
  printf 'PASS: EasyCrypt NTRU+768 NTT/Basemul/InvNTT polynomial semantics\n'
}

main "$@"
