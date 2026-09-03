#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ring_semantics"
M1_PROOF_FILE="$PROOF_DIR/NTRUPlus768ValidKeyDecapM1Semantics.ec"
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
ENCAP_BASEMUL_ADD_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/encap_poly_basemul_add"
ENCAP_BASEMUL_ADD_PROOF_FILE="$ENCAP_BASEMUL_ADD_PROOF_DIR/NTRUPlus768EncapPolyBasemulAddAlgebra.ec"
BASEMUL_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/basemul"
SCHEDULE_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_schedule"
FQINV_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/fqinv"

CACHE_FILES=(
  "${M1_PROOF_FILE%.ec}.eco"
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
  "${ENCAP_BASEMUL_ADD_PROOF_FILE%.ec}.eco"
)

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-valid-key-decap-m1.XXXXXX")

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

  grep -Eq "^lemma[[:space:]]+$lemma([[:space:](]|$)" "$M1_PROOF_FILE" ||
    fail "missing required EasyCrypt lemma: $lemma"
}

require_operation() {
  local operation=$1

  grep -Eq "^op[[:space:]]+$operation([[:space:](]|$)" "$M1_PROOF_FILE" ||
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
    "$ENCAP_BASEMUL_ADD_PROOF_DIR" "$BASEMUL_PROOF_DIR" \
    "$SCHEDULE_PROOF_DIR" "$FQINV_PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "valid-key decapsulation m1 proof tree contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the proof tree for holes"
  fi
}

compile_easycrypt_via_makefile() {
  local easycrypt_bin

  easycrypt_bin=$(command -v easycrypt)
  if ! make -C "$PROOF_DIR" valid-key-decap-m1 EASYCRYPT="$easycrypt_bin"; then
    fail "EasyCrypt valid-key decapsulation m1 semantics proof failed"
  fi
}

main() {
  require_command bash
  require_command easycrypt
  require_command grep
  require_command make

  [[ -f "$M1_PROOF_FILE" ]] || fail "missing EasyCrypt proof: $M1_PROOF_FILE"
  [[ -f "$PROOF_DIR/Makefile" ]] || fail "missing proof Makefile"

  rm -f "${CACHE_FILES[@]}"

  bash -n "$0"
  require_operation valid_key_decap_m1_semantics
  require_lemma poly_basemul_add_qring_block_eqm4
  require_lemma poly_basemul_add_qring_represents_product_plus
  require_lemma terminal_valid_key_decap_product_local
  require_lemma terminal_valid_key_decap_product
  require_lemma valid_key_decap_m1_local_spec_semantics
  require_lemma valid_key_decap_m1_spec_semantics
  reject_proof_holes

  # Keygen/encapsulation/decapsulation implementation checks remain separate.
  # This target rebuilds the complete polynomial-semantics dependency chain.
  compile_easycrypt_via_makefile

  printf 'PASS: poly_basemul_add lifts to terminal representation of H*R+M\n'
  printf 'PASS: valid-key composition needs no global polynomial representative for h\n'
  printf 'PASS: the local valid-key relation h*f=g rewrites every terminal quartic\n'
  printf 'PASS: the decapsulation product represents G*R+M*F without global CRT injectivity\n'
  printf 'PASS: inverse NTT reconstructs the valid-key pre-crepmod3 m1 polynomial\n'
  printf 'PASS: EasyCrypt NTRU+768 valid-key decapsulation m1 semantics\n'
}

main "$@"
