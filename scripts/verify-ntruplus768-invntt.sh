#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
JASMIN_SOURCE="$REPO_ROOT/ntruplus/jasmin/768/ref/invntt.jazz"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/invntt"
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/invntt"
TRACKED_EXTRACTED="$PROOF_DIR/extracted"
BASEMUL_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/basemul"
BASEMUL_EXTRACTED="$BASEMUL_PROOF/extracted"
RADIX2_64_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/ntt_radix2_64"
RADIX2_64_EXTRACTED="$RADIX2_64_PROOF/extracted"
NTT_SCHEDULE_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/ntt_schedule"
INVNTT_RADIX2_4_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_4"
INVNTT_RADIX2_4_EXTRACTED="$INVNTT_RADIX2_4_PROOF/extracted"
INVNTT_RADIX2_8_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_8"
INVNTT_RADIX2_8_EXTRACTED="$INVNTT_RADIX2_8_PROOF/extracted"
INVNTT_RADIX2_16_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_16"
INVNTT_RADIX2_16_EXTRACTED="$INVNTT_RADIX2_16_PROOF/extracted"
INVNTT_RADIX2_32_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_32"
INVNTT_RADIX2_32_EXTRACTED="$INVNTT_RADIX2_32_PROOF/extracted"
INVNTT_RADIX2_64_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix2_64"
INVNTT_RADIX2_64_EXTRACTED="$INVNTT_RADIX2_64_PROOF/extracted"
INVNTT_RADIX3_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt_radix3"
INVNTT_RADIX3_EXTRACTED="$INVNTT_RADIX3_PROOF/extracted"
INVNTT_FINAL_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/invntt_final"
INVNTT_FINAL_EXTRACTED="$INVNTT_FINAL_PROOF/extracted"
FORMOSA_ECLIB="$REPO_ROOT/external/formosa-mlkem/proof/eclib"
FORMOSA_COMMON="$REPO_ROOT/external/formosa-mlkem/crypto-specs/common"
SLICE=jade_ntruplus_ntruplus768_amd64_ref_invntt

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-invntt.XXXXXX")

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

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status_code

  if grep -ERni --include='*.ec' \
    '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
    "$PROOF_DIR" "$BASEMUL_PROOF" "$RADIX2_64_PROOF" "$NTT_SCHEDULE_PROOF" \
    "$INVNTT_RADIX2_4_PROOF" "$INVNTT_RADIX2_8_PROOF" \
    "$INVNTT_RADIX2_16_PROOF" "$INVNTT_RADIX2_32_PROOF" \
    "$INVNTT_RADIX2_64_PROOF" "$INVNTT_RADIX3_PROOF" "$INVNTT_FINAL_PROOF" \
    >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "EasyCrypt proof trees contain a proof-hole keyword"
  else
    status_code=$?
    [[ $status_code -eq 1 ]] || fail "could not scan the EasyCrypt proof trees for holes"
  fi
}

compile_easycrypt() {
  local proof=$1
  local tag=$2

  if ! easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
    -I "$GENERATED_DIR" \
    -I "$PROOF_DIR" \
    -I "$BASEMUL_PROOF" \
    -I "$BASEMUL_EXTRACTED" \
    -I "$RADIX2_64_PROOF" \
    -I "$RADIX2_64_EXTRACTED" \
    -I "$NTT_SCHEDULE_PROOF" \
    -I "$INVNTT_RADIX2_4_PROOF" \
    -I "$INVNTT_RADIX2_4_EXTRACTED" \
    -I "$INVNTT_RADIX2_8_PROOF" \
    -I "$INVNTT_RADIX2_8_EXTRACTED" \
    -I "$INVNTT_RADIX2_16_PROOF" \
    -I "$INVNTT_RADIX2_16_EXTRACTED" \
    -I "$INVNTT_RADIX2_32_PROOF" \
    -I "$INVNTT_RADIX2_32_EXTRACTED" \
    -I "$INVNTT_RADIX2_64_PROOF" \
    -I "$INVNTT_RADIX2_64_EXTRACTED" \
    -I "$INVNTT_RADIX3_PROOF" \
    -I "$INVNTT_RADIX3_EXTRACTED" \
    -I "$INVNTT_FINAL_PROOF" \
    -I "$INVNTT_FINAL_EXTRACTED" \
    -I "$FORMOSA_ECLIB" \
    -I "$FORMOSA_COMMON" \
    "$proof"; then
    fail "EasyCrypt $tag proof failed"
  fi
}

compare_extraction() {
  local generated_dir=$1
  local expected_list="$WORKDIR/expected-extracted.txt"
  local generated_list="$WORKDIR/generated-extracted.txt"
  local name

  printf '%s\n' \
    Array768.ec \
    NTRUPlus768InvNTT.ec \
    WArray1536.ec >"$expected_list"
  find "$generated_dir" -maxdepth 1 -type f -name '*.ec' -printf '%f\n' | sort >"$generated_list"

  if ! cmp -s "$expected_list" "$generated_list"; then
    diff -u "$expected_list" "$generated_list" >&2 || true
    fail "generated extraction file set does not match expected composed inverse NTT extraction"
  fi

  while IFS= read -r name; do
    if ! cmp -s "$generated_dir/$name" "$TRACKED_EXTRACTED/$name"; then
      diff -u "$TRACKED_EXTRACTED/$name" "$generated_dir/$name" | sed -n '1,120p' >&2 || true
      fail "tracked composed inverse NTT EasyCrypt extraction is stale: $name"
    fi
  done <"$expected_list"
}

require_stage() {
  local proof_dir=$1
  local proof_name=$2
  local extracted_dir=$3
  local label=$4

  [[ -f "$proof_dir/$proof_name" ]] || fail "missing dependent $label algebra proof tree"
  [[ -d "$extracted_dir" ]] || fail "missing dependent $label extraction tree"
}

main() {
  local generated_dir="$WORKDIR/extracted"
  local asm_dir="$WORKDIR/asm"

  require_command bash
  require_command easycrypt
  require_command grep
  require_command jasmin-ct
  require_command jasmin2ec
  require_command jasminc
  require_command make
  require_command python3
  require_command "${CC:-cc}"

  [[ -f "$JASMIN_SOURCE" ]] || fail "missing composed inverse NTT Jasmin source: $JASMIN_SOURCE"
  [[ -f "$TEST_DIR/Makefile" ]] || fail "missing composed inverse NTT test Makefile"
  [[ -f "$TEST_DIR/check_invntt.py" ]] || fail "missing composed inverse NTT checker"
  [[ -f "$TEST_DIR/invntt_diff.c" ]] || fail "missing composed inverse NTT differential test"
  [[ -f "$PROOF_DIR/Makefile" ]] || fail "missing composed inverse NTT proof Makefile"
  [[ -f "$PROOF_DIR/easycrypt.project" ]] || fail "missing composed inverse NTT easycrypt.project"
  [[ -f "$PROOF_DIR/NTRUPlus768InvNTTProof.ec" ]] ||
    fail "missing composed inverse NTT word-level proof"
  [[ -f "$PROOF_DIR/NTRUPlus768InvNTTAlgebra.ec" ]] ||
    fail "missing composed inverse NTT algebra proof"
  [[ -d "$TRACKED_EXTRACTED" ]] ||
    fail "missing tracked composed inverse NTT extraction tree: $TRACKED_EXTRACTED"
  [[ -f "$FORMOSA_ECLIB/W16extra.ec" ]] ||
    fail "Formosa proof dependency is missing; initialize recursive submodules"
  [[ -f "$FORMOSA_COMMON/JWord_extra.ec" ]] ||
    fail "Formosa crypto-specs dependency is missing; initialize recursive submodules"
  [[ -f "$BASEMUL_PROOF/NTRUPlus768BasemulAlgebra.ec" ]] ||
    fail "missing dependent basemul proof tree"
  [[ -d "$BASEMUL_EXTRACTED" ]] || fail "missing dependent basemul extraction tree"
  [[ -f "$RADIX2_64_PROOF/NTRUPlus768NTTRadix2_64Algebra.ec" ]] ||
    fail "missing dependent forward radix-2 step64 algebra tree"
  [[ -d "$RADIX2_64_EXTRACTED" ]] ||
    fail "missing dependent forward radix-2 step64 extraction tree"
  [[ -f "$NTT_SCHEDULE_PROOF/NTRUPlus768NTTSchedule.ec" ]] ||
    fail "missing dependent NTT schedule proof tree"

  require_stage "$INVNTT_RADIX2_4_PROOF" \
    NTRUPlus768InvNTTRadix2_4Algebra.ec "$INVNTT_RADIX2_4_EXTRACTED" \
    "inverse radix-2 step4"
  require_stage "$INVNTT_RADIX2_8_PROOF" \
    NTRUPlus768InvNTTRadix2_8Algebra.ec "$INVNTT_RADIX2_8_EXTRACTED" \
    "inverse radix-2 step8"
  require_stage "$INVNTT_RADIX2_16_PROOF" \
    NTRUPlus768InvNTTRadix2_16Algebra.ec "$INVNTT_RADIX2_16_EXTRACTED" \
    "inverse radix-2 step16"
  require_stage "$INVNTT_RADIX2_32_PROOF" \
    NTRUPlus768InvNTTRadix2_32Algebra.ec "$INVNTT_RADIX2_32_EXTRACTED" \
    "inverse radix-2 step32"
  require_stage "$INVNTT_RADIX2_64_PROOF" \
    NTRUPlus768InvNTTRadix2_64Algebra.ec "$INVNTT_RADIX2_64_EXTRACTED" \
    "inverse radix-2 step64"
  require_stage "$INVNTT_RADIX3_PROOF" \
    NTRUPlus768InvNTTRadix3Algebra.ec "$INVNTT_RADIX3_EXTRACTED" \
    "inverse radix-3"
  require_stage "$INVNTT_FINAL_PROOF" \
    NTRUPlus768InvNTTFinalAlgebra.ec "$INVNTT_FINAL_EXTRACTED" \
    "inverse final"

  bash -n "$0"
  mkdir -p "$asm_dir" "$generated_dir"
  GENERATED_DIR=$generated_dir

  jasmin2ec "$JASMIN_SOURCE" --array-model=old \
    -o "$generated_dir/NTRUPlus768InvNTT.ec" -f "$SLICE"
  compare_extraction "$generated_dir"
  reject_proof_holes

  compile_easycrypt "$PROOF_DIR/NTRUPlus768InvNTTProof.ec" word-level
  compile_easycrypt "$PROOF_DIR/NTRUPlus768InvNTTAlgebra.ec" algebra

  jasminc -arch x86-64 -call-conv linux -system linux \
    -slice "$SLICE" -o "$asm_dir/invntt.s" "$JASMIN_SOURCE"
  jasminc -arch x86-64 -call-conv linux -system linux -checksafety \
    -slice "$SLICE" -o "$asm_dir/invntt-safety.s" "$JASMIN_SOURCE"
  jasmin-ct --slice="$SLICE" "$JASMIN_SOURCE"
  jasmin-ct --slice="$SLICE" --sct "$JASMIN_SOURCE"

  make -C "$TEST_DIR" OUTDIR="$WORKDIR/test" selfcheck run ubsan

  printf 'PASS: verify-ntruplus768-invntt.sh syntax check\n'
  printf 'PASS: NTRU+768 composed inverse-NTT C/Jasmin coupling and checker self-check\n'
  printf 'PASS: NTRU+768 composed inverse-NTT Jasmin build, safety, CT, and SCT checks\n'
  printf 'PASS: NTRU+768 composed inverse-NTT disjoint, exact-alias, differential, and UBSan tests\n'
  printf 'PASS: NTRU+768 composed inverse-NTT fresh extraction matches tracked EasyCrypt model\n'
  printf 'PASS: NTRU+768 composed inverse-NTT EasyCrypt word-level functional proof\n'
  printf 'PASS: NTRU+768 composed inverse-NTT whole-chain range and algebra proof\n'
}

main "$@"
