#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
JASMIN_DIR="$REPO_ROOT/ntruplus/jasmin/768/ref"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/basemul"
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/basemul"
TRACKED_EXTRACTED="$PROOF_DIR/extracted"
FORMOSA_ECLIB="$REPO_ROOT/external/formosa-mlkem/proof/eclib"
FORMOSA_COMMON="$REPO_ROOT/external/formosa-mlkem/crypto-specs/common"
JASMIN_SOURCE="$JASMIN_DIR/basemul.jazz"
SLICE=jade_ntruplus_ntruplus768_amd64_ref_basemul

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-basemul.XXXXXX")

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

compare_extraction() {
  local generated_dir=$1
  local name

  for name in Array4.ec NTRUPlus768Basemul.ec WArray8.ec; do
    if ! cmp -s "$generated_dir/$name" "$TRACKED_EXTRACTED/$name"; then
      diff -u "$TRACKED_EXTRACTED/$name" "$generated_dir/$name" | sed -n '1,80p' >&2 || true
      fail "tracked EasyCrypt extraction is stale: $name"
    fi
  done
}

main() {
  local generated_dir="$WORKDIR/extracted"

  require_command make
  require_command jasminc
  require_command jasmin-ct
  require_command jasmin2ec
  require_command easycrypt
  require_command "${CC:-cc}"

  [[ -f "$FORMOSA_ECLIB/Montgomery.ec" ]] ||
    fail "Formosa proof dependency is missing; initialize recursive submodules"
  [[ -f "$FORMOSA_COMMON/JWord_extra.ec" ]] ||
    fail "Formosa crypto-specs dependency is missing; initialize recursive submodules"

  make -C "$JASMIN_DIR" OUTDIR="$WORKDIR/asm" asm safety ct sct
  make -C "$TEST_DIR" OUTDIR="$WORKDIR/test" run ubsan

  mkdir -p "$generated_dir"
  jasmin2ec "$JASMIN_SOURCE" --array-model=old \
    -o "$generated_dir/NTRUPlus768Basemul.ec" -f "$SLICE"
  compare_extraction "$generated_dir"

  easycrypt compile -no-eco -I "$generated_dir" -I "$PROOF_DIR" \
    -I "$FORMOSA_ECLIB" -I "$FORMOSA_COMMON" \
    "$PROOF_DIR/NTRUPlus768BasemulProof.ec"
  easycrypt compile -no-eco -I "$generated_dir" -I "$PROOF_DIR" \
    -I "$FORMOSA_ECLIB" -I "$FORMOSA_COMMON" \
    "$PROOF_DIR/NTRUPlus768BasemulAlgebra.ec"

  printf 'PASS: NTRU+768 basemul Jasmin build and safety checks\n'
  printf 'PASS: NTRU+768 basemul CT and SCT checks\n'
  printf 'PASS: C/Jasmin differential and UBSan tests\n'
  printf 'PASS: fresh extraction matches tracked EasyCrypt model\n'
  printf 'PASS: EasyCrypt word-level functional-correctness proof\n'
  printf 'PASS: EasyCrypt Z_q[X]/(X^4-zeta) bridge proof\n'
}

main "$@"
