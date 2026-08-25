#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
JASMIN_SOURCE="$REPO_ROOT/ntruplus/jasmin/768/ref/poly_baseinv.jazz"
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/poly_baseinv_jasmin"
PROOF="$PROOF_DIR/NTRUPlus768PolyBaseInvProof.ec"
EXTRACTED_DIR="$PROOF_DIR/extracted"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/poly_baseinv_jasmin"
PREDECESSOR="$SCRIPT_DIR/verify-ntruplus768-baseinv-jasmin.sh"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-poly-baseinv-jasmin.XXXXXX")

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

require_file() {
  [[ -f "$1" ]] || fail "missing required file: $1"
}

require_lemma() {
  local lemma=$1

  grep -Eq "^lemma[[:space:]]+$lemma([[:space:](]|$)" "$PROOF" ||
    fail "missing required EasyCrypt lemma: $lemma"
}

require_pattern() {
  local file=$1
  local pattern=$2
  local label=$3

  grep -Eq -- "$pattern" "$file" || fail "missing required $label"
}

compare_extraction_set() {
  local expected="$WORKDIR/expected.txt"
  local actual="$WORKDIR/actual.txt"

  printf '%s\n' \
    Array4.ec \
    Array768.ec \
    Array96.ec \
    NTRUPlus768PolyBaseInv.ec \
    WArray1536.ec \
    WArray192.ec \
    WArray8.ec >"$expected"
  sort "$expected" -o "$expected"
  find "$EXTRACTED_DIR" -maxdepth 1 -type f -name '*.ec' -printf '%f\n' | sort >"$actual"

  if ! cmp -s "$expected" "$actual"; then
    diff -u "$expected" "$actual" >&2 || true
    fail "tracked extraction file set changed"
  fi
}

main() {
  require_command bash
  require_command cmp
  require_command diff
  require_command easycrypt
  require_command find
  require_command grep
  require_command jasminc
  require_command make
  require_command python3
  require_command sort
  require_command "${CC:-cc}"

  require_file "$JASMIN_SOURCE"
  require_file "$PROOF"
  require_file "$PROOF_DIR/Makefile"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$EXTRACTED_DIR/NTRUPlus768PolyBaseInv.ec"
  require_file "$EXTRACTED_DIR/Array4.ec"
  require_file "$EXTRACTED_DIR/Array96.ec"
  require_file "$EXTRACTED_DIR/Array768.ec"
  require_file "$EXTRACTED_DIR/WArray1536.ec"
  require_file "$EXTRACTED_DIR/WArray192.ec"
  require_file "$EXTRACTED_DIR/WArray8.ec"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_poly_baseinv_jasmin.py"
  require_file "$TEST_DIR/poly_baseinv_diff.c"
  [[ -x "$PREDECESSOR" ]] || fail "missing executable baseinv Jasmin predecessor verifier"

  bash -n "$0"
  compare_extraction_set

  require_pattern "$PROOF" 'fail-closed zeroization outcomes' 'failure-zeroing scope statement'
  require_pattern "$PROOF" 'no CT or SCT claim' 'CT/SCT scope disclaimer'
  require_pattern "$JASMIN_SOURCE" 'status != 1' 'second-block skip on early failure'
  require_pattern "$JASMIN_SOURCE" 'i < NTRUPLUS_N / 8' '96-pair schedule'
  require_pattern "$JASMIN_SOURCE" 'rp = __poly_baseinv_zero\(rp\)' 'failure zeroization helper call'
  require_pattern "$PROOF_DIR/Makefile" '-auto-spill-all' 'auto-spill proof build contract'
  require_pattern "$TEST_DIR/Makefile" '-auto-spill-all' 'auto-spill test build contract'

  require_lemma poly_baseinv_apply_functional
  require_lemma poly_baseinv_pair_functional
  require_lemma poly_baseinv_zero_functional
  require_lemma poly_baseinv_functional
  require_lemma poly_exact_success_implies_poly_baseinv_success
  require_lemma poly_baseinv_exact_success_semantic
  require_lemma poly_baseinv_success_bridge
  require_lemma poly_baseinv_output_qrange_on_success
  require_lemma poly_baseinv_product_identity_on_success

  jasmin2ec "$JASMIN_SOURCE" --array-model=old \
    -o "$WORKDIR/NTRUPlus768PolyBaseInv.ec" -f __poly_baseinv_core
  cmp -s "$WORKDIR/NTRUPlus768PolyBaseInv.ec" "$EXTRACTED_DIR/NTRUPlus768PolyBaseInv.ec" ||
    fail "tracked poly_baseinv EasyCrypt extraction is stale"
  make -C "$PROOF_DIR" OUTDIR="$WORKDIR/proof" check
  jasminc -auto-spill-all -arch x86-64 -call-conv linux -system linux \
    -slice jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv \
    -o "$WORKDIR/poly_baseinv.s" "$JASMIN_SOURCE"
  jasminc -auto-spill-all -arch x86-64 -call-conv linux -system linux -checksafety \
    -slice jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv \
    -o "$WORKDIR/poly_baseinv-safety.s" "$JASMIN_SOURCE"

  make -C "$TEST_DIR" OUTDIR="$WORKDIR/test" all
  "$PREDECESSOR"

  printf 'PASS: NTRU+768 poly_baseinv Jasmin pair-fold realization and extracted EasyCrypt proof\n'
  printf 'PASS: tracked 7-file extraction set present and fresh core extraction matches the source\n'
  printf 'PASS: jasminc build and safety checks require -auto-spill-all for this register-heavy source\n'
  printf 'PASS: structural checker fixes the 96-entry zeta table, block/apply/pair/zero/core/export contract, and rejects CT/SCT annotations\n'
  printf 'PASS: 17 fixed and 32 random full-polynomial cases match production C under normal and UBSan builds\n'
  printf 'PASS: disjoint inputs stay immutable, success outputs stay strict-q-range and blockwise inverse, failures zero disjoint and alias outputs\n'
  printf 'PASS: aliasing matches disjoint success output and zeroes in-place on failure\n'
  printf 'PASS: complete baseinv Jasmin predecessor verifier chain\n'
  printf '%s\n' \
    'SCOPE: formal proof-facing Jasmin poly_baseinv core plus executable production-C differential anchoring; no formal production-C semantics or C/Jasmin equivalence, and no CT/SCT claim because determinant-driven early failure is secret-dependent'
}

main "$@"
