#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
JASMIN_SOURCE="$REPO_ROOT/ntruplus/jasmin/768/ref/fqinv.jazz"
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/fqinv_jasmin"
PROOF="$PROOF_DIR/NTRUPlus768FqInvProof.ec"
TRACKED_EXTRACTED="$PROOF_DIR/extracted"
FQINV_ALGEBRA="$REPO_ROOT/ntruplus/proof/768/ref/fqinv"
FQINV_ALGEBRA_PROOF="$FQINV_ALGEBRA/NTRUPlus768FqInvAlgebra.ec"
BASEMUL_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/basemul"
BASEMUL_EXTRACTED="$BASEMUL_PROOF/extracted"
FORMOSA_ECLIB="$REPO_ROOT/external/formosa-mlkem/proof/eclib"
FORMOSA_COMMON="$REPO_ROOT/external/formosa-mlkem/crypto-specs/common"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/fqinv_jasmin"
FQINV_PREDECESSOR="$SCRIPT_DIR/verify-ntruplus768-fqinv.sh"
SLICE=jade_ntruplus_ntruplus768_amd64_ref_fqinv

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-fqinv-jasmin.XXXXXX")

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

  grep -Eq "$pattern" "$file" || fail "missing required $label"
}

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
      '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry|abort)([^[:alnum:]_]|$)' \
      "$PROOF_DIR" "$FQINV_ALGEBRA" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "fqinv Jasmin proof tree contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan fqinv Jasmin proof tree"
  fi
}

reject_overclaims() {
  local findings="$WORKDIR/overclaims.txt"
  local pattern='^lemma[[:space:]]+.*(c_fqinv|baseinv|poly_baseinv|fqinv_zero|return_code|keygen|decap)'

  if grep -En "$pattern" "$PROOF" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "fqinv Jasmin proof contains a C, zero-input, or downstream overclaim"
  fi
}

compare_extraction() {
  local generated_dir=$1
  local expected_list="$WORKDIR/expected-extracted.txt"
  local generated_list="$WORKDIR/generated-extracted.txt"
  local name

  printf '%s\n' NTRUPlus768FqInv.ec >"$expected_list"
  find "$generated_dir" -maxdepth 1 -type f -name '*.ec' -printf '%f\n' |
    sort >"$generated_list"

  if ! cmp -s "$expected_list" "$generated_list"; then
    diff -u "$expected_list" "$generated_list" >&2 || true
    fail "generated extraction file set does not match expected fqinv extraction"
  fi

  while IFS= read -r name; do
    if ! cmp -s "$generated_dir/$name" "$TRACKED_EXTRACTED/$name"; then
      diff -u "$TRACKED_EXTRACTED/$name" "$generated_dir/$name" |
        sed -n '1,120p' >&2 || true
      fail "tracked fqinv EasyCrypt extraction is stale: $name"
    fi
  done <"$expected_list"
}

compile_easycrypt() {
  local generated_dir=$1
  local attempt

  for ((attempt = 1; attempt <= 3; ++attempt)); do
    if easycrypt compile -no-eco -p Z3 -timeout 10 -max-provers 1 \
      -I "$generated_dir" \
      -I "$PROOF_DIR" \
      -I "$FQINV_ALGEBRA" \
      -I "$BASEMUL_PROOF" \
      -I "$BASEMUL_EXTRACTED" \
      -I "$FORMOSA_ECLIB" \
      -I "$FORMOSA_COMMON" \
      "$PROOF"; then
      return
    fi
    sleep 0.2
  done
  fail "EasyCrypt extracted fqinv proof failed after three attempts"
}

main() {
  local generated_dir="$WORKDIR/extracted"
  local asm_dir="$WORKDIR/asm"

  require_command bash
  require_command cmp
  require_command easycrypt
  require_command find
  require_command grep
  require_command jasmin-ct
  require_command jasmin2ec
  require_command jasminc
  require_command make
  require_command python3
  require_command sort
  require_command "${CC:-cc}"

  require_file "$JASMIN_SOURCE"
  require_file "$PROOF"
  require_file "$TRACKED_EXTRACTED/NTRUPlus768FqInv.ec"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$FQINV_ALGEBRA_PROOF"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_fqinv_jasmin.py"
  require_file "$TEST_DIR/fqinv_diff.c"
  require_file "$FORMOSA_ECLIB/W16extra.ec"
  require_file "$FORMOSA_COMMON/JWord_extra.ec"
  [[ -x "$FQINV_PREDECESSOR" ]] || fail "missing executable fqinv predecessor verifier"

  bash -n "$0"
  reject_proof_holes
  reject_overclaims
  require_pattern "$PROOF" 'production-C' 'production-C scope disclaimer'
  require_pattern "$PROOF" 'fqinv\(0\)' 'zero-input scope disclaimer'
  require_pattern "$FQINV_ALGEBRA_PROOF" \
    '^lemma[[:space:]]+fqinv_word_spec_inverse([[:space:](]|$)' \
    'nonzero word-spec inverse theorem'

  require_lemma fqinv_mul_i16_functional
  require_lemma fqinv_montgomery_reduce_functional
  require_lemma fqinv_fqmul_functional
  require_lemma fqinv_state_step
  require_lemma fqinv_concrete_spec_power_relation
  require_lemma fqinv_functional

  mkdir -p "$generated_dir" "$asm_dir"
  jasmin2ec "$JASMIN_SOURCE" --array-model=old \
    -o "$generated_dir/NTRUPlus768FqInv.ec" -f "$SLICE"
  compare_extraction "$generated_dir"
  compile_easycrypt "$generated_dir"

  jasminc -arch x86-64 -call-conv linux -system linux \
    -slice "$SLICE" -o "$asm_dir/fqinv.s" "$JASMIN_SOURCE"
  jasminc -arch x86-64 -call-conv linux -system linux -checksafety \
    -slice "$SLICE" -o "$asm_dir/fqinv-safety.s" "$JASMIN_SOURCE"
  jasmin-ct --slice="$SLICE" "$JASMIN_SOURCE"
  jasmin-ct --slice="$SLICE" --sct "$JASMIN_SOURCE"

  make -C "$TEST_DIR" OUTDIR="$WORKDIR/test" all
  "$FQINV_PREDECESSOR"

  printf 'PASS: NTRU+768 fqinv C/Jasmin exact helper and addition-chain seam; 17 mutations rejected\n'
  printf 'PASS: NTRU+768 fqinv Jasmin build, safety, CT, and SCT checks\n'
  printf 'PASS: all 65536 input words match production C under normal and UBSan builds\n'
  printf 'PASS: all 3456 nonzero residues produce strict-q-range multiplicative inverses\n'
  printf 'PASS: fresh extraction matches the tracked EasyCrypt procedure\n'
  printf 'PASS: extracted fqinv realizes the exact word trace and verified power relation\n'
  printf 'PASS: the power relation combines with the existing nonzero inverse lemma\n'
  printf 'PASS: prime-field, conditional baseinv, functional, and KAT predecessors\n'
  printf '%s\n' \
    'SCOPE: formal Jasmin fqinv realization plus fail-closed C/Jasmin source and exhaustive executable anchoring; no formal production-C semantics or C/Jasmin program equivalence, no inverse contract for fqinv(0), no Jasmin baseinv/poly_baseinv realization, no current C baseinv return-code theorem, keygen retry/success distribution, h*f=g, serialization provenance, NTT/InvNTT high-level ring semantics, no-wrap/noise theorem, m1/r2 recovery, or full-KEM proof'
}

main "$@"
