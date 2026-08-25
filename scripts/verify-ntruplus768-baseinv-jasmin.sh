#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
JASMIN_SOURCE="$REPO_ROOT/ntruplus/jasmin/768/ref/baseinv.jazz"
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/baseinv_jasmin"
PROOF="$PROOF_DIR/NTRUPlus768BaseInvProof.ec"
TRACKED_EXTRACTED="$PROOF_DIR/extracted"
FQINV_JASMIN="$REPO_ROOT/ntruplus/proof/768/ref/fqinv_jasmin"
FQINV_JASMIN_EXTRACTED="$FQINV_JASMIN/extracted"
FQINV_WORD="$REPO_ROOT/ntruplus/proof/768/ref/fqinv"
BASEINV_ALGEBRA="$REPO_ROOT/ntruplus/proof/768/ref/baseinv"
BASEMUL_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/basemul"
BASEMUL_EXTRACTED="$BASEMUL_PROOF/extracted"
FORMOSA_ECLIB="$REPO_ROOT/external/formosa-mlkem/proof/eclib"
FORMOSA_COMMON="$REPO_ROOT/external/formosa-mlkem/crypto-specs/common"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/baseinv_jasmin"
FQINV_PREDECESSOR="$SCRIPT_DIR/verify-ntruplus768-fqinv-jasmin.sh"
PROOF_SLICE=__baseinv_core
EXPORT_SLICE=jade_ntruplus_ntruplus768_amd64_ref_baseinv

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-baseinv-jasmin.XXXXXX")

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
      "$PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "baseinv Jasmin proof tree contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan baseinv Jasmin proof tree"
  fi
}

reject_overclaims() {
  local findings="$WORKDIR/overclaims.txt"
  local pattern='^lemma[[:space:]]+.*(c_baseinv|production_c|poly_baseinv|baseinv_ct|baseinv_sct|keygen|decap)'

  if grep -En "$pattern" "$PROOF" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "baseinv Jasmin proof contains a C, CT/SCT, or downstream overclaim"
  fi
}

reject_ct_sct_annotations() {
  local findings="$WORKDIR/ct-sct-annotations.txt"

  if grep -En '#\[[[:space:]]*(ct|sct)[[:space:]]*=' \
      "$JASMIN_SOURCE" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "secret-dependent baseinv must not carry a CT or SCT annotation"
  fi
}

compare_extraction() {
  local generated_dir=$1
  local expected_list="$WORKDIR/expected-extracted.txt"
  local generated_list="$WORKDIR/generated-extracted.txt"
  local name

  printf '%s\n' Array4.ec NTRUPlus768BaseInv.ec WArray8.ec >"$expected_list"
  find "$generated_dir" -maxdepth 1 -type f -name '*.ec' -printf '%f\n' |
    sort >"$generated_list"

  if ! cmp -s "$expected_list" "$generated_list"; then
    diff -u "$expected_list" "$generated_list" >&2 || true
    fail "generated extraction file set does not match expected baseinv extraction"
  fi

  while IFS= read -r name; do
    if ! cmp -s "$generated_dir/$name" "$TRACKED_EXTRACTED/$name"; then
      diff -u "$TRACKED_EXTRACTED/$name" "$generated_dir/$name" |
        sed -n '1,120p' >&2 || true
      fail "tracked baseinv EasyCrypt extraction is stale: $name"
    fi
  done <"$expected_list"
}

compile_easycrypt() {
  local generated_dir=$1
  local attempt

  for ((attempt = 1; attempt <= 3; ++attempt)); do
    if easycrypt compile -no-eco -p Z3 -timeout 30 -max-provers 1 \
      -I "$generated_dir" \
      -I "$PROOF_DIR" \
      -I "$FQINV_JASMIN" \
      -I "$FQINV_JASMIN_EXTRACTED" \
      -I "$FQINV_WORD" \
      -I "$BASEINV_ALGEBRA" \
      -I "$BASEMUL_PROOF" \
      -I "$BASEMUL_EXTRACTED" \
      -I "$FORMOSA_ECLIB" \
      -I "$FORMOSA_COMMON" \
      "$PROOF"; then
      return
    fi
    sleep 0.2
  done
  fail "EasyCrypt extracted baseinv proof failed after three attempts"
}

main() {
  local generated_dir="$WORKDIR/extracted"
  local asm_dir="$WORKDIR/asm"

  require_command bash
  require_command cmp
  require_command easycrypt
  require_command find
  require_command grep
  require_command jasmin2ec
  require_command jasminc
  require_command make
  require_command python3
  require_command sort
  require_command "${CC:-cc}"

  require_file "$JASMIN_SOURCE"
  require_file "$PROOF"
  require_file "$TRACKED_EXTRACTED/Array4.ec"
  require_file "$TRACKED_EXTRACTED/NTRUPlus768BaseInv.ec"
  require_file "$TRACKED_EXTRACTED/WArray8.ec"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_baseinv_jasmin.py"
  require_file "$TEST_DIR/baseinv_diff.c"
  [[ -x "$FQINV_PREDECESSOR" ]] ||
    fail "missing executable fqinv Jasmin predecessor verifier"

  bash -n "$0"
  reject_proof_holes
  reject_overclaims
  reject_ct_sct_annotations

  require_pattern "$PROOF" 'Production-C semantics' 'production-C scope disclaimer'
  require_pattern "$PROOF" 'no CT or SCT claim' 'CT/SCT scope disclaimer'
  require_pattern "$PROOF" 'no poly_baseinv' 'poly_baseinv scope disclaimer'
  require_pattern "$JASMIN_SOURCE" 'if \(t3 == 0\)' 'determinant failure branch'
  require_pattern "$JASMIN_SOURCE" 'return rp, status;' 'mutable-pointer/status return'

  require_lemma mul_i16_functional
  require_lemma montgomery_reduce_functional
  require_lemma fqmul_functional
  require_lemma fqinv_functional
  require_lemma baseinv_pretrace_word_functional
  require_lemma baseinv_pretrace_functional
  require_lemma baseinv_success_functional
  require_lemma exact_status_trace5_zero
  require_lemma exact_output_fail_unchanged
  require_lemma exact_status_determinant_zero_iff
  require_lemma exact_status_determinant_nonzero_iff
  require_lemma exact_success_inverse_relation
  require_lemma exact_success_block_inverse
  require_lemma baseinv_functional
  require_lemma baseinv_lossless
  require_lemma baseinv_correct

  mkdir -p "$generated_dir" "$asm_dir"
  jasmin2ec "$JASMIN_SOURCE" --array-model=old \
    -o "$generated_dir/NTRUPlus768BaseInv.ec" -f "$PROOF_SLICE"
  compare_extraction "$generated_dir"
  compile_easycrypt "$generated_dir"

  jasminc -arch x86-64 -call-conv linux -system linux \
    -slice "$EXPORT_SLICE" -o "$asm_dir/baseinv.s" "$JASMIN_SOURCE"
  jasminc -arch x86-64 -call-conv linux -system linux -checksafety \
    -slice "$EXPORT_SLICE" -o "$asm_dir/baseinv-safety.s" "$JASMIN_SOURCE"

  make -C "$TEST_DIR" OUTDIR="$WORKDIR/test" all
  "$FQINV_PREDECESSOR"

  printf 'PASS: NTRU+768 baseinv C/Jasmin exact helper, branch, store, and ABI seam; 20 mutations rejected\n'
  printf 'PASS: NTRU+768 baseinv Jasmin build and safety checks\n'
  printf 'PASS: 12 fixed and 20,000 random cases match production C under normal and UBSan builds\n'
  printf 'PASS: Jasmin in-place aliasing matches disjoint success and preserves input on failure\n'
  printf 'PASS: failure preserves the output; success is strict-q-range and an independently checked quartic inverse\n'
  printf 'PASS: fresh __baseinv_core extraction matches the tracked EasyCrypt procedure\n'
  printf 'PASS: extracted status is one iff the determinant is zero, and zero iff it is nonzero\n'
  printf 'PASS: extracted success realizes the verified inverse relation and quartic block inverse\n'
  printf 'PASS: fqinv Jasmin realization and complete earlier predecessor chain\n'
  printf '%s\n' \
    'SCOPE: formal proof-facing Jasmin __baseinv_core realization plus fail-closed C/Jasmin source and executable ABI anchoring; the mutable pointer is a Jasmin source return while the C caller observes the status projection; no formal production-C semantics or C/Jasmin program equivalence, no CT/SCT claim because determinant branching is secret-dependent, no full poly_baseinv correctness, keygen retry/success distribution, h*f=g, serialization provenance, NTT/InvNTT high-level ring semantics, no-wrap/noise theorem, m1/r2 recovery, or full-KEM proof'
}

main "$@"
