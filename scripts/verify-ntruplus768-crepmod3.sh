#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
JASMIN_SOURCE="$REPO_ROOT/ntruplus/jasmin/768/ref/crepmod3.jazz"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/crepmod3"
PROOF_ROOT="$REPO_ROOT/ntruplus/proof/768/ref"
PROOF_DIR="$PROOF_ROOT/crepmod3"
TRACKED_EXTRACTED="$PROOF_DIR/extracted"
FORMOSA_ROOT="$REPO_ROOT/external/formosa-mlkem"
FORMOSA_ECLIB="$FORMOSA_ROOT/proof/eclib"
FORMOSA_COMMON="$FORMOSA_ROOT/crypto-specs/common"
FORMOSA_ARRAYS="$FORMOSA_ROOT/crypto-specs/arrays"
SLICE=jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-crepmod3.XXXXXX")
WHY3_PID=
WHY3SERVER_BIN=
WHY3_SOCKET=
GENERATED_DIR=

EASYCRYPT_INCLUDES=(
  -I "$PROOF_DIR"
  -I "$PROOF_ROOT/basemul"
  -I "$PROOF_ROOT/basemul/extracted"
  -I "$PROOF_ROOT/poly_basemul"
  -I "$PROOF_ROOT/poly_basemul/extracted"
  -I "$PROOF_ROOT/poly_basemul_invntt"
  -I "$PROOF_ROOT/poly_frombytes"
  -I "$PROOF_ROOT/invntt"
  -I "$PROOF_ROOT/invntt/extracted"
  -I "$PROOF_ROOT/invntt_radix2_4"
  -I "$PROOF_ROOT/invntt_radix2_4/extracted"
  -I "$PROOF_ROOT/invntt_radix2_8"
  -I "$PROOF_ROOT/invntt_radix2_8/extracted"
  -I "$PROOF_ROOT/invntt_radix2_16"
  -I "$PROOF_ROOT/invntt_radix2_16/extracted"
  -I "$PROOF_ROOT/invntt_radix2_32"
  -I "$PROOF_ROOT/invntt_radix2_32/extracted"
  -I "$PROOF_ROOT/invntt_radix2_64"
  -I "$PROOF_ROOT/invntt_radix2_64/extracted"
  -I "$PROOF_ROOT/invntt_radix3"
  -I "$PROOF_ROOT/invntt_radix3/extracted"
  -I "$PROOF_ROOT/invntt_final"
  -I "$PROOF_ROOT/invntt_final/extracted"
  -I "$PROOF_ROOT/ntt_radix2_64"
  -I "$PROOF_ROOT/ntt_radix2_64/extracted"
  -I "$PROOF_ROOT/ntt_stage1"
  -I "$PROOF_ROOT/ntt_stage1/extracted"
  -I "$PROOF_ROOT/ntt_schedule"
  -I "$FORMOSA_ECLIB"
  -I "$FORMOSA_COMMON"
  -I "$FORMOSA_ARRAYS"
)

cleanup() {
  if [[ -n "$WHY3_PID" ]]; then
    kill "$WHY3_PID" 2>/dev/null || true
    wait "$WHY3_PID" 2>/dev/null || true
  fi
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
  local file=$1
  local lemma=$2
  grep -Eq "^lemma[[:space:]]+$lemma([[:space:](]|$)" "$file" ||
    fail "missing required EasyCrypt lemma: $lemma"
}

normalize_extraction_whitespace() {
  find "$1" -maxdepth 1 -type f -name '*.ec' \
    -exec sed -i 's/[[:space:]]\+$//' {} +
}

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
    '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
    "$PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "crepmod3 EasyCrypt proof tree contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the crepmod3 EasyCrypt proof tree for holes"
  fi
}

start_why3_server() {
  local socket=$1
  local server_log=$2
  local attempt
  local launch
  local ready=0

  : >"$server_log"
  for ((launch = 1; launch <= 3; ++launch)); do
    rm -f "$socket"
    "$WHY3SERVER_BIN" --socket "$socket" --single-client -j1 \
      >>"$server_log" 2>&1 &
    WHY3_PID=$!

    for ((attempt = 0; attempt < 200; ++attempt)); do
      if [[ -S "$socket" ]]; then
        ready=1
        break
      fi
      sleep 0.05
    done
    [[ $ready -eq 1 ]] && break

    kill "$WHY3_PID" 2>/dev/null || true
    wait "$WHY3_PID" 2>/dev/null || true
    WHY3_PID=
    sleep 0.1
  done

  if [[ $ready -ne 1 ]]; then
    sed -n '1,120p' "$server_log" >&2 || true
    fail "Why3 server did not become ready after three attempts"
  fi
}

compile_easycrypt() {
  local proof=$1
  local tag=$2

  if ! easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
    -server "$WHY3_SOCKET" \
    -I "$GENERATED_DIR" \
    "${EASYCRYPT_INCLUDES[@]}" \
    "$proof"; then
    sed -n '1,120p' "$WORKDIR/why3.log" >&2 || true
    fail "EasyCrypt $tag proof failed"
  fi
}

compare_extraction() {
  local expected_list="$WORKDIR/expected-extracted.txt"
  local generated_list="$WORKDIR/generated-extracted.txt"
  local name

  printf '%s\n' \
    Array768.ec \
    NTRUPlus768Crepmod3.ec \
    WArray1536.ec >"$expected_list"
  find "$GENERATED_DIR" -maxdepth 1 -type f -name '*.ec' -printf '%f\n' \
    | sort >"$generated_list"

  if ! cmp -s "$expected_list" "$generated_list"; then
    diff -u "$expected_list" "$generated_list" >&2 || true
    fail "generated extraction file set does not match expected crepmod3 extraction"
  fi

  while IFS= read -r name; do
    if ! cmp -s "$GENERATED_DIR/$name" "$TRACKED_EXTRACTED/$name"; then
      diff -u "$TRACKED_EXTRACTED/$name" "$GENERATED_DIR/$name" \
        | sed -n '1,120p' >&2 || true
      fail "tracked crepmod3 EasyCrypt extraction is stale: $name"
    fi
  done <"$expected_list"
}

main() {
  local easycrypt_bin
  local easycrypt_bindir
  local asm_dir="$WORKDIR/asm"

  require_command bash
  require_command cmp
  require_command diff
  require_command easycrypt
  require_command grep
  require_command jasmin-ct
  require_command jasmin2ec
  require_command jasminc
  require_command make
  require_command python3
  [[ -x /usr/bin/gcc ]] || fail "missing required GCC compiler: /usr/bin/gcc"

  easycrypt_bin=$(command -v easycrypt)
  easycrypt_bindir=$(cd -- "$(dirname -- "$easycrypt_bin")" && pwd)
  WHY3SERVER_BIN="$easycrypt_bindir/../lib/why3/why3server"
  [[ -x "$WHY3SERVER_BIN" ]] ||
    fail "missing Why3 server next to the EasyCrypt installation: $WHY3SERVER_BIN"

  require_file "$JASMIN_SOURCE"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_crepmod3.py"
  require_file "$TEST_DIR/crepmod3_diff.c"
  require_file "$PROOF_DIR/NTRUPlus768Crepmod3Proof.ec"
  require_file "$PROOF_DIR/NTRUPlus768Crepmod3Algebra.ec"
  require_file "$PROOF_DIR/NTRUPlus768Crepmod3DecapBridge.ec"
  require_file "$FORMOSA_ECLIB/W16extra.ec"
  require_file "$FORMOSA_COMMON/JWord_extra.ec"
  require_file "$FORMOSA_ARRAYS/Array1152.ec"

  require_lemma "$PROOF_DIR/NTRUPlus768Crepmod3Proof.ec" \
    poly_crepmod3_functional
  require_lemma "$PROOF_DIR/NTRUPlus768Crepmod3Algebra.ec" \
    crepmod3_word_qrangeE
  require_lemma "$PROOF_DIR/NTRUPlus768Crepmod3Algebra.ec" \
    poly_crepmod3_spec_algebra
  require_lemma "$PROOF_DIR/NTRUPlus768Crepmod3Algebra.ec" \
    poly_crepmod3_spec_input_qrange
  require_lemma "$PROOF_DIR/NTRUPlus768Crepmod3DecapBridge.ec" \
    poly_frombytes_two_decoder_specs_decap_m1_crepmod3_value_flow

  bash -n "$0"
  mkdir -p "$asm_dir" "$WORKDIR/extracted"
  GENERATED_DIR="$WORKDIR/extracted"
  WHY3_SOCKET="$WORKDIR/why3.sock"
  start_why3_server "$WHY3_SOCKET" "$WORKDIR/why3.log"

  jasmin2ec "$JASMIN_SOURCE" --array-model=old \
    -o "$GENERATED_DIR/NTRUPlus768Crepmod3.ec" -f "$SLICE"
  normalize_extraction_whitespace "$GENERATED_DIR"
  compare_extraction
  reject_proof_holes

  compile_easycrypt "$PROOF_DIR/NTRUPlus768Crepmod3Proof.ec" word-level
  compile_easycrypt "$PROOF_DIR/NTRUPlus768Crepmod3Algebra.ec" algebra
  compile_easycrypt "$PROOF_DIR/NTRUPlus768Crepmod3DecapBridge.ec" decap-bridge

  jasminc -arch x86-64 -call-conv linux -system linux \
    -slice "$SLICE" -o "$asm_dir/crepmod3.s" "$JASMIN_SOURCE"
  jasminc -arch x86-64 -call-conv linux -system linux -checksafety \
    -slice "$SLICE" -o "$asm_dir/crepmod3-safety.s" "$JASMIN_SOURCE"
  jasmin-ct --slice="$SLICE" "$JASMIN_SOURCE"
  jasmin-ct --slice="$SLICE" --sct "$JASMIN_SOURCE"

  make -C "$TEST_DIR" CC=/usr/bin/gcc OUTDIR="$WORKDIR/test" \
    check selfcheck run ubsan

  printf 'PASS: NTRU+768 crepmod3 fail-closed C/Jasmin/caller source checks\n'
  printf 'PASS: NTRU+768 crepmod3 Jasmin build, safety, CT, and SCT checks\n'
  printf 'PASS: NTRU+768 crepmod3 fresh extraction matches the tracked model\n'
  printf 'PASS: NTRU+768 crepmod3 word, qrange algebra, and NTT-readiness proofs\n'
  printf 'PASS: NTRU+768 decoded m1 value-flow bridge through inverse_invntt_spec\n'
  printf 'PASS: NTRU+768 crepmod3 GCC differential/UBSan tests on boundary, random, and full int16 inputs\n'
  printf '%s\n' \
    'SCOPE: value-level old-array proof plus exact-alias source/tests; no partial-overlap, shared-memory, C-AST, or full-KEM theorem'
}

main "$@"
