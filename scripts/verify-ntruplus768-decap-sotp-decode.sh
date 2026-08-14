#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_ROOT="$REPO_ROOT/ntruplus/proof/768/ref"
PROOF_DIR="$PROOF_ROOT/poly_sotp_decode"
ALGEBRA_PROOF="$PROOF_DIR/NTRUPlus768PolySOTPDecodeAlgebra.ec"
BRIDGE_PROOF="$PROOF_DIR/NTRUPlus768PolySOTPDecodeDecapBridge.ec"
HASH_G_BRIDGE="$PROOF_ROOT/decap_hash_g/NTRUPlus768DecapHashGBridge.ec"
JASMIN_SOURCE="$REPO_ROOT/ntruplus/jasmin/768/ref/poly_sotp_decode.jazz"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/poly_sotp_decode"
BASE_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-decap-hash-g.sh"
SLICE=jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-decap-sotp-decode.XXXXXX")
WHY3_PID=
WHY3SERVER_BIN=
WHY3_SOCKET="$WORKDIR/why3.sock"
CC_BIN=

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

resolve_compiler() {
  if [[ -n "${CC:-}" ]]; then
    command -v "$CC" >/dev/null 2>&1 ||
      fail "configured C compiler is unavailable: $CC"
    CC_BIN=$(command -v "$CC")
  elif command -v gcc >/dev/null 2>&1; then
    CC_BIN=$(command -v gcc)
  elif command -v cc >/dev/null 2>&1; then
    CC_BIN=$(command -v cc)
  else
    fail "missing required C compiler: set CC or install gcc/cc"
  fi
}

require_lemma() {
  local file=$1
  local lemma=$2

  grep -Eq "^(hoare|phoare|lemma)[[:space:]]+$lemma([[:space:](]|$)" "$file" ||
    fail "missing required EasyCrypt result: $lemma"
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
    '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
    "$PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "poly_sotp_decode EasyCrypt proof tree contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] ||
      fail "could not scan the poly_sotp_decode EasyCrypt proof tree for holes"
  fi
}

start_why3_server() {
  local server_log=$1
  local attempt
  local launch
  local ready=0

  : >"$server_log"
  for ((launch = 1; launch <= 3; ++launch)); do
    rm -f "$WHY3_SOCKET"
    "$WHY3SERVER_BIN" --socket "$WHY3_SOCKET" --single-client -j1 \
      >>"$server_log" 2>&1 &
    WHY3_PID=$!

    for ((attempt = 0; attempt < 200; ++attempt)); do
      if [[ -S "$WHY3_SOCKET" ]]; then
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

stop_why3_server() {
  if [[ -n "$WHY3_PID" ]]; then
    kill "$WHY3_PID" 2>/dev/null || true
    wait "$WHY3_PID" 2>/dev/null || true
    WHY3_PID=
  fi
}

compile_proof() {
  local proof=$1
  local label=$2

  if ! (
    cd "$PROOF_DIR"
    easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
      -server "$WHY3_SOCKET" "$proof"
  ); then
    sed -n '1,120p' "$WORKDIR/why3.log" >&2 || true
    fail "EasyCrypt poly_sotp_decode $label proof failed"
  fi
}

check_extraction() {
  local generated_dir="$WORKDIR/extracted"
  local generated="$generated_dir/NTRUPlus768PolySOTPDecode.ec"

  mkdir -p "$generated_dir"
  jasmin2ec "$JASMIN_SOURCE" --array-model=old \
    -o "$generated" -f "$SLICE"
  require_file "$generated"
  require_pattern "$generated" \
    "proc[[:space:]]+$SLICE[[:space:]]*\\(msg:W8\\.t Array96\\.t," \
    'old-array extracted poly_sotp_decode procedure'
  require_pattern "$generated" \
    'ap:W16\.t Array768\.t,' \
    'old-array extracted 768-coefficient input'
  require_pattern "$generated" \
    'buf:W8\.t Array192\.t\)' \
    'old-array extracted 192-byte input'
  require_pattern "$generated" \
    'W8\.t Array96\.t \* W32\.t = \{' \
    'old-array extracted message/fail result'
}

main() {
  local easycrypt_bin
  local easycrypt_bindir
  local asm_dir="$WORKDIR/asm"

  require_command bash
  require_command easycrypt
  require_command grep
  require_command jasmin-ct
  require_command jasmin2ec
  require_command jasminc
  require_command make
  require_command python3
  resolve_compiler

  easycrypt_bin=$(command -v easycrypt)
  easycrypt_bindir=$(cd -- "$(dirname -- "$easycrypt_bin")" && pwd)
  WHY3SERVER_BIN="$easycrypt_bindir/../lib/why3/why3server"
  [[ -x "$WHY3SERVER_BIN" ]] ||
    fail "missing Why3 server next to the EasyCrypt installation: $WHY3SERVER_BIN"

  require_file "$ALGEBRA_PROOF"
  require_file "$BRIDGE_PROOF"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$PROOF_DIR/Makefile"
  require_file "$HASH_G_BRIDGE"
  require_file "$JASMIN_SOURCE"
  require_file "$BASE_VERIFIER"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_poly_sotp_decode.py"
  require_file "$TEST_DIR/check_poly_sotp_decode_vectors.py"
  require_file "$TEST_DIR/poly_sotp_decode_driver.c"

  require_pattern "$JASMIN_SOURCE" \
    '^#\[safety[[:space:]]*=' 'Jasmin safety contract'
  require_pattern "$JASMIN_SOURCE" \
    '^#\[ct[[:space:]]*=' 'Jasmin constant-time contract'
  require_pattern "$JASMIN_SOURCE" \
    '^#\[sct[[:space:]]*=' 'Jasmin speculative constant-time contract'
  require_pattern "$JASMIN_SOURCE" \
    "^export fn[[:space:]]+$SLICE\\(" 'Jasmin export'
  require_pattern "$JASMIN_SOURCE" \
    'r >>= 1;' 'Jasmin failure accumulator fold'
  require_pattern "$JASMIN_SOURCE" \
    'norm >>= 31;' 'Jasmin normalized one-bit failure result'
  require_pattern "$JASMIN_SOURCE" \
    'msg\[i\] &= mask;' 'Jasmin fail-closed message mask'

  require_lemma "$HASH_G_BRIDGE" decap_r2_hash_g_value_flow
  require_lemma "$ALGEBRA_PROOF" poly_sotp_bit_bound
  require_lemma "$ALGEBRA_PROOF" poly_sotp_raw_byte_int_range
  require_lemma "$ALGEBRA_PROOF" poly_sotp_trit_sum_range
  require_lemma "$ALGEBRA_PROOF" poly_sotp_decode_success_valid
  require_lemma "$ALGEBRA_PROOF" poly_sotp_decode_failure_zero
  require_lemma "$BRIDGE_PROOF" inverse_invntt_crepmod3_spec_trit_input
  require_lemma "$BRIDGE_PROOF" \
    poly_basemul_qring_inverse_invntt_crepmod3_trit_input
  require_lemma "$BRIDGE_PROOF" decap_terminal_poly_sotp_decode_value_flow

  bash -n "$0"
  reject_proof_holes
  mkdir -p "$asm_dir"
  start_why3_server "$WORKDIR/why3.log"
  compile_proof "$ALGEBRA_PROOF" algebra
  compile_proof "$BRIDGE_PROOF" decap-bridge
  stop_why3_server

  check_extraction
  jasminc -arch x86-64 -call-conv linux -system linux \
    -slice "$SLICE" -o "$asm_dir/poly_sotp_decode.s" "$JASMIN_SOURCE"
  jasminc -arch x86-64 -call-conv linux -system linux -checksafety \
    -slice "$SLICE" -o "$asm_dir/poly_sotp_decode-safety.s" "$JASMIN_SOURCE"
  jasmin-ct --slice="$SLICE" "$JASMIN_SOURCE"
  jasmin-ct --slice="$SLICE" --sct "$JASMIN_SOURCE"

  make -C "$TEST_DIR" CC="$CC_BIN" JASMINC=jasminc \
    OUTDIR="$WORKDIR/test" all
  "$BASE_VERIFIER"

  printf 'PASS: NTRU+768 poly_sotp_decode array-value algebra and fail-closed specification\n'
  printf 'PASS: NTRU+768 decapsulation m1/hash_g to decoded-prefix/fail value-flow bridge\n'
  printf 'PASS: NTRU+768 poly_sotp_decode Jasmin extraction, build, safety, CT, and SCT checks\n'
  printf 'PASS: NTRU+768 C/Jasmin/Python differential, UBSan, and source mutation checks\n'
  printf 'PASS: NTRU+768 predecessor decap hash_g and arithmetic regressions\n'
  printf '%s\n' \
    'SCOPE: trit-input old-array value proof plus Jasmin safety/CT/SCT and source/differential checks; no EasyCrypt functional proof of the Jasmin or C procedure, C-AST/pointer-alias model, encode/decode inverse, hash_h, reencryption, comparison, fallback selection, or full-KEM correctness'
}

main "$@"
