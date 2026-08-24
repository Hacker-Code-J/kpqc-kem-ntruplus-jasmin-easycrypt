#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/encap_poly_basemul_add"
ALGEBRA_PROOF="$PROOF_DIR/NTRUPlus768EncapPolyBasemulAddAlgebra.ec"
BRIDGE_PROOF="$PROOF_DIR/NTRUPlus768EncapPolyBasemulAddBridge.ec"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/encap_poly_basemul_add"
POLY_BASEMUL_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-poly-basemul.sh"
LATEST_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-poly-sotp-roundtrip.sh"
NTRU_ROOT="$REPO_ROOT/NTRU+/NTRU+768"
PARAMS_HEADER="$NTRU_ROOT/params.h"
NTT_HEADER="$NTRU_ROOT/ntt.h"
POLY_HEADER="$NTRU_ROOT/poly.h"
NTT_SOURCE="$NTRU_ROOT/ntt.c"
POLY_SOURCE="$NTRU_ROOT/poly.c"
KEM_SOURCE="$NTRU_ROOT/kem.c"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-encap-basemul-add.XXXXXX")
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

  grep -Eq "^lemma[[:space:]]+$lemma([[:space:](]|$)" "$file" ||
    fail "missing required EasyCrypt lemma: $lemma"
}

require_pattern() {
  local file=$1
  local pattern=$2
  local label=$3

  grep -Eq "$pattern" "$file" || fail "missing required $label"
}

reject_pattern() {
  local file=$1
  local pattern=$2
  local label=$3

  if grep -Eq "$pattern" "$file"; then
    fail "unexpected $label"
  fi
}

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
      '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
      "$PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "encapsulation poly_basemul_add theories contain a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] ||
      fail "could not scan encapsulation poly_basemul_add theories for proof holes"
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

  [[ $ready -eq 1 ]]
}

stop_why3_server() {
  if [[ -n "$WHY3_PID" ]]; then
    kill "$WHY3_PID" 2>/dev/null || true
    wait "$WHY3_PID" 2>/dev/null || true
    WHY3_PID=
  fi
}

compile_easycrypt_target() {
  local proof=$1
  local label=$2
  local server_log="$WORKDIR/$(basename -- "$proof").why3.log"

  if start_why3_server "$server_log"; then
    if ! (
      cd "$PROOF_DIR"
      easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
        -server "$WHY3_SOCKET" "$proof"
    ); then
      sed -n '1,120p' "$server_log" >&2 || true
      fail "EasyCrypt $label failed"
    fi
  else
    if ! (
      cd "$PROOF_DIR"
      easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 "$proof"
    ); then
      sed -n '1,120p' "$server_log" >&2 || true
      fail "EasyCrypt $label failed without Why3 server fallback"
    fi
  fi
  stop_why3_server
}

main() {
  local easycrypt_bin
  local easycrypt_bindir

  require_command bash
  require_command easycrypt
  require_command grep
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
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_encap_poly_basemul_add.py"
  require_file "$TEST_DIR/check_encap_poly_basemul_add_vectors.py"
  require_file "$TEST_DIR/encap_poly_basemul_add_driver.c"
  require_file "$POLY_BASEMUL_VERIFIER"
  require_file "$LATEST_VERIFIER"
  require_file "$PARAMS_HEADER"
  require_file "$NTT_HEADER"
  require_file "$POLY_HEADER"
  require_file "$NTT_SOURCE"
  require_file "$POLY_SOURCE"
  require_file "$KEM_SOURCE"

  require_pattern "$ALGEBRA_PROOF" \
    'poly_basemul_add_qring' \
    'blockwise multiply-plus-add q-ring relation'
  require_pattern "$ALGEBRA_PROOF" \
    'centered_sum_int' \
    'single-step centered q representative'
  require_pattern "$BRIDGE_PROOF" \
    'poly_frombytes_spec[[:space:]]+pk' \
    'decoded encapsulation public-key input'
  require_pattern "$BRIDGE_PROOF" \
    'forward_ntt_spec[[:space:]]+encoded_m' \
    'encoded-message forward NTT value'
  reject_pattern "$BRIDGE_PROOF" \
    'inverse_invntt_crepmod3|decap_m1|valid_key' \
    'unproved valid-key or decapsulation-m1 conclusion'

  require_lemma "$ALGEBRA_PROOF" poly_basemul_qring_product_in_qrange768
  require_lemma "$ALGEBRA_PROOF" centered_sum_int_range
  require_lemma "$ALGEBRA_PROOF" centered_sum_int_mod_q
  require_lemma "$ALGEBRA_PROOF" centered_add_word_coeff
  require_lemma "$ALGEBRA_PROOF" centered_add_word_mod_q
  require_lemma "$ALGEBRA_PROOF" poly_centered_add_spec_coeff
  require_lemma "$ALGEBRA_PROOF" poly_centered_add_spec_coeff_mod_q
  require_lemma "$ALGEBRA_PROOF" poly_centered_add_spec_qring
  require_lemma "$ALGEBRA_PROOF" poly_basemul_qring_centered_add_qring
  require_lemma "$ALGEBRA_PROOF" poly_basemul_add_spec_qring
  require_lemma "$BRIDGE_PROOF" encap_encoded_m_trit_output
  require_lemma "$BRIDGE_PROOF" encap_encoded_m_input_qrange
  require_lemma "$BRIDGE_PROOF" encap_m_ntt_algebra
  require_lemma "$BRIDGE_PROOF" encap_m_ntt_centered_output
  require_lemma "$BRIDGE_PROOF" encap_ciphertext_spec_qring
  require_lemma "$BRIDGE_PROOF" encap_poly_basemul_add_value_flow_intro
  require_lemma "$BRIDGE_PROOF" encap_poly_basemul_add_value_flow_outcome
  require_lemma "$BRIDGE_PROOF" encap_ciphertext_spec_in_qrange768

  bash -n "$0"
  reject_proof_holes
  compile_easycrypt_target "$ALGEBRA_PROOF" \
    "encapsulation poly_basemul_add q-ring algebra"
  compile_easycrypt_target "$BRIDGE_PROOF" \
    "encoded-message NTT and ciphertext value-flow bridge"
  make -C "$TEST_DIR" CC="$CC_BIN" OUTDIR="$WORKDIR/test" all
  "$POLY_BASEMUL_VERIFIER"
  "$LATEST_VERIFIER"

  printf 'PASS: NTRU+768 encoded SOTP message is a trit polynomial ready for forward NTT\n'
  printf 'PASS: NTRU+768 m_ntt satisfies the exact centered [-1728,1728] addend premise\n'
  printf 'PASS: NTRU+768 ciphertext blocks equal h*r + m_ntt in the terminal q-ring\n'
  printf 'PASS: NTRU+768 exact basemul_add/poly_basemul_add/encapsulation source seam and 16 mutations\n'
  printf 'PASS: NTRU+768 22 full-polynomial q-ring oracle vectors in normal and UBSan builds\n'
  printf 'PASS: NTRU+768 poly_basemul and full latest SOTP/terminal predecessor regressions\n'
  printf '%s\n' \
    'SCOPE: canonical array-value q-ring relation for encapsulation c = h*r + m_ntt with source/runtime anchoring; no exact raw C word or formal C procedure equivalence, key-generation sampler/inverse provenance, valid-key m1 recovery, r2=r, pad/hash/shared-secret agreement, API agreement, or full-KEM correctness'
}

main "$@"
