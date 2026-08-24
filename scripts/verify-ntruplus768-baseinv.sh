#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/baseinv"
ALGEBRA_PROOF="$PROOF_DIR/NTRUPlus768BaseInvAlgebra.ec"
BRIDGE_PROOF="$PROOF_DIR/NTRUPlus768PolyBaseInvBridge.ec"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/baseinv"
POLY_BASEMUL_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-poly-basemul.sh"
KEYGEN_SAMPLER_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-keygen-sampler.sh"
BASELINE_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-baseline.sh"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-baseinv.XXXXXX")
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

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
      '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
      "$PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "baseinv theories contain a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan baseinv theories for proof holes"
  fi
}

reject_overclaims() {
  local findings="$WORKDIR/overclaims.txt"
  local pattern='^lemma[[:space:]]+.*(c_baseinv|fqinv_correct|return_zero|keygen_inverse|h_f|valid_key|m1|r2|no_wrap)'

  if grep -En "$pattern" "$ALGEBRA_PROOF" "$BRIDGE_PROOF" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "baseinv proof contains a C-equivalence, keygen, or recovery overclaim"
  fi
}

resolve_compiler() {
  if [[ -n "${CC:-}" ]]; then
    command -v "$CC" >/dev/null 2>&1 || fail "configured C compiler is unavailable: $CC"
    CC_BIN=$(command -v "$CC")
  elif command -v gcc >/dev/null 2>&1; then
    CC_BIN=$(command -v gcc)
  elif command -v cc >/dev/null 2>&1; then
    CC_BIN=$(command -v cc)
  else
    fail "missing required C compiler: set CC or install gcc/cc"
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
  WHY3SERVER_BIN=$(cd -- "$easycrypt_bindir/../lib/why3" && pwd)/why3server
  [[ -x "$WHY3SERVER_BIN" ]] ||
    fail "missing Why3 server next to the EasyCrypt installation: $WHY3SERVER_BIN"

  require_file "$ALGEBRA_PROOF"
  require_file "$BRIDGE_PROOF"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_baseinv.py"
  require_file "$TEST_DIR/check_baseinv_vectors.py"
  require_file "$TEST_DIR/baseinv_driver.c"
  require_file "$TEST_DIR/fqinv_wrapper.c"
  [[ -x "$POLY_BASEMUL_VERIFIER" ]] || fail "missing executable poly_basemul verifier"
  [[ -x "$KEYGEN_SAMPLER_VERIFIER" ]] || fail "missing executable keygen sampler verifier"
  [[ -x "$BASELINE_VERIFIER" ]] || fail "missing executable baseline verifier"

  bash -n "$0"
  reject_proof_holes
  reject_overclaims
  require_pattern "$ALGEBRA_PROOF" 'does not claim word-level equivalence' 'scalar scope disclaimer'
  require_pattern "$BRIDGE_PROOF" 'No correspondence with' 'poly scope disclaimer'

  require_lemma "$ALGEBRA_PROOF" numerator_product0_identity
  require_lemma "$ALGEBRA_PROOF" numerator_product1_zero
  require_lemma "$ALGEBRA_PROOF" numerator_product2_zero
  require_lemma "$ALGEBRA_PROOF" numerator_product3_zero
  require_lemma "$ALGEBRA_PROOF" baseinv_math_spec_relation
  require_lemma "$ALGEBRA_PROOF" inverse_coeff_relation_implies_block_inverse
  require_lemma "$ALGEBRA_PROOF" baseinv_math_spec_block_inverse
  require_lemma "$BRIDGE_PROOF" ntt_block_identity_qrange
  require_lemma "$BRIDGE_PROOF" poly_baseinv_witness_contract_implies_success
  require_lemma "$BRIDGE_PROOF" poly_baseinv_success_output_qrange
  require_lemma "$BRIDGE_PROOF" poly_baseinv_success_product_identity

  compile_easycrypt_target "$ALGEBRA_PROOF" "quartic inverse algebra"
  compile_easycrypt_target "$BRIDGE_PROOF" "192-block inverse bridge"

  OUTDIR="$WORKDIR/tests" CC="$CC_BIN" make -C "$TEST_DIR" all
  "$POLY_BASEMUL_VERIFIER"
  "$KEYGEN_SAMPLER_VERIFIER"
  "$BASELINE_VERIFIER"

  printf 'PASS: NTRU+768 quartic determinant and inverse-numerator identities\n'
  printf 'PASS: explicit determinant witness yields a canonical q-range block inverse\n'
  printf 'PASS: 192-block logical success contract yields the terminal NTT identity\n'
  printf 'PASS: exact fqinv/baseinv/poly_baseinv source seam; 24 mutations rejected\n'
  printf 'PASS: all 3456 nonzero fqinv residues and 24 scalar baseinv cases\n'
  printf 'PASS: 17 full-polynomial poly_baseinv cases under normal and UBSan builds\n'
  printf 'PASS: poly_basemul, keygen sampler/NTT, functional, and 100-vector KAT regressions\n'
  printf '%s\n' \
    'SCOPE: universal conditional quartic/192-block q-ring inverse algebra plus fail-closed source and representative executable anchoring; no formal C/Jasmin fqinv/baseinv/poly_baseinv equivalence, no theorem that C return 0 supplies the determinant witness, no universal C arithmetic-safety theorem, no fqinv(0) contract, keygen retry/success distribution, h*f=g, serialization provenance, NTT/InvNTT high-level ring semantics, no-wrap/noise theorem, m1/r2 recovery, or full-KEM proof'
}

main "$@"
