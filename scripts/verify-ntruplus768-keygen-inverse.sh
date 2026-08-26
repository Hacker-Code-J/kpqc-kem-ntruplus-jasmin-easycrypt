#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/keygen_inverse"
PROOF="$PROOF_DIR/NTRUPlus768KeygenInverseBridge.ec"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/keygen_inverse"
KEYGEN_SAMPLER_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-keygen-sampler.sh"
POLY_BASEINV_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-poly-baseinv-jasmin.sh"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-keygen-inverse.XXXXXX")
WHY3_SOCKET="$WORKDIR/why3.sock"
WHY3_PID=
WHY3SERVER_BIN=
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
  local lemma=$1

  grep -Eq "^lemma[[:space:]]+$lemma([[:space:](]|$)" "$PROOF" ||
    fail "missing required EasyCrypt lemma: $lemma"
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

start_why3_server() {
  local log=$1
  local launch
  local attempt

  : >"$log"
  for ((launch = 1; launch <= 3; ++launch)); do
    rm -f "$WHY3_SOCKET"
    "$WHY3SERVER_BIN" --socket "$WHY3_SOCKET" --single-client -j1 \
      >>"$log" 2>&1 &
    WHY3_PID=$!
    for ((attempt = 0; attempt < 200; ++attempt)); do
      [[ -S "$WHY3_SOCKET" ]] && return 0
      sleep 0.05
    done
    kill "$WHY3_PID" 2>/dev/null || true
    wait "$WHY3_PID" 2>/dev/null || true
    WHY3_PID=
    sleep 0.1
  done
  return 1
}

compile_proof() {
  local log="$WORKDIR/why3.log"

  start_why3_server "$log" || {
    sed -n '1,120p' "$log" >&2 || true
    fail "could not start the dedicated Why3 server"
  }
  if ! (
    cd "$PROOF_DIR"
    easycrypt compile -no-eco -p Z3 -timeout 30 -max-provers 1 \
      -server "$WHY3_SOCKET" "$PROOF"
  ); then
    sed -n '1,120p' "$log" >&2 || true
    fail "strict EasyCrypt keygen inverse bridge failed"
  fi
  kill "$WHY3_PID" 2>/dev/null || true
  wait "$WHY3_PID" 2>/dev/null || true
  WHY3_PID=
}

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
      '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry|abort)([^[:alnum:]_]|$)' \
      "$PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "keygen inverse proof contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the keygen inverse proof"
  fi
}

reject_overclaims() {
  local findings="$WORKDIR/overclaims.txt"
  local pattern='^lemma[[:space:]]+.*(retry|probability|production_c|c_equiv|keypair|h_f|full_kem|_ct|_sct)'

  if grep -En "$pattern" "$PROOF" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "keygen inverse proof contains an out-of-scope claim"
  fi
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
    fail "missing Why3 server next to the EasyCrypt installation"

  require_file "$PROOF"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$PROOF_DIR/Makefile"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_keygen_inverse.py"
  require_file "$TEST_DIR/keygen_inverse_driver.c"
  [[ -x "$KEYGEN_SAMPLER_VERIFIER" ]] ||
    fail "missing executable keygen sampler predecessor verifier"
  [[ -x "$POLY_BASEINV_VERIFIER" ]] ||
    fail "missing executable poly_baseinv predecessor verifier"

  bash -n "$0"
  reject_proof_holes
  reject_overclaims
  grep -Fq 'retry termination or' "$PROOF" ||
    fail "missing random-retry scope disclaimer"
  grep -Fq 'production-C semantics' "$PROOF" ||
    fail "missing production-C scope disclaimer"
  grep -Fq 'serialization, CT/SCT' "$PROOF" ||
    fail "missing CT/SCT scope disclaimer"

  require_lemma keygen_f_ntt_qrange
  require_lemma keygen_g_ntt_qrange
  require_lemma keygen_f_inverse_success_bridge
  require_lemma keygen_g_inverse_success_bridge
  require_lemma keygen_f_inverse_qrange_on_success
  require_lemma keygen_g_inverse_qrange_on_success
  require_lemma keygen_f_inverse_product_identity_on_success
  require_lemma keygen_g_inverse_product_identity_on_success
  require_lemma keygen_f_inverse_zero_on_failure
  require_lemma keygen_g_inverse_zero_on_failure

  compile_proof
  OUTDIR="$WORKDIR/tests" CC="$CC_BIN" make -C "$TEST_DIR" all
  "$KEYGEN_SAMPLER_VERIFIER"
  "$POLY_BASEINV_VERIFIER"

  printf 'PASS: NTRU+768 keygen f/g centered NTT outputs satisfy the poly_baseinv q-range precondition\n'
  printf 'PASS: status zero yields finv/ginv block inverses, q-range outputs, and terminal identity products\n'
  printf 'PASS: status one carries an exact failed block witness and fully zero inverse output\n'
  printf 'PASS: strict single-Z3 proof completed through a dedicated Why3 server\n'
  printf 'PASS: genf/geng composition checker rejected 9 representative mutations\n'
  printf 'PASS: 23 f plus 23 g normal/UBSan C/Jasmin cases preserve inputs and cover both status branches per lane\n'
  printf 'PASS: complete keygen sampler and poly_baseinv predecessor verifier chains\n'
  printf '%s\n' \
    'SCOPE: proof-level sampler/NTT-to-Jasmin-poly_baseinv composition plus exact-source and executable C/Jasmin anchoring; no random retry termination or probability, formal production-C semantics or C/Jasmin equivalence, h*f=g keypair algebra, serialization provenance, CT/SCT claim, or full-KEM correctness'
}

main "$@"
