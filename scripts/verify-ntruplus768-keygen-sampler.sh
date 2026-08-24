#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/keygen_sampler"
ALGEBRA_PROOF="$PROOF_DIR/NTRUPlus768KeygenSamplerAlgebra.ec"
BRIDGE_PROOF="$PROOF_DIR/NTRUPlus768KeygenSamplerBridge.ec"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/keygen_sampler"
CBD1_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-decap-poly-cbd1.sh"
NTT_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-ntt.sh"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-keygen-sampler.XXXXXX")
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

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
      '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
      "$PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "keygen sampler theories contain a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan keygen sampler theories for proof holes"
  fi
}

reject_overclaims() {
  if grep -En \
      '^lemma[[:space:]]+.*(baseinv|finv|ginv|h_f|valid_key|m1|noise_wrap)' \
      "$ALGEBRA_PROOF" "$BRIDGE_PROOF" >"$WORKDIR/overclaims.txt"; then
    sed -n '1,120p' "$WORKDIR/overclaims.txt" >&2
    fail "keygen sampler proof contains a downstream inverse or recovery claim"
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
  require_file "$TEST_DIR/check_keygen_sampler.py"
  require_file "$TEST_DIR/keygen_sampler_driver.c"
  [[ -x "$CBD1_VERIFIER" ]] || fail "missing executable CBD1 predecessor verifier"
  [[ -x "$NTT_VERIFIER" ]] || fail "missing executable NTT predecessor verifier"

  bash -n "$0"
  reject_proof_holes
  reject_overclaims

  require_lemma "$ALGEBRA_PROOF" poly_triple_sampled_coeff
  require_lemma "$ALGEBRA_PROOF" keygen_f_pre_ntt_matches_triple_plus_one
  require_lemma "$ALGEBRA_PROOF" keygen_f_pre_ntt_mod3
  require_lemma "$ALGEBRA_PROOF" keygen_g_pre_ntt_mod3
  require_lemma "$ALGEBRA_PROOF" keygen_f_pre_ntt_small
  require_lemma "$ALGEBRA_PROOF" keygen_g_pre_ntt_small
  require_lemma "$ALGEBRA_PROOF" keygen_f_pre_ntt_input_qrange
  require_lemma "$ALGEBRA_PROOF" keygen_g_pre_ntt_input_qrange
  require_lemma "$BRIDGE_PROOF" keygen_f_ntt_algebra
  require_lemma "$BRIDGE_PROOF" keygen_g_ntt_algebra
  require_lemma "$BRIDGE_PROOF" keygen_f_ntt_centered_output
  require_lemma "$BRIDGE_PROOF" keygen_g_ntt_centered_output
  require_lemma "$BRIDGE_PROOF" keygen_sampler_value_flow_intro

  compile_easycrypt_target "$ALGEBRA_PROOF" "sampler-shaping algebra"
  compile_easycrypt_target "$BRIDGE_PROOF" "sampler-to-NTT bridge"

  OUTDIR="$WORKDIR/tests" CC="$CC_BIN" make -C "$TEST_DIR" all
  "$CBD1_VERIFIER"
  "$NTT_VERIFIER"

  printf 'PASS: NTRU+768 keygen f = 1 + 3F and g = 3G coefficient shapes\n'
  printf 'PASS: NTRU+768 keygen f/g exact mod-3 and small-coefficient bounds\n'
  printf 'PASS: NTRU+768 keygen f/g forward-NTT readiness and centered output\n'
  printf 'PASS: exact poly_triple and genf/geng source seams; 18 mutations rejected\n'
  printf 'PASS: 22 full-polynomial normal/UBSan sampler, alias, and NTT cases\n'
  printf 'PASS: complete CBD1 and forward-NTT predecessor regressions\n'
  printf '%s\n' \
    'SCOPE: coefficient-domain keygen sampler shaping through forward NTT only; no SHAKE proof, C-AST/Jasmin poly_triple equivalence, poly_baseinv correctness or success, finv/ginv provenance, h*f=g, NTT/InvNTT high-level ring homomorphism, no-q-wrap/noise theorem, m1 recovery, r2 recovery, or full-KEM correctness'
}

main "$@"
