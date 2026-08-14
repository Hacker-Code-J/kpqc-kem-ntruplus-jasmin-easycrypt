#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_ROOT="$REPO_ROOT/ntruplus/proof/768/ref"
BRIDGE_DIR="$PROOF_ROOT/decap_r2_tobytes"
BRIDGE_PROOF="$BRIDGE_DIR/NTRUPlus768DecapR2ToBytesBridge.ec"
BASE_BRIDGE="$PROOF_ROOT/decap_r2/NTRUPlus768DecapR2Bridge.ec"
POLY_TOBYTES_PROOF="$PROOF_ROOT/poly_tobytes/NTRUPlus768PolyToBytesProof.ec"
BASE_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-decap-r2.sh"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/decap_r2_tobytes"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-decap-r2-tobytes.XXXXXX")
WHY3_PID=
WHY3SERVER_BIN=
WHY3_SOCKET="$WORKDIR/why3.sock"

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
    "$BRIDGE_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "decap-r2 poly_tobytes bridge contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the decap-r2 poly_tobytes bridge for holes"
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

compile_bridge() {
  local server_log="$WORKDIR/why3.log"

  start_why3_server "$server_log"
  if ! (
    cd "$BRIDGE_DIR"
    easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
      -server "$WHY3_SOCKET" "$BRIDGE_PROOF"
  ); then
    sed -n '1,120p' "$server_log" >&2 || true
    fail "EasyCrypt decap-r2 poly_tobytes bridge proof failed"
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

  easycrypt_bin=$(command -v easycrypt)
  easycrypt_bindir=$(cd -- "$(dirname -- "$easycrypt_bin")" && pwd)
  WHY3SERVER_BIN="$easycrypt_bindir/../lib/why3/why3server"
  [[ -x "$WHY3SERVER_BIN" ]] ||
    fail "missing Why3 server next to the EasyCrypt installation: $WHY3SERVER_BIN"

  require_file "$BRIDGE_PROOF"
  require_file "$BRIDGE_DIR/easycrypt.project"
  require_file "$BASE_BRIDGE"
  require_file "$POLY_TOBYTES_PROOF"
  require_file "$BASE_VERIFIER"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_decap_r2_tobytes.py"

  require_lemma "$BASE_BRIDGE" poly_basemul_qring_output_in_qrange768
  require_lemma "$POLY_TOBYTES_PROOF" poly_tobytes_correct
  require_lemma "$BRIDGE_PROOF" decap_r2_poly_tobytes_correct
  require_lemma "$BRIDGE_PROOF" decap_r2_serialized_value_flow

  bash -n "$0"
  reject_proof_holes
  compile_bridge
  make -C "$TEST_DIR" check selfcheck
  "$BASE_VERIFIER"

  printf 'PASS: NTRU+768 decap-r2 poly_tobytes bridge proof and proof-hole checks\n'
  printf 'PASS: NTRU+768 r2 quotient-ring output range feeds exact poly_tobytes procedure\n'
  printf 'PASS: NTRU+768 concrete poly_basemul -> poly_tobytes source seam and mutation checks\n'
  printf 'PASS: NTRU+768 predecessor decap-r2, poly_tobytes, poly_basemul, and poly_sub regressions\n'
  printf '%s\n' \
    'SCOPE: exact r2 serialization through poly_tobytes before hash_g; hash_g/SHAKE, SOTP decode, reencryption, verify, fallback selection, pointer overlap, C-AST equivalence, and full-KEM correctness remain out of scope'
}

main "$@"
