#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_ROOT="$REPO_ROOT/ntruplus/proof/768/ref"
BRIDGE_DIR="$PROOF_ROOT/decap_r1_tobytes"
BRIDGE_PROOF="$BRIDGE_DIR/NTRUPlus768DecapR1ToBytesBridge.ec"
PREDECESSOR_BRIDGE="$PROOF_ROOT/decap_r1_ntt/NTRUPlus768DecapR1NTTBridge.ec"
PREDECESSOR_DIR="$PROOF_ROOT/decap_r1_ntt"
PREDECESSOR_TEST_DIR="$REPO_ROOT/tests/ntruplus768/decap_r1_ntt"
POLY_TOBYTES_PROOF="$PROOF_ROOT/poly_tobytes/NTRUPlus768PolyToBytesProof.ec"
POLY_TOBYTES_ALGEBRA="$PROOF_ROOT/poly_tobytes/NTRUPlus768PolyToBytesAlgebra.ec"
POLY_TOBYTES_DIR="$PROOF_ROOT/poly_tobytes"
POLY_TOBYTES_TEST_DIR="$REPO_ROOT/tests/ntruplus768/poly_tobytes"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/decap_r1_tobytes"
NTRU_ROOT="$REPO_ROOT/NTRU+/NTRU+768"
PARAMS_SOURCE="$NTRU_ROOT/params.h"
POLY_SOURCE="$NTRU_ROOT/poly.c"
POLY_HEADER="$NTRU_ROOT/poly.h"
NTT_SOURCE="$NTRU_ROOT/ntt.c"
NTT_JASMIN_SOURCE="$REPO_ROOT/ntruplus/jasmin/768/ref/ntt.jazz"
POLY_TOBYTES_SOURCE="$REPO_ROOT/ntruplus/jasmin/768/ref/poly_tobytes.jazz"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-decap-r1-tobytes.XXXXXX")
WHY3_PID=
WHY3SERVER_BIN=
WHY3_SOCKET="$WORKDIR/why3.sock"
CC_BIN=
JASMINC_BIN=

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

resolve_tools() {
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

  require_command jasminc
  JASMINC_BIN=$(command -v jasminc)
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
    "$BRIDGE_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "decap-r1 poly_tobytes bridge contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the decap-r1 poly_tobytes bridge for holes"
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
    return 1
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
  compile_easycrypt_target "$BRIDGE_DIR" "$BRIDGE_PROOF" \
    "decap-r1 poly_tobytes bridge proof"
}

compile_easycrypt_target() {
  local workdir=$1
  local proof=$2
  local label=$3
  local server_log="$WORKDIR/$(basename -- "$proof").why3.log"

  if start_why3_server "$server_log"; then
    if ! (
      cd "$workdir"
      easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
        -server "$WHY3_SOCKET" "$proof"
    ); then
      sed -n '1,120p' "$server_log" >&2 || true
      fail "EasyCrypt $label failed"
    fi
  else
    if ! (
      cd "$workdir"
      easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
        "$proof"
    ); then
      sed -n '1,120p' "$server_log" >&2 || true
      fail "EasyCrypt $label failed without Why3 server fallback"
    fi
  fi
  stop_why3_server
}

run_predecessor_regressions() {
  compile_easycrypt_target "$PREDECESSOR_DIR" "$PREDECESSOR_BRIDGE" \
    "decap-r1 NTT predecessor proof"
  make -C "$PREDECESSOR_TEST_DIR" CC="$CC_BIN" JASMINC="$JASMINC_BIN" \
    OUTDIR="$WORKDIR/decap-r1-ntt-test" all
}

run_poly_tobytes_regressions() {
  compile_easycrypt_target "$POLY_TOBYTES_DIR" "$POLY_TOBYTES_PROOF" \
    "poly_tobytes word-level proof"
  compile_easycrypt_target "$POLY_TOBYTES_DIR" "$POLY_TOBYTES_ALGEBRA" \
    "poly_tobytes algebra proof"
  make -C "$POLY_TOBYTES_TEST_DIR" CC="$CC_BIN" JASMINC="$JASMINC_BIN" \
    OUTDIR="$WORKDIR/poly-tobytes-test" check selfcheck run ubsan
}

main() {
  local easycrypt_bin
  local easycrypt_bindir

  require_command bash
  require_command easycrypt
  require_command grep
  require_command make
  require_command python3
  resolve_tools

  easycrypt_bin=$(command -v easycrypt)
  easycrypt_bindir=$(cd -- "$(dirname -- "$easycrypt_bin")" && pwd)
  WHY3SERVER_BIN="$easycrypt_bindir/../lib/why3/why3server"
  [[ -x "$WHY3SERVER_BIN" ]] ||
    fail "missing Why3 server next to the EasyCrypt installation: $WHY3SERVER_BIN"

  require_file "$BRIDGE_PROOF"
  require_file "$BRIDGE_DIR/easycrypt.project"
  require_file "$BRIDGE_DIR/Makefile"
  require_file "$PREDECESSOR_BRIDGE"
  require_file "$POLY_TOBYTES_PROOF"
  require_file "$POLY_TOBYTES_ALGEBRA"
  require_file "$PREDECESSOR_DIR/easycrypt.project"
  require_file "$PREDECESSOR_DIR/Makefile"
  require_file "$PREDECESSOR_TEST_DIR/Makefile"
  require_file "$PREDECESSOR_TEST_DIR/check_decap_r1_ntt.py"
  require_file "$PREDECESSOR_TEST_DIR/check_decap_r1_ntt_vectors.py"
  require_file "$PREDECESSOR_TEST_DIR/decap_r1_ntt_driver.c"
  require_file "$POLY_TOBYTES_DIR/easycrypt.project"
  require_file "$POLY_TOBYTES_TEST_DIR/Makefile"
  require_file "$POLY_TOBYTES_TEST_DIR/check_poly_tobytes.py"
  require_file "$POLY_TOBYTES_TEST_DIR/poly_tobytes_diff.c"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_decap_r1_tobytes.py"
  require_file "$TEST_DIR/check_decap_r1_tobytes_vectors.py"
  require_file "$TEST_DIR/decap_r1_tobytes_driver.c"
  require_file "$PARAMS_SOURCE"
  require_file "$POLY_SOURCE"
  require_file "$POLY_HEADER"
  require_file "$NTT_SOURCE"
  require_file "$NTT_JASMIN_SOURCE"
  require_file "$POLY_TOBYTES_SOURCE"

  require_pattern "$BRIDGE_PROOF" \
    'buf2[[:space:]]*=[[:space:]]*NTRUPlus768PolyToBytesProof\.poly_tobytes_spec[[:space:]]+r1_post' \
    'exact r1 poly_tobytes serialization value'
  require_pattern "$BRIDGE_PROOF" \
    'ap[[:space:]]*=[[:space:]]*r1_post' \
    'poly_tobytes procedure input specialization'
  require_pattern "$BRIDGE_PROOF" \
    'res[[:space:]]*=[[:space:]]*buf2' \
    'value-flow procedure postcondition'

  require_lemma "$PREDECESSOR_BRIDGE" decap_r1_ntt_poly_tobytes_ready
  require_lemma "$POLY_TOBYTES_PROOF" poly_tobytes_functional
  require_lemma "$POLY_TOBYTES_PROOF" poly_tobytes_lossless
  require_lemma "$POLY_TOBYTES_PROOF" poly_tobytes_correct
  require_lemma "$POLY_TOBYTES_ALGEBRA" poly_tobytes_procedure_specE
  require_lemma "$BRIDGE_PROOF" decap_r1_ntt_to_tobytes_value_flow
  require_lemma "$BRIDGE_PROOF" decap_r1_tobytes_input_qrange
  require_lemma "$BRIDGE_PROOF" decap_r1_tobytes_algebra_spec
  require_lemma "$BRIDGE_PROOF" decap_r1_tobytes_functional
  require_lemma "$BRIDGE_PROOF" decap_r1_tobytes_lossless
  require_lemma "$BRIDGE_PROOF" decap_r1_tobytes_correct
  require_lemma "$BRIDGE_PROOF" decap_r1_tobytes_value_flow_functional
  require_lemma "$BRIDGE_PROOF" decap_r1_tobytes_value_flow_correct
  require_lemma "$BRIDGE_PROOF" decap_terminal_r1_tobytes_functional
  require_lemma "$BRIDGE_PROOF" decap_terminal_r1_tobytes_correct

  bash -n "$0"
  reject_proof_holes
  compile_bridge
  make -C "$TEST_DIR" CC="$CC_BIN" JASMINC="$JASMINC_BIN" \
    OUTDIR="$WORKDIR/test" all
  run_predecessor_regressions
  run_poly_tobytes_regressions

  printf 'PASS: NTRU+768 decap-r1 poly_tobytes bridge proof and proof-hole checks\n'
  printf 'PASS: NTRU+768 exact r1 NTT output range feeds the verified poly_tobytes procedure\n'
  printf 'PASS: NTRU+768 concrete hash_h -> poly_cbd1 -> in-place poly_ntt -> poly_tobytes -> verify seam checks\n'
  printf 'PASS: NTRU+768 61-vector Python CBD / C+Jasmin NTT / independent packing / C+Jasmin poly_tobytes differential and UBSan checks\n'
  printf 'PASS: NTRU+768 predecessor decap-r1-ntt and standalone poly_tobytes proofs/tests/regressions\n'
  printf '%s\n' \
    'SCOPE: exact r1 serialization through poly_tobytes before verify semantics; verify/fail-mask behavior, fallback selection, reencryption comparison, pointer aliasing, C-AST equivalence, and full-KEM correctness remain out of scope'
}

main "$@"
