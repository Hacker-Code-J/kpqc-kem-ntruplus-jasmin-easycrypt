#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/poly_sotp_roundtrip"
ENCODE_PROOF="$PROOF_DIR/NTRUPlus768PolySOTPEncodeAlgebra.ec"
ROUNDTRIP_PROOF="$PROOF_DIR/NTRUPlus768PolySOTPRoundTrip.ec"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/poly_sotp_roundtrip"
ROUNDTRIP_DRIVER="$TEST_DIR/poly_sotp_roundtrip_driver.c"
CBD1_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-decap-poly-cbd1.sh"
LATEST_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-encap-hash-f-agreement.sh"
NTRU_ROOT="$REPO_ROOT/NTRU+/NTRU+768"
PARAMS_SOURCE="$NTRU_ROOT/params.h"
POLY_SOURCE="$NTRU_ROOT/poly.c"
POLY_HEADER="$NTRU_ROOT/poly.h"
KEM_SOURCE="$NTRU_ROOT/kem.c"
JASMIN_SOURCE="$REPO_ROOT/ntruplus/jasmin/768/ref/poly_sotp_decode.jazz"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-sotp-roundtrip.XXXXXX")
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

  if [[ -n "${JASMINC:-}" ]]; then
    command -v "$JASMINC" >/dev/null 2>&1 ||
      fail "configured Jasmin compiler is unavailable: $JASMINC"
    JASMINC_BIN=$(command -v "$JASMINC")
  else
    require_command jasminc
    JASMINC_BIN=$(command -v jasminc)
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
    fail "poly_sotp round-trip theories contain a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] ||
      fail "could not scan poly_sotp round-trip theories for proof holes"
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
  resolve_tools

  easycrypt_bin=$(command -v easycrypt)
  easycrypt_bindir=$(cd -- "$(dirname -- "$easycrypt_bin")" && pwd)
  WHY3SERVER_BIN="$easycrypt_bindir/../lib/why3/why3server"
  [[ -x "$WHY3SERVER_BIN" ]] ||
    fail "missing Why3 server next to the EasyCrypt installation: $WHY3SERVER_BIN"

  require_file "$ENCODE_PROOF"
  require_file "$ROUNDTRIP_PROOF"
  require_file "$PROOF_DIR/easycrypt.project"
  require_file "$PROOF_DIR/Makefile"
  require_file "$TEST_DIR/Makefile"
  require_file "$TEST_DIR/check_poly_sotp_roundtrip.py"
  require_file "$TEST_DIR/check_poly_sotp_roundtrip_vectors.py"
  require_file "$ROUNDTRIP_DRIVER"
  require_file "$CBD1_VERIFIER"
  require_file "$LATEST_VERIFIER"
  require_file "$PARAMS_SOURCE"
  require_file "$POLY_SOURCE"
  require_file "$POLY_HEADER"
  require_file "$KEM_SOURCE"
  require_file "$JASMIN_SOURCE"

  require_pattern "$ENCODE_PROOF" \
    'pad\.\[k\][[:space:]]*\+\^[[:space:]]*msg\.\[k\]' \
    'XORed 96-byte encode head'
  require_pattern "$ENCODE_PROOF" \
    'NTRUPlus768PolyCBD1Algebra\.poly_cbd1_spec' \
    'existing poly_cbd1 value specification reuse'
  require_pattern "$ROUNDTRIP_PROOF" \
    'pad[[:space:]]*=[[:space:]]*\(msg,[[:space:]]*false\)' \
    'same-pad decoded message and false failure result'
  require_pattern "$ROUNDTRIP_DRIVER" \
    'encoded\.coeffs\[8[[:space:]]*\*[[:space:]]*i[[:space:]]*\+[[:space:]]*j\][[:space:]]*!=[[:space:]]*expected' \
    'all-768-coefficient runtime oracle'
  reject_pattern "$ENCODE_PROOF" \
    '^require import .*(DecapBridge|Hash|NTT)' \
    'direct decapsulation/hash/NTT import in encode algebra'
  reject_pattern "$ROUNDTRIP_PROOF" \
    '^require import .*(DecapBridge|Hash|NTT)' \
    'direct decapsulation/hash/NTT import in round-trip theorem'

  require_lemma "$ENCODE_PROOF" poly_sotp_bit_b2i
  require_lemma "$ENCODE_PROOF" poly_sotp_encode_input_head_byte
  require_lemma "$ENCODE_PROOF" poly_sotp_encode_input_tail_byte
  require_lemma "$ENCODE_PROOF" poly_sotp_encode_input_head_bit
  require_lemma "$ENCODE_PROOF" poly_sotp_encode_input_tail_bit
  require_lemma "$ENCODE_PROOF" poly_sotp_encode_spec_coeff
  require_lemma "$ENCODE_PROOF" poly_sotp_encode_sum_int_xor
  require_lemma "$ENCODE_PROOF" poly_sotp_encode_sum_valid
  require_lemma "$ENCODE_PROOF" poly_sotp_encode_fail_spec
  require_lemma "$ENCODE_PROOF" poly_sotp_encode_fail_spec_false
  require_lemma "$ROUNDTRIP_PROOF" xor_b2i_cancel_mod2
  require_lemma "$ROUNDTRIP_PROOF" poly_sotp_encode_decoded_bit
  require_lemma "$ROUNDTRIP_PROOF" poly_sotp_encode_raw_byte_int
  require_lemma "$ROUNDTRIP_PROOF" poly_sotp_encode_raw_byte
  require_lemma "$ROUNDTRIP_PROOF" poly_sotp_encode_raw_msg
  require_lemma "$ROUNDTRIP_PROOF" poly_sotp_encode_decode_msg
  require_lemma "$ROUNDTRIP_PROOF" poly_sotp_encode_decode_spec
  require_lemma "$ROUNDTRIP_PROOF" poly_sotp_encode_decode_roundtrip

  bash -n "$0"
  reject_proof_holes
  compile_easycrypt_target "$ENCODE_PROOF" \
    "poly_sotp_encode Array96/Array192 value algebra"
  compile_easycrypt_target "$ROUNDTRIP_PROOF" \
    "poly_sotp encode/decode inverse theorem"
  make -C "$TEST_DIR" CC="$CC_BIN" JASMINC="$JASMINC_BIN" \
    OUTDIR="$WORKDIR/test" all
  "$CBD1_VERIFIER"
  "$LATEST_VERIFIER"

  printf 'PASS: NTRU+768 poly_sotp_encode uses (pad[0..95] XOR msg) || pad[96..191]\n'
  printf 'PASS: NTRU+768 encoded CBD1 coefficients make every decode sum valid\n'
  printf 'PASS: NTRU+768 same-pad poly_sotp_decode returns the original Array96 and fail=false\n'
  printf 'PASS: NTRU+768 exact encode caller seam and 12 negative source mutations\n'
  printf 'PASS: NTRU+768 55-vector C, UBSan, and Jasmin decode round-trip checks\n'
  printf 'PASS: NTRU+768 coefficient oracle plus CBD1 and full latest predecessor regressions\n'
  printf '%s\n' \
    'SCOPE: exact Array96/Array192 encode value and same-pad decode inverse with source/runtime anchors; no proof that encapsulation and decapsulation derive the same pad, formal C/Jasmin procedure equivalence, NTT/ciphertext/key or r-recovery relation, hash_g/hash_h/shared-secret agreement, API agreement, or full-KEM correctness'
}

main "$@"
