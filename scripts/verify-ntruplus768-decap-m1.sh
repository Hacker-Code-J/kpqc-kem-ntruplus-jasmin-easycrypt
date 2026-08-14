#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF="$REPO_ROOT/ntruplus/proof/768/ref/poly_frombytes/NTRUPlus768PolyFromBytesAlgebra.ec"
POLY_FROMBYTES_VERIFIER="$REPO_ROOT/scripts/verify-ntruplus768-poly-frombytes.sh"
INVNTT_VERIFIER="$REPO_ROOT/scripts/verify-ntruplus768-invntt.sh"

fail() {
  printf 'FAIL: %s\n' "$1" >&2
  exit 1
}

require_command() {
  command -v "$1" >/dev/null 2>&1 || fail "missing required command: $1"
}

require_lemma_declaration() {
  local lemma_name=$1

  grep -Eq "^lemma ${lemma_name}([[:space:]]|$)" "$PROOF" ||
    fail "missing required terminal lemma declaration: $lemma_name"
}

main() {
  require_command bash
  require_command grep

  bash -n "$0"

  [[ -f "$PROOF" ]] || fail "missing decap-m1 EasyCrypt proof"
  [[ -x "$POLY_FROMBYTES_VERIFIER" ]] ||
    fail "missing executable poly_frombytes verifier"
  [[ -x "$INVNTT_VERIFIER" ]] ||
    fail "missing executable inverse-NTT verifier with exact-alias coverage"

  require_lemma_declaration poly_frombytes_two_decoder_specs_inverse_invntt_spec_algebra
  require_lemma_declaration poly_frombytes_two_decoder_specs_inverse_invntt_output_qrange

  "$POLY_FROMBYTES_VERIFIER"
  "$INVNTT_VERIFIER"

  printf 'PASS: verify-ntruplus768-decap-m1.sh syntax check\n'
  printf 'PASS: NTRU+768 decap m1 terminal lemma declarations and value-flow proof compile\n'
  printf 'PASS: NTRU+768 authoritative decoded-input/crypto_kem_dec seam regression\n'
  printf 'PASS: NTRU+768 inverse-NTT exact-alias, differential, and proof regression\n'
  printf 'PASS: NTRU+768 decap m1 package is value-flow only; no shared-memory/pointer-identity theorem claimed\n'
}

main "$@"
