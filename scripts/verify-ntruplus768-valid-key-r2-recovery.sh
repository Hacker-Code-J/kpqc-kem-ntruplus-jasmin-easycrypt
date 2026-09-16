#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/valid_key_r2_recovery"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/valid_key_r2_recovery"
FULL_PREDECESSOR=${NTRUPLUS768_FULL_PREDECESSOR:-0}
WORKDIR=$(mktemp -d "${TMPDIR:-/tmp}/ntruplus768-valid-key-r2-recovery.XXXXXX")

PROOFS=(
  NTRUPlus768R2Serialization.ec
  NTRUPlus768ValidKeyR2Algebra.ec
  NTRUPlus768ValidKeyR2Recovery.ec
)

cleanup() {
  rm -rf -- "$WORKDIR"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

fail() {
  printf 'FAIL: %s\n' "$1" >&2
  exit 1
}

require_declaration() {
  local file=$1 kind=$2 name=$3
  grep -Eq "^$kind[[:space:]]+$name([[:space:](]|$)" "$PROOF_DIR/$file" ||
    fail "missing $kind $name in $file"
}

check_sources() {
  local proof status file
  for proof in "${PROOFS[@]}"; do
    [[ -f "$PROOF_DIR/$proof" ]] || fail "missing proof: $proof"
  done
  for file in easycrypt.project Makefile; do
    [[ -f "$PROOF_DIR/$file" ]] || fail "missing proof file: $file"
  done
  for file in Makefile valid_key_r2_recovery_driver.c check_valid_key_r2_recovery.py; do
    [[ -f "$TEST_DIR/$file" ]] || fail "missing test file: $file"
  done
  if grep -ERni --include='*.ec' \
      '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry|abort)([^[:alnum:]_]|$)' \
      "$PROOF_DIR" >"$WORKDIR/proof-holes.txt"; then
    sed -n '1,100p' "$WORKDIR/proof-holes.txt" >&2
    fail "r2 recovery proof contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "proof-hole scan failed"
  fi
  require_declaration NTRUPlus768R2Serialization.ec op r2_serialization_relation
  require_declaration NTRUPlus768R2Serialization.ec lemma poly_tobytes_mod_q_congr
  require_declaration NTRUPlus768R2Serialization.ec lemma decoded_cipher_product_transfer
  require_declaration NTRUPlus768ValidKeyR2Algebra.ec lemma keygen_h_hinv_inverse
  require_declaration NTRUPlus768ValidKeyR2Algebra.ec lemma valid_key_r2_mod_q
  require_declaration NTRUPlus768ValidKeyR2Recovery.ec op serialized_hash_g_pad
  require_declaration NTRUPlus768ValidKeyR2Recovery.ec op r2_pad_message_recovery
  require_declaration NTRUPlus768ValidKeyR2Recovery.ec lemma serialized_cipher_no_wrap_m1_recovery
  require_declaration NTRUPlus768ValidKeyR2Recovery.ec lemma serialized_r2_pad_agreement
  require_declaration NTRUPlus768ValidKeyR2Recovery.ec lemma no_wrap_serialized_message_recovery
}

main() {
  local command proof easycrypt_bin cc_bin
  for command in bash easycrypt grep make python3; do
    command -v "$command" >/dev/null 2>&1 || fail "missing command: $command"
  done
  cc_bin=$(command -v "${CC:-gcc}") || fail "missing compiler: ${CC:-gcc}"
  case "$FULL_PREDECESSOR" in
    0|1) ;;
    *) fail "NTRUPLUS768_FULL_PREDECESSOR must be 0 or 1" ;;
  esac
  easycrypt_bin=$(command -v easycrypt)
  bash -n "$0"
  check_sources

  # Check every new theory as a primary target, independently of imports.
  for proof in "${PROOFS[@]}"; do
    printf 'VERIFY: %s\n' "$proof"
    if ! (
      cd "$PROOF_DIR"
      "$easycrypt_bin" compile -no-eco -p Z3 -timeout 30 -max-provers 1 "$proof"
    ); then
      fail "EasyCrypt verification failed: $proof"
    fi
  done
  make -C "$TEST_DIR" OUTDIR="$WORKDIR/tests" CC="$cc_bin" all
  if [[ "$FULL_PREDECESSOR" == 1 ]]; then
    "$SCRIPT_DIR/verify-ntruplus768-valid-key-m1-recovery.sh"
    "$SCRIPT_DIR/verify-ntruplus768-decap-r2.sh"
    "$SCRIPT_DIR/verify-ntruplus768-decap-hash-g.sh"
  else
    printf 'NOTE: set NTRUPLUS768_FULL_PREDECESSOR=1 for predecessor verifier replay\n'
  fi
  printf 'PASS: ciphertext and secret hinv block decoding preserve the needed congruences\n'
  printf 'PASS: the successful keypair relation proves h*hinv=1 in each terminal quartic\n'
  printf 'PASS: conditional r2 congruence yields exact canonical serialization equality\n'
  printf 'PASS: hash_g pad equality and SOTP message recovery are derived, not assumed\n'
  printf 'PASS: source mutations, representative invariance, normal/UBSan recovery regressions, GCC analysis\n'
  printf '%s\n' 'SCOPE: conditional array-value message recovery under key/arithmetic contracts and no-wrap; no full C-memory or C/Jasmin equivalence, full-KEM/shared-secret theorem, or failure-probability estimate'
}

main "$@"
