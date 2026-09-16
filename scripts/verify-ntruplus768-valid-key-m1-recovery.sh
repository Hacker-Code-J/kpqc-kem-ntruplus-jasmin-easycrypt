#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/valid_key_m1_recovery"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/valid_key_m1_recovery"
FULL_PREDECESSOR=${NTRUPLUS768_FULL_PREDECESSOR:-0}
WORKDIR=$(mktemp -d "${TMPDIR:-/tmp}/ntruplus768-valid-key-m1-recovery.XXXXXX")

PROOFS=(
  NTRUPlus768CoefficientRecovery.ec
  NTRUPlus768IntegerConvolution.ec
  NTRUPlus768Crepmod3Recovery.ec
  NTRUPlus768ValidKeyM1Recovery.ec
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
  local proof status
  for proof in "${PROOFS[@]}"; do
    [[ -f "$PROOF_DIR/$proof" ]] || fail "missing proof: $proof"
  done
  [[ -f "$PROOF_DIR/easycrypt.project" ]] || fail "missing EasyCrypt project"
  [[ -f "$PROOF_DIR/Makefile" ]] || fail "missing proof Makefile"
  [[ -f "$TEST_DIR/Makefile" ]] || fail "missing test Makefile"
  [[ -f "$TEST_DIR/valid_key_m1_recovery_driver.c" ]] || fail "missing runtime oracle"
  if grep -ERni --include='*.ec' \
      '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry|abort)([^[:alnum:]_]|$)' \
      "$PROOF_DIR" >"$WORKDIR/proof-holes.txt"; then
    sed -n '1,100p' "$WORKDIR/proof-holes.txt" >&2
    fail "recovery proof contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "proof-hole scan failed"
  fi
  require_declaration NTRUPlus768CoefficientRecovery.ec op int_poly
  require_declaration NTRUPlus768CoefficientRecovery.ec lemma eqm_global_int_poly_coeff
  require_declaration NTRUPlus768IntegerConvolution.ec op integer_product
  require_declaration NTRUPlus768IntegerConvolution.ec lemma integer_product_eqm_global
  require_declaration NTRUPlus768Crepmod3Recovery.ec lemma poly_crepmod3_exact_recovery
  require_declaration NTRUPlus768Crepmod3Recovery.ec lemma poly_crepmod3_exact_recovery_correct
  require_declaration NTRUPlus768ValidKeyM1Recovery.ec op sampled_m1_integer_lift
  require_declaration NTRUPlus768ValidKeyM1Recovery.ec op sampled_m1_no_wrap
  require_declaration NTRUPlus768ValidKeyM1Recovery.ec lemma sampled_m1_integer_lift_semantics
  require_declaration NTRUPlus768ValidKeyM1Recovery.ec lemma keygen_secret_f_no_wrap_m1_recovery
  require_declaration NTRUPlus768ValidKeyM1Recovery.ec lemma keygen_secret_f_no_wrap_sotp_recovery
}

main() {
  local command proof easycrypt_bin cc_bin
  for command in bash easycrypt grep make; do
    command -v "$command" >/dev/null 2>&1 || fail "missing command: $command"
  done
  cc_bin=$(command -v "${CC:-cc}") || fail "missing C compiler: ${CC:-cc}"
  case "$FULL_PREDECESSOR" in
    0|1) ;;
    *) fail "NTRUPLUS768_FULL_PREDECESSOR must be 0 or 1" ;;
  esac
  easycrypt_bin=$(command -v easycrypt)
  bash -n "$0"
  check_sources

  # Each new theory is a primary compile target: do not rely on importing
  # a theory as evidence that its proof scripts were independently checked.
  for proof in "${PROOFS[@]}"; do
    printf 'VERIFY: %s\n' "$proof"
    if ! (
      cd "$PROOF_DIR"
      "$easycrypt_bin" compile -no-eco -p Z3 -timeout 30 -max-provers 1 \
        "$proof"
    ); then
      fail "EasyCrypt verification failed: $proof"
    fi
  done

  make -C "$TEST_DIR" OUTDIR="$WORKDIR/tests" CC="$cc_bin" all
  if [[ "$FULL_PREDECESSOR" == 1 ]]; then
    "$SCRIPT_DIR/verify-ntruplus768-keygen-secret-f.sh"
    "$SCRIPT_DIR/verify-ntruplus768-crepmod3.sh"
    "$SCRIPT_DIR/verify-ntruplus768-poly-sotp-roundtrip.sh"
  else
    printf 'NOTE: set NTRUPLUS768_FULL_PREDECESSOR=1 for predecessor verifier replay\n'
  fi
  printf 'PASS: integer cyclotomic convolution represents the global polynomial product\n'
  printf 'PASS: low-degree global congruence yields coefficientwise congruence modulo q\n'
  printf 'PASS: sampled no-wrap condition implies exact m1 recovery with decoded secret f\n'
  printf 'PASS: exact Jasmin crepmod3 contracts and same-pad SOTP round trip\n'
  printf 'PASS: independent integer oracle, centered-boundary and wrap-counterexample regressions, normal and UBSan\n'
  printf '%s\n' 'SCOPE: conditional array-value recovery; no universal no-wrap or failure-probability bound, actual decapsulation-pad agreement, formal production-C equivalence, or full-KEM theorem'
}

main "$@"
