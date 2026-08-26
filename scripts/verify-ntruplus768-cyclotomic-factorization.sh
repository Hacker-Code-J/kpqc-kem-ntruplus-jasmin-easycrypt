#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ring_semantics"
PROOF_FILE="$PROOF_DIR/NTRUPlus768CyclotomicFactorization.ec"
SCHEDULE_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_schedule"
FQINV_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/fqinv"
BASEMUL_PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/basemul"
SCHEDULE_TEST_DIR="$REPO_ROOT/tests/ntruplus768/ntt_schedule"
NTT_SOURCE="$REPO_ROOT/NTRU+/NTRU+768/ntt.c"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-cyclotomic-factorization.XXXXXX")

cleanup() {
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

require_lemma() {
  local lemma=$1

  grep -Eq "^lemma[[:space:]]+$lemma([[:space:](]|$)" "$PROOF_FILE" ||
    fail "missing required EasyCrypt lemma: $lemma"
}

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
    '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
    "$PROOF_DIR" "$SCHEDULE_PROOF_DIR" "$FQINV_PROOF_DIR" \
    "$BASEMUL_PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "cyclotomic factorization proof tree contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the proof tree for holes"
  fi
}

compile_easycrypt_via_makefile() {
  local easycrypt_bin

  easycrypt_bin=$(command -v easycrypt)
  if ! make -C "$PROOF_DIR" check EASYCRYPT="$easycrypt_bin"; then
    fail "EasyCrypt cyclotomic factorization proof failed"
  fi
}

main() {
  require_command bash
  require_command easycrypt
  require_command grep
  require_command make
  require_command python3

  [[ -f "$PROOF_FILE" ]] || fail "missing EasyCrypt proof: $PROOF_FILE"
  [[ -f "$PROOF_DIR/Makefile" ]] || fail "missing proof Makefile"
  [[ -f "$NTT_SOURCE" ]] || fail "missing authoritative NTT source: $NTT_SOURCE"

  bash -n "$0"
  require_lemma figure22_indices192_uniq
  require_lemma factor_split_tree
  require_lemma scheduled_factorization
  require_lemma terminal_root_fieldE
  require_lemma terminal_factor_productE
  require_lemma terminal_linear_factorization
  require_lemma terminal_quartic_factorization
  require_lemma terminal_quartic_factorization_explicit
  reject_proof_holes
  make -C "$SCHEDULE_TEST_DIR" selfcheck SOURCE="$NTT_SOURCE"
  make -C "$SCHEDULE_TEST_DIR" check SOURCE="$NTT_SOURCE"
  compile_easycrypt_via_makefile

  printf 'PASS: cyclotomic factorization verifier syntax check\n'
  printf 'PASS: required cyclotomic factorization theorem surface\n'
  printf 'PASS: proof-hole scan for factorization and dependencies\n'
  printf 'PASS: NTRU+768 NTT schedule predecessor\n'
  printf 'PASS: EasyCrypt NTRU+768 cyclotomic quartic factorization\n'
}

main "$@"
