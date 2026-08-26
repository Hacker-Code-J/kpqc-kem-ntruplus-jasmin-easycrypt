#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
UPSTREAM_URL=https://github.com/ntruplus/ntruplus.git
BASELINE_COMMIT=38201624477a7dbb2f46d1ae7686ae5ceee4eb80
TARGET_COMMIT=3991b2ae08d6f0008d37e41b8aceaaab27b4ec89
LOCAL_SRC="$REPO_ROOT/NTRU+/NTRU+768"
LOCAL_KAT="$REPO_ROOT/NTRU+/KAT/NTRU+768"
PROVENANCE="$REPO_ROOT/THIRD_PARTY.md"
BASELINE_VERIFIER="$SCRIPT_DIR/verify-ntruplus768-baseline.sh"
LOCAL_PATCH="$REPO_ROOT/patches/ntruplus768-3820162-comment-fix.patch"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-upstream-audit.XXXXXX")
UPSTREAM_REPO="$WORKDIR/upstream"
BASELINE_TREE="$WORKDIR/baseline"
TARGET_TREE="$WORKDIR/target"

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

require_file() {
  [[ -f "$1" ]] || fail "missing required file: $1"
}

require_pattern() {
  local file=$1
  local pattern=$2
  local label=$3

  grep -Eq "$pattern" "$file" || fail "candidate target is missing $label"
}

reject_pattern() {
  local file=$1
  local pattern=$2
  local label=$3

  if grep -Eq "$pattern" "$file"; then
    fail "verified baseline unexpectedly contains $label"
  fi
}

extract_tree() {
  local commit=$1
  local destination=$2

  mkdir -p "$destination"
  git -C "$UPSTREAM_REPO" archive "$commit" \
    Reference_Implementation/NTRU+768 KAT/NTRU+768 \
    | tar -xf - -C "$destination"
}

require_tree_match() {
  local actual=$1
  local expected=$2
  local label=$3
  local findings="$WORKDIR/tree-diff.txt"

  if ! diff -qr "$actual" "$expected" >"$findings"; then
    sed -n '1,80p' "$findings" >&2
    fail "$label does not byte-match the pinned upstream baseline"
  fi
}

fetch_upstream() {
  if [[ -n "${NTRUPLUS_UPSTREAM_REPO:-}" ]]; then
    UPSTREAM_REPO=$(cd -- "$NTRUPLUS_UPSTREAM_REPO" && pwd)
  else
    git clone --filter=blob:none --no-checkout --quiet \
      "$UPSTREAM_URL" "$UPSTREAM_REPO"
  fi

  git -C "$UPSTREAM_REPO" cat-file -e "$BASELINE_COMMIT^{commit}" ||
    fail "upstream repository does not contain baseline commit $BASELINE_COMMIT"
  git -C "$UPSTREAM_REPO" cat-file -e "$TARGET_COMMIT^{commit}" ||
    fail "upstream repository does not contain target commit $TARGET_COMMIT"
}

check_changed_file_set() {
  local changed="$WORKDIR/changed-files.txt"
  local changed_count
  local insertions
  local deletions

  git -C "$UPSTREAM_REPO" diff --name-only \
    "$BASELINE_COMMIT" "$TARGET_COMMIT" -- \
    Reference_Implementation/NTRU+768 >"$changed"
  changed_count=$(wc -l <"$changed")
  [[ $changed_count -eq 15 ]] ||
    fail "expected 15 changed NTRU+768 reference files, found $changed_count"
  read -r insertions deletions < <(
    git -C "$UPSTREAM_REPO" diff --numstat \
      "$BASELINE_COMMIT" "$TARGET_COMMIT" -- \
      Reference_Implementation/NTRU+768 \
      | awk '{ insertions += $1; deletions += $2 } END { print insertions + 0, deletions + 0 }'
  )
  [[ $insertions -eq 319 && $deletions -eq 611 ]] ||
    fail "unexpected NTRU+768 delta size: +$insertions/-$deletions"

  printf 'INFO: changed NTRU+768 reference files (%d, +%d/-%d):\n' \
    "$changed_count" "$insertions" "$deletions"
  sed -n '1,80p' "$changed"

  if ! git -C "$UPSTREAM_REPO" diff --quiet \
      "$BASELINE_COMMIT" "$TARGET_COMMIT" -- KAT/NTRU+768; then
    fail "candidate target changes the NTRU+768 KAT tree"
  fi
}

check_semantic_delta_fingerprints() {
  local baseline_src="$BASELINE_TREE/Reference_Implementation/NTRU+768"
  local target_src="$TARGET_TREE/Reference_Implementation/NTRU+768"

  require_pattern "$target_src/poly.h" \
    'int[[:space:]]+poly_frombytes' 'fallible poly_frombytes ABI'
  require_pattern "$target_src/poly.c" \
    'return[[:space:]]+fail[[:space:]]*>>[[:space:]]*31' \
    'canonical polynomial-decoding rejection'
  require_pattern "$target_src/kem.c" \
    'if[[:space:]]*\(poly_frombytes\(&h,[[:space:]]*pk\)\)' \
    'invalid-public-key encapsulation branch'
  require_pattern "$target_src/kem.c" \
    'fail[[:space:]]*=[[:space:]]*1' \
    'fail-closed decapsulation initialization'
  require_pattern "$target_src/kem.c" \
    'ntruplus_declassify' 'key-generation retry-status declassification'
  require_pattern "$target_src/kem.c" \
    'secure_clear' 'KEM temporary-state clearing'
  require_pattern "$target_src/ntt.h" \
    'void[[:space:]]+ntt\(int16_t[[:space:]]+r\[NTRUPLUS_N\]\)' \
    'in-place NTT ABI'
  require_pattern "$target_src/ntt.c" \
    'shortest addition chain' 'revised fqinv addition chain'
  require_pattern "$target_src/ntt.c" \
    'r\[i\][[:space:]]*=[[:space:]]*barrett_reduce\(r\[i\]\)' \
    'deferred whole-array NTT reduction'
  require_pattern "$target_src/poly.h" \
    'void[[:space:]]+poly_triple\(poly[[:space:]]*\*r\)' \
    'in-place poly_triple ABI'
  require_pattern "$target_src/poly.h" \
    'void[[:space:]]+poly_crepmod3\(poly[[:space:]]*\*r\)' \
    'in-place poly_crepmod3 ABI'

  reject_pattern "$baseline_src/poly.c" \
    'return[[:space:]]+fail[[:space:]]*>>[[:space:]]*31' \
    'canonical polynomial-decoding rejection'
  reject_pattern "$baseline_src/kem.c" \
    'ntruplus_declassify' 'key-generation retry-status declassification'
  reject_pattern "$baseline_src/kem.c" \
    'secure_clear' 'KEM temporary-state clearing'
}

run_candidate_baseline() {
  local candidate_src="$TARGET_TREE/Reference_Implementation/NTRU+768"
  local candidate_rsp="$TARGET_TREE/KAT/NTRU+768/PQCkemKAT_2336.rsp"

  NTRUPLUS768_SRC_DIR="$candidate_src" \
  NTRUPLUS768_EXPECTED_RSP="$candidate_rsp" \
    "$BASELINE_VERIFIER"
}

report_head() {
  local upstream_head
  local upstream_main

  if ! upstream_head=$(git -C "$UPSTREAM_REPO" rev-parse refs/remotes/origin/HEAD 2>/dev/null); then
    printf 'INFO: local upstream repository has no origin/HEAD; audited target remains %s\n' \
      "$TARGET_COMMIT"
    return 0
  fi
  if ! upstream_main=$(git -C "$UPSTREAM_REPO" rev-parse refs/remotes/origin/main 2>/dev/null); then
    printf 'WARN: upstream repository has no origin/main; audited target remains %s\n' \
      "$TARGET_COMMIT"
    return 0
  fi
  if [[ "$upstream_head" == "$TARGET_COMMIT" && "$upstream_main" == "$TARGET_COMMIT" ]]; then
    printf 'PASS: candidate target is the current upstream HEAD and main (%s)\n' \
      "$TARGET_COMMIT"
  else
    printf 'WARN: upstream HEAD=%s main=%s; audited target remains %s\n' \
      "$upstream_head" "$upstream_main" "$TARGET_COMMIT"
  fi
}

main() {
  require_command awk
  require_command diff
  require_command git
  require_command grep
  require_command make
  require_command patch
  require_command tar
  require_file "$PROVENANCE"
  require_file "$BASELINE_VERIFIER"
  require_file "$LOCAL_PATCH"
  require_file "$LOCAL_SRC/kem.c"
  require_file "$LOCAL_KAT/PQCkemKAT_2336.rsp"

  grep -Fq "$BASELINE_COMMIT" "$PROVENANCE" ||
    fail "THIRD_PARTY.md does not pin the verified baseline commit"
  bash -n "$0"
  fetch_upstream
  extract_tree "$BASELINE_COMMIT" "$BASELINE_TREE"
  extract_tree "$TARGET_COMMIT" "$TARGET_TREE"
  patch --silent -p1 -d "$BASELINE_TREE" <"$LOCAL_PATCH"

  require_tree_match "$LOCAL_SRC" \
    "$BASELINE_TREE/Reference_Implementation/NTRU+768" \
    'local NTRU+768 reference tree'
  require_tree_match "$LOCAL_KAT" "$BASELINE_TREE/KAT/NTRU+768" \
    'local NTRU+768 KAT tree'
  check_changed_file_set
  check_semantic_delta_fingerprints
  run_candidate_baseline
  report_head

  printf 'PASS: local verified baseline matches upstream %s plus the tracked comment-only patch\n' \
    "$BASELINE_COMMIT"
  printf 'PASS: candidate %s preserves the NTRU+768 KAT tree and regenerates it exactly\n' \
    "$TARGET_COMMIT"
  printf 'PASS: canonical decoding, invalid-input, in-place ABI, reduction, fqinv, and clearing deltas are present\n'
  printf '%s\n' \
    'RESULT: migration is required before claiming the current official NTRU+768 implementation as the verified paper target'
  printf '%s\n' \
    'SCOPE: provenance, source/KAT delta, semantic fingerprint, functional test, and KAT audit only; no mutation of imported sources and no claim that existing Jasmin/EasyCrypt proofs cover the candidate target'
}

main "$@"
