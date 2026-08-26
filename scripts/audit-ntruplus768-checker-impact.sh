#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
UPSTREAM_URL=https://github.com/ntruplus/ntruplus.git
TARGET_COMMIT=3991b2ae08d6f0008d37e41b8aceaaab27b4ec89
VERIFIED_TREE_COMMIT=d2cb239d262fb4f656992d6bd7e6220dc82748b4

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-checker-impact.XXXXXX")
BASELINE_REPO="$WORKDIR/baseline"
CANDIDATE_REPO="$WORKDIR/candidate"
UPSTREAM_REPO="$WORKDIR/upstream"
TARGET_TREE="$WORKDIR/target"
BASELINE_SUMMARY="$WORKDIR/baseline-summary.tsv"
CANDIDATE_SUMMARY="$WORKDIR/candidate-summary.tsv"

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

clone_inputs() {
  git clone --shared --no-checkout --quiet "$REPO_ROOT" "$BASELINE_REPO"
  git clone --shared --no-checkout --quiet "$REPO_ROOT" "$CANDIDATE_REPO"
  git -C "$BASELINE_REPO" checkout --quiet "$VERIFIED_TREE_COMMIT" ||
    fail "local repository does not contain verified tree $VERIFIED_TREE_COMMIT"
  git -C "$CANDIDATE_REPO" checkout --quiet "$VERIFIED_TREE_COMMIT" ||
    fail "local repository does not contain verified tree $VERIFIED_TREE_COMMIT"

  if [[ -n "${NTRUPLUS_UPSTREAM_REPO:-}" ]]; then
    UPSTREAM_REPO=$(cd -- "$NTRUPLUS_UPSTREAM_REPO" && pwd)
  else
    git clone --filter=blob:none --no-checkout --quiet \
      "$UPSTREAM_URL" "$UPSTREAM_REPO"
  fi
  git -C "$UPSTREAM_REPO" cat-file -e "$TARGET_COMMIT^{commit}" ||
    fail "upstream repository does not contain target commit $TARGET_COMMIT"

  mkdir -p "$TARGET_TREE"
  git -C "$UPSTREAM_REPO" archive "$TARGET_COMMIT" \
    Reference_Implementation/NTRU+768 KAT/NTRU+768 \
    | tar -xf - -C "$TARGET_TREE"

  rm -rf "$CANDIDATE_REPO/NTRU+/NTRU+768" \
    "$CANDIDATE_REPO/NTRU+/KAT/NTRU+768"
  mkdir -p "$CANDIDATE_REPO/NTRU+/NTRU+768" \
    "$CANDIDATE_REPO/NTRU+/KAT/NTRU+768"
  cp -a "$TARGET_TREE/Reference_Implementation/NTRU+768/." \
    "$CANDIDATE_REPO/NTRU+/NTRU+768/"
  cp -a "$TARGET_TREE/KAT/NTRU+768/." \
    "$CANDIDATE_REPO/NTRU+/KAT/NTRU+768/"
}

first_failure_line() {
  local log=$1
  local first

  first=$(grep -Em1 '(failed:|FAIL:|FAILED:|error:|Error )' "$log" || true)
  if [[ -z "$first" ]]; then
    first=$(sed -n '2p' "$log")
  fi
  printf '%s' "$first" | tr '\t\n' '  '
}

run_matrix() {
  local repo=$1
  local summary=$2
  local makefile
  local dir
  local phony
  local target
  local log
  local first

  : >"$summary"
  while IFS= read -r makefile; do
    dir=$(dirname -- "$makefile")
    phony=$(sed -n 's/^\.PHONY:[[:space:]]*//p' "$repo/$makefile")
    for target in check selfcheck; do
      if [[ " $phony " != *" $target "* ]]; then
        printf '%s\t%s\tSKIP\tmissing-target\n' \
          "$dir" "$target" >>"$summary"
        continue
      fi

      log="$WORKDIR/$(basename -- "$repo")-$(basename -- "$dir")-$target.log"
      if make -s -C "$repo/$dir" "$target" >"$log" 2>&1; then
        printf '%s\t%s\tPASS\t-\n' "$dir" "$target" >>"$summary"
      else
        first=$(first_failure_line "$log")
        printf '%s\t%s\tFAIL\t%s\n' \
          "$dir" "$target" "$first" >>"$summary"
      fi
    done
  done < <(
    cd "$repo"
    find tests/ntruplus768 -mindepth 2 -maxdepth 2 -name Makefile \
      -printf '%p\n' | sort
  )
}

count_status() {
  local summary=$1
  local status=$2

  awk -F '\t' -v status="$status" '$3 == status { count += 1 } END { print count + 0 }' \
    "$summary"
}

verify_pass_directories() {
  local actual="$WORKDIR/candidate-pass-dirs.txt"
  local expected="$WORKDIR/expected-pass-dirs.txt"

  awk -F '\t' '$3 == "PASS" { print $1 }' "$CANDIDATE_SUMMARY" \
    | sort -u >"$actual"
  printf '%s\n' \
    tests/ntruplus768/decap_verify \
    tests/ntruplus768/invntt_final \
    tests/ntruplus768/ntt_schedule >"$expected"
  if ! cmp -s "$actual" "$expected"; then
    diff -u "$expected" "$actual" >&2 || true
    fail "candidate checker pass-directory set changed"
  fi
}

verify_counts() {
  local baseline_pass
  local baseline_fail
  local baseline_skip
  local candidate_pass
  local candidate_fail
  local candidate_skip

  baseline_pass=$(count_status "$BASELINE_SUMMARY" PASS)
  baseline_fail=$(count_status "$BASELINE_SUMMARY" FAIL)
  baseline_skip=$(count_status "$BASELINE_SUMMARY" SKIP)
  candidate_pass=$(count_status "$CANDIDATE_SUMMARY" PASS)
  candidate_fail=$(count_status "$CANDIDATE_SUMMARY" FAIL)
  candidate_skip=$(count_status "$CANDIDATE_SUMMARY" SKIP)

  [[ $baseline_pass -eq 88 && $baseline_fail -eq 0 && $baseline_skip -eq 4 ]] ||
    fail "unexpected baseline matrix: pass=$baseline_pass fail=$baseline_fail skip=$baseline_skip"
  [[ $candidate_pass -eq 6 && $candidate_fail -eq 82 && $candidate_skip -eq 4 ]] ||
    fail "unexpected candidate matrix: pass=$candidate_pass fail=$candidate_fail skip=$candidate_skip"
  verify_pass_directories

  printf 'PASS: verified baseline checker matrix: %d pass, %d fail, %d skip\n' \
    "$baseline_pass" "$baseline_fail" "$baseline_skip"
  printf 'PASS: candidate checker matrix reproduced: %d pass, %d fail, %d skip\n' \
    "$candidate_pass" "$candidate_fail" "$candidate_skip"
}

report_failures() {
  printf '%s\n' 'INFO: first candidate failures (up to 20 targets):'
  awk -F '\t' '$3 == "FAIL" { print $1 " " $2 ": " $4 }' \
    "$CANDIDATE_SUMMARY" | sed -n '1,20p'
}

main() {
  require_command awk
  require_command cmp
  require_command cp
  require_command diff
  require_command find
  require_command git
  require_command grep
  require_command make
  require_command sed
  require_command sort
  require_command tar
  require_command tr
  bash -n "$0"

  clone_inputs
  run_matrix "$BASELINE_REPO" "$BASELINE_SUMMARY"
  run_matrix "$CANDIDATE_REPO" "$CANDIDATE_SUMMARY"
  verify_counts
  report_failures

  printf '%s\n' \
    'RESULT: 82 of 88 fail-closed checker targets require migration before the candidate source can replace the verified baseline'
  printf '%s\n' \
    'SCOPE: bounded check/selfcheck source-shape audit only; basemul and poly_basemul have no such targets, and no EasyCrypt, Jasmin safety, differential, or UBSan chain is run here'
}

main "$@"
