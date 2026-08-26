#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
SRC_DIR=${NTRUPLUS768_SRC_DIR:-"$REPO_ROOT/NTRU+/NTRU+768"}
EXPECTED_RSP=${NTRUPLUS768_EXPECTED_RSP:-"$REPO_ROOT/NTRU+/KAT/NTRU+768/PQCkemKAT_2336.rsp"}

CC=${CC:-gcc}
TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-baseline.XXXXXX")

cleanup() {
  rm -rf "$WORKDIR"
}
trap cleanup EXIT INT TERM

fail() {
  printf 'FAIL: %s\n' "$1" >&2
  exit 1
}

show_log_tail() {
  local label=$1
  local logfile=$2
  if [[ -f "$logfile" ]]; then
    printf '%s\n' "--- $label (tail) ---" >&2
    tail -n 20 "$logfile" >&2 || true
    printf '%s\n' '-------------------' >&2
  fi
}

require_file() {
  local path=$1
  [[ -f "$path" ]] || fail "missing required file: $path"
}

build_test() {
  "$CC" \
    -Wall -Wextra -Wpedantic -Wmissing-prototypes -Wredundant-decls \
    -Wshadow -Wpointer-arith -O3 -fomit-frame-pointer \
    -I"$SRC_DIR" \
    -I"$SRC_DIR/test" \
    -o "$WORKDIR/test" \
    "$SRC_DIR/randombytes.c" \
    "$SRC_DIR/test/test.c" \
    "$SRC_DIR/kem.c" \
    "$SRC_DIR/poly.c" \
    "$SRC_DIR/ntt.c" \
    "$SRC_DIR/symmetric.c" \
    "$SRC_DIR/fips202/fips202.c"
}

build_kat() {
  "$CC" \
    -Wno-unused-result -O3 -fomit-frame-pointer \
    -I"$SRC_DIR" \
    -I"$SRC_DIR/kat" \
    -o "$WORKDIR/PQCgenKAT_kem" \
    "$SRC_DIR/kat/PQCgenKAT_kem.c" \
    "$SRC_DIR/kat/aes.c" \
    "$SRC_DIR/kat/rng.c" \
    "$SRC_DIR/kem.c" \
    "$SRC_DIR/poly.c" \
    "$SRC_DIR/ntt.c" \
    "$SRC_DIR/symmetric.c" \
    "$SRC_DIR/fips202/fips202.c"
}

run_test() {
  local logfile=$WORKDIR/test.log
  if ! "$WORKDIR/test" >"$logfile" 2>&1; then
    show_log_tail "test failed" "$logfile"
    fail "functional test executable exited non-zero"
  fi

  if ! grep -q '^count: 0$' "$logfile"; then
    show_log_tail "unexpected test output" "$logfile"
    fail "functional test did not report 'count: 0'"
  fi
}

run_kat() {
  local logfile=$WORKDIR/kat.log
  if ! (
    cd "$WORKDIR"
    ./PQCgenKAT_kem >"$logfile" 2>&1
  ); then
    show_log_tail "KAT generator failed" "$logfile"
    fail "KAT generator exited non-zero"
  fi

  [[ -f "$WORKDIR/PQCkemKAT_2336.rsp" ]] || fail "KAT generator did not produce PQCkemKAT_2336.rsp"
}

compare_rsp() {
  local generated=$WORKDIR/PQCkemKAT_2336.rsp
  if ! cmp -s "$generated" "$EXPECTED_RSP"; then
    printf '%s\n' "--- rsp diff (first 40 lines) ---" >&2
    diff -u "$EXPECTED_RSP" "$generated" | sed -n '1,40p' >&2 || true
    printf '%s\n' '--------------------------------' >&2
    fail "generated KAT differs from $EXPECTED_RSP"
  fi
}

report_success() {
  local generated=$WORKDIR/PQCkemKAT_2336.rsp
  local generated_sha
  generated_sha=$(sha256sum "$generated" | awk '{print $1}')
  printf 'PASS: NTRU+768 functional test reported count: 0\n'
  printf 'PASS: regenerated KAT matches reference byte-for-byte\n'
  printf 'INFO: generated rsp sha256 %s\n' "$generated_sha"
}

main() {
  require_file "$EXPECTED_RSP"
  require_file "$SRC_DIR/Makefile"
  build_test
  build_kat
  run_test
  run_kat
  compare_rsp
  report_success
}

main "$@"
