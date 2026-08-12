#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
JASMIN_SOURCE="$REPO_ROOT/ntruplus/jasmin/768/ref/poly_basemul.jazz"
TEST_DIR="$REPO_ROOT/tests/ntruplus768/poly_basemul"
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/poly_basemul"
TRACKED_EXTRACTED="$PROOF_DIR/extracted"
BASEMUL_TRACKED_EXTRACTED="$REPO_ROOT/ntruplus/proof/768/ref/basemul/extracted"
FORMOSA_ECLIB="$REPO_ROOT/external/formosa-mlkem/proof/eclib"
FORMOSA_COMMON="$REPO_ROOT/external/formosa-mlkem/crypto-specs/common"
BASEMUL_PROOF="$REPO_ROOT/ntruplus/proof/768/ref/basemul"
BASEMUL_EXTRACTED="$BASEMUL_PROOF/extracted"
SLICE=jade_ntruplus_ntruplus768_amd64_ref_poly_basemul

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-poly-basemul.XXXXXX")
WHY3_PID=
WHY3SERVER_BIN=

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

reject_proof_holes() {
  local findings="$WORKDIR/proof-holes.txt"
  local status

  if grep -ERni --include='*.ec' \
    '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
    "$PROOF_DIR" "$BASEMUL_PROOF" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "EasyCrypt proof trees contain a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the EasyCrypt proof trees for holes"
  fi
}

compile_easycrypt() {
  local proof=$1
  local tag=$2
  local socket="$WORKDIR/why3-$tag.sock"
  local server_log="$WORKDIR/why3-$tag.log"
  local attempt
  local launch
  local ready=0

  : >"$server_log"
  for ((launch = 1; launch <= 3; ++launch)); do
    rm -f "$socket"
    "$WHY3SERVER_BIN" --socket "$socket" --single-client -j1 >>"$server_log" 2>&1 &
    WHY3_PID=$!

    for ((attempt = 0; attempt < 200; ++attempt)); do
      if [[ -S "$socket" ]]; then
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
    fail "Why3 server did not accept the $tag proof after three attempts"
  fi

  if ! easycrypt compile -no-eco -p Z3 -timeout 5 -max-provers 1 \
    -server "$socket" \
    -I "$GENERATED_DIR" \
    -I "$PROOF_DIR" \
    -I "$BASEMUL_PROOF" \
    -I "$BASEMUL_EXTRACTED" \
    -I "$FORMOSA_ECLIB" \
    -I "$FORMOSA_COMMON" \
    "$proof"; then
    kill "$WHY3_PID" 2>/dev/null || true
    wait "$WHY3_PID" 2>/dev/null || true
    WHY3_PID=
    sed -n '1,120p' "$server_log" >&2 || true
    fail "EasyCrypt $tag proof failed"
  fi

  kill "$WHY3_PID" 2>/dev/null || true
  wait "$WHY3_PID" 2>/dev/null || true
  WHY3_PID=
}

compare_extraction() {
  local generated_dir=$1
  local tracked_list=$2
  local generated_list=$3
  local name
  local expected_list="$WORKDIR/expected-extracted.txt"

  cat >"$expected_list" <<'EOF'
Array4.ec
Array768.ec
Array96.ec
NTRUPlus768PolyBasemul.ec
WArray1536.ec
WArray192.ec
WArray8.ec
EOF
  find "$generated_dir" -maxdepth 1 -type f -name '*.ec' -printf '%f\n' | sort >"$generated_list"

  if ! cmp -s "$expected_list" "$generated_list"; then
    diff -u "$expected_list" "$generated_list" >&2 || true
    fail "generated extraction file set does not match expected poly_basemul extraction"
  fi

  cat >"$tracked_list" <<'EOF'
Array96.ec
Array768.ec
NTRUPlus768PolyBasemul.ec
WArray1536.ec
WArray192.ec
EOF
  while IFS= read -r name; do
    if ! cmp -s "$generated_dir/$name" "$TRACKED_EXTRACTED/$name"; then
      diff -u "$TRACKED_EXTRACTED/$name" "$generated_dir/$name" | sed -n '1,120p' >&2 || true
      fail "tracked poly_basemul EasyCrypt extraction is stale: $name"
    fi
  done <"$tracked_list"

  while IFS= read -r name; do
    if ! cmp -s "$generated_dir/$name" "$BASEMUL_TRACKED_EXTRACTED/$name"; then
      diff -u "$BASEMUL_TRACKED_EXTRACTED/$name" "$generated_dir/$name" | sed -n '1,120p' >&2 || true
      fail "tracked shared EasyCrypt extraction is stale: $name"
    fi
  done <<'EOF'
Array4.ec
WArray8.ec
EOF
}

main() {
  local easycrypt_bin
  local easycrypt_bindir
  local generated_dir="$WORKDIR/extracted"
  local asm_dir="$WORKDIR/asm"
  local tracked_list="$WORKDIR/tracked-extracted.txt"
  local generated_list="$WORKDIR/generated-extracted.txt"

  require_command make
  require_command jasminc
  require_command jasmin-ct
  require_command jasmin2ec
  require_command easycrypt
  require_command grep
  require_command "${CC:-cc}"

  easycrypt_bin=$(command -v easycrypt)
  easycrypt_bindir=$(cd -- "$(dirname -- "$easycrypt_bin")" && pwd)
  WHY3SERVER_BIN="$easycrypt_bindir/../lib/why3/why3server"
  [[ -x "$WHY3SERVER_BIN" ]] ||
    fail "missing Why3 server next to the EasyCrypt installation: $WHY3SERVER_BIN"

  [[ -f "$JASMIN_SOURCE" ]] || fail "missing Jasmin source: $JASMIN_SOURCE"
  [[ -f "$FORMOSA_ECLIB/W16extra.ec" ]] ||
    fail "Formosa proof dependency is missing; initialize recursive submodules"
  [[ -f "$FORMOSA_COMMON/JWord_extra.ec" ]] ||
    fail "Formosa crypto-specs dependency is missing; initialize recursive submodules"
  [[ -f "$BASEMUL_PROOF/NTRUPlus768BasemulAlgebra.ec" ]] ||
    fail "missing dependent basemul proof tree"

  mkdir -p "$asm_dir" "$generated_dir"
  GENERATED_DIR=$generated_dir

  jasmin2ec "$JASMIN_SOURCE" --array-model=old \
    -o "$generated_dir/NTRUPlus768PolyBasemul.ec" -f "$SLICE"
  compare_extraction "$generated_dir" "$tracked_list" "$generated_list"
  reject_proof_holes

  compile_easycrypt "$PROOF_DIR/NTRUPlus768PolyBasemulProof.ec" word-level
  compile_easycrypt "$PROOF_DIR/NTRUPlus768PolyBasemulAlgebra.ec" algebra

  jasminc -arch x86-64 -call-conv linux -system linux \
    -slice "$SLICE" -o "$asm_dir/poly_basemul.s" "$JASMIN_SOURCE"
  jasminc -arch x86-64 -call-conv linux -system linux -checksafety \
    -slice "$SLICE" -o "$asm_dir/poly_basemul-safety.s" "$JASMIN_SOURCE"
  jasmin-ct --slice="$SLICE" "$JASMIN_SOURCE"
  jasmin-ct --slice="$SLICE" --sct "$JASMIN_SOURCE"

  make -C "$TEST_DIR" OUTDIR="$WORKDIR/test" run ubsan

  printf 'PASS: NTRU+768 poly_basemul Jasmin build and safety checks\n'
  printf 'PASS: NTRU+768 poly_basemul CT and SCT checks\n'
  printf 'PASS: NTRU+768 poly_basemul C/Jasmin differential and UBSan tests\n'
  printf 'PASS: NTRU+768 poly_basemul fresh extraction matches tracked EasyCrypt model\n'
  printf 'PASS: NTRU+768 poly_basemul EasyCrypt word-level functional proof\n'
  printf 'PASS: NTRU+768 poly_basemul EasyCrypt blockwise quotient-ring bridge\n'
}

main "$@"
