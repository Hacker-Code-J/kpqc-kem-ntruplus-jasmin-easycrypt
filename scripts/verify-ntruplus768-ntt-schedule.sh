#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
TEST_DIR="$REPO_ROOT/tests/ntruplus768/ntt_schedule"
CHECKER="$TEST_DIR/check_ntt_schedule.py"
NTT_SOURCE="$REPO_ROOT/NTRU+/NTRU+768/ntt.c"
PROOF_DIR="$REPO_ROOT/ntruplus/proof/768/ref/ntt_schedule"

TMPDIR_PARENT=${TMPDIR:-/tmp}
WORKDIR=$(mktemp -d "$TMPDIR_PARENT/ntruplus768-ntt-schedule.XXXXXX")
WHY3_PID=

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

  [[ -d "$PROOF_DIR" ]] || fail "missing EasyCrypt proof directory: $PROOF_DIR"
  find "$PROOF_DIR" -maxdepth 1 -type f -name '*.ec' | grep -q . ||
    fail "EasyCrypt proof directory has no .ec files: $PROOF_DIR"

  if grep -ERni --include='*.ec' \
    '(^|[^[:alnum:]_])(admit|admitted|assume|axiom|sorry)([^[:alnum:]_]|$)' \
    "$PROOF_DIR" >"$findings"; then
    sed -n '1,120p' "$findings" >&2
    fail "EasyCrypt proof tree contains a proof-hole keyword"
  else
    status=$?
    [[ $status -eq 1 ]] || fail "could not scan the EasyCrypt proof tree for holes"
  fi
}

compile_easycrypt_via_makefile() {
  local easycrypt_bin
  local easycrypt_bindir
  local why3server_bin
  local wrapper="$WORKDIR/easycrypt-wrapper.sh"
  local socket="$WORKDIR/why3-ntt-schedule.sock"
  local server_log="$WORKDIR/why3-ntt-schedule.log"
  local attempt
  local launch
  local ready=0

  [[ -f "$PROOF_DIR/Makefile" ]] || fail "missing EasyCrypt proof Makefile: $PROOF_DIR/Makefile"

  easycrypt_bin=$(command -v easycrypt)
  easycrypt_bindir=$(cd -- "$(dirname -- "$easycrypt_bin")" && pwd)
  why3server_bin="$easycrypt_bindir/../lib/why3/why3server"
  [[ -x "$why3server_bin" ]] ||
    fail "missing Why3 server next to the EasyCrypt installation: $why3server_bin"

  cat >"$wrapper" <<EOF
#!/usr/bin/env bash
set -euo pipefail
[[ \$# -ge 1 ]] || { printf 'FAIL: easycrypt wrapper needs a subcommand\n' >&2; exit 1; }
[[ \$1 == compile ]] || { printf 'FAIL: expected easycrypt compile, got %s\n' "\$1" >&2; exit 1; }
shift
exec "$easycrypt_bin" compile -no-eco -p Z3 -timeout 5 -max-provers 1 -server "$socket" "\$@"
EOF
  chmod +x "$wrapper"

  : >"$server_log"
  for ((launch = 1; launch <= 3; ++launch)); do
    rm -f "$socket"
    "$why3server_bin" --socket "$socket" --single-client -j1 >>"$server_log" 2>&1 &
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
    fail "Why3 server did not become ready after three attempts"
  fi

  if ! make -C "$PROOF_DIR" check EASYCRYPT="$wrapper"; then
    kill "$WHY3_PID" 2>/dev/null || true
    wait "$WHY3_PID" 2>/dev/null || true
    WHY3_PID=
    sed -n '1,120p' "$server_log" >&2 || true
    fail "EasyCrypt proof Makefile check failed"
  fi

  kill "$WHY3_PID" 2>/dev/null || true
  wait "$WHY3_PID" 2>/dev/null || true
  WHY3_PID=
}

main() {
  require_command bash
  require_command grep
  require_command make
  require_command python3
  require_command easycrypt

  [[ -f "$CHECKER" ]] || fail "missing checker: $CHECKER"
  [[ -f "$NTT_SOURCE" ]] || fail "missing NTT source: $NTT_SOURCE"

  bash -n "$0"
  make -C "$TEST_DIR" selfcheck SOURCE="$NTT_SOURCE"
  make -C "$TEST_DIR" check SOURCE="$NTT_SOURCE"
  reject_proof_holes
  compile_easycrypt_via_makefile

  printf 'PASS: verify-ntruplus768-ntt-schedule.sh syntax check\n'
  printf 'PASS: NTRU+768 NTT checker self-check\n'
  printf 'PASS: NTRU+768 NTT schedule verification\n'
  printf 'PASS: EasyCrypt proof-hole scan for ntt_schedule\n'
  printf 'PASS: EasyCrypt ntt_schedule Makefile check via Why3 server\n'
}

main "$@"
