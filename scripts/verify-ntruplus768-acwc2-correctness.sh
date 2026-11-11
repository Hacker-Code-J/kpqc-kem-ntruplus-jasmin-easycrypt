#!/usr/bin/env bash
set -euo pipefail
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$script_dir/.." && pwd)
exec python3 "$root/tests/ntruplus768/acwc2_correctness/verify_acwc2_correctness.py" "$@"
