#!/usr/bin/env bash
set -euo pipefail
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$script_dir/.." && pwd)
exec python3 "$root/tests/ntruplus768/kem_numerical_dfr/verify_kem_numerical_dfr.py" "$@"
