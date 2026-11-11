#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
exec python3 "$repo_root/tests/ntruplus768/poly_frombytes_checked/verify_checked.py" "$@"
