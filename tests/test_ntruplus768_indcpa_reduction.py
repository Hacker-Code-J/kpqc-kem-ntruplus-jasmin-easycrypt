#!/usr/bin/env python3
"""Proof-only IND-CPA reduction verification entry point."""
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent / "ntruplus768/indcpa_reduction"))
from verify_indcpa_reduction import main

if __name__ == "__main__":
    sys.exit(main())
