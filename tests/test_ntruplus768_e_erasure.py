#!/usr/bin/env python3
"""Proof-only E-erasure verification entry point."""
from pathlib import Path
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent / "ntruplus768/e_erasure"))
from verify_e_erasure import main

if __name__ == "__main__":
    sys.exit(main())
