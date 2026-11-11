#!/usr/bin/env python3
"""Proof-only ACWC2-to-INJ/OW security verification entry point."""
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent / "ntruplus768/acwc2_security"))
from verify_acwc2_security import main

if __name__ == "__main__":
    sys.exit(main())
