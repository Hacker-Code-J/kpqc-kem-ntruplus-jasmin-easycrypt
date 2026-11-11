#!/usr/bin/env python3
"""Weighted base-PKE OW hardness verification entry point."""
from pathlib import Path
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent / "ntruplus768/ow_hardness"))
from verify_ow_hardness import main
if __name__ == "__main__":
    sys.exit(main())
