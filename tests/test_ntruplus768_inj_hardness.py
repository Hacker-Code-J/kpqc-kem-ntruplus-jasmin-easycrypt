#!/usr/bin/env python3
"""Weighted INJ and uniform short-relation verification entry point."""
from pathlib import Path
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent / "ntruplus768/inj_hardness"))
from verify_inj_hardness import main
if __name__ == "__main__":
    sys.exit(main())
