#!/usr/bin/env python3
"""Weighted INJ and uniform short-relation verification entry point."""
from pathlib import Path
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent / "ntruplus768/short_relation_bound"))
from verify_short_relation_bound import main
if __name__ == "__main__":
    sys.exit(main())
