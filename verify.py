#!/usr/bin/env python3
"""Check the unified source graph, then build and audit every local declaration."""
from pathlib import Path
import sys

PACKAGE = Path(__file__).resolve().parent
sys.path.insert(0, str(PACKAGE / "scripts"))
from verify_package import main

if __name__ == "__main__":
    main(PACKAGE)
