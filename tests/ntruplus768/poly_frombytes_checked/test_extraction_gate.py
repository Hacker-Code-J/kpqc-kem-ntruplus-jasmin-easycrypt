#!/usr/bin/env python3
"""Exercise whole-file extraction binding using disposable stored copies."""
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
import check_poly_frombytes_checked as policy

EXTRACTED = policy.ROOT / "ntruplus/proof/768/ref/poly_frombytes_checked/extracted"
MAIN = "NTRUPlus768PolyFromBytesChecked.ec"


def snapshot(directory):
    return {str(path.relative_to(directory)): policy.sha(path.read_bytes())
            for path in directory.rglob("*") if path.is_file()}


class ExtractionGateTests(unittest.TestCase):
    def setUp(self):
        self.original = snapshot(EXTRACTED)
        temporary = tempfile.TemporaryDirectory(prefix="checked-extraction-gate-")
        self.addCleanup(temporary.cleanup)
        self.stored = Path(temporary.name) / "stored"
        shutil.copytree(EXTRACTED, self.stored)

    def tearDown(self):
        self.assertEqual(self.original, snapshot(EXTRACTED), "live extraction changed")

    def test_identical_copy_passes(self):
        self.assertEqual(self.original, policy.check_extraction(self.stored, EXTRACTED))

    def test_changed_instruction_rejected(self):
        main = self.stored / MAIN
        data = main.read_bytes()
        instruction = b"fail_0 <- (W32.of_int 0);"
        self.assertEqual(data.count(instruction), 1)
        main.write_bytes(data.replace(instruction, b"fail_0 <- (W32.of_int 2147483648);"))
        with self.assertRaisesRegex(ValueError, "raw extraction byte drift"):
            policy.check_extraction(self.stored, EXTRACTED)

    def test_missing_file_rejected(self):
        (self.stored / "Array768.ec").unlink()
        with self.assertRaisesRegex(ValueError, "whole extraction file inventory drift"):
            policy.check_extraction(self.stored, EXTRACTED)

    def test_extra_file_rejected(self):
        (self.stored / "Unexpected.ec").write_text("(* unexpected extraction file *)\n")
        with self.assertRaisesRegex(ValueError, "whole extraction file inventory drift"):
            policy.check_extraction(self.stored, EXTRACTED)


if __name__ == "__main__":
    unittest.main(verbosity=2)
