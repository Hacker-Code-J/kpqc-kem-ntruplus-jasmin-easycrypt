"""Public historical-evidence checks must fail closed without running provers."""

import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from contextlib import redirect_stdout, redirect_stderr
from io import StringIO


SPEC = importlib.util.spec_from_file_location(
    "check_public_evidence",
    Path(__file__).resolve().parents[1] / "scripts/check_public_evidence.py")
evidence = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(evidence)


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.name = "handoff/verification/example/summary.json"
        self.path = self.root / self.name
        self.path.parent.mkdir(parents=True)
        self.report = {"status": "PASS", "inputs_unchanged": True,
                       "source_hashes_before": {"proof.ec": "hash"},
                       "source_hashes_after": {"proof.ec": "hash"}}
        self.record = self.write_report()

    def write_report(self):
        data = json.dumps(self.report).encode()
        self.path.write_bytes(data)
        return {"path": self.name, "sha256": hashlib.sha256(data).hexdigest()}

    def test_valid_legacy_summary(self):
        evidence.check_record(self.record, self.root)

    def test_valid_external_audit(self):
        self.report.update(external_inputs_unchanged=True,
                           external_hashes_before={"tool": "hash"},
                           external_hashes_after={"tool": "hash"})
        evidence.check_record(self.write_report(), self.root)

    def test_byte_tampering(self):
        self.path.write_bytes(self.path.read_bytes() + b"\n")
        with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
            evidence.check_record(self.record, self.root)

    def test_missing_summary(self):
        self.path.unlink()
        with self.assertRaisesRegex(ValueError, "missing evidence"):
            evidence.check_record(self.record, self.root)

    def test_non_pass_even_if_pinned(self):
        self.report["status"] = "SOURCE_ONLY_PASS"
        with self.assertRaisesRegex(ValueError, "does not record PASS"):
            evidence.check_record(self.write_report(), self.root)

    def test_unstable_source_even_if_pinned(self):
        self.report["source_hashes_after"] = {"proof.ec": "changed"}
        with self.assertRaisesRegex(ValueError, "unstable historical source"):
            evidence.check_record(self.write_report(), self.root)

    def test_incomplete_external_audit(self):
        self.report["external_hashes_after"] = {}
        with self.assertRaisesRegex(ValueError, "unstable historical external"):
            evidence.check_record(self.write_report(), self.root)

    def test_noncanonical_paths(self):
        for name in ("../outside.json", "/tmp/outside.json", "a/../b", "./a",
                     "a//b", "a\\b", "."):
            with self.subTest(name=name), self.assertRaises(ValueError):
                evidence.check_record({**self.record, "path": name}, self.root)

    def test_file_symlink(self):
        link = self.path.parent / "link.json"
        link.symlink_to(self.path)
        with self.assertRaisesRegex(ValueError, "symlink"):
            evidence.check_record(
                {**self.record, "path": str(link.relative_to(self.root))}, self.root)

    def test_directory_symlink(self):
        (self.root / "linked").symlink_to(self.path.parent, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlink"):
            evidence.check_record(
                {**self.record, "path": "linked/summary.json"}, self.root)

    def write_pins(self, group, pins):
        path = self.root / "tests/ntruplus768" / group / "prior-evidence-pins.json"
        path.parent.mkdir(parents=True)
        path.write_text(json.dumps(pins))

    def test_inventory_deduplicates_and_records_consumers(self):
        for group in ("a", "b"):
            self.write_pins(group, {self.name: self.record["sha256"]})
        records = evidence.inventory(self.root)
        self.assertEqual(len(records), 1)
        self.assertEqual(len(records[0]["required_by"]), 2)

    def test_conflicting_pins(self):
        self.write_pins("a", {self.name: self.record["sha256"]})
        self.write_pins("b", {self.name: "0" * 64})
        with self.assertRaisesRegex(ValueError, "conflicting"):
            evidence.inventory(self.root)

    def test_empty_inventory_fails(self):
        with self.assertRaisesRegex(ValueError, "no prior"):
            evidence.inventory(self.root)

    def test_cli_inventory_does_not_read_evidence(self):
        with patch.object(evidence, "inventory", return_value=[self.record]), \
                patch.object(evidence, "check_record") as check, \
                redirect_stdout(StringIO()) as output:
            self.assertEqual(evidence.main([]), 0)
            check.assert_not_called()
            self.assertIn("no files checked", json.loads(output.getvalue())["scope"])

    def test_cli_failure_exit_code(self):
        self.path.unlink()
        with patch.object(evidence, "inventory", return_value=[self.record]), \
                redirect_stderr(StringIO()):
            self.assertEqual(evidence.main(["--evidence-root", str(self.root)]), 1)


if __name__ == "__main__":
    unittest.main()
