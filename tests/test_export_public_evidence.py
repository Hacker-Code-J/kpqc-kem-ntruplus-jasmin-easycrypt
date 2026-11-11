"""Export only authenticated, explicitly pinned evidence into a new directory."""

import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest


SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))
SPEC = importlib.util.spec_from_file_location(
    "export_public_evidence", SCRIPTS / "export_public_evidence.py")
exporter = importlib.util.module_from_spec(SPEC)
try:
    SPEC.loader.exec_module(exporter)
finally:
    sys.path.pop(0)


class ExportTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.repo = self.root / "repo"
        self.source = self.root / "private"
        self.source.mkdir()
        self.destination = self.root / "bundle"
        self.summary_name = "handoff/verification/example/summary.json"
        self.summary = {
            "status": "PASS", "inputs_unchanged": True,
            "source_hashes_before": {"proof.ec": "hash"},
            "source_hashes_after": {"proof.ec": "hash"},
        }
        self.summary_bytes = json.dumps(self.summary).encode()
        self.write_source(self.summary_name, self.summary_bytes)
        self.write_pins("example/prior-evidence-pins.json", {
            self.summary_name: hashlib.sha256(self.summary_bytes).hexdigest()})
        self.specs = {}
        for kind, filename in (("contract", "contract.json"),
                               ("source_text", "spec.txt")):
            name = "handoff/verification/spec/" + filename
            data = (kind + "\n").encode()
            self.write_source(name, data)
            self.specs[kind] = {"path": name,
                                "sha256": hashlib.sha256(data).hexdigest()}
        self.write_pins("keygen_gen_law/specification-pins.json", self.specs)
        self.write_source("private-unrelated.txt", b"Must not be exported")

    def write_source(self, name, data):
        path = self.source / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)

    def write_pins(self, name, data):
        path = self.repo / "tests/ntruplus768" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(data))

    def export(self, source=None, destination=None):
        return exporter.export_evidence(
            source or self.source, destination or self.destination, self.repo)

    def test_exact_bytes_inventory_and_checksums(self):
        manifest = self.export()
        self.assertEqual(len(manifest["files"]), 3)
        self.assertFalse(manifest["proofs_replayed"])
        self.assertEqual((self.destination / self.summary_name).read_bytes(),
                         self.summary_bytes)
        self.assertFalse((self.destination / "private-unrelated.txt").exists())
        self.assertNotIn(str(self.source),
                         (self.destination / "BUNDLE-MANIFEST.json").read_text())
        for line in (self.destination / "SHA256SUMS").read_text().splitlines():
            digest, name = line.split("  ", 1)
            actual = hashlib.sha256((self.destination / name).read_bytes()).hexdigest()
            self.assertEqual(actual, digest)
        names = {str(p.relative_to(self.destination))
                 for p in self.destination.rglob("*") if p.is_file()}
        expected = {self.summary_name, *(x["path"] for x in self.specs.values()),
                    "BUNDLE-MANIFEST.json", "SHA256SUMS", "README.txt"}
        self.assertEqual(names, expected)

    def test_repeat_exports_are_deterministic(self):
        first = self.export()
        second_destination = self.root / "second"
        self.assertEqual(first, self.export(destination=second_destination))
        self.assertEqual((self.destination / "SHA256SUMS").read_bytes(),
                         (second_destination / "SHA256SUMS").read_bytes())

    def test_existing_destination_is_untouched(self):
        self.destination.mkdir()
        marker = self.destination / "keep"
        marker.write_text("keep")
        with self.assertRaisesRegex(ValueError, "already exists"):
            self.export()
        self.assertEqual(marker.read_text(), "keep")

    def test_missing_source_root(self):
        with self.assertRaises((FileNotFoundError, ValueError)):
            self.export(source=self.root / "missing")
        self.assertFalse(self.destination.exists())

    def test_missing_input_creates_no_bundle(self):
        (self.source / self.specs["source_text"]["path"]).unlink()
        with self.assertRaisesRegex(ValueError, "missing evidence"):
            self.export()
        self.assertFalse(self.destination.exists())

    def test_tampered_specification_creates_no_bundle(self):
        self.write_source(self.specs["contract"]["path"], b"changed")
        with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
            self.export()
        self.assertFalse(self.destination.exists())

    def test_pinned_non_pass_summary_is_rejected(self):
        self.summary["status"] = "FAIL"
        data = json.dumps(self.summary).encode()
        self.write_source(self.summary_name, data)
        self.write_pins("example/prior-evidence-pins.json", {
            self.summary_name: hashlib.sha256(data).hexdigest()})
        with self.assertRaisesRegex(ValueError, "does not record PASS"):
            self.export()
        self.assertFalse(self.destination.exists())

    def test_source_symlink_is_rejected(self):
        target = self.source / self.specs["source_text"]["path"]
        target.unlink()
        target.symlink_to(self.source / "private-unrelated.txt")
        with self.assertRaisesRegex(ValueError, "symlink"):
            self.export()
        self.assertFalse(self.destination.exists())

    def test_symlinked_source_root_is_rejected(self):
        link = self.root / "linked-source"
        link.symlink_to(self.source, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlink"):
            self.export(source=link)

    def test_symlinked_destination_parent_is_rejected(self):
        link = self.root / "linked-destination"
        link.symlink_to(self.root, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlink"):
            self.export(destination=link / "bundle")

    def test_output_cannot_overlap_inputs_or_repository(self):
        for destination in (self.source / "bundle", self.repo / "bundle", self.root):
            with self.subTest(destination=destination), self.assertRaises(ValueError):
                self.export(destination=destination)

    def test_specification_schema_is_exact(self):
        del self.specs["source_text"]
        self.write_pins("keygen_gen_law/specification-pins.json", self.specs)
        with self.assertRaisesRegex(ValueError, "contract and source_text"):
            self.export()

    def test_invalid_specification_path_or_digest(self):
        for change in ({"path": "../private-unrelated.txt"}, {"sha256": "bad"},
                       {"path": "handoff/verification/a\nb"}, {"path": "./a"},
                       {"path": "README.txt"}):
            original = dict(self.specs["contract"])
            self.specs["contract"].update(change)
            self.write_pins("keygen_gen_law/specification-pins.json", self.specs)
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.export()
            self.assertFalse(self.destination.exists())
            self.specs["contract"] = original


if __name__ == "__main__":
    unittest.main()
