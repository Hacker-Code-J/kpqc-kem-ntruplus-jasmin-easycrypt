"""Immutable historical bytes remain mandatory behind English metadata keys."""

import hashlib
import importlib.util
import json
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "preserved_environment", ROOT / "scripts/preserved_environment.py")
manifest_tools = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(manifest_tools)


class PreservedManifestTests(unittest.TestCase):
    def setUp(self):
        self.path = "/old research café/handoff/verification/run/summary.json"
        self.original = {
            "files": {"/fixed/tool": {"sha256": "a" * 64}},
            "separate_evidence_inputs": {
                self.path: {"sha256": "b" * 64, "required_by": ["proof/pins.json"]},
            },
        }
        self.raw = json.dumps(self.original, ensure_ascii=False).encode()
        self.public = manifest_tools.project_manifest(self.raw)

    def encoded(self):
        return json.dumps(self.public, ensure_ascii=False).encode()

    def test_relative_keys_preserve_payload_and_historical_identity(self):
        actual = manifest_tools.authenticate_manifest(self.raw, self.encoded())
        self.assertEqual(actual["files"], self.original["files"])
        record = actual["separate_evidence_inputs"][
            "handoff/verification/run/summary.json"]
        self.assertEqual(record["sha256"], "b" * 64)
        self.assertEqual(record["historical_absolute_path_sha256"],
                         hashlib.sha256(self.path.encode()).hexdigest())
        self.assertNotIn(self.path, self.encoded().decode())

    def test_semantically_equal_reserialization_does_not_replace_original_bytes(self):
        changed = json.dumps(self.original, indent=2, ensure_ascii=False).encode()
        with self.assertRaisesRegex(ValueError, "pinned original"):
            manifest_tools.authenticate_manifest(changed, self.encoded())

    def test_current_payload_metadata_cannot_drift(self):
        self.public["files"]["/fixed/tool"]["sha256"] = "c" * 64
        with self.assertRaisesRegex(ValueError, "projection differs"):
            manifest_tools.authenticate_manifest(self.raw, self.encoded())

    def test_boolean_cannot_replace_integer_metadata(self):
        self.original["schema"] = 1
        self.raw = json.dumps(self.original).encode()
        self.public = manifest_tools.project_manifest(self.raw)
        self.public["schema"] = True
        with self.assertRaisesRegex(ValueError, "projection differs"):
            manifest_tools.authenticate_manifest(self.raw, self.encoded())

    def test_float_cannot_replace_integer_payload_size(self):
        self.original["files"]["/fixed/tool"]["size"] = 1
        self.raw = json.dumps(self.original).encode()
        self.public = manifest_tools.project_manifest(self.raw)
        self.public["files"]["/fixed/tool"]["size"] = 1.0
        with self.assertRaisesRegex(ValueError, "projection differs"):
            manifest_tools.authenticate_manifest(self.raw, self.encoded())

    def test_nonfinite_json_numbers_are_rejected(self):
        self.public["files"]["/fixed/tool"]["size"] = float("nan")
        with self.assertRaises(ValueError):
            manifest_tools.authenticate_manifest(self.raw, self.encoded())

    def test_historical_path_identity_cannot_drift(self):
        self.public["separate_evidence_inputs"][
            "handoff/verification/run/summary.json"][
                "historical_absolute_path_sha256"] = "c" * 64
        with self.assertRaisesRegex(ValueError, "projection differs"):
            manifest_tools.authenticate_manifest(self.raw, self.encoded())

    def test_record_omission_is_rejected(self):
        self.public["separate_evidence_inputs"] = {}
        with self.assertRaisesRegex(ValueError, "projection differs"):
            manifest_tools.authenticate_manifest(self.raw, self.encoded())

    def test_original_hash_is_checked_before_projection(self):
        with self.assertRaisesRegex(ValueError, "pinned original"):
            manifest_tools.authenticate_manifest(b"not JSON", self.encoded())

    def test_projection_collision_is_rejected(self):
        self.original["separate_evidence_inputs"][
            "/another/handoff/verification/run/summary.json"] = {"sha256": "b" * 64}
        with self.assertRaisesRegex(ValueError, "collide"):
            manifest_tools.project_manifest(json.dumps(self.original).encode())

    def test_noncanonical_historical_paths_are_rejected(self):
        for path in ("relative/handoff/verification/run/file",
                     "/root/../old/handoff/verification/run/file",
                     "/root//handoff/verification/run/file",
                     "/root/no-evidence-marker"):
            with self.subTest(path=path), self.assertRaises(ValueError):
                manifest_tools.project_manifest(json.dumps({
                    "separate_evidence_inputs": {path: {"sha256": "b" * 64}}}).encode())

    def test_duplicate_json_keys_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "duplicate key"):
            manifest_tools.authenticate_manifest(b"{}", b'{"files":{},"files":{}}')

    def test_legacy_unprojected_inventory_remains_byte_exact(self):
        self.assertEqual(manifest_tools.authenticate_manifest(self.raw, self.raw),
                         self.original)
        with self.assertRaisesRegex(ValueError, "manifest differs"):
            manifest_tools.authenticate_manifest(self.raw + b" ", self.raw)

    def test_unknown_projection_version_is_rejected(self):
        self.public["metadata_representation"]["format"] = "unreviewed"
        with self.assertRaisesRegex(ValueError, "unsupported"):
            manifest_tools.authenticate_manifest(self.raw, self.encoded())


if __name__ == "__main__":
    unittest.main()
