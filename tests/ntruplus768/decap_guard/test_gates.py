#!/usr/bin/env python3
"""Negative gate regressions operate only on disposable copies or byte strings."""
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
import check_decap_guard as policy
import prepare_reference as reference

EXTRACTED = policy.ROOT / "ntruplus/proof/768/ref/decap_guard/extracted"


class GateTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="decap-guard-gates-")
        self.addCleanup(temp.cleanup)
        self.temp = Path(temp.name)
        self.stored = self.temp / "extracted"
        shutil.copytree(EXTRACTED, self.stored)
        self.original_extraction = policy.check_extraction(self.stored, EXTRACTED)

    def tearDown(self):
        current = {str(p.relative_to(EXTRACTED)): policy.sha(p.read_bytes())
                   for p in EXTRACTED.rglob("*") if p.is_file()}
        self.assertEqual(current, self.original_extraction, "live extraction changed")

    def test_unmodified_inputs_pass(self):
        policy.check()
        self.assertEqual(policy.check_extraction(self.stored, EXTRACTED), self.original_extraction)

    def test_changed_extracted_instruction_rejected(self):
        main = self.stored / "NTRUPlus768DecapGuard.ec"
        data = main.read_bytes()
        old = b"(W8.of_int 0)"
        self.assertIn(old, data)
        main.write_bytes(data.replace(old, b"(W8.of_int 1)", 1))
        with self.assertRaisesRegex(ValueError, "raw extraction byte drift"):
            policy.check_extraction(self.stored, EXTRACTED)

    def test_missing_extracted_file_rejected(self):
        (self.stored / "Array32.ec").unlink()
        with self.assertRaisesRegex(ValueError, "whole extraction inventory drift"):
            policy.check_extraction(self.stored, EXTRACTED)

    def test_added_extracted_file_rejected(self):
        (self.stored / "Unexpected.ec").write_text("(* unexpected *)\n")
        with self.assertRaisesRegex(ValueError, "whole extraction inventory drift"):
            policy.check_extraction(self.stored, EXTRACTED)

    def test_guard_source_mutation_rejected(self):
        changed = policy.SOURCE.read_bytes().replace(b"ss[i] = 0;", b"ss[i] = 1;")
        self.assertNotEqual(changed, policy.SOURCE.read_bytes())
        with self.assertRaisesRegex(ValueError, "guard Jasmin source pin drift"):
            policy.check_source(changed)

    def test_official_source_mutation_rejected(self):
        with self.assertRaisesRegex(ValueError, "official kem.c pin drift"):
            reference.splice((reference.TEST / "reference/kem.c").read_bytes() + b"\n")

    def test_mixed_success_body_mutation_rejected(self):
        original = (reference.TEST / "reference/kem.c").read_bytes()
        mixed = reference.splice(original)
        changed = mixed.replace(b"hash_h(buf3, msg);", b"hash_h(buf3, ct);", 1)
        self.assertNotEqual(changed, mixed)
        with self.assertRaisesRegex(ValueError, "outside approved guard splice"):
            reference.check_mixed(original, changed)

    def test_mixed_guard_return_mutation_rejected(self):
        original = (reference.TEST / "reference/kem.c").read_bytes()
        mixed = reference.splice(original)
        changed = mixed.replace(reference.NEW_BLOCK, reference.NEW_BLOCK.replace(b"goto cleanup;", b"return 0;"))
        with self.assertRaisesRegex(ValueError, "outside approved guard splice"):
            reference.check_mixed(original, changed)

    def test_reference_and_manifest_forgery_rejected(self):
        import json
        copy = self.temp / "reference"
        shutil.copytree(reference.TEST / "reference", copy)
        (copy / "poly.c").write_bytes((copy / "poly.c").read_bytes() + b"\n")
        manifest = self.temp / "manifest.json"
        shutil.copyfile(reference.TEST / "reference-manifest.json", manifest)
        with self.assertRaisesRegex(ValueError, "reference file drift"):
            reference.check_reference(copy, manifest)
        forged = json.loads(manifest.read_text())
        forged["files"]["poly.c"] = reference.sha((copy / "poly.c").read_bytes())
        manifest.write_text(json.dumps(forged))
        with self.assertRaisesRegex(ValueError, "reference manifest drift"):
            reference.check_reference(copy, manifest)

    def test_declassification_policy_mutation_rejected(self):
        changed = policy.SOURCE.read_bytes().replace(b"#declassify(status)", b"#declassify(skpoly)", 1)
        with self.assertRaisesRegex(ValueError, "guard Jasmin source pin drift"):
            policy.check_source(changed)

    def test_short_circuit_mutation_rejected(self):
        original = (reference.TEST / "reference/kem.c").read_bytes()
        changed = reference.splice(original).replace(b"goto cleanup;", b"return 0;", 1)
        with self.assertRaisesRegex(ValueError, "outside approved guard splice"):
            reference.check_mixed(original, changed)

    def test_proof_escapes_rejected(self):
        for code in ("lemma bad : false. proof. admit. qed.", "pragma -check.",
                     "axiom bad : false.", "op trusted : int.", "(* unclosed"):
            with self.subTest(code=code), self.assertRaises(ValueError):
                policy.check_proof_text(code)


if __name__ == "__main__":
    unittest.main(verbosity=2)
