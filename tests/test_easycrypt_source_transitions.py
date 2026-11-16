#!/usr/bin/env python3
"""Exercise the reviewed proof-port boundary, including tampering failures."""
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import easycrypt_source_transitions as transition


class ReviewedProofTransitions(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        manifest = json.loads((ROOT / transition.MANIFEST).read_text())
        self.relative, self.record = next(iter(manifest['files'].items()))
        for relative in (transition.MANIFEST, transition.BEFORE / self.relative,
                         Path(self.relative)):
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / relative, target)

    def checked(self, relative=None, before=None, after=None):
        return transition.reviewed_import(
            self.root, relative or self.relative,
            before or self.record['before_sha256'], after or self.record['after_sha256'])

    def test_exact_reviewed_pair(self):
        self.assertEqual(self.checked()['source'], self.relative)

    def test_all_twelve_real_pairs(self):
        manifest = json.loads((ROOT / transition.MANIFEST).read_text())
        self.assertEqual(len(manifest['files']), 12)
        for relative, record in manifest['files'].items():
            transition.reviewed_import(ROOT, relative, record['before_sha256'],
                                       record['after_sha256'])

    def test_wrong_historical_or_current_hash(self):
        for kwargs in ({'before': '0' * 64}, {'after': '0' * 64}):
            with self.assertRaisesRegex(ValueError, 'hash mismatch'):
                self.checked(**kwargs)

    def test_changed_current_or_preserved_bytes(self):
        for prefix in (Path(), transition.BEFORE):
            path = self.root / prefix / self.relative
            original = path.read_bytes()
            path.write_bytes(original + b'\n(* unreviewed *)\n')
            with self.assertRaisesRegex(ValueError, 'input bytes changed'):
                self.checked()
            path.write_bytes(original)

    def test_manifest_tampering(self):
        path = self.root / transition.MANIFEST
        path.write_bytes(path.read_bytes() + b'\n')
        with self.assertRaisesRegex(ValueError, 'manifest changed'):
            self.checked()

    def test_unknown_and_escaping_path(self):
        for relative in ('ntruplus/proof/unreviewed.ec', '../outside.ec', '/outside.ec'):
            with self.assertRaises(ValueError):
                self.checked(relative=relative)

    def test_symlink_input(self):
        path = self.root / self.relative
        original = path.read_bytes()
        path.unlink()
        outside = self.root / 'elsewhere.ec'
        outside.write_bytes(original)
        path.symlink_to(outside)
        with self.assertRaisesRegex(ValueError, 'symlink'):
            self.checked()

    def test_declarations_keep_premises_and_reject_escapes(self):
        original = 'lemma bound x : 0 <= x => x < x+1. proof. smt(). qed.'
        body_port = 'lemma bound x : 0 <= x => x < x+1. proof. move=> hx; smt(). qed.'
        weakened = 'lemma bound x : true => x < x+1. proof. smt(). qed.'
        self.assertEqual(transition.declarations(original), transition.declarations(body_port))
        self.assertNotEqual(transition.declarations(original), transition.declarations(weakened))
        for escape in ('admit.', 'axiom invented : false.'):
            with self.assertRaisesRegex(ValueError, 'escape or assumption'):
                transition.declarations(original.replace('smt().', escape))


if __name__ == '__main__':
    unittest.main()
