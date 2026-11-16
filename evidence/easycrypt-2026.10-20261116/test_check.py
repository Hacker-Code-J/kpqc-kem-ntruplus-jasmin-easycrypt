#!/usr/bin/env python3
"""Exercise evidence/source tampering checks without executing a prover."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
INDEX = json.loads((HERE / 'index.json').read_text())


class EvidenceIntegrity(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='ec202610-evidence-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.evidence = self.root / 'evidence'
        shutil.copytree(HERE, self.evidence,
                        ignore=shutil.ignore_patterns('__pycache__'))

    def run_check(self, repo=REPO):
        return subprocess.run(
            [sys.executable, str(self.evidence / 'check.py'),
             '--repo-root', str(repo)], capture_output=True, text=True)

    def test_portable_copy_passes(self):
        result = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_modified_log_rejected(self):
        path = self.evidence / INDEX['records'][0]['log']
        path.write_bytes(path.read_bytes() + b'\nmodified evidence\n')
        result = self.run_check()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('payload digest mismatch', result.stderr)

    def test_modified_index_rejected(self):
        path = self.evidence / 'index.json'
        value = json.loads(path.read_text())
        value['counts']['primary'] += 1
        path.write_text(json.dumps(value))
        result = self.run_check()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('index digest mismatch', result.stderr)

    def test_modified_proof_rejected(self):
        repo = self.root / 'source'
        for relative in INDEX['source_bindings']:
            target = repo / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(REPO / relative, target)
        primary = next(r for r in INDEX['records'] if r['kind'] == 'primary')
        path = repo / primary['source']
        path.write_bytes(path.read_bytes() + b'\n(* changed source *)\n')
        result = self.run_check(repo)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('current source digest mismatch', result.stderr)

    def test_escaping_log_symlink_rejected(self):
        path = self.evidence / INDEX['records'][0]['log']
        external = self.root / 'outside.log'
        external.write_bytes(path.read_bytes())
        path.unlink()
        path.symlink_to(external)
        result = self.run_check()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('missing or escaping file', result.stderr)


if __name__ == '__main__':
    unittest.main(verbosity=2)
