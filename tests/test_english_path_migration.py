"""Guard the reviewed path-only migration without rewriting historical evidence."""

import ast
import hashlib
import json
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]
LEDGER = json.loads((ROOT / "docs/english-path-migration.json").read_text())


def digest(data):
    return hashlib.sha256(data).hexdigest()


def normalized_ast(text, changes):
    tree = ast.parse(text)
    counts = [0] * len(changes)
    for node in ast.walk(tree):
        if not isinstance(node, ast.Constant) or not isinstance(node.value, str):
            continue
        for index, change in enumerate(changes):
            if node.value == change["after_literal"]:
                node.value = f"<reviewed-path-literal-{index}>"
                counts[index] += 1
                break
    if counts != [1] * len(changes):
        raise ValueError("reviewed path-literal inventory differs")
    return digest(ast.dump(tree, include_attributes=False).encode())


class EnglishPathMigrationTests(unittest.TestCase):
    def test_only_reviewed_path_literals_change_the_normalized_program(self):
        self.assertEqual(len(LEDGER["source_changes"]), 25)
        for record in LEDGER["source_changes"]:
            with self.subTest(path=record["path"]):
                data = (ROOT / record["path"]).read_bytes()
                self.assertEqual(digest(data), record["after_sha256"])
                self.assertEqual(normalized_ast(data.decode(), record["replacements"]),
                                 record["normalized_ast_sha256"])
                self.assertFalse(any(0xAC00 <= ord(c) <= 0xD7A3
                                     for c in data.decode()))

    def test_narrow_pin_updates_keep_all_proof_entries(self):
        self.assertEqual(len(LEDGER["pin_changes"]), 9)
        self.assertEqual(sum(len(x["entries"]) for x in LEDGER["pin_changes"]), 19)
        for record in LEDGER["pin_changes"]:
            data = (ROOT / record["path"]).read_bytes()
            pins = json.loads(data)
            self.assertEqual(digest(data), record["after_sha256"])
            for entry in record["entries"]:
                self.assertTrue(entry["path"].endswith(".py"))
                self.assertEqual(pins[entry["path"]], entry["after_sha256"])
            proofs = {name: value for name, value in pins.items()
                      if name.endswith((".ec", ".v"))}
            self.assertEqual(len(proofs), record["unchanged_proof_entry_count"])
            encoded = json.dumps(proofs, sort_keys=True, separators=(",", ":")).encode()
            self.assertEqual(digest(encoded), record["unchanged_proof_entries_sha256"])

    def test_gate_weakening_is_not_a_path_only_change(self):
        record = next(x for x in LEDGER["source_changes"]
                      if x["path"].endswith("verify_runtime_bound.py"))
        text = (ROOT / record["path"]).read_text()
        self.assertIn("Proofs:check", text)
        weakened = text.replace("Proofs:check", "Proofs:weak")
        self.assertNotEqual(normalized_ast(weakened, record["replacements"]),
                            record["normalized_ast_sha256"])

    def test_non_ascii_path_regression_remains_non_ascii(self):
        labels = [change["after_literal"] for record in LEDGER["source_changes"]
                  for change in record["replacements"]
                  if change["kind"].startswith("unicode-")]
        self.assertEqual(len(labels), 2)
        self.assertTrue(all(" " in label and not label.isascii() for label in labels))


if __name__ == "__main__":
    unittest.main()
