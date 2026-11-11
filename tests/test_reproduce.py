"""Boundary tests for the public runner; never launch expensive proof jobs."""

import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "reproduce", ROOT / "scripts/reproduce.py"
)
reproduce = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = reproduce
SPEC.loader.exec_module(reproduce)


class ReproduceTests(unittest.TestCase):
    def setUp(self):
        self.inventory = {
            "plain": reproduce.Target(Path("plain.sh"), frozenset()),
            "prior": reproduce.Target(
                Path("prior.sh"), frozenset({"--prior-evidence-root"})
            ),
            "baseline": reproduce.Target(Path("baseline.sh"), frozenset()),
        }

    def test_prior_requires_explicit_root_before_any_launch(self):
        with self.assertRaisesRegex(ValueError, "required for prior"):
            reproduce.proof_commands(self.inventory, ["plain", "prior"])

    def test_only_accepting_target_receives_evidence_option(self):
        with tempfile.TemporaryDirectory(prefix="evidence with spaces ") as directory:
            commands = reproduce.proof_commands(
                self.inventory, ["plain", "prior"], Path(directory)
            )
        self.assertEqual(commands[0], ["bash", "plain.sh"])
        self.assertEqual(
            commands[1], ["bash", "prior.sh", "--prior-evidence-root", directory]
        )

    def test_missing_evidence_directory_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, "not a directory"):
                reproduce.proof_commands(
                    self.inventory, ["prior"], Path(directory) / "missing"
                )

    def test_invalid_selection_rejected(self):
        for names in ([], ["missing"], ["baseline"]):
            with self.subTest(names=names), self.assertRaises(ValueError):
                reproduce.proof_commands(self.inventory, names)

    def test_process_failure_stops_following_commands(self):
        with patch.object(
            reproduce.shutil, "which", return_value="/bin/bash"
        ), patch.object(
            reproduce.subprocess, "run", return_value=subprocess.CompletedProcess([], 7)
        ) as run:
            self.assertEqual(
                reproduce.execute([["bash", "first"], ["bash", "second"]]), 7
            )
            run.assert_called_once()

    def test_missing_executable_rejected(self):
        with patch.object(reproduce.shutil, "which", return_value=None), patch.object(
            reproduce.subprocess, "run"
        ) as run:
            with self.assertRaisesRegex(ValueError, "missing required executable"):
                reproduce.execute([["bash", "first"]])
            run.assert_not_called()

    def test_current_inventory_matches_all_shell_entries(self):
        inventory = reproduce.targets()
        expected = {
            p.name[len(reproduce.PREFIX) : -3]
            for p in (ROOT / "scripts").glob(reproduce.PREFIX + "*.sh")
        }
        self.assertEqual(set(inventory), expected)
        self.assertIn("--prior-evidence-root", inventory["runtime-bound"].options)
        self.assertIn(
            "--prior-evidence-root", inventory["short-relation-bound"].options
        )
        self.assertNotIn("--prior-evidence-root", inventory["keygen-complete"].options)

    def test_all_prior_harnesses_are_exposed(self):
        inventory = reproduce.targets()
        expected = sum(
            "--prior-evidence-root" in p.read_text()
            for p in (ROOT / "tests/ntruplus768").glob("*/verify*.py")
        )
        actual = sum(
            "--prior-evidence-root" in target.options for target in inventory.values()
        )
        self.assertEqual(actual, expected)

    def test_unrecognized_python_wrapper_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            scripts = Path(directory) / "scripts"
            scripts.mkdir()
            (scripts / "verify-ntruplus768-new.sh").write_text(
                "exec python3 mystery.py\n"
            )
            with self.assertRaisesRegex(ValueError, "unrecognized Python wrapper"):
                reproduce.targets(Path(directory))


if __name__ == "__main__":
    unittest.main()
