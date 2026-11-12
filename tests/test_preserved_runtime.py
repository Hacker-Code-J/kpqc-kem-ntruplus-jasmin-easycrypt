"""The preserved-layout launcher authenticates inputs before any process launch."""

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location(
    "replay_runtime", Path(__file__).resolve().parents[1] / "env/replay_runtime.py")
launcher = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(launcher)


class PreservedRuntimeTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.repo = self.root / "repo"
        self.package = self.root / "environment with spaces"
        self.evidence = self.root / "evidence"
        self.output = self.root / "results" / "new-run"
        for path in (self.repo / "env", self.evidence, self.output.parent):
            path.mkdir(parents=True)
        self.files = {}
        for original in (launcher.AUDITED_HOME + "/.config/easycrypt/easycrypt.conf",
                         *launcher.SYSTEM_FILES):
            archive = "rootfs" + original
            path = self.package / archive
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(original.encode())
            path.chmod(0o755)
            self.files[original] = {
                "archive_path": archive,
                "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                "mode": "0o755", "size": path.stat().st_size,
            }
        self.write_manifest()
        self.checker = patch.object(launcher, "check_record")
        self.record_check = self.checker.start()
        self.addCleanup(self.checker.stop)
        inventory = patch.object(launcher, "inventory", return_value=[{"test": True}])
        inventory.start()
        self.addCleanup(inventory.stop)
        environment = patch.dict(
            launcher.os.environ, {"HOME": launcher.AUDITED_HOME}, clear=True)
        environment.start()
        self.addCleanup(environment.stop)
        which = patch.object(launcher.shutil, "which", return_value="/usr/bin/bwrap")
        which.start()
        self.addCleanup(which.stop)

    def write_manifest(self):
        manifest = {"files": self.files, "file_count": len(self.files),
                    "missing_or_mismatched_inputs": {},
                    "all_captured_input_hashes_and_modes_verified": True}
        data = json.dumps(manifest).encode()
        (self.repo / "env/preserved-inputs.json").write_bytes(data)
        (self.package / "manifest.json").write_bytes(data)

    def command(self, **kwargs):
        return launcher.replay_command(
            self.package, self.evidence, self.output, repo=self.repo, **kwargs)

    def test_full_command_has_fixed_mounts_and_explicit_paths(self):
        command = self.command()
        self.assertEqual(command[0], "/usr/bin/bwrap")
        self.assertNotIn("--check-only", command)
        self.assertNotIn("--draft", command)
        self.assertNotIn("--unshare-user", command)
        self.assertEqual(command[-4:], ["--prior-evidence-root", "/tmp/work/evidence",
                                      "--output", "/tmp/work/results/new-run"])
        for original in launcher.SYSTEM_FILES:
            at = command.index(str(self.package / ("rootfs" + original)))
            self.assertEqual(command[at - 1:at + 2],
                             ["--ro-bind", command[at], original])
        self.assertIn(str(self.package), " ".join(command))
        self.record_check.assert_called_once_with({"test": True}, self.evidence)

    def test_source_only_is_explicit(self):
        self.assertEqual(self.command(check_only=True)[-1], "--check-only")

    def test_english_projection_keeps_original_package_and_fixed_payload_mounts(self):
        original = json.loads((self.package / "manifest.json").read_bytes())
        original["separate_evidence_inputs"] = {
            "/archived research/handoff/verification/run/summary.json": {
                "sha256": "b" * 64, "required_by": []}}
        raw = json.dumps(original).encode()
        (self.package / "manifest.json").write_bytes(raw)
        projected = launcher.preserved_environment.project_manifest(raw)
        (self.repo / "env/preserved-inputs.json").write_text(json.dumps(projected))
        command = self.command(check_only=True)
        self.assertIn("/tmp/work/evidence", command)
        self.assertEqual((self.package / "manifest.json").read_bytes(), raw)

    def test_package_manifest_cannot_replace_trusted_inventory(self):
        (self.package / "manifest.json").write_text("{}")
        with self.assertRaisesRegex(ValueError, "manifest differs"):
            self.command()

    def test_payload_tampering_is_rejected(self):
        path = self.package / self.files[launcher.SYSTEM_FILES[0]]["archive_path"]
        path.write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError, "payload mismatch"):
            self.command()

    def test_payload_mode_tampering_is_rejected(self):
        path = self.package / self.files[launcher.SYSTEM_FILES[0]]["archive_path"]
        path.chmod(0o644)
        with self.assertRaisesRegex(ValueError, "payload mismatch"):
            self.command()

    def test_payload_symlink_is_rejected(self):
        path = self.package / self.files[launcher.SYSTEM_FILES[0]]["archive_path"]
        path.unlink()
        path.symlink_to("/usr/bin/env")
        with self.assertRaisesRegex(ValueError, "symlink"):
            self.command()

    def test_extra_payload_is_rejected(self):
        (self.package / "rootfs/extra").write_text("unreviewed")
        with self.assertRaisesRegex(ValueError, "inventory differs"):
            self.command()

    def test_missing_payload_is_rejected(self):
        path = self.package / self.files[launcher.SYSTEM_FILES[0]]["archive_path"]
        path.unlink()
        with self.assertRaises((ValueError, OSError)):
            self.command()

    def test_unsafe_manifest_paths_are_rejected_even_if_identical(self):
        for original in ("/etc/passwd", "/home/hacker-code-j/../escape"):
            with self.subTest(original=original):
                self.files[original] = dict(self.files[launcher.SYSTEM_FILES[0]])
                self.write_manifest()
                with self.assertRaisesRegex(ValueError, "unaudited path"):
                    self.command()
                del self.files[original]

    def test_existing_output_is_preserved(self):
        self.output.mkdir()
        (self.output / "keep").write_text("keep")
        with self.assertRaisesRegex(ValueError, "already exists"):
            self.command()
        self.assertEqual((self.output / "keep").read_text(), "keep")

    def test_writable_output_parent_cannot_expose_input_tree(self):
        for output in (self.repo / "new", self.root / "new"):
            with self.subTest(output=output), self.assertRaisesRegex(
                    ValueError, "output parent overlaps"):
                launcher.replay_command(self.package, self.evidence, output,
                                        repo=self.repo)

    def test_missing_output_parent_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "output parent"):
            launcher.replay_command(self.package, self.evidence,
                                    self.root / "missing" / "new", repo=self.repo)

    def test_external_why3_server_is_rejected(self):
        with patch.dict(launcher.os.environ, {"WHY3_SERVER_SOCKET": "/tmp/server"}), \
                self.assertRaisesRegex(ValueError, "WHY3_SERVER_SOCKET"):
            self.command()

    def test_missing_bwrap_is_rejected(self):
        with patch.object(launcher.shutil, "which", return_value=None), \
                self.assertRaisesRegex(ValueError, "bwrap"):
            self.command()

    def test_explicit_tools_and_config_support_different_host_home(self):
        with patch.dict(launcher.os.environ, {
                "HOME": "/home/another-user", "EASYCRYPT": "/untrusted/easycrypt",
                "WHY3": "/untrusted/why3", "XDG_CONFIG_HOME": "/untrusted/config"}):
            command = self.command()
            self.assertEqual(launcher.os.environ["HOME"], "/home/another-user")
        self.assertNotIn("HOME", command)
        for name, suffix in (("EASYCRYPT", "/.opam/cryptotools-2026.09/bin/easycrypt"),
                             ("WHY3", "/.opam/cryptotools-2026.09/bin/why3"),
                             ("XDG_CONFIG_HOME", "/.config")):
            at = command.index(name)
            self.assertEqual(command[at - 1:at + 2],
                             ["--setenv", name, launcher.AUDITED_HOME + suffix])

    def test_supplied_parent_traversal_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "parent traversal"):
            launcher.replay_command(self.package, self.evidence,
                                    self.output.parent / ".." / "new", repo=self.repo)

    def test_invalid_evidence_is_rejected(self):
        self.record_check.side_effect = ValueError("invalid evidence")
        with self.assertRaisesRegex(ValueError, "invalid evidence"):
            self.command()

    def test_symlinked_input_or_output_parent_is_rejected(self):
        link = self.root / "link"
        link.symlink_to(self.package, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlink"):
            launcher.replay_command(link, self.evidence, self.output, repo=self.repo)
        link.unlink()
        link.symlink_to(self.output.parent, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlink"):
            launcher.replay_command(self.package, self.evidence, link / "new",
                                    repo=self.repo)

    def test_cli_validation_failure_never_launches(self):
        with patch.object(launcher, "replay_command", side_effect=ValueError("bad")), \
                patch.object(launcher.subprocess, "run") as run:
            result = launcher.main(["--environment", str(self.package),
                                    "--evidence-root", str(self.evidence),
                                    "--output", str(self.output)])
            self.assertEqual(result, 1)
            run.assert_not_called()

    def test_cli_propagates_verifier_status_without_shell(self):
        command = ["/usr/bin/bwrap", "fixed", "arguments"]
        with patch.object(launcher, "replay_command", return_value=command), \
                patch.object(launcher.subprocess, "run", return_value=
                             subprocess.CompletedProcess(command, 7)) as run:
            result = launcher.main(["--environment", str(self.package),
                                    "--evidence-root", str(self.evidence),
                                    "--output", str(self.output)])
            self.assertEqual(result, 7)
            run.assert_called_once_with(command, check=False)


if __name__ == "__main__":
    unittest.main()
