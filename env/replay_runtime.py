#!/usr/bin/env python3
"""Replay runtime-bound with authenticated files at their historical paths."""

import argparse
import hashlib
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from check_public_evidence import check_record, inventory  # noqa: E402
from export_public_evidence import checked_path  # noqa: E402
import preserved_environment  # noqa: E402
sys.path.pop(0)

AUDITED_HOME = "/home/hacker-code-j"
SYSTEM_FILES = ("/usr/bin/bash", "/usr/bin/env", "/usr/bin/python3.10")


def explicit_path(path):
    path = Path(path)
    if ".." in path.parts:
        raise ValueError("parent traversal in supplied path")
    return checked_path(path)


def authenticate_environment(package, repo):
    expected = checked_path(repo / "env/preserved-inputs.json").read_bytes()
    original = checked_path(package / "manifest.json").read_bytes()
    manifest = preserved_environment.authenticate_manifest(original, expected)
    files = manifest["files"]
    if (not files or len(files) != manifest["file_count"]
            or manifest["missing_or_mismatched_inputs"]
            or manifest["all_captured_input_hashes_and_modes_verified"] is not True):
        raise ValueError("environment inventory is incomplete")
    if not set(SYSTEM_FILES).issubset(files):
        raise ValueError("environment lacks required system executables")
    for original, record in files.items():
        path = Path(original)
        if (str(path) != original or ".." in path.parts
                or not (original.startswith(AUDITED_HOME + "/")
                        or original in SYSTEM_FILES)
                or record["archive_path"] != "rootfs" + original):
            raise ValueError("unaudited path in environment inventory")
        payload = checked_path(package / record["archive_path"])
        info = payload.stat()
        if (not stat.S_ISREG(info.st_mode) or info.st_size != record["size"]
                or stat.S_IMODE(info.st_mode) != int(record["mode"], 8)
                or hashlib.sha256(payload.read_bytes()).hexdigest()
                != record["sha256"]):
            raise ValueError("environment payload mismatch: " + original)
    actual = set()
    for path in (package / "rootfs").rglob("*"):
        if path.is_symlink():
            raise ValueError("symlink in environment payload")
        if not path.is_dir():
            actual.add(str(path.relative_to(package)))
    if actual != {record["archive_path"] for record in files.values()}:
        raise ValueError("environment payload inventory differs")


def replay_command(environment, evidence_root, output, check_only=False, repo=ROOT):
    repo, environment, evidence_root, output = map(
        explicit_path, (repo, environment, evidence_root, output))
    for path in (repo, environment, evidence_root):
        if not path.is_dir():
            raise ValueError("input directory is unavailable: " + str(path))
    if output.exists():
        raise ValueError("output already exists")
    if not output.parent.is_dir():
        raise ValueError("output parent must be an existing separate results directory")
    for source in (repo, environment, evidence_root):
        if (output.parent == source or source in output.parent.parents
                or output.parent in source.parents):
            raise ValueError("writable output parent overlaps an input tree")
    if os.environ.get("WHY3_SERVER_SOCKET"):
        raise ValueError("WHY3_SERVER_SOCKET override is not supported")
    bwrap = shutil.which("bwrap")
    if bwrap is None:
        raise ValueError("required host executable bwrap is unavailable")
    authenticate_environment(environment, repo)
    for record in inventory(repo):
        check_record(record, evidence_root)
    command = [
        bwrap, "--die-with-parent", "--ro-bind", "/", "/",
        "--tmpfs", "/tmp", "--dir", "/tmp/work",
        "--ro-bind", str(environment / ("rootfs" + AUDITED_HOME)), AUDITED_HOME,
    ]
    for original in SYSTEM_FILES:
        command.extend(
            ["--ro-bind", str(environment / ("rootfs" + original)), original])
    tool_bin = AUDITED_HOME + "/.opam/cryptotools-2026.09/bin"
    command.extend([
        "--ro-bind", str(repo), "/tmp/work/source",
        "--ro-bind", str(evidence_root), "/tmp/work/evidence",
        "--bind", str(output.parent), "/tmp/work/results",
        "--proc", "/proc", "--dev", "/dev",
        "--setenv", "PATH", tool_bin + ":/usr/bin:/bin",
        "--setenv", "EASYCRYPT", tool_bin + "/easycrypt",
        "--setenv", "WHY3", tool_bin + "/why3",
        "--setenv", "XDG_CONFIG_HOME", AUDITED_HOME + "/.config",
        "--chdir", "/tmp/work/source", "/usr/bin/python3.10",
        "tests/ntruplus768/runtime_bound/verify_runtime_bound.py",
        "--prior-evidence-root", "/tmp/work/evidence",
        "--output", "/tmp/work/results/" + output.name,
    ])
    if check_only:
        command.append("--check-only")
    return command


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--environment", type=Path, required=True)
    parser.add_argument("--evidence-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--check-only", action="store_true",
                        help="source controls only, never a full proof PASS")
    args = parser.parse_args(argv)
    try:
        command = replay_command(args.environment, args.evidence_root, args.output,
                                 args.check_only)
        return subprocess.run(command, check=False).returncode
    except (OSError, ValueError, KeyError, TypeError) as error:
        print("Replay refused: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
