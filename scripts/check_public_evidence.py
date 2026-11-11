#!/usr/bin/env python3
"""Inventory or authenticate historical proof summaries; never replay proofs."""

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys


ROOT = Path(__file__).resolve().parents[1]


def relative_path(value):
    """Require a canonical relative POSIX path before touching the filesystem."""
    if not isinstance(value, str) or not value or "\\" in value:
        raise ValueError("invalid evidence path")
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or str(path) != value or value == ".":
        raise ValueError("evidence path must be canonical and relative: " + value)
    return path


def inventory(repo=ROOT):
    """Combine the checked-in pin files without consulting private evidence."""
    records = {}
    manifests = sorted((repo / "tests/ntruplus768").glob("*/prior-evidence-pins.json"))
    if not manifests:
        raise ValueError("no prior-evidence-pins.json manifests found")
    for manifest in manifests:
        pins = json.loads(manifest.read_text())
        if not isinstance(pins, dict) or not pins:
            raise ValueError("empty or invalid pin manifest: "
                             + str(manifest.relative_to(repo)))
        for name, digest in pins.items():
            relative_path(name)
            if (not isinstance(digest, str)
                    or re.fullmatch(r"[0-9a-f]{64}", digest) is None):
                raise ValueError("invalid SHA-256 pin: " + name)
            record = records.setdefault(
                name, {"path": name, "sha256": digest, "required_by": []})
            if record["sha256"] != digest:
                raise ValueError("conflicting evidence pins: " + name)
            record["required_by"].append(str(manifest.relative_to(repo)))
    return [records[name] for name in sorted(records)]


def check_record(record, root):
    """Check identity and recorded audit status, not current source/tool validity."""
    relative = relative_path(record["path"])
    root = root.resolve(strict=True)
    if not root.is_dir():
        raise ValueError("evidence root is not a directory")
    path = root
    for part in relative.parts:
        path = path / part
        if path.is_symlink():
            raise ValueError("symlink in evidence path: " + str(relative))
    if not path.is_file():
        raise ValueError("missing evidence: " + str(relative))
    if not path.resolve().is_relative_to(root):
        raise ValueError("evidence escapes root: " + str(relative))
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != record["sha256"]:
        raise ValueError("SHA-256 mismatch: " + str(relative))
    report = json.loads(data)
    if not isinstance(report, dict) or report.get("status") != "PASS":
        raise ValueError("historical summary does not record PASS: " + str(relative))
    if (report.get("inputs_unchanged") is not True
            or not isinstance(report.get("source_hashes_before"), dict)
            or report["source_hashes_before"] != report.get("source_hashes_after")):
        raise ValueError("unstable historical source audit: " + str(relative))
    # Legacy summaries have no external audit. Preserve that distinction rather
    # than manufacturing a claim about their compiler/prover inputs.
    if any(key in report for key in ("external_hashes_before", "external_hashes_after",
                                      "external_inputs_unchanged")):
        if (report.get("external_inputs_unchanged") is not True
                or not isinstance(report.get("external_hashes_before"), dict)
                or report["external_hashes_before"]
                != report.get("external_hashes_after")):
            raise ValueError("unstable historical external audit: " + str(relative))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--evidence-root", type=Path,
        help="explicit directory containing handoff/verification; omit to inventory")
    args = parser.parse_args(argv)
    try:
        records = inventory()
        if args.evidence_root is None:
            print(json.dumps({
                "scope": ("historical evidence inventory; "
                          "no files checked or proofs replayed"),
                "records": records}, indent=2))
            return 0
        errors = []
        for record in records:
            try:
                check_record(record, args.evidence_root)
            except (OSError, ValueError) as error:
                errors.append(str(error))
        if errors:
            for error in errors:
                print("FAIL: " + error, file=sys.stderr)
            return 1
        print(f"VERIFIED: {len(records)} historical summaries match pinned bytes "
              "and recorded PASS audits.")
        print("No proofs replayed; current source/tool compatibility "
              "and artifact completeness were not checked.")
        return 0
    except (OSError, ValueError) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
