#!/usr/bin/env python3
"""Copy the pinned historical inputs into a new local release-candidate bundle."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sys

from check_public_evidence import ROOT, check_record, inventory, relative_path


SPECIFICATION_PINS = Path("tests/ntruplus768/keygen_gen_law/specification-pins.json")
NOTICE = """NTRU+768 historical-input bundle (local release candidate)

This directory contains exactly the hash-pinned historical summaries and two
KeyGen specification inputs selected by the source repository's pin manifests.
The original bytes and evidence-relative paths are preserved. SHA256SUMS covers
the inputs, BUNDLE-MANIFEST.json and this notice; verify it from this directory:

    sha256sum --check SHA256SUMS

These are authenticated historical records, NOT a fresh proof replay or a
complete archive of logs, source dependencies, tools or current results.
Commands and absolute host paths recorded inside the files are historical data.
The exporter does not execute them or follow references to additional files.

Publication gates remain: review the preserved host paths and provenance,
establish redistribution terms for the extracted NTRU+ specification text,
and provide or reconstruct the compatible environment and final replay logs.
The source repository's MIT license does not automatically license this entire
bundle. No DOI, public upload or redistribution clearance is implied.
"""


def checked_path(path):
    """Reject links before resolving roots, parents and evidence paths."""
    path = Path(os.path.abspath(path))
    for part in (path, *path.parents):
        if part.is_symlink():
            raise ValueError("symlink in path: " + str(path))
    return path


def bundle_inventory(repo):
    records = {record["path"]: {**record, "kind": "historical_summary"}
               for record in inventory(repo)}
    pins = json.loads((repo / SPECIFICATION_PINS).read_text())
    if not isinstance(pins, dict) or set(pins) != {"contract", "source_text"}:
        raise ValueError("specification pins must contain contract and source_text")
    for kind, pin in pins.items():
        if not isinstance(pin, dict) or set(pin) != {"path", "sha256"}:
            raise ValueError("invalid specification pin: " + kind)
        name = pin["path"]
        relative_path(name)
        if name in records:
            raise ValueError("duplicate evidence path: " + name)
        records[name] = {**pin, "kind": "specification_" + kind,
                         "required_by": [str(SPECIFICATION_PINS)]}
    for record in records.values():
        name = record["path"]
        if relative_path(name).parts[:2] != ("handoff", "verification"):
            raise ValueError("evidence path must start with handoff/verification/")
        if any(ord(char) < 32 or ord(char) == 127 for char in name):
            raise ValueError("control character in evidence path")
        digest = record["sha256"]
        if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
            raise ValueError("invalid SHA-256 pin: " + name)
    return [records[name] for name in sorted(records)]


def export_evidence(evidence_root, destination, repo=ROOT):
    """Validate every input before writing; never overwrite previous evidence."""
    repo = checked_path(repo).resolve(strict=True)
    evidence_root = checked_path(evidence_root).resolve(strict=True)
    destination = checked_path(destination)
    if not evidence_root.is_dir():
        raise ValueError("evidence root is not a directory")
    for source in (repo, evidence_root):
        if (destination == source or source in destination.parents
                or destination in source.parents):
            raise ValueError("destination overlaps repository or evidence root")
    if destination.exists():
        raise ValueError("destination already exists")
    records = bundle_inventory(repo)
    contents = {}
    for record in records:
        name = record["path"]
        path = checked_path(evidence_root / name)
        if not path.is_file():
            raise ValueError("missing evidence: " + name)
        if record["kind"] == "historical_summary":
            check_record(record, evidence_root)
        data = path.read_bytes()
        if hashlib.sha256(data).hexdigest() != record["sha256"]:
            raise ValueError("SHA-256 mismatch: " + name)
        contents[name] = data
        record["bytes"] = len(data)
    pin_names = sorted({name for record in records for name in record["required_by"]})
    report = {
        "schema": 1,
        "kind": "local release candidate of pinned historical inputs",
        "proofs_replayed": False,
        "publication_status": "not published; redistribution review required",
        "scope": "historical summaries and KeyGen specification inputs only",
        "pin_manifests": {name: hashlib.sha256((repo / name).read_bytes()).hexdigest()
                          for name in pin_names},
        "files": records,
    }
    contents["BUNDLE-MANIFEST.json"] = (json.dumps(report, indent=2) + "\n").encode()
    contents["README.txt"] = NOTICE.encode()
    checksums = "".join(hashlib.sha256(data).hexdigest() + "  " + name + "\n"
                        for name, data in sorted(contents.items()))
    contents["SHA256SUMS"] = checksums.encode()
    destination.mkdir(parents=True, exist_ok=False)
    try:
        for name, data in sorted(contents.items()):
            output = destination / name
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(data)
    except OSError:
        shutil.rmtree(destination)
        raise
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--evidence-root", type=Path, required=True,
        help="existing directory containing the pinned handoff/verification inputs")
    parser.add_argument(
        "destination", type=Path,
        help="new directory outside source and evidence trees")
    args = parser.parse_args(argv)
    try:
        report = export_evidence(args.evidence_root, args.destination)
    except (OSError, ValueError) as error:
        print("Export failed: " + str(error), file=sys.stderr)
        return 1
    print(f"EXPORTED: {len(report['files'])} pinned inputs to {args.destination}")
    print("Local candidate only; no proofs replayed or publication clearance implied.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
