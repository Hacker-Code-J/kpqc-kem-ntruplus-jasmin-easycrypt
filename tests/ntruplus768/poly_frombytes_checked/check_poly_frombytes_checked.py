#!/usr/bin/env python3
"""Check exact reference/source identity and proof policy, not C-AST equivalence."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

TEST = Path(__file__).resolve().parent
ROOT = TEST.parents[2]
SLICE = "jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes"
SOURCE = ROOT / "ntruplus/jasmin/768/ref/poly_frombytes.jazz"
SOURCE_SHA256 = "3bc951679734c56a327df50aecd505bb664905a8bfc2127f4b15a95da9d82b04"
REFERENCE_MANIFEST_SHA256 = "99aa96c4dc8e97b3115b0dbf056d6df77569a2c6cd9c6abbcee35da9c855cca5"
REFERENCE_SHA256 = {
    "poly.c": "923990d51c526f2c46d1a40dc6fb6ef4e50ada35f74647ad73fd597a25fda592",
    "poly.h": "9a3ac9414dd75412d7dbc888aab82cf7659531b7993256123eee687e85f1d743",
    "params.h": "420bef5432154798239e1f09b18f31947e3afff248ff98d4e83346b84d27ebb8",
    "ntt.h": "1edc2346f1705cc98af0f64b2f0ac974f3d58ab9b6603ebbfa415f4e135f5851",
    "symmetric.h": "d56d67dbf50c7b89de87eb5acbcfb11ece0fe90e7744762c0bc9a47350d80f65",
    "util.h": "561a5b1e0611985890d9eff695f1ac34f88605631dcef620100ab6aed1b1276d",
    "api.h": "1912c6a38e7f1449321520570020266836a4cace70f7e5901d0e8c172a707865",
    "LICENSE": "fc50cdff5695ed2aedde871816fbd86cb0e33a3b315b25948489418dacd9c81a",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def check_reference(manifest_data=None, files=None):
    manifest_data = (TEST / "reference-manifest.json").read_bytes() if manifest_data is None else manifest_data
    require(sha(manifest_data) == REFERENCE_MANIFEST_SHA256, "reference manifest pin drift")
    manifest = json.loads(manifest_data)
    require(manifest["upstream_commit"] == "3991b2ae08d6f0008d37e41b8aceaaab27b4ec89", "reference commit drift")
    require(manifest["files"] == REFERENCE_SHA256, "reference file pins drift")
    if files is None:
        reference = TEST / "reference"
        paths = sorted(reference.rglob("*"))
        require(all(p.is_file() and not p.is_symlink() for p in paths), "unexpected reference path")
        files = {str(p.relative_to(reference)): p.read_bytes() for p in paths}
    require(set(files) == set(REFERENCE_SHA256), "reference file inventory drift")
    for name, expected in REFERENCE_SHA256.items():
        require(sha(files[name]) == expected, "reference source drift: " + name)


def check_jasmin(data=None):
    data = SOURCE.read_bytes() if data is None else data
    require(sha(data) == SOURCE_SHA256, "checked Jasmin source pin drift")
    code = re.sub(r"//[^\n]*|/\*.*?\*/", "", data.decode(), flags=re.S)
    require("#declassify" not in code, "checked decoder must not declassify data or status")
    require('#[ct = "secret × secret → secret × secret"]' in code, "CT input/output policy drift")
    require('#[sct=' in code and 'secret\n"]' in code, "SCT status policy drift")
    require("export fn " + SLICE in code, "checked decoder export drift")


def without_comments(text):
    depth = 0
    parts = []
    for token in re.split(r"(\(\*|\*\))", text):
        if token == "(*":
            depth += 1
            parts.append(" ")
        elif token == "*)":
            require(depth > 0, "unmatched EasyCrypt comment terminator")
            depth -= 1
        elif not depth:
            parts.append(token)
    require(depth == 0, "unclosed EasyCrypt comment")
    return "".join(parts)


def check_proof_text(text):
    code = without_comments(text)
    require(not re.search(r"\b(admit|admitted|abort|assume|axiom|sorry|pragma)\b", code), "proof escape or pragma")
    require(not re.search(r"\baxiomatized\s+by\b", code), "opaque proof assumption")
    require(not re.search(r"(?m)^\s*print\s+(?:goal|all)\b", code), "debug proof command")
    for statement in re.split(r"\.(?=\s|$)", code):
        if re.match(r"\s*(?:local\s+)?(?:op|type)\b", statement):
            require("=" in statement, "abstract project declaration")
            require("{" not in statement.partition("=")[0], "constrained project declaration")


def check_extraction(stored, fresh):
    def contents(directory):
        files = list(directory.rglob("*"))
        require(all(not p.is_symlink() for p in files), "symlink in extraction")
        require(all(p.suffix == ".ec" for p in files if p.is_file()), "unexpected extraction file")
        return {str(p.relative_to(directory)): p.read_bytes() for p in files if p.is_file()}
    before, after = contents(stored), contents(fresh)
    require(set(before) == set(after), "whole extraction file inventory drift")
    require(before == after, "raw extraction byte drift")
    require(len(before) == 5, "expected five old-array extraction files")
    return {name: sha(data) for name, data in before.items()}


def selfcheck():
    def rejects(call, label):
        try:
            call()
        except ValueError:
            return
        raise ValueError("mutation accepted: " + label)
    reference = {name: (TEST / "reference" / name).read_bytes() for name in REFERENCE_SHA256}
    changed = reference | {"poly.c": reference["poly.c"] + b"\n/* changed */\n"}
    rejects(lambda: check_reference(files=changed), "reference bytes")
    forged = json.loads((TEST / "reference-manifest.json").read_text())
    forged["files"]["poly.c"] = sha(changed["poly.c"])
    rejects(lambda: check_reference(json.dumps(forged).encode(), changed), "reference plus manifest")
    rejects(lambda: check_jasmin(SOURCE.read_bytes().replace(b"fail >>= 31;", b"fail = 0;")), "status removed")
    rejects(lambda: check_jasmin(SOURCE.read_bytes() + b"\n// changed\n"), "Jasmin bytes")
    for text in ["lemma forged : false. proof. admit. qed.", "pragma -check.",
                 "op trusted : int.", "axiom impossible : false.", "(* unclosed"]:
        rejects(lambda text=text: check_proof_text(text), "proof policy")
    check_proof_text("(* outer (* nested *) *) lemma okay : true. proof. trivial. qed.")
    print("PASS: nine reference/source/proof-policy mutations rejected")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-check", action="store_true")
    args = parser.parse_args()
    check_reference()
    check_jasmin()
    if args.self_check:
        selfcheck()
    print("PASS: exact official 3991b2a reference subset and checked Jasmin source/policy pins")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        sys.exit(1)
