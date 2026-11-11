#!/usr/bin/env python3
"""Bounded source-value compatibility audit, not a C-AST equivalence proof."""
import argparse
import hashlib
import json
import re
from pathlib import Path


def function_body(path, name):
    text = path.read_text()
    match = re.search(r"\b" + name + r"\s*\([^;{}]*\)\s*\{", text)
    if match is None:
        raise ValueError(f"missing function {name}: {path}")
    start = match.end()
    depth, end = 1, start
    while depth:
        depth += (text[end] == "{") - (text[end] == "}")
        end += 1
    return re.sub(r"/\*.*?\*/|//[^\n]*", "", text[start:end - 1], flags=re.S)


def normalized(text):
    return re.sub(r"\s+", "", text)


def substituted_outputs(body):
    environment = {}
    assignments = re.findall(r"(?:int16_t\s+)?(r\[\d\]|[tc]\d)\s*=\s*([^;]+);", body)
    if len(assignments) != 11:
        raise ValueError("expected exactly eleven basemul assignments")
    for lhs, rhs in assignments:
        rhs = normalized(rhs)
        rhs = re.sub(r"r\[\d\]|\b[tc]\d\b",
                     lambda m: "(" + environment[m[0]] + ")"
                     if m[0] in environment else m[0], rhs)
        environment[lhs] = rhs
    return {f"r[{i}]": environment[f"r[{i}]"] for i in range(4)}


def audit(root):
    old = root / "NTRU+" / "NTRU+768"
    official = root / "tests/ntruplus768/decap_guard/reference"
    before = function_body(old / "ntt.c", "invntt")
    after = function_body(official / "ntt.c", "invntt")
    before, removed = re.subn(
        r"for\s*\(int i = 0; i < NTRUPLUS_N; i\+\+\)\s*\{\s*r\[i\] = a\[i\];\s*\}",
        "", before)
    source = root / "ntruplus/jasmin/768/ref/poly_basemul.jazz"
    jasmin_values = re.search(r"NTRUPLUS_ZETAS96 = \{(.*?)\}", source.read_text(), re.S)[1]
    official_values = re.search(r"zetas\[192\] = \{(.*?)\}",
                                (official / "ntt.c").read_text(), re.S)[1]
    jasmin_zetas = list(map(int, jasmin_values.replace(",", " ").split()))
    official_zetas = list(map(int, official_values.replace(",", " ").split()))
    checks = {
        "invntt_body_identical_after_removing_one_old_copy":
            removed == 1 and normalized(before) == normalized(after),
        "crepmod3_scalar_body_identical":
            normalized(function_body(old / "poly.c", "crepmod3")) ==
            normalized(function_body(official / "poly.c", "crepmod3")),
        "basemul_same_substituted_outputs_for_disjoint_regions":
            substituted_outputs(function_body(old / "ntt.c", "basemul")) ==
            substituted_outputs(function_body(official / "ntt.c", "basemul")),
        "basemul_twiddles_exact_mod65536":
            len(jasmin_zetas) == 96 and len(official_zetas) == 192 and
            jasmin_zetas == [x % 65536 for x in official_zetas[96:]],
    }
    if not all(checks.values()):
        raise ValueError(f"compatibility audit failed: {checks}")
    paths = [old / "ntt.c", old / "poly.c", official / "ntt.c", official / "poly.c", source,
             root / "ntruplus/jasmin/768/ref/decap_candidate.jazz"]
    return {
        "result": "PASS",
        "official_commit": "3991b2ae08d6f0008d37e41b8aceaaab27b4ec89",
        "checks": checks,
        "scope": "Source-level value audit, not a C-AST proof. Original kernels unchanged; "
                 "native differential execution and extracted-procedure proofs are separate. "
                 "The old out-of-place inverse retains its copy and scratch storage, so "
                 "neither trace nor erasure equivalence is asserted. Forward NTT reduction "
                 "relocation and the fqinv chain are not exercised.",
        "files": {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = audit(args.root.resolve())
    rendered = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")
