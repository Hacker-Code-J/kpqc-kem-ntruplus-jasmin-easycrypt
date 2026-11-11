"""Fail-closed inventory, trust, semantic EOF, and provenance checks.

The generic comment parser and proof-copy mechanics are reused from the
previous verified family and included in this family's frozen inputs.
"""
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
TEST = Path(__file__).resolve().parent
ROOT = TEST.parents[2]
BASE = ROOT / "ntruplus/proof/768/ref"
GROUP = "kem_runtime_bound"
PROOF = BASE / GROUP
SCRIPT = ROOT / "scripts/verify-ntruplus768-runtime-bound.sh"
ENTRY = TEST / "verify_runtime_bound.py"
SHARED = TEST.parent / "fo_simulation"
sys.path.append(str(SHARED))
import check_fo_simulation as shared
from verify_fo_simulation import (check_negative_diagnostic, check_sentinel,
    completed_proof_text, unfinished_proof_text, run_phase)

require, sha, compact = shared.require, shared.sha, shared.compact
without_comments = shared.without_comments

def check_proof_text(text):
    # The shared scanner predates unnamed EasyCrypt sections and treats
    # "end section" as a theory close. Check their balance separately,
    # then mask only these delimiters while retaining every declaration.
    code = without_comments(text)
    require(not re.search(r'\b(?:op|pred|abbrev)\s+(?:\[[^]]*\]\s*)?"', code), 'new quoted operator outside reviewed source fragment')
    depth = 0
    chunks, offset = [], 0
    for delimiter in re.finditer(r"(?m)^\s*(section|end\s+section)\s*\.", code):
        if delimiter.group(1) == "section":
            depth += 1
        else:
            require(depth > 0, "section close without opener")
            depth -= 1
        chunks.append(code[offset:delimiter.start()])
        chunks.append("".join("\n" if c == "\n" else " " for c in delimiter.group()))
        offset = delimiter.end()
    require(depth == 0, "unclosed section")
    chunks.append(code[offset:])
    shared.check_proof_text("".join(chunks))
    require(not re.search(r"\bcoq\s+(?:check|edit|fix)\b", without_comments(text)),
            "new runtime-bound mains must remain EC-only")


def include_arguments():
    args, directories, seen = [], [], set()
    for raw in (PROOF / "easycrypt.project").read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith(("#", "[")):
            continue
        key, separator, value = line.partition("=")
        key, value = key.strip(), value.strip()
        require(separator and key in ("rdirs", "idirs", "timeout"), "unsupported project setting")
        if key == "timeout":
            require(value == "60", "project timeout must remain 60")
            continue
        namespace, colon, relative = value.partition(":")
        if not colon:
            namespace, relative = "", value
        directory = (PROOF / relative).resolve()
        require(directory.is_dir() and directory.is_relative_to(ROOT), "include outside checkout")
        flag = "-R" if key == "rdirs" else "-I"
        value = (namespace + ":" if colon else "") + str(directory)
        if (flag, value) not in seen:
            args.extend((flag, value))
            directories.append(directory)
            seen.add((flag, value))
    require(PROOF in directories, "new proof family is absent from include path")
    return args, directories


def manifest(path=None):
    path = path or TEST / "proof-manifest.json"
    require(path.is_file() and not path.is_symlink(), "proof inventory awaits reviewed freeze")
    data = json.loads(path.read_text())
    require(data.get("schema") == 1 and data.get("status") == "FROZEN", "manifest is not FROZEN schema 1")
    mains = data.get("mains", [])
    require(mains and isinstance(mains, list), "empty proof inventory")
    names = [item["source"] for item in mains]
    require(len(names) == len(set(names)), "duplicate proof main")
    inventory = {str(p.relative_to(BASE)) for p in PROOF.glob("*.ec")}
    require(set(names) == inventory, "new proof inventory drift")
    require(set(PROOF.rglob("*.ec")) == {BASE / name for name in names}, "development EC inputs remain in production family")
    for item in mains:
        name = item["source"]
        require(Path(name).parent == Path(GROUP), "main outside declared family")
        source = (BASE / name).read_text()
        check_proof_text(source)
        lemmas = re.findall(r"(?m)^\s*(?:local\s+)?lemma\s+(\w+)", without_comments(source))
        require(lemmas and item["semantic_target"] == lemmas[-1], "EOF target must be last semantic theorem: " + name)
        check_sentinel(name, item["sentinel"], item["semantic_target"], item["module_binders"], source_text=source)
        require("__runtime_bound_eof" in item["sentinel"], "wrong EOF namespace")
        require(item.get("source_sha256") == sha(source.encode()), "main changed since manifest review: " + name)
    for contract in data.get("contracts", []):
        require(contract["source"] in names and contract.get("ordered"), "invalid source contract")
        shared.ordered(compact((BASE / contract["source"]).read_text()), contract["ordered"])
    import scope_controls
    scope_controls.validate_export_spec(data)
    return data


def source_paths():
    paths = {SCRIPT, ENTRY, SHARED / "check_fo_simulation.py", SHARED / "verify_fo_simulation.py"}
    import scope_controls
    paths.update(TEST / item["source"] for item in scope_controls.fixture_manifest())
    paths.add(TEST.parent / "history_refinement/executable_policy.py")
    for directory in include_arguments()[1]:
        paths.update(directory.rglob("*.ec"))
        for child in ("coq", ".interactive"):
            paths.update((directory / child).glob("*.v"))
        paths.update(p for p in (directory / "Makefile", directory / "easycrypt.project") if p.is_file())
    paths.update(p for p in TEST.rglob("*") if p.is_file() and p.suffix in (".py", ".json")
                 and p.name != "source-pins.json")
    require(all(p.is_file() and not p.is_symlink() for p in paths), "missing or symlink input")
    return paths


def snapshot(include_pins=True):
    paths = source_paths()
    if include_pins and (TEST / "source-pins.json").is_file():
        paths.add(TEST / "source-pins.json")
    return {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in sorted(paths)}


def dependency_layers(mains):
    """Only independent new mains share a replay layer; imports finish first."""
    indexed = {Path(item["source"]).stem: (i, item) for i, item in enumerate(mains)}
    dependencies = {}
    for name, (_index, item) in indexed.items():
        code = without_comments((BASE / item["source"]).read_text())
        imports = set(re.findall(r"\b\w+\b", " ".join(
            re.findall(r"\brequire\s+import\s+([^.]*)\.", code))))
        dependencies[name] = (imports & set(indexed)) - {name}
    remaining, completed, layers = set(indexed), set(), []
    while remaining:
        ready = sorted(name for name in remaining if dependencies[name] <= completed)
        require(ready, "new proof import dependency cycle")
        layers.append([indexed[name] for name in ready])
        remaining.difference_update(ready)
        completed.update(ready)
    return layers


def check(draft=False):
    import model_contract
    if draft:
        model_contract.check(require_complete=False)
        return {"schema": 1, "status": "DRAFT", "mains": []}, snapshot(False)
    data = manifest()
    model_contract.check(reviewed_manifest=data)
    pins_path = TEST / "source-pins.json"
    require(pins_path.is_file(), "source pins await reviewed freeze")
    pins = json.loads(pins_path.read_text())
    actual = snapshot(False)
    require(set(pins) == set(actual), "source/import inventory drift")
    for name, value in actual.items():
        require(pins[name] == value, "source/import pin drift: " + name)
    return data, pins


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--draft", action="store_true", help="inspect current sources without freeze or proof claims")
    args = parser.parse_args()
    data, pins = check(args.draft)
    import model_contract
    executable_audit = model_contract.check(require_complete=not args.draft, reviewed_manifest=data)
    print(json.dumps({"status": "DRAFT_SOURCE_CHECK_ONLY" if args.draft else "PASS",
                      "declared_mains": len(data["mains"]), "source_inputs": len(pins),
                      "executable_audit": executable_audit}))
