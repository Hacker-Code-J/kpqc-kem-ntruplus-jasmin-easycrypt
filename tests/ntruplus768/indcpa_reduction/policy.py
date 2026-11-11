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
GROUP = "kem_indcpa_reduction"
PROOF = BASE / GROUP
SCRIPT = ROOT / "scripts/verify-ntruplus768-indcpa-reduction.sh"
ENTRY = ROOT / "tests/test_ntruplus768_indcpa_reduction.py"
SHARED = TEST.parent / "fo_simulation"
sys.path.append(str(SHARED))
import check_fo_simulation as shared
from verify_fo_simulation import (check_negative_diagnostic, check_sentinel,
    completed_proof_text, unfinished_proof_text, run_phase)

require, sha, compact = shared.require, shared.sha, shared.compact
without_comments, check_proof_text = shared.without_comments, shared.check_proof_text


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
    for item in mains:
        name = item["source"]
        require(Path(name).parent == Path(GROUP), "main outside declared family")
        source = (BASE / name).read_text()
        check_proof_text(source)
        lemmas = re.findall(r"(?m)^\s*(?:local\s+)?lemma\s+(\w+)", without_comments(source))
        require(lemmas and item["semantic_target"] == lemmas[-1], "EOF target must be last semantic theorem: " + name)
        check_sentinel(name, item["sentinel"], item["semantic_target"], item["module_binders"], source_text=source)
        require("__indcpa_eof" in item["sentinel"], "wrong EOF namespace")
        require(item.get("source_sha256") == sha(source.encode()), "main changed since manifest review: " + name)
    for contract in data.get("contracts", []):
        require(contract["source"] in names and contract.get("ordered"), "invalid source contract")
        shared.ordered(compact((BASE / contract["source"]).read_text()), contract["ordered"])
    return data


def source_paths():
    paths = {SCRIPT, ENTRY, SHARED / "check_fo_simulation.py", SHARED / "verify_fo_simulation.py"}
    for directory in include_arguments()[1]:
        paths.update(directory.rglob("*.ec"))
        paths.update(p for p in (directory / "Makefile", directory / "easycrypt.project") if p.is_file())
    paths.update(p for p in TEST.iterdir() if p.is_file() and p.suffix in (".py", ".json")
                 and p.name != "source-pins.json")
    require(all(p.is_file() and not p.is_symlink() for p in paths), "missing or symlink input")
    return paths


def snapshot(include_pins=True):
    paths = source_paths()
    if include_pins:
        paths.add(TEST / "source-pins.json")
    return {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in sorted(paths)}


def check():
    data = manifest()
    import model_contract
    model_contract.check()
    pins_path = TEST / "source-pins.json"
    require(pins_path.is_file(), "source pins await reviewed freeze")
    pins = json.loads(pins_path.read_text())
    actual = snapshot(False)
    require(set(pins) == set(actual), "source/import inventory drift")
    for name, value in actual.items():
        require(pins[name] == value, "source/import pin drift: " + name)
    return data, pins


if __name__ == "__main__":
    data, pins = check()
    print(json.dumps({"status": "PASS", "new_mains": len(data["mains"]), "pinned_sources": len(pins)}))
