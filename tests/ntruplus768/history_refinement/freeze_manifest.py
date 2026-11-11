#!/usr/bin/env python3
"""Freeze an explicit, reviewed inventory; never discover or approve mains implicitly.

Input schema:
 {"schema":1,"status":"FROZEN","mains":[
   {"source":"kem_history_refinement/Foo.ec", "source_sha256":"...",
    "semantic_target":"last_lemma", "module_binders":["A"],
    "sentinel":"\\nlemma __history_refinement_eof ... proof. exact(last_lemma ...). qed.\\n"}],
  "contracts":[{"source":"kem_history_refinement/Foo.ec","ordered":["..."]}]}

The caller supplies exact theorem declarations and references. This command
checks them before writing pins; it does not generate a positive proof result.
"""
import argparse
import json
from pathlib import Path
import policy


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    args = parser.parse_args()
    import model_contract
    model_contract.check()
    data = policy.manifest(args.manifest.resolve())
    target = policy.TEST / "proof-manifest.json"
    target.write_text(json.dumps(data, indent=2) + "\n")
    pins = policy.snapshot(False)
    (policy.TEST / "source-pins.json").write_text(json.dumps(pins, indent=2) + "\n")
    policy.check()
    print(json.dumps({"status": "FROZEN_NOT_REPLAYED", "mains": len(data["mains"]), "pinned_sources": len(pins)}))


if __name__ == "__main__":
    main()
