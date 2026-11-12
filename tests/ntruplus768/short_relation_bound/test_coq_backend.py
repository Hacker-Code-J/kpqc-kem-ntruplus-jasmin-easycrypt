#!/usr/bin/env python3
"""Backend controls; --integration also replays a real native goal in spaced paths."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
import coq_backend as backend


def controls():
    skeleton = ("Axiom old_context : Type.\n\n" + backend.GOAL +
                "\nTheorem goal : True.\nProof.\nexact I.\nQed.\n")
    parts = backend.split_script(skeleton)
    assert backend.split_script(backend.authored_script(parts)) == parts
    parts["prelude"] = "Require Import Coq.Init.Logic."
    assert backend.split_script(backend.authored_script(parts)) == parts
    rejected = [skeleton.replace("Qed.", "Admitted."),
                skeleton + "Axiom added : False.\n",
                skeleton.replace(backend.GOAL, backend.GOAL * 2),
                backend.BEGIN + "\n" + skeleton,
                skeleton.replace("Theorem goal", "Theorem different")]
    for text in rejected:
        try:
            backend.split_script(text)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid native layout accepted")
    for fragment in ["Admitted.", "Axiom hole : False.", "Unset Guard Checking."]:
        unsafe = dict(parts, body=fragment)
        try:
            backend.authored_script(unsafe)
        except ValueError:
            pass
        else:
            raise AssertionError("unsafe proof accepted")
    assert backend.assumption_names("Closed under the global context") == set()
    assert backend.assumption_names("Axioms:\nold_context : Type\nsecond\n  : True") == {"old_context", "second"}
    for text in ["", "Closed under the global context\nAxioms:\nhole:False", "Axioms:"]:
        try:
            backend.assumption_names(text)
        except ValueError:
            pass
        else:
            raise AssertionError("ambiguous assumptions accepted")
    guard = object.__new__(backend.CoqBackend)
    for name in backend.LINKER_OVERRIDES:
        with patch.dict(os.environ, {name: "/untrusted/library"}):
            try:
                guard.environment()
            except ValueError:
                pass
            else:
                raise AssertionError("dynamic-linker override accepted")
    with tempfile.TemporaryDirectory(prefix="backend-diagnostic-") as directory:
        main, log = Path(directory) / "Own.ec", Path(directory) / "failure.log"
        main.write_text('lemma test : true.\nproof. coq check "owned" (). qed.\n')
        log.write_text('[critical] [' + str(main) + ': line 2 (7-25)] cannot prove goal (strict)\n')
        backend.native_failure(log, main, "owned")
        for location in [str(main) + ': line 1', str(main.parent / 'Other.ec') + ': line 2']:
            log.write_text('[critical] [' + location + '] cannot prove goal (strict)\n')
            try:
                backend.native_failure(log, main, "owned")
            except ValueError:
                pass
            else:
                raise AssertionError("unrelated native failure accepted")
        config = Path(directory) / "base.conf"
        config.write_text('[main]\nmagic = 14\nmemlimit = 1000\ntimelimit = 5.000000\n')
        original = config.read_bytes()
        instance = backend.CoqBackend(Path(directory), Path(directory) / 'evidence', None, set(), {},
            coqc='/bin/true', coqtop='/bin/true', why3_config=config,
            why3_support_source=directory, driver=Path(directory) / 'coq.drv')
        isolated = Path(directory) / 'isolated.conf'
        instance.write_config(isolated)
        assert config.read_bytes() == original
        assert 'timelimit = 60.0' in isolated.read_text() and 'memlimit = 1000' in isolated.read_text()
        assert instance.records['actual_native_limits']['timelimit_seconds'] == 60.0
        assert instance.records['actual_native_limits']['memlimit_mb'] == 1000
    return {"result": "PASS", "layout_rejections": len(rejected),
            "authored_rejections": 3, "assumption_rejections": 3,
            "linker_rejections": 3, "wrong_location_rejections": 2,
            "native_time_limit_override_preserving_base_and_memory": "PASS"}


def integration(output):
    inputs = [Path(__file__), Path(backend.__file__), Path(backend.coq_policy.__file__)]
    inputs_before = backend.snapshot(inputs)
    output.mkdir(parents=True, exist_ok=False)
    root = output / "source tree café with spaces"
    root.mkdir()
    helper = root / "BackendMath.v"
    helper.write_text("From Coq Require Import ZArith Lia.\n"
                      "Lemma backend_square (x:Z) : (0 <= x*x)%Z.\n"
                      "Proof. nia. Qed.\n")
    old = Path.home() / ".opam/ocaml-base-compiler.4.12.0"
    current = Path.home() / ".opam/cryptotools-2026.09"
    records = []

    def run(label, argv, expected_failure=False, cwd=root):
        log = output / (str(len(records)).zfill(3) + "-" + label + ".log")
        with log.open("wb") as stream:
            result = subprocess.run(list(map(str, argv)), cwd=cwd, stdout=stream,
                                    stderr=subprocess.STDOUT, timeout=120,
                                    env={**os.environ, "OCAMLRUNPARAM": "o=20"})
        records.append({"label": label, "argv": list(map(str, argv)), "cwd": str(cwd),
                        "exit_code": result.returncode, "expected_failure": expected_failure,
                        "log": str(log), "log_sha256": backend.digest(log)})
        if (result.returncode != 0) != expected_failure:
            raise AssertionError(label + ": " + log.read_text(errors="replace")[-5000:])
        return log

    options = dict(coqc=old / "bin/coqc", coqtop=old / "bin/coqtop",
                   why3_config=Path.home() / ".config/easycrypt/why3.conf",
                   why3_support_source=current / ".opam-switch/sources/why3.1.8.2/lib/coq",
                   driver=current / "share/why3/drivers/coq.drv")
    manifest = {"helpers": [{"source": helper.name, "source_sha256": backend.digest(helper),
                            "module": helper.stem, "exports": ["backend_square"]}], "natives": {}}
    external = set()
    bootstrap = backend.CoqBackend(root, output / "bootstrap evidence", run, external, manifest, **options)
    bootstrap.prepare()
    ec_text = ('require import AllCore.\n'
               'lemma square_nonnegative : forall (x:int), 0 <= x*x.\n'
               'proof. coq check "square" (). qed.\n'
               'lemma __backend_semantic_eof : forall (x:int), 0 <= x*x.\n'
               'proof. exact square_nonnegative. qed.\n')
    initial = output / "fresh template"
    initial.mkdir()
    source = initial / "Smoke.ec"
    source.write_text(ec_text)
    argv = [current / "bin/easycrypt", "compile", "-no-eco", "-pragmas", "Proofs:check",
            "-p", "Z3", "-timeout", "60", "-max-provers", "1"]
    log = run("bootstrap-goal", [*bootstrap.native_argv(argv), source], True, initial)
    assert "cannot prove goal (strict)" in log.read_text()
    parts = backend.split_script((initial / ".interactive/square.v").read_text())
    parts.update(prelude="Require Import BackendMath.", body="intros x.\nexact (backend_square x).")
    template = root / "square.v"
    template.write_text(backend.authored_script(parts))
    spec = {"scripts": [{"name": "square", "source": template.name,
                         "source_sha256": backend.digest(template)}],
            "changed_goal": {"old": "lemma square_nonnegative : forall (x:int), 0 <= x*x.",
                             "new": "lemma square_nonnegative : forall (x:int), 1 <= x*x."}}
    manifest["natives"] = {"Smoke.ec": spec}
    production = backend.CoqBackend(root, output / "actual evidence café with spaces", run, external, manifest, **options)
    production.prepare()
    assert production.records['actual_native_limits']['timelimit_seconds'] == 60.0
    positive = production.output / "main with spaces" / "Smoke.ec"
    positive.parent.mkdir(parents=True)
    positive.write_text(ec_text)
    prepared = production.prepare_native(positive, "positive", spec, argv)
    run("positive-final", prepared["command"], cwd=positive.parent)
    production.validate_native(positive, spec)
    production.negative_controls(positive, "native", spec, argv)
    production.scope_control(positive)
    # The same native goal must remain checkable when the EC final qed is absent.
    negative = production.output / "open main with spaces" / "Smoke.ec"
    negative.parent.mkdir(parents=True)
    negative.write_text(ec_text.replace("qed.", "", 1))
    prepared = production.prepare_native(negative, "open-main", spec, argv)
    log = run("open-main-final", prepared["command"], True, negative.parent)
    import re
    diagnostic = re.search(r'\[critical\]\s*\[' + re.escape(str(negative)) + r':[^\r\n]+', log.read_text())
    assert diagnostic and "cannot process [axiom] inside a proof script" in diagnostic.group()
    assert "external theory" not in log.read_text().lower()
    production.validate_native(negative, spec)
    evidence = production.finalize()
    inputs_after = backend.snapshot(inputs)
    assert inputs_before == inputs_after
    result = {"status": "PASS", "scope": "Native backend integration smoke only, not the NTRU+ mathematical bound",
              "records": records, "backend": evidence, "paths_with_spaces": True, "unicode_paths": True,
              "native_controls": 4, "own_unfinished_ec_main_rejected": True}
    result.update(test_inputs_before=inputs_before, test_inputs_after=inputs_after, test_inputs_unchanged=True)
    (output / "summary.json").write_text(json.dumps(result, indent=2) + "\n")
    return {"status": "PASS", "summary": str(output / "summary.json")}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--integration", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = {"status": "PASS", "controls": controls()}
    if args.integration:
        target = args.output or Path(tempfile.mkdtemp(prefix="coq-backend-parent-")) / "backend proof space"
        result["integration"] = integration(target)
    print(json.dumps(result, indent=2))
