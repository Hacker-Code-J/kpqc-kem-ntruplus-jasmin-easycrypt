"""Fresh Coq helpers and native EasyCrypt proof replay in an evidence directory.

The caller owns EC semantic-EOF checks.  This module never changes checkout
sources or toolchain configuration, and does not treat standalone Coq proofs
as proofs of an EasyCrypt caller.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import shlex

import coq_policy


BEGIN = "(* SR AUTHORED PRELUDE BEGIN *)"
END = "(* SR AUTHORED PRELUDE END *)"
GOAL = "(* Why3 goal *)"
IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*\Z")
IMPORT_OVERRIDES = ("COQPATH", "COQLIB", "COQCORELIB", "COQBIN", "OCAMLPATH",
                    "CAML_LD_LIBRARY_PATH", "OCAMLFIND_CONF", "OCAMLFIND_TOOLCHAIN")
LINKER_OVERRIDES = ("LD_PRELOAD", "LD_LIBRARY_PATH", "LD_AUDIT")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def snapshot(paths):
    return {str(p): digest(p) for p in sorted(set(map(Path, paths)))}


def native_failure(log, main, script_name):
    text, main = Path(log).read_text(), Path(main)
    call = re.search(r'\bcoq\s+check\s+"' + re.escape(script_name) + r'"', main.read_text())
    require(call is not None, "native control script is not called by its main")
    line = main.read_text()[:call.start()].count("\n") + 1
    match = re.search(r'\[critical\]\s*\[' + re.escape(str(main)) +
                      r':\s*(?:line\s+)?' + str(line) + r'\b[^\r\n]*cannot prove goal \(strict\)', text)
    require(match is not None and "external theory" not in text.lower(),
            "native failure is not at the intended copied-main Coq call")
    return match.group()


def source_path(root, item):
    root, relative = Path(root).resolve(), Path(item["source"])
    require(not relative.is_absolute() and ".." not in relative.parts, "source must be checkout relative")
    path = root / relative
    require(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(root),
            "missing or indirect Coq input: " + str(relative))
    require(digest(path) == item["source_sha256"], "Coq source pin drift: " + str(relative))
    return path


def validate_spec_sources(root, manifest):
    """Read-only authored-input checks, also usable by SOURCE_CHECK_ONLY."""
    checked = []
    helpers = manifest["helpers"]
    require(helpers and len({h["module"] for h in helpers}) == len(helpers), "empty or duplicate helper inventory")
    for item in helpers:
        path = source_path(root, item)
        require(item["module"] == path.stem and IDENTIFIER.fullmatch(item["module"]),
                "helper module must match source filename")
        require(item.get("exports") and len(set(item["exports"])) == len(item["exports"]),
                "empty or duplicate helper exports")
        require(all(IDENTIFIER.fullmatch(x) for x in item["exports"]), "invalid theorem export")
        coq_policy.check_authored(path.read_text())
        checked.append(path)
    for spec in manifest.get("natives", {}).values():
        scripts = spec["scripts"]
        require(scripts and len({s["name"] for s in scripts}) == len(scripts), "empty or duplicate native scripts")
        for item in scripts:
            require(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", item["name"]), "invalid native script name")
            path = source_path(root, item)
            authored_script(split_script(path.read_text()))
            checked.append(path)
    return checked


def split_script(text):
    """Separate generated context/statement from reviewed authored sections."""
    require(text.count(GOAL) == 1, "native script must have exactly one Why3 goal")
    head, tail = text.split(GOAL)
    prelude = ""
    require(head.count(BEGIN) == head.count(END) <= 1, "invalid authored prelude markers")
    if BEGIN in head:
        header, remainder = head.split(BEGIN)
        prelude, remainder = remainder.split(END)
        require(not remainder.strip(), "authored prelude must immediately precede Why3 goal")
        head = header
    require(BEGIN not in tail and END not in tail, "prelude marker in theorem body")
    proof = re.search(r"(?m)^Proof\.\s*$", tail)
    require(proof is not None, "missing generated Proof delimiter")
    statement, after = tail[:proof.start()].strip(), tail[proof.end():]
    # Why3 adds this advisory comment on the second export. It is not part
    # of the proposition and must not be mistaken for a changed goal.
    statement = re.sub(r"\(\* Why3 intros\b.*?\*\)", "", statement, flags=re.S).strip()
    require(re.match(r"Theorem\s+goal\s*:", statement) is not None,
            "unexpected generated theorem name")
    closers = list(re.finditer(r"(?m)^Qed\.\s*$", after))
    require(len(closers) == 1, "native script must have one goal closer")
    closer = closers[0]
    trailing = coq_policy.code_only(after[closer.end():]).strip()
    require(trailing in ("", "Print Assumptions goal."), "unexpected native trailing declarations")
    return {"header": head.strip(), "statement": statement,
            "prelude": prelude.strip(), "body": after[:closer.start()].strip()}


def authored_script(parts):
    coq_policy.check_authored(parts["prelude"])
    coq_policy.check_authored(parts["body"], proof_body=True)
    prelude = ""
    if parts["prelude"]:
        prelude = BEGIN + "\n" + parts["prelude"] + "\n" + END + "\n\n"
    return (parts["header"] + "\n\n" + prelude + GOAL + "\n" +
            parts["statement"] + "\nProof.\n" + parts["body"] + "\nQed.\n")


def semantic_guarded_script(parts):
    """Capture the exported proposition before imports can change notation."""
    text = authored_script(parts)
    require("sr_fresh_exported_goal" not in text and "sr_checked_goal" not in text,
            "native source collides with semantic guard names")
    statement = parts["statement"]
    require(statement.endswith("."), "generated proposition has no terminator")
    proposition = re.sub(r"^Theorem\s+goal\s*:\s*", "", statement[:-1], count=1)
    reference = "\n\nDefinition sr_fresh_exported_goal : Prop := (" + proposition + ").\n"
    boundary = len(parts["header"])
    return (text[:boundary] + reference + text[boundary:] +
            "\nDefinition sr_checked_goal : sr_fresh_exported_goal := goal.\n")


def assumption_names(text):
    """Names in Coq's Print Assumptions output; fail on ambiguous formatting."""
    text = text.strip()
    if text == "Closed under the global context":
        return set()
    require(text.startswith("Axioms:\n"), "unexpected native assumption response")
    names = set()
    for line in text.splitlines()[1:]:
        if line and not line[0].isspace():
            name = line.split(":", 1)[0].strip()
            require(IDENTIFIER.fullmatch(name), "unrecognized native assumption name")
            names.add(name)
    require(names, "empty Axioms response")
    return names


class CoqBackend:
    def __init__(self, root, output, run, external, manifest, *, coqc, coqtop,
                 why3_config, why3_support_source, driver):
        self.root, self.output = Path(root).resolve(), Path(output).resolve()
        self.runner, self.external, self.manifest = run, external, manifest
        self.coqc, self.coqtop = Path(coqc).resolve(), Path(coqtop).resolve()
        self.base_config = Path(why3_config).resolve()
        self.why_source, self.driver = Path(why3_support_source).resolve(), Path(driver).resolve()
        self.directory = self.output / "coq-backend"
        self.support, self.helpers = self.directory / "support", self.directory / "helpers"
        self.config = self.directory / "why3.conf"
        self.env_tool = Path("/usr/bin/env").resolve()
        self.artifacts, self.prepared = {}, {}
        self.records = {"scope": "Fresh helper checks and native EC caller replay",
                        "helpers": [], "native": [], "negative_controls": []}

    def environment(self):
        require(not any(os.environ.get(name) for name in LINKER_OVERRIDES),
                "dynamic-linker environment override is not allowed")
        return {name: {"nonempty": bool(os.environ.get(name)),
                       "value_sha256": hashlib.sha256(os.environ.get(name, "").encode()).hexdigest()}
                for name in (*IMPORT_OVERRIDES, *LINKER_OVERRIDES)}

    def clean_command(self, argv):
        return [str(self.env_tool), *[item for name in (*IMPORT_OVERRIDES, *LINKER_OVERRIDES)
                                     for item in ("-u", name)], *map(str, argv)]

    def run(self, label, argv, expected_failure=False, cwd=None):
        return self.runner(label, self.clean_command(argv), expected_failure, cwd or self.directory)

    def source(self, item):
        return source_path(self.root, item)

    def pin_artifact(self, path):
        path = Path(path)
        self.artifacts[str(path)] = digest(path)

    def coq_arguments(self, helper_directory=None):
        return ["-q", "-R", str(self.support), "Why3", "-Q",
                str(helper_directory or self.helpers), ""]

    def write_config(self, path, helper_directory=None):
        baseline = self.base_config.read_text()
        # Replace a stock/system Coq entry only in this isolated copy.  The
        # original configuration and every unrelated prover remain untouched.
        sections = list(re.finditer(r"(?m)^\[([^]\n]+)\][ \t]*$", baseline))
        kept = [baseline[:sections[0].start()]] if sections else [baseline]
        main_count = 0
        for index, section in enumerate(sections):
            stop = sections[index + 1].start() if index + 1 < len(sections) else len(baseline)
            block = baseline[section.start():stop]
            if section.group(1) == "main":
                main_count += 1
                memory = re.findall(r"(?m)^\s*memlimit\s*=\s*([0-9]+)\s*$", block)
                require(len(memory) == 1, "explicit native memory limit is missing or ambiguous")
                # ecCoq.run_batch reads Whyconf's main limits directly. The
                # EasyCrypt -timeout option only controls the SMT path.
                require(len(re.findall(r"(?m)^\s*timelimit\s*=", block)) <= 1,
                        "ambiguous native time limit")
                if re.search(r"(?m)^\s*timelimit\s*=", block):
                    block = re.sub(r"(?m)^\s*timelimit\s*=[^\r\n]*", "timelimit = 60.0", block)
                else:
                    block = block.rstrip() + "\ntimelimit = 60.0\n\n"
                self.records["actual_native_limits"] = {
                    "timelimit_seconds": 60.0, "memlimit_mb": int(memory[0]),
                    "scope": "Isolated Why3 [main] limits consumed by native coq check; memory limit preserved from base configuration."}
            old_coq = (section.group(1) in ("prover", "partial_prover") and
                       re.search(r'(?m)^\s*name\s*=\s*"Coq"\s*$', block))
            if not old_coq:
                kept.append(block)
        require(main_count == 1, "Why3 configuration must have one main section")
        baseline = "".join(kept)
        argv = self.clean_command([str(self.coqtop), "-batch", *self.coq_arguments(helper_directory), "-l", "%f"])
        command = shlex.join(argv)
        block = ('\n[prover]\nname = "Coq"\nversion = "8.20.1"\ncommand = ' +
                 json.dumps(command, ensure_ascii=False) + '\ndriver = ' + json.dumps(str(self.driver), ensure_ascii=False) +
                 '\ninteractive = true\nin_place = true\n')
        Path(path).write_text(baseline.rstrip() + "\n" + block)

    def query_assumptions(self, label, theorem, *, module=None, script=None):
        require(IDENTIFIER.fullmatch(theorem), "invalid theorem export")
        require((module is None) != (script is None), "one assumption query input required")
        token = hashlib.sha256(label.encode()).hexdigest()[:16]
        first, last = "SR_QUERY_BEGIN_" + token, "SR_QUERY_END_" + token
        query = self.directory / (label + ".v")
        text = ""
        if module is not None:
            require(IDENTIFIER.fullmatch(module), "invalid helper module")
            text += "Require Import " + module + ".\n"
        text += ('Goal True. idtac "' + first + '". exact I. Qed.\n' +
                 "Print Assumptions " + theorem + ".\n" +
                 'Goal True. idtac "' + last + '". exact I. Qed.\n')
        query.write_text(text)
        argv = [self.coqtop, "-batch", *self.coq_arguments()]
        if script is not None:
            argv += ["-l", str(script)]
        log = self.run(label, [*argv, "-l", query], cwd=self.directory)
        output = Path(log).read_text()
        require(output.count(first) == output.count(last) == 1, "missing or ambiguous assumption boundaries")
        response = output.split(first, 1)[1].split(last, 1)[0].strip()
        # Importing opaque proofs can produce informational lines before the result.
        response = "\n".join(line for line in response.splitlines()
                             if not line.startswith("Fetching opaque proofs from disk for ")).strip()
        self.pin_artifact(query)
        return response, Path(log)

    def prepare(self):
        self.records["environment_before"] = self.environment()
        self.records["environment_strategy"] = (
            "Remove recorded import/plugin overrides in every Coq subprocess and Why3 Coq command; "
            "reject nonempty dynamic-linker overrides before any compilation. Parent environment is unchanged.")
        require(not self.directory.exists(), "Coq output directory must be fresh")
        self.directory.mkdir(parents=True)
        self.support.mkdir()
        self.helpers.mkdir()
        validate_spec_sources(self.root, self.manifest)
        helpers = self.manifest["helpers"]
        support = self.manifest.get("support", ["BuiltIn.v", "HighOrd.v", "int/Int.v",
                                                "int/Abs.v", "int/EuclideanDivision.v", "map/Map.v"])
        require(helpers and len({h["module"] for h in helpers}) == len(helpers), "empty or duplicate helper inventory")
        inputs = {self.coqc, self.coqtop, self.env_tool, self.base_config, self.driver}
        # Pin the installed Coq library/plugin superset, including all transitive
        # MathComp and word_ssrZ dependencies, rather than guessing loaded files.
        library = self.coqc.parent.parent / "lib"
        require(library.is_dir(), "missing Coq library tree")
        inputs.update(p for p in library.rglob("*") if p.is_file() and
                      (p.suffix in (".v", ".vo", ".vos", ".cmxs", ".cma", ".so") or p.name == "META"))
        inputs.update(p for p in self.driver.parent.rglob("*") if p.is_file())
        for item in helpers:
            source = self.source(item)
            require(item["module"] == source.stem and IDENTIFIER.fullmatch(item["module"]),
                    "helper module must match source filename")
            require(item.get("exports") and len(set(item["exports"])) == len(item["exports"]),
                    "empty or duplicate helper exports")
            coq_policy.check_authored(source.read_text())
            inputs.add(source)
        for relative in support:
            part = Path(relative)
            require(not part.is_absolute() and ".." not in part.parts and part.suffix == ".v", "invalid Why3 support path")
            source = self.why_source / part
            require(source.is_file() and not source.is_symlink(), "missing stock Why3 support")
            inputs.add(source)
        for spec in self.manifest.get("natives", {}).values():
            for script in spec["scripts"]:
                source = self.source(script)
                parts = split_script(source.read_text())
                authored_script(parts)
                inputs.add(source)
        self.records["inputs_before"] = snapshot(inputs)
        self.external.update(p for p in inputs if not p.is_relative_to(self.root))
        version = self.run("coq-tool-version", [self.coqc, "--version"], cwd=self.directory)
        require("version 8.20.1" in Path(version).read_text(), "unreviewed Coq version")
        for relative in support:
            local = self.support / relative
            local.parent.mkdir(parents=True, exist_ok=True)
            local.write_bytes((self.why_source / relative).read_bytes())
            self.run("coq-support-" + relative.replace("/", "-"),
                     [self.coqc, *self.coq_arguments(), local], cwd=self.directory)
            self.pin_artifact(local)
            self.pin_artifact(local.with_suffix(".vo"))
        for index, item in enumerate(helpers):
            source = self.source(item)
            local = self.helpers / source.name
            local.write_bytes(source.read_bytes())
            log = self.run("coq-helper-" + str(index).zfill(2) + "-" + source.stem,
                           [self.coqc, *self.coq_arguments(), local], cwd=self.directory)
            exports = []
            for theorem in item["exports"]:
                qualified = item["module"] + "." + theorem
                response, query_log = self.query_assumptions("coq-closed-" + qualified, qualified, module=item["module"])
                coq_policy.require_closed_assumptions(response)
                exports.append({"theorem": qualified, "log": str(query_log), "result": "CLOSED"})
            self.pin_artifact(local)
            self.pin_artifact(local.with_suffix(".vo"))
            self.records["helpers"].append({"source": str(source), "source_sha256": digest(source),
                "checked_copy": str(local), "vo_sha256": digest(local.with_suffix(".vo")),
                "log": str(log), "exports": exports, "result": "PASS"})
        self.write_config(self.config)
        self.pin_artifact(self.config)
        self.records["inputs_after_prepare"] = snapshot(inputs)
        require(self.records["inputs_before"] == self.records["inputs_after_prepare"],
                "Coq input changed during helper preparation")
        require(self.environment() == self.records["environment_before"], "Coq execution environment changed during preparation")
        self.records["config"] = str(self.config)
        self.records["prepared_artifacts"] = dict(self.artifacts)
        return self.records

    def native_argv(self, argv, config=None):
        argv = list(map(str, argv))
        config = str(config or self.config)
        if "-why3" in argv:
            index = argv.index("-why3")
            require(argv.count("-why3") == 1, "duplicate Why3 configuration")
            argv[index + 1] = config
        else:
            argv[2:2] = ["-why3", config]
        return argv

    def prepare_native(self, copied_main, label, spec, ec_argv_without_source):
        copied_main = Path(copied_main).resolve()
        require(copied_main.is_relative_to(self.output), "native main copy must be inside evidence")
        interactive = copied_main.parent / ".interactive"
        require(not interactive.exists(), "native interactive directory is not fresh")
        expected = {}
        argv = self.native_argv(ec_argv_without_source)
        for item in spec["scripts"]:
            require(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", item["name"]), "invalid native script name")
            script = interactive / (item["name"] + ".v")
            log = self.run(label + "-generate-" + item["name"], [*argv, copied_main], True, copied_main.parent)
            native_failure(log, copied_main, item["name"])
            require(script.is_file(), "native goal was not freshly generated")
            skeleton = script.read_text()
            fresh = split_script(skeleton)
            require(not fresh["prelude"], "fresh skeleton already has authored code")
            frozen = split_script(self.source(item).read_text())
            require(fresh["header"] == frozen["header"] and fresh["statement"] == frozen["statement"],
                    "fresh native context/goal differs from reviewed template")
            original = copied_main.parent / (item["name"] + ".generated.v")
            original.write_text(skeleton)
            self.pin_artifact(original)
            fresh.update(prelude=frozen["prelude"], body=frozen["body"])
            script.write_text(authored_script(fresh))
            expected[item["name"]] = fresh
        key = str(copied_main)
        require(key not in self.prepared, "native main prepared twice")
        self.prepared[key] = {"parts": expected, "label": label, "source_sha256": digest(copied_main),
                              "argv": argv, "spec": spec}
        return {"config": str(self.config), "command": [*argv, str(copied_main)],
                "scripts": [str(interactive / (name + ".v")) for name in expected]}

    def validate_native(self, copied_main, spec):
        copied_main = Path(copied_main).resolve()
        item = self.prepared[str(copied_main)]
        require(spec == item["spec"] and digest(copied_main) == item["source_sha256"], "native prepared input changed")
        records = []
        for name, expected in item["parts"].items():
            script = copied_main.parent / ".interactive" / (name + ".v")
            actual = split_script(script.read_text())
            require(actual == expected, "native regeneration changed reviewed header, goal, prelude or proof")
            guarded = copied_main.parent / (name + ".semantic.v")
            guarded.write_text(semantic_guarded_script(actual))
            response, log = self.query_assumptions(item["label"] + "-assumptions-" + name,
                                                  "sr_checked_goal", script=guarded)
            declared = set(re.findall(r"(?m)^\s*(?:Axiom|Parameter)\s+([A-Za-z_][A-Za-z_0-9']*)\s*:", expected["header"]))
            used = assumption_names(response)
            require(used <= declared, "native proof uses assumptions outside its fresh EC header: " + str(sorted(used - declared)))
            self.pin_artifact(script)
            self.pin_artifact(guarded)
            records.append({"script": str(script), "sha256": digest(script),
                "generated_header_sha256": hashlib.sha256(expected["header"].encode()).hexdigest(),
                "goal_sha256": hashlib.sha256(expected["statement"].encode()).hexdigest(),
                "assumptions": sorted(used), "assumptions_log": str(log),
                "semantic_guard": str(guarded), "semantic_guard_sha256": digest(guarded), "result": "PASS"})
        record = {"main": str(copied_main), "scripts": records, "result": "PASS"}
        self.records["native"].append(record)
        return record

    def negative_controls(self, copied_main, label, spec, ec_argv_without_source):
        copied_main = Path(copied_main).resolve()
        prepared = self.prepared[str(copied_main)]
        require(spec.get("changed_goal") is not None, "native changed-goal control is undeclared")
        original = copied_main.read_text()
        old, new = spec["changed_goal"]["old"], spec["changed_goal"]["new"]
        require(old != new and original.count(old) == 1, "changed-goal mutation must have one exact target")
        first = spec["scripts"][0]["name"]
        results = []
        for kind in ("wrong-proof", "changed-ec-goal", "missing-helper"):
            directory = self.directory / (label + "-" + kind)
            (directory / ".interactive").mkdir(parents=True)
            main = directory / copied_main.name
            main.write_text(original.replace(old, new) if kind == "changed-ec-goal" else original)
            for name, parts in prepared["parts"].items():
                mutated = dict(parts)
                if kind == "wrong-proof" and name == first:
                    mutated["body"] = 'fail 1 "SR invalid proof control".'
                (directory / ".interactive" / (name + ".v")).write_text(authored_script(mutated))
            config = self.config
            if kind == "missing-helper":
                config = directory / "missing-helper.conf"
                self.write_config(config, directory / "absent-helpers")
                self.pin_artifact(config)
            argv = self.native_argv(ec_argv_without_source, config)
            log = self.run(label + "-" + kind, [*argv, main], True, directory)
            critical = native_failure(log, main, first)
            target = directory / ".interactive" / (first + ".v")
            actual = split_script(target.read_text())
            if kind == "changed-ec-goal":
                require(actual["statement"] != prepared["parts"][first]["statement"], "changed EC goal was not regenerated")
                require(actual["body"] == prepared["parts"][first]["body"], "changed-goal control did not reuse the original proof")
            elif kind == "wrong-proof":
                require(actual["body"] == 'fail 1 "SR invalid proof control".', "wrong proof was not replayed")
                require(actual["statement"] == prepared["parts"][first]["statement"], "wrong-proof control changed the goal")
            helper_path = directory / "absent-helpers" if kind == "missing-helper" else self.helpers
            direct = self.run(label + "-" + kind + "-coq-diagnostic",
                              [self.coqtop, "-batch", *self.coq_arguments(helper_path), "-l", target], True, directory)
            diagnostic = Path(direct).read_text()
            require('File "' + str(target) + '"' in diagnostic and "Error:" in diagnostic,
                    "negative Coq diagnostic is not in its mutated script")
            if kind == "wrong-proof":
                require("SR invalid proof control" in diagnostic, "wrong-proof rejection has another cause")
            elif kind == "missing-helper":
                names = [h["module"] for h in self.manifest["helpers"]]
                require("Cannot find" in diagnostic and any(re.search(r"\b" + re.escape(n) + r"\b", diagnostic) for n in names),
                        "missing-helper rejection does not identify a declared helper import")
            self.pin_artifact(main)
            self.pin_artifact(target)
            results.append({"label": kind, "log": str(log), "critical_diagnostic": critical,
                            "coq_diagnostic": str(direct), "result": "EXPECTED_REJECTION"})
        try:
            coq_policy.check_authored(prepared["parts"][first]["body"] + "\nAdmitted.", proof_body=True)
        except ValueError:
            results.append({"label": "admitted-source-guard", "result": "EXPECTED_REJECTION"})
        else:
            raise ValueError("Admitted native proof accepted")
        self.records["negative_controls"].extend(results)
        return results

    def scope_control(self, copied_main):
        """An altered notation can prove a different proposition; reject it."""
        prepared = self.prepared[str(Path(copied_main).resolve())]
        header = next(iter(prepared["parts"].values()))["header"]
        prelude = "From Coq Require Import ZArith Lia."
        body = "intros x. nia."
        parts = {"header": header, "statement":
                 "Theorem goal : forall (x:Numbers.BinNums.Z), (0%Z <= (x*x)%Z)%Z.",
                 "prelude": prelude, "body": body}
        mutation = (prelude + '\nDefinition sr_fake_le (_ _:Z) : Prop := True.\n'
                    'Notation "x <= y" := (sr_fake_le x y) (at level 70, no associativity) : Z_scope.')
        records = []
        for guarded in (False, True):
            text = semantic_guarded_script(parts) if guarded else authored_script(parts)
            # This deliberately unsafe input is a fixed negative control, not
            # an authored-source acceptance path.
            text = text.replace(prelude, mutation).replace(body, "intros x. exact I.")
            path = self.directory / ("scope-mutation-guarded.v" if guarded else "scope-mutation-unguarded.v")
            path.write_text(text)
            log = self.run("coq-scope-" + ("semantic-rejection" if guarded else "wrong-goal-accepted"),
                           [self.coqtop, "-batch", *self.coq_arguments(), "-l", path], guarded, self.directory)
            if guarded:
                require("Error:" in Path(log).read_text() and "sr_fresh_exported_goal" in Path(log).read_text(),
                        "scope mutation did not fail at the semantic type gate")
            self.pin_artifact(path)
            records.append({"case": "scope-semantic-guard" if guarded else "scope-local-proof",
                            "result": "EXPECTED_REJECTION" if guarded else "PASS", "log": str(log)})
        self.records["scope_control"] = records
        return records

    def finalize(self):
        require(self.environment() == self.records["environment_before"], "Coq execution environment changed")
        after = snapshot(map(Path, self.records["inputs_before"]))
        require(after == self.records["inputs_before"], "Coq source/toolchain inputs changed")
        artifacts = snapshot(map(Path, self.artifacts))
        require(artifacts == self.artifacts, "prepared Coq artifact changed after validation")
        self.records.update(inputs_after=after, inputs_unchanged=True,
                            artifact_hashes=artifacts, artifacts_unchanged=True)
        return self.records
