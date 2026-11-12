#!/usr/bin/env python3
"""Strict EC-only replay of explicit history tables and simulator lookup refinement."""
import argparse
import ast
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time

sys.dont_write_bytecode = True
import policy


def timestamp():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    return policy.sha(path.read_bytes())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true", help="source controls only; never full PASS")
    parser.add_argument("--output", type=Path, help="new/empty evidence directory outside checkout")
    parser.add_argument("--prior-evidence-root", type=Path,
                        default=policy.ROOT.parent / "research-evidence")
    parser.add_argument("--draft", action="store_true", help="with --check-only, inspect moving sources without frozen proof claims")
    args = parser.parse_args()
    policy.require(not args.draft or args.check_only, "--draft requires --check-only")
    output = (args.output or Path(tempfile.mkdtemp(prefix="ntruplus-history-refinement-"))).resolve()
    policy.require(not output.is_relative_to(policy.ROOT), "evidence must be outside checkout")
    output.mkdir(parents=True, exist_ok=True)
    policy.require(not any(output.iterdir()), "output must be empty")
    report = {
        "status": "RUNNING", "started_at": timestamp(), "output": str(output),
        "platform": platform.platform(), "commands": [], "tools": {},
        "scope": "Explicit byte-comparison and list-based public-H history table/lookup refinement, conditional order agreement and declared resource counts; no full runtime or PPT theorem.",
        "proof_scope": "Only frozen new EC mains are freshly compiled. Imported EC and prior native Coq sources are hash-linked to the preceding reduction-cost full PASS; no native Coq proof is replayed here.",
        "call_scope": "Executable table/key/lookup bodies use explicit byte tests, list operations and actual backend/kernel calls. Builder ROH.get remains an ideal ROM call. Map operations are confined to specifications and proofs, not counted as implemented constant-time operations.",
        "not_claimed": ["all ROM tables implemented", "unconditional equality under arbitrary table permutation", "machine-cycle or wall-clock cost", "constant-time or cache behavior theorem", "complete reduction running-time theorem", "PPT from query counts alone", "actual ROM KeyGen losslessness", "new security assumption", "new native Coq replay", "native/C replay", "Safety/CT/SCT replay", "fixed SHAKE versus ROM equivalence"],
        "import_axiom_scope": "Imported proof contexts retain their reviewed scope. No new local axiom, abstract law, admit, native Coq invocation or checker-disable pragma is permitted.",
        "python": {"path": str(Path(sys.executable).resolve()), "version": sys.version,
                   "sha256": digest(Path(sys.executable))},
        "environment": {"EC_TIMEOUT": int(os.environ.get("EC_TIMEOUT", "60")),
                        "EC_JOBS": int(os.environ.get("EC_JOBS", "2")),
                        "OCAMLRUNPARAM": "o=20", "max_provers": 1,
                        "prover": "Z3", "Proofs": "check", "eco": False},
        "per_command_log_limit_bytes": 33554432, "prior_evidence": [],
        "proof_mains": [], "negative_proofs": [], "negative_preflight": []}
    summary = output / "summary.json"
    lock = threading.RLock()
    external = {Path(sys.executable).resolve(), Path(shutil.which("bash")).resolve()}

    def save():
        with lock:
            temporary = summary.with_suffix(".tmp")
            temporary.write_text(json.dumps(report, indent=2) + "\n")
            temporary.replace(summary)

    def run(label, argv, expected_failure=False, cwd=policy.ROOT):
        log = output / (label + ".log")
        record = {"label": label, "argv": [str(x) for x in argv], "cwd": str(cwd),
                  "started_at": timestamp(), "log": str(log), "expected_failure": expected_failure}
        with lock:
            report["commands"].append(record)
            save()
        start, emitted, overflow = time.monotonic(), 0, False
        with log.open("wb") as stream:
            process = subprocess.Popen(record["argv"], cwd=cwd, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, env={**os.environ, "OCAMLRUNPARAM": "o=20", "PYTHONDONTWRITEBYTECODE": "1"})
            while chunk := process.stdout.read1(65536):
                emitted += len(chunk)
                if emitted > report["per_command_log_limit_bytes"]:
                    overflow = True
                    process.kill()
                    stream.write(b"\nHARNESS: bounded log budget exceeded.\n")
                    break
                stream.write(chunk)
                stream.flush()
            process.stdout.close()
            process.wait()
        okay = not overflow and (process.returncode != 0 if expected_failure else process.returncode == 0)
        with lock:
            record.update(exit_code=process.returncode, log_limit_exceeded=overflow,
                seconds=round(time.monotonic() - start, 3), completed_at=timestamp(),
                log_sha256=digest(log), result="EXPECTED_REJECTION" if okay and expected_failure else "PASS" if okay else "FAIL")
            save()
        print(record["result"], label, record["seconds"], flush=True)
        if not okay:
            print("\n".join(log.read_text(errors="replace").replace("\r", "\n").splitlines()[-20:]))
            raise RuntimeError("command failed: " + label)
        return log

    def prior_evidence():
        imported = {str(p.relative_to(policy.ROOT)): digest(p) for p in policy.source_paths()
                    if p.suffix in (".ec", ".v") and not p.is_relative_to(policy.PROOF)}
        covered = set()
        pins = json.loads((policy.TEST / "prior-evidence-pins.json").read_text())
        policy.require(pins, "missing prior evidence pins")
        for relative, expected in pins.items():
            path = (args.prior_evidence_root.resolve() / relative).resolve()
            policy.require(path.is_file() and not path.is_symlink(), "missing prior evidence: " + relative)
            policy.require(digest(path) == expected, "prior evidence pin drift: " + relative)
            prior = json.loads(path.read_text())
            policy.require(prior.get("status") == "PASS", "prior evidence is not full PASS")
            for before, after, stable in (("source_hashes_before", "source_hashes_after", "inputs_unchanged"),
                    ("external_hashes_before", "external_hashes_after", "external_inputs_unchanged")):
                policy.require(prior.get(stable) is True and prior[before] == prior[after], "unstable prior audit")
            matched = []
            for name, value in imported.items():
                if name in prior["source_hashes_after"]:
                    policy.require(value == prior["source_hashes_after"][name], "import differs from prior PASS: " + name)
                    matched.append(name)
                    covered.add(name)
            report["prior_evidence"].append({"path": str(path), "sha256": expected, "status": "PASS",
                "matched_imported_ec": sum(name.endswith(".ec") for name in matched),
                "matched_imported_coq_sources": sum(name.endswith(".v") for name in matched), "scope": "hash-linked prior result; no fresh replay"})
            external.add(path)
        policy.require(covered == set(imported), "imported theory lacks prior provenance: " + str(sorted(set(imported) - covered)))
        report["prior_imported_source_hashes"] = imported

    def tool(name, default, version):
        path = Path(os.environ.get(name.upper(), default))
        policy.require(path.is_absolute() and path.is_file(), name + " must name an absolute executable")
        path = path.resolve()
        external.add(path)
        log = run("tool-" + name, [path, *version], cwd=policy.PROOF)
        report["tools"][name] = {"path": str(path), "sha256": digest(path), "version": log.read_text()}
        return path

    try:
        policy.require(report["environment"]["EC_JOBS"] in (1, 2), "EC_JOBS must be 1 or 2")
        policy.require(report["environment"]["EC_TIMEOUT"] == 60, "reviewed timeout must remain 60")
        report["source_hashes_before"] = policy.snapshot()
        data, pins = policy.check(args.draft)
        mains = data["mains"]
        report.update(pinned_sources=len(pins), declared_proof_mains=len(mains), declared_negative_proofs=len(mains),
                      manifest_sha256=None if args.draft else digest(policy.TEST / "proof-manifest.json"),
                      draft=args.draft, discovered_history_sources=len(list(policy.PROOF.glob("*.ec"))))
        for path in [policy.ENTRY, *policy.TEST.glob("*.py")]:
            ast.parse(path.read_text(), filename=str(path))
        report["python_ast"] = "PASS"
        run("shell-syntax", ["bash", "-n", policy.SCRIPT])
        log = run("source-policy", [sys.executable, policy.TEST / "policy.py", *(["--draft"] if args.draft else [])])
        report["source_policy"] = json.loads(log.read_text())
        log = run("mutation-gates", [sys.executable, policy.TEST / "test_controls.py"])
        report["mutation_controls"] = json.loads(log.read_text())
        log = run("finite-domain-diagnostics", [sys.executable, policy.TEST / "test_reference.py"])
        report["finite_domain_diagnostics"] = json.loads(log.read_text())
        # Prepare every positive/negative before launching any compiler. Each
        # negative deletes only its own final qed, retaining all trailing text.
        prepared = []
        for index, item in enumerate(mains):
            path = policy.BASE / item["source"]
            original = path.read_text()
            copies = {}
            for kind, transform in (("proof-inputs", policy.completed_proof_text), ("open-proof", policy.unfinished_proof_text)):
                copied = output / kind / str(index) / path.name
                copied.parent.mkdir(parents=True)
                copied.write_text(transform(original, item["sentinel"]))
                copies[kind] = (copied, digest(copied))
            prepared.append(copies)
            report["negative_preflight"].append({"source": str(path.relative_to(policy.ROOT)),
                "prepared_sha256": copies["open-proof"][1]})
        prior_evidence()
        if args.check_only:
            report["external_hashes_before"] = {str(p): digest(p) for p in sorted(external)}
            report["status"] = "DRAFT_SOURCE_CHECK_ONLY" if args.draft else "SOURCE_CHECK_ONLY"
        else:
            prefix = str(Path.home() / ".opam/cryptotools-2026.09")
            easycrypt = tool("easycrypt", prefix + "/bin/easycrypt", ["config"])
            why3 = tool("why3", prefix + "/bin/why3", ["--version"])
            config = report["tools"]["easycrypt"]["version"]
            match = re.search(r"why3 configuration file\s*\n\s*(\S+)", config)
            policy.require(match, "effective Why3 config absent")
            why_config = Path(match.group(1))
            external.add(why_config)
            blocks = re.split(r"(?m)^\[", why_config.read_text())
            paths = {m.group(1) for b in blocks if re.search(r'(?m)^name\s*=\s*"Z3"', b)
                     for m in re.finditer(r'(?m)^(?:path|command)\s*=\s*"([^" ]+)', b)}
            policy.require(len(paths) == 1, "effective Z3 executable ambiguous")
            z3 = Path(paths.pop()).resolve()
            external.add(z3)
            log = run("tool-z3", [z3, "--version"])
            report["tools"]["z3"] = {"path": str(z3), "sha256": digest(z3), "version": log.read_text()}
            for line in config.splitlines():
                name = line.strip()
                if name.startswith("/") and name.endswith(".conf") and Path(name).is_file():
                    external.add(Path(name))
                if "@/" in name:
                    directory = Path(name.split("@", 1)[1])
                    if directory.is_dir() and not directory.is_relative_to(policy.ROOT):
                        external.update(directory.rglob("*.ec"))
            for directory in (why3.parent.parent / "share/why3", easycrypt.parent.parent / "lib/easycrypt/config"):
                if directory.is_dir():
                    external.update(p for p in directory.rglob("*") if p.is_file())
            for name in ("why3server", "why3cpulimit"):
                path = why3.parent.parent / "lib/why3" / name
                policy.require(path.is_file(), "missing Why3 helper: " + name)
                external.add(path)
            report["external_hashes_before"] = {str(p): digest(p) for p in sorted(external)}
            for name, value in report["tools"].items():
                policy.require(report["external_hashes_before"][value["path"]] == value["sha256"], "tool changed during version query: " + name)
            report["prior_external_overlap"] = []
            for evidence in report["prior_evidence"]:
                prior = json.loads(Path(evidence["path"]).read_text())
                inherited = prior["external_hashes_after"]
                overlap = set(inherited) & set(report["external_hashes_before"])
                policy.require(overlap, "no shared prior toolchain inputs")
                for name, current in report["tools"].items():
                    policy.require(name in prior["tools"] and
                                   current["sha256"] == prior["tools"][name]["sha256"],
                                   "prover binary differs from prior full PASS: " + name)
                for path in overlap:
                    policy.require(inherited[path] == report["external_hashes_before"][path],
                                   "inherited toolchain/library changed since prior proof: " + path)
                report["prior_external_overlap"].append({"prior": evidence["path"],
                    "matched_paths": len(overlap), "matched_provers": sorted(report["tools"]), "result": "PASS"})
            includes = policy.include_arguments()[0]
            report["include_arguments"] = {policy.GROUP: includes}
            server = []
            if os.environ.get("WHY3_SERVER_SOCKET"):
                socket = Path(os.environ["WHY3_SERVER_SOCKET"])
                policy.require(socket.is_socket(), "invalid Why3 server socket")
                server = ["-server", str(socket)]

            def replay(index, item, negative=False):
                path = policy.BASE / item["source"]
                relative = str(path.relative_to(policy.ROOT))
                policy.require(digest(path) == pins[relative], "source changed before replay")
                copied, expected = prepared[index]["open-proof" if negative else "proof-inputs"]
                policy.require(digest(copied) == expected, "preflight copy changed")
                command = [easycrypt, "compile", "-no-eco", "-pragmas", "Proofs:check", "-p", "Z3",
                           "-timeout", "60", "-max-provers", "1", *server, *includes, copied]
                label = ("eof-open-proof-" if negative else "proof-") + str(index).zfill(2) + "-" + path.stem
                log = run(label, command, negative, path.parent)
                policy.require(digest(copied) == expected, "checked copy changed")
                result = {"source": relative, "source_sha256": pins[relative], "checked_copy": str(copied),
                    "checked_copy_sha256": expected, "sentinel_sha256": policy.sha(item["sentinel"].encode()),
                    "semantic_target": item["semantic_target"], "explicit_module_binders": item["module_binders"],
                    "log": str(log), "result": "EXPECTED_REJECTION" if negative else "PASS"}
                if negative:
                    result["critical_diagnostic"] = policy.check_negative_diagnostic(log.read_text(errors="replace"), copied)
                    result["rejection_scope"] = "own isolated main, not an imported theory"
                else:
                    result["sentinel_placement"] = "after last original proof closer, before trailing declarations or theory end"
                return result

            jobs = report["environment"]["EC_JOBS"]
            for layer in policy.dependency_layers(mains):
                done = policy.run_phase(lambda _i, entry: replay(*entry), layer, jobs)
                report["proof_mains"].extend(done)
                save()
            report["negative_proofs"] = policy.run_phase(lambda i, item: replay(i, item, True), mains, jobs)
            policy.require(len(report["proof_mains"]) == len(mains) == len(report["negative_proofs"]), "proof replay inventory mismatch")
            report.update(status="PASS", new_authored_mains=len(mains),
                new_lemmas=sum(len(re.findall(r"(?m)^\s*(?:local\s+)?lemma\s+", policy.without_comments((policy.BASE / item["source"]).read_text()))) for item in mains))
    except Exception as error:
        report.update(status="FAIL", error_type=type(error).__name__, error=str(error))
    finally:
        try:
            if "source_hashes_before" in report:
                report["source_hashes_after"] = policy.snapshot()
                report["inputs_unchanged"] = report["source_hashes_before"] == report["source_hashes_after"]
                if not report["inputs_unchanged"]:
                    report.update(status="FAIL", error="source inputs changed during replay")
            if "external_hashes_before" in report:
                report["external_hashes_after"] = {str(p): digest(p) for p in sorted(external)}
                report["external_inputs_unchanged"] = report["external_hashes_before"] == report["external_hashes_after"]
                if not report["external_inputs_unchanged"]:
                    report.update(status="FAIL", error="external inputs changed during replay")
        except (OSError, ValueError) as error:
            report.update(status="FAIL", inputs_unchanged=False, error="final input audit failed: " + str(error))
        report["completed_at"] = timestamp()
        save()
    print(report["status"], summary)
    return 0 if report["status"] in ("PASS", "SOURCE_CHECK_ONLY", "DRAFT_SOURCE_CHECK_ONLY") else 1


if __name__ == "__main__":
    sys.exit(main())
