#!/usr/bin/env python3
"""Replay the guard proofs and exact-splice native API tests with retained evidence."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import shlex
import shutil
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
import check_decap_guard as policy
import prepare_reference as reference
import eof_sentinels
import verify_checked as checked_driver

ROOT = policy.ROOT
TEST = policy.TEST
PROOF = ROOT / "ntruplus/proof/768/ref/decap_guard"
EXTRACTED = PROOF / "extracted"
EXTRACTED_MAIN = "NTRUPlus768DecapGuard.ec"
SPEC = "NTRUPlus768DecapGuardSpec.ec"
MAIN = "NTRUPlus768DecapGuardProof.ec"
CALLER = "NTRUPlus768DecapGuardCaller.ec"
CANONICAL = checked_driver.CANONICAL
ENCAP_SPEC = ROOT / "ntruplus/proof/768/ref/encap_guard/NTRUPlus768EncapGuardSpec.ec"
ENCAP_SPEC_PIN = "030837a27ec5aad6b680c960e0dc44962ab2ceaac63bd8b830e679b6e545b7a6"
ENCAP_SPEC_EOF = r"""
lemma __decap_reused_encap_spec_eof pk : encap_status pk = W32.zero <=> encap_key_canonical pk.
proof. exact (encap_status_zero pk). qed.
"""
GENERATED_EOF = checked_driver.GENERATED_EOF


def timestamp():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def include_arguments():
    arguments = []
    directories = []
    for raw in (PROOF / "easycrypt.project").read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith(("#", "[")):
            continue
        key, separator, value = line.partition("=")
        key, value = key.strip(), value.strip()
        policy.require(separator and key in ("rdirs", "idirs", "timeout"), "unsupported project setting")
        if key == "timeout":
            continue
        namespace, colon, directory = value.partition(":")
        if not colon:
            namespace, directory = "", value
        path = (PROOF / directory).resolve()
        policy.require(path.is_dir(), "missing EasyCrypt include directory: " + str(path))
        directories.append(path)
        arguments += ["-R" if key == "rdirs" else "-I", namespace + ":" + str(path) if colon else str(path)]
    return arguments, directories


def source_snapshot(directories):
    paths = {policy.SOURCE, policy.checked.SOURCE, PROOF / "Makefile", PROOF / "easycrypt.project",
             ROOT / "scripts/verify-ntruplus768-decap-guard.sh",
             TEST.parent / "toolchain/check_model_compatibility.py"}
    paths.update(p for p in TEST.rglob("*") if p.is_file())
    paths.update(TEST.parent / "poly_frombytes_checked" / name for name in
                 ("check_poly_frombytes_checked.py", "verify_checked.py"))
    for directory in directories:
        paths.update(directory.rglob("*.ec"))
    return {str(path.relative_to(ROOT)): digest(path) for path in sorted(paths) if path.is_file()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-only", action="store_true", help="run native/source/extraction/safety/policy checks only; never reports full proof PASS")
    parser.add_argument("--output", type=Path, help="new or empty evidence directory; default keeps a new /tmp directory")
    args = parser.parse_args()
    output = args.output or Path(tempfile.mkdtemp(prefix="ntruplus-decap-guard-tests-"))
    output = output.resolve()
    policy.require(not output.is_relative_to(ROOT), "keep verification output outside the source checkout")
    output.mkdir(parents=True, exist_ok=True)
    policy.require(not any(output.iterdir()), "output directory must be empty: " + str(output))
    report = {"status": "RUNNING", "started_at": timestamp(), "output": str(output),
              "scope": "Standalone Decaps entry guard and mixed official-C/Jasmin API regression. Extracted-Jasmin guard and abstract caller theorems. No C-AST proof, full-Jasmin API/KEM, complete implementation refinement, or IND-CCA proof.",
              "commands": [], "tools": {}, "reference_commit": "3991b2ae08d6f0008d37e41b8aceaaab27b4ec89",
              "buffer_contract": "Six disjoint buffers: c/f/h each 1536 bytes u16-aligned writable, ss32 writable, ct1152 and skpoly2304 initialized readable. Official full secret key is2336 bytes; guard reads only its polynomial prefix. Short-circuited polynomial outputs and canonical ss remain unchanged. Native tests use initialized outputs to observe preservation; safety tests establish no initial-output read under their model.",
              "proof_scope": "Nine fresh extracted guard mains, existing canonical decoder and checked-decoder proof mains, reused EncapGuardSpec, and guard Spec/Proof/Caller. Imported baseline theories are hashed as dependencies; their prior suites are not all replayed. No C-AST theorem or full-Jasmin API/IND-CCA claim.",
              "platform": platform.platform(),
              "python": {"path": sys.executable, "sha256": digest(Path(sys.executable)), "version": sys.version},
              "environment": {"EC_TIMEOUT": os.environ.get("EC_TIMEOUT", "30"), "EC_MAX_PROVERS": "1", "prover": "Z3", "ct_sct_phase": "after inline", "ct_policy": "ciphertext public architecturally, transient speculatively; key bytes secret; only f/h canonicality predicates declassified. Canonical-key inputs make both predicates zero; malformed-key functional tests do not establish unconditional secret-key CT/SCT"}}
    summary = output / "summary.json"

    def save():
        pending = summary.with_suffix(".tmp")
        pending.write_text(json.dumps(report, indent=2) + "\n")
        pending.replace(summary)

    def run(label, argv, *, cwd=ROOT, expected_failure=False, overrides=None):
        log = output / (label + ".log")
        record = {"label": label, "argv": [str(x) for x in argv], "cwd": str(cwd),
                  "environment_overrides": overrides or {}, "started_at": timestamp(), "log": str(log)}
        report["commands"].append(record)
        save()
        start = time.monotonic()
        with log.open("w") as stream:
            process = subprocess.run(record["argv"], cwd=cwd, env={**os.environ, **(overrides or {})},
                                     stdout=stream, stderr=subprocess.STDOUT)
        record.update(exit_code=process.returncode, seconds=round(time.monotonic() - start, 3),
                      completed_at=timestamp(), log_sha256=digest(log), expected_failure=expected_failure)
        okay = process.returncode != 0 if expected_failure else process.returncode == 0
        record["result"] = "EXPECTED_REJECTION" if okay and expected_failure else "PASS" if okay else "FAIL"
        save()
        print(record["result"], label, record["seconds"], flush=True)
        if not okay:
            print("\n".join(log.read_text(errors="replace").replace("\r", "\n").splitlines()[-25:]))
            raise RuntimeError("command failed: " + label)
        return log

    def tool(variable, name, version):
        command = shlex.split(os.environ.get(variable, name))
        path = shutil.which(command[0])
        policy.require(path, "missing tool: " + command[0])
        command[0] = str(Path(path).resolve())
        log = run("tool-" + name, command + version)
        report["tools"][name] = {"environment_variable": variable,
                                 "argv_prefix": command, "binary_sha256": digest(Path(command[0])),
                                 "version_log": str(log), "version_output": log.read_text(errors="replace")}
        return command

    save()
    directories = []
    try:
        include, directories = include_arguments()
        report["source_hashes_before"] = source_snapshot(directories)
        policy.check()
        if not args.native_only:
            policy.require({p.name for p in PROOF.glob("*.ec")} == {SPEC, MAIN, CALLER}, "unexpected guard proof inventory")
            policy.require(set(eof_sentinels.PROOF_PINS) == {SPEC, MAIN, CALLER}, "incomplete reviewed proof pins")
            proof_pins = {**checked_driver.PROOF_PINS, ENCAP_SPEC: ENCAP_SPEC_PIN,
                          **{PROOF / name: digest_value for name,digest_value in eof_sentinels.PROOF_PINS.items()}}
            for path, expected in proof_pins.items():
                policy.require(digest(path) == expected, "reviewed proof source pin drift: " + str(path))
                policy.check_proof_text(path.read_text())
        run("source-model-compatibility", [sys.executable, ROOT / "tests/ntruplus768/toolchain/check_model_compatibility.py", "--source-only"])
        run("source-policy-check", [sys.executable, TEST / "check_decap_guard.py"])
        run("mutation-gate-selfcheck", [sys.executable, TEST / "test_gates.py"])
        jasmin = tool("JASMINC", "jasminc", ["-version"])
        extractor = tool("JASMIN2EC", "jasmin2ec", ["--version"])
        safety = tool("JASMIN_CHECKSAFETY", "jasmin-checksafety", ["--version"])
        # JASMINCT is the repository convention; retain the underscored alias.
        ct = tool("JASMINCT" if "JASMINCT" in os.environ else "JASMIN_CT", "jasmin-ct", ["--version"])
        easycrypt = tool("EASYCRYPT", "easycrypt", ["config"]) if not args.native_only else []
        if not args.native_only:
            tool("WHY3", "why3", ["--version"])
        cc = tool("CC", "cc", ["--version"])
        run("compiler-target", cc + ["-dumpmachine"])
        fresh = output / "fresh-extraction"
        fresh.mkdir()
        run("fresh-extraction", extractor + ["--array-model=old", "--arch=x86-64", "--cc=linux",
            "--output-array=" + str(fresh), "-o", str(fresh / EXTRACTED_MAIN), "-f", policy.SLICE, str(policy.SOURCE)])
        report["fresh_extraction"] = {"result": "PASS", "files": policy.check_extraction(EXTRACTED, fresh),
                                      "comparison": "complete file set and raw bytes; no whitespace normalization"}
        checked_fresh = output / "checked-decoder-fresh-extraction"
        checked_fresh.mkdir()
        run("reused-decoder-fresh-extraction", extractor + ["--array-model=old", "--arch=x86-64", "--cc=linux",
            "--output-array=" + str(checked_fresh), "-o", str(checked_fresh / checked_driver.EXTRACTED_MAIN),
            "-f", policy.checked.SLICE, str(policy.checked.SOURCE)])
        report["reused_decoder_fresh_extraction"] = {"result":"PASS",
            "files": policy.checked.check_extraction(checked_driver.EXTRACTED, checked_fresh)}
        run("compile", jasmin + ["-arch", "x86-64", "-call-conv", "linux", "-system", "linux",
            "-slice", policy.SLICE, "-o", str(output / "decap_guard.s"), str(policy.SOURCE)])
        safety_log = run("safety", safety + ["--arch=x86-64", "--call-conv=linux", "--slice=" + policy.SLICE, str(policy.SOURCE)])
        policy.require("No Safety Violation" in safety_log.read_text(), "missing positive safety diagnostic")
        run("ct", ct + ["--after=inline", "--slice=" + policy.SLICE, str(policy.SOURCE)])
        run("sct", ct + ["--sct", "--after=inline", "--slice=" + policy.SLICE, str(policy.SOURCE)])
        # Demonstrate that the two disclosed key-validity predicates are
        # necessary for this policy, and cannot be silently omitted from it.
        strict_dir = output / "strict-policy-control"
        strict_dir.mkdir()
        strict = strict_dir / policy.SOURCE.name
        source = policy.SOURCE.read_text()
        policy.require(source.count("() = #declassify(status);") == 2,
                       "strict policy control requires exactly two key-validity disclosures")
        strict.write_text(source.replace("() = #declassify(status);", ""))
        shutil.copyfile(policy.checked.SOURCE, strict_dir / policy.checked.SOURCE.name)
        report["strict_policy_control"] = {"source_sha256": digest(strict),
            "meaning": "Without the declared canonicality-bit disclosures, both CT/SCT checks must reject the secret status branch. This is not a whole-key-public policy."}
        for checker, flags in (("ct", []), ("sct", ["--sct"])):
            log = run("strict-policy-" + checker + "-rejection", ct + flags +
                      ["--after=inline", "--slice=" + policy.SLICE, str(strict)], expected_failure=True)
            diagnostic = log.read_text(errors="replace")
            policy.require("constant type checker" in diagnostic and "secret" in diagnostic and "public" in diagnostic,
                           "strict policy check failed for a reason other than secret-to-public flow")
            report["strict_policy_control"][checker] = "EXPECTED_REJECTION"
        generated = output / "generated-c"
        run("prepare-reference-splice", [sys.executable, TEST / "prepare_reference.py", "--output", generated])
        report["reference_splice"] = json.loads((generated / "splice.json").read_text())
        native_sources = [TEST / "decap_guard_test.c", TEST / "trace.c",
                          generated / "official_kem.c", generated / "mixed_kem.c"]
        native_sources += [TEST / "reference" / name for name in
                           ("poly.c", "ntt.c", "symmetric.c", "fips202/fips202.c", "kat/rng.c", "kat/aes.c")]
        native_sources += [output / "decap_guard.s"]
        report["native_compiled_sources"] = {str(path): digest(path) for path in native_sources}
        report["differential"] = {}
        report["native_test_scope"] = {
            "rng": "Exact official KAT AES-CTR-DRBG replaces production randombytes for controlled full-KeyGen/Encaps replay; Decaps is checked to make no RNG call.",
            "instrumentation": "Namespace macros and trace wrappers call unchanged official dependencies. Official decoder short-circuit counts and C/mixed continuation order are checked. The Jasmin guard is one native trace event; its internal short-circuit output behavior is checked by standalone output comparisons and the extracted-code proof. Invalid inputs never invoke arithmetic, hash, SOTP, or serialization continuation. Cleanup and verify stay exact original C.",
            "warnings": "Authored native code compiles with -Werror. Exact upstream KAT RNG/AES retain upstream warnings; no source edits or sanitizer exclusions.",
            "finite_scope": "Finite native regressions and UBSan; not a formal C-to-Jasmin equivalence theorem."}
        for variant in ("normal", "ubsan"):
            objects = []
            flags = ["-std=c11", "-O2", "-g", "-Wall", "-Wextra", "-Wpedantic", "-ffunction-sections", "-fdata-sections",
                     "-I" + str(TEST), "-I" + str(TEST / "reference")]
            sanitizer = ["-O1", "-fsanitize=undefined", "-fno-sanitize-recover=undefined", "-fno-omit-frame-pointer"] if variant == "ubsan" else []
            directory = output / ("native-" + variant)
            directory.mkdir()
            for index, path in enumerate(native_sources):
                obj = directory / (str(index) + ".o")
                extra = ["-Werror"] if path.parent == TEST else []
                if path.name == "rng.c":
                    extra += ["-Drandombytes=kat_randombytes", "-include", "stdlib.h"]
                run("native-" + variant + "-compile-" + str(index),
                    cc + flags + sanitizer + extra + ["-c", str(path), "-o", str(obj)])
                objects.append(str(obj))
            binary = directory / "decap-guard-test"
            run("native-" + variant + "-link", cc + objects + sanitizer +
                ["-Wl,--gc-sections", "-Wl,-z,noexecstack", "-o", str(binary)])
            log = run("native-" + variant + "-run", [binary, TEST / "reference/PQCkemKAT_2336.rsp"],
                      overrides={"UBSAN_OPTIONS": "halt_on_error=1:print_stacktrace=1"} if variant == "ubsan" else {})
            counts = json.loads(log.read_text())
            expected = {"status":"PASS", "guard_cases":87851,"guard_success_cases":68414,
                        "ct_rejection_cases":6489,"f_rejection_cases":6477,"h_rejection_cases":6471,
                        "kat_api_runs":200,"malformed_api_pairs":4622,
                        "canonical_api_pairs":356,"fresh_api_pairs":32}
            policy.require(counts.get("guard_success_cases", 0) > 0 and
                           all(counts.get(k, 0) > 0 for k in ("ct_rejection_cases", "f_rejection_cases", "h_rejection_cases")),
                           "missing a standalone guard branch")
            policy.require(all(counts.get(key) == value for key,value in expected.items()), "incomplete native coverage")
            counts["binary_sha256"] = digest(binary)
            report["differential"][variant] = counts
        if not args.native_only:
            timeout = str(int(report["environment"]["EC_TIMEOUT"]))
            policy.require(int(timeout) > 0, "EC_TIMEOUT must be positive")
            server = []
            if os.environ.get("WHY3_SERVER_SOCKET"):
                socket = Path(os.environ["WHY3_SERVER_SOCKET"])
                policy.require(socket.is_socket(), "WHY3_SERVER_SOCKET is not a socket")
                server = ["-server", str(socket)]

            def proof_command(source):
                return easycrypt + ["compile", "-no-eco", "-pragmas", "Proofs:check", "-p", "Z3",
                    "-timeout", timeout, "-max-provers", "1", *server, *include, str(source)]

            targets = [(path, GENERATED_EOF) for path in sorted(EXTRACTED.glob("*.ec"))]
            targets += [(ENCAP_SPEC, ENCAP_SPEC_EOF), (CANONICAL, checked_driver.CANONICAL_EOF),
                        (checked_driver.PROOF / checked_driver.WORDS, checked_driver.WORDS_EOF),
                        (checked_driver.PROOF / checked_driver.MAIN, checked_driver.MAIN_EOF)]
            targets += [(PROOF / name, eof_sentinels.SENTINELS[name]) for name in (SPEC, MAIN, CALLER)]
            report["proof_mains"] = []
            main_source = None
            for index, (path, sentinel) in enumerate(targets):
                source_bytes = path.read_bytes()
                source_sha256 = policy.sha(source_bytes)
                relative = str(path.relative_to(ROOT))
                policy.require(source_sha256 == report["source_hashes_before"][relative],
                               "proof source changed before snapshot: " + relative)
                if path == PROOF / MAIN:
                    main_source = source_bytes.decode()
                directory = output / "proof-inputs" / str(index)
                directory.mkdir(parents=True)
                copy = directory / path.name
                copy.write_bytes(source_bytes + sentinel.encode())
                checked_copy_sha256 = digest(copy)
                log = run("proof-" + path.stem, proof_command(copy), cwd=PROOF)
                policy.require(digest(copy) == checked_copy_sha256, "checked proof copy changed during compilation")
                report["proof_mains"].append({"source": relative, "source_sha256": source_sha256,
                    "checked_copy": str(copy), "checked_copy_sha256": checked_copy_sha256,
                    "checked_copy_unchanged": True, "sentinel_sha256": policy.sha(sentinel.encode()),
                    "result": "PASS", "log": str(log), "log_sha256": digest(log)})
            # The same semantic endpoint guard must reject a proof that reaches
            # EOF without closing its final proof; the live source is never edited.
            policy.require(main_source is not None, "missing main proof snapshot")
            original = main_source
            cut = original.rfind("qed.")
            policy.require(cut >= 0 and not original[cut + 4:].strip(), "unexpected final proof structure")
            negative = output / "open-proof" / MAIN
            negative.parent.mkdir()
            negative.write_text(original[:cut] + eof_sentinels.SENTINELS[MAIN])
            rejection = run("eof-open-proof-rejection", proof_command(negative), cwd=PROOF, expected_failure=True)
            policy.require("inside a proof script" in rejection.read_text(errors="replace"),
                           "EOF regression failed for a reason other than the pending proof")
        report["native_compiled_sources_after"] = {str(path): digest(path) for path in native_sources}
        policy.require(report["native_compiled_sources"] == report["native_compiled_sources_after"],
                       "native compilation inputs changed during verification")
        report["status"] = "NATIVE_PASS" if args.native_only else "PASS"
        report["proofs_replayed"] = not args.native_only
    except Exception as error:
        report.update(status="FAIL", error_type=type(error).__name__, error=str(error))
    finally:
        if directories and "source_hashes_before" in report:
            try:
                report["source_hashes_after"] = source_snapshot(directories)
                report["inputs_unchanged"] = report["source_hashes_before"] == report["source_hashes_after"]
                if not report["inputs_unchanged"]:
                    report.update(status="FAIL", error="source inputs changed during verification")
            except (OSError, ValueError) as error:
                report.update(status="FAIL", inputs_unchanged=False, error="final source snapshot failed: " + str(error))
        report["completed_at"] = timestamp()
        save()
    print("RESULT", report["status"], str(summary), flush=True)
    return 0 if report["status"] in ("PASS", "NATIVE_PASS") else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError) as error:
        print("FAIL:", error, file=sys.stderr)
        sys.exit(1)
