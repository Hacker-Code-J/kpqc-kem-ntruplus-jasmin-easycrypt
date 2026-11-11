#!/usr/bin/env python3
"""Replay the standalone checked-decoder artifact and retain exact run evidence."""
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
import check_poly_frombytes_checked as policy

ROOT = policy.ROOT
TEST = policy.TEST
PROOF = ROOT / "ntruplus/proof/768/ref/poly_frombytes_checked"
EXTRACTED = PROOF / "extracted"
EXTRACTED_MAIN = "NTRUPlus768PolyFromBytesChecked.ec"
WORDS = "NTRUPlus768PolyFromBytesCheckedWords.ec"
MAIN = "NTRUPlus768PolyFromBytesCheckedProof.ec"
CANONICAL = ROOT / "ntruplus/proof/768/ref/poly_frombytes/NTRUPlus768CanonicalDecoder.ec"
PROOF_PINS = {
    CANONICAL: "4f84589164127dc62fec2c4755e97d05b6bc61b24af97c7bc01df0fc83006457",
    PROOF / WORDS: "89f56166b71591d2bf64c609a49839a00a52021b6aae1202063cbdae324fc02b",
    PROOF / MAIN: "64b33218f20317081fc3ed42cdebf9711f33be02d13b1b4a7dfec731298f5bf8",
}
MAIN_EOF = r"""
lemma __checked_decoder_eof_canonical (rp0 : W16.t Array768.t) (ap0 : W8.t Array1152.t) :
  phoare [NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes :
    rp = rp0 /\ ap = ap0 ==>
    res.`1 = decoded_poly ap0 /\
    (W32.to_uint res.`2 = 0 <=> forall j, 0 <= j < 768 => W16.to_uint res.`1.[j] < 3457) /\
    (W32.to_uint res.`2 = 0 \/ W32.to_uint res.`2 = 1)] = 1%r.
proof. exact (poly_frombytes_checked_canonical rp0 ap0). qed.
lemma __checked_decoder_eof_roundtrip (rp0 p : W16.t Array768.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange p =>
  phoare [NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes :
    rp = rp0 /\ ap = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec p ==>
    res.`1 = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_canonical_spec p /\ res.`2 = W32.zero] = 1%r.
proof. exact (poly_frombytes_checked_tobytes_roundtrip rp0 p). qed.
"""
WORDS_EOF = r"""
lemma __checked_words_eof (b0 b1 : W8.t) :
  checked_even_word b0 b1 = W16.of_int (W8.to_uint b0 + 256 * (W8.to_uint b1 %% 16)).
proof. exact (checked_even_wordE b0 b1). qed.
"""
CANONICAL_EOF = r"""
lemma __checked_canonical_eof (a : W8.t Array1152.t) :
  canonical_return a = 0 \/ canonical_return a = 1.
proof. exact (canonical_return_binary a). qed.
"""
GENERATED_EOF = "\nlemma __checked_extraction_eof : true.\nproof. trivial. qed.\n"


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
    paths = {policy.SOURCE, TEST / "reference-manifest.json", TEST / "Makefile",
             TEST / "poly_frombytes_checked_diff.c", TEST / "check_poly_frombytes_checked.py",
             TEST / "test_extraction_gate.py",
             Path(__file__), PROOF / "Makefile", PROOF / "easycrypt.project",
             ROOT / "scripts/verify-ntruplus768-poly-frombytes-checked.sh"}
    paths.update((TEST / "reference").iterdir())
    for directory in directories:
        paths.update(directory.rglob("*.ec"))
    return {str(path.relative_to(ROOT)): digest(path) for path in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="new or empty evidence directory; default keeps a new /tmp directory")
    args = parser.parse_args()
    output = args.output or Path(tempfile.mkdtemp(prefix="ntruplus768-frombytes-checked-"))
    output = output.resolve()
    policy.require(not output.is_relative_to(ROOT), "keep verification output outside the source checkout")
    output.mkdir(parents=True, exist_ok=True)
    policy.require(not any(output.iterdir()), "output directory must be empty: " + str(output))
    report = {"status": "RUNNING", "started_at": timestamp(), "output": str(output),
              "scope": "Standalone official-3991b2a checked poly_frombytes versus compiled Jasmin, plus extracted-Jasmin functional/total/canonical/roundtrip theorems. No C-AST equivalence, full API/KEM or IND-CCA claim.",
              "commands": [], "tools": {}, "reference_commit": "3991b2ae08d6f0008d37e41b8aceaaab27b4ec89",
              "buffer_contract": "Disjoint 1536-byte u16-aligned writable output and 1152 initialized input bytes.",
              "proof_scope": "Five fresh extracted mains, the existing canonical-decoder main, and both new checked-decoder mains. Imported baseline theories are hashed as dependencies; their entire previous proof suite is not rerun here.",
              "platform": platform.platform(), "environment": {"EC_TIMEOUT": os.environ.get("EC_TIMEOUT", "30"), "EC_MAX_PROVERS": "1", "prover": "Z3"}}
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
        policy.check_reference()
        policy.check_jasmin()
        policy.selfcheck()
        policy.require({p.name for p in PROOF.glob("*.ec")} == {WORDS, MAIN}, "unexpected local proof inventory")
        for path, expected in PROOF_PINS.items():
            policy.require(digest(path) == expected, "reviewed proof source pin drift: " + str(path))
            policy.check_proof_text(path.read_text())
        run("source-model-compatibility", [sys.executable, ROOT / "tests/ntruplus768/toolchain/check_model_compatibility.py", "--source-only"])
        run("source-policy-selfcheck", [sys.executable, TEST / "check_poly_frombytes_checked.py", "--self-check"])
        run("extraction-gate-selfcheck", [sys.executable, TEST / "test_extraction_gate.py"])
        jasmin = tool("JASMINC", "jasminc", ["-version"])
        extractor = tool("JASMIN2EC", "jasmin2ec", ["--version"])
        safety = tool("JASMIN_CHECKSAFETY", "jasmin-checksafety", ["--version"])
        # JASMINCT is the repository convention; retain the underscored alias.
        ct = tool("JASMINCT" if "JASMINCT" in os.environ else "JASMIN_CT", "jasmin-ct", ["--version"])
        easycrypt = tool("EASYCRYPT", "easycrypt", ["config"])
        tool("WHY3", "why3", ["--version"])
        cc = tool("CC", "cc", ["--version"])
        run("compiler-target", cc + ["-dumpmachine"])
        fresh = output / "fresh-extraction"
        fresh.mkdir()
        run("fresh-extraction", extractor + ["--array-model=old", "--arch=x86-64", "--cc=linux",
            "--output-array=" + str(fresh), "-o", str(fresh / EXTRACTED_MAIN), "-f", policy.SLICE, str(policy.SOURCE)])
        report["fresh_extraction"] = {"result": "PASS", "files": policy.check_extraction(EXTRACTED, fresh),
                                      "comparison": "complete file set and raw bytes; no whitespace normalization"}
        run("compile", jasmin + ["-arch", "x86-64", "-call-conv", "linux", "-system", "linux",
            "-slice", policy.SLICE, "-o", str(output / "poly_frombytes.s"), str(policy.SOURCE)])
        safety_log = run("safety", safety + ["--arch=x86-64", "--call-conv=linux", "--slice=" + policy.SLICE, str(policy.SOURCE)])
        policy.require("No Safety Violation" in safety_log.read_text(), "missing positive safety diagnostic")
        run("ct", ct + ["--slice=" + policy.SLICE, str(policy.SOURCE)])
        run("sct", ct + ["--sct", "--slice=" + policy.SLICE, str(policy.SOURCE)])
        run("differential-build", ["make", "-B", "-j1", "-C", str(TEST),
            "OUTDIR=" + str(output / "tests"), "JASMINC=" + shlex.join(jasmin), "CC=" + shlex.join(cc),
            "build-normal", "build-ubsan"])
        report["differential"] = {}
        for variant in ("normal", "ubsan"):
            binary = output / "tests" / ("checked-" + variant)
            log = run("differential-" + variant, [binary],
                      overrides={"UBSAN_OPTIONS": "halt_on_error=1:print_stacktrace=1"} if variant == "ubsan" else {})
            counts = json.loads(log.read_text())
            policy.require(counts["status"] == "PASS" and counts["cases"] == 36102, "incomplete differential coverage")
            policy.require(counts["success_cases"] == 26562 and counts["failure_cases"] == 9540, "status coverage changed")
            counts["binary_sha256"] = digest(binary)
            report["differential"][variant] = counts
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
        targets += [(CANONICAL, CANONICAL_EOF), (PROOF / WORDS, WORDS_EOF), (PROOF / MAIN, MAIN_EOF)]
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
        # The same canonical/roundtrip guard must reject a proof that reaches
        # EOF without closing its final proof; the live source is never edited.
        policy.require(main_source is not None, "missing main proof snapshot")
        original = main_source
        cut = original.rfind("qed.")
        policy.require(cut >= 0 and not original[cut + 4:].strip(), "unexpected final proof structure")
        negative = output / "open-proof" / MAIN
        negative.parent.mkdir()
        negative.write_text(original[:cut] + MAIN_EOF)
        rejection = run("eof-open-proof-rejection", proof_command(negative), cwd=PROOF, expected_failure=True)
        policy.require("inside a proof script" in rejection.read_text(errors="replace"),
                       "EOF regression failed for a reason other than the pending proof")
        report["status"] = "PASS"
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
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError) as error:
        print("FAIL:", error, file=sys.stderr)
        sys.exit(1)
