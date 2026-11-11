#!/usr/bin/env python3
"""Check that legacy Formosa imports use the installed Jasmin x86 model."""

import argparse
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
SHIM = ROOT / "ntruplus/proof/compat/jasmin"
PROBE = """from Jasmin require import JModel.
op legacy_to_uint = W16.to_uint.
require import W16extra.
from Jasmin require import JModel_x86.
lemma legacy_name_same_word (x : W16.t) : legacy_to_uint x = W16.to_uint x.
proof. by rewrite /legacy_to_uint. qed.
"""


EXPORT = "from Jasmin require export JModel_x86."


def check_source(directory):
    files = sorted(p.relative_to(directory) for p in directory.rglob("*.ec"))
    if files != [Path("JModel.ec")]:
        raise ValueError("compatibility directory must only define JModel.ec")
    source = (directory / "JModel.ec").read_text()
    # EasyCrypt comments can nest. Treat comments as whitespace; reject an
    # unmatched delimiter instead of allowing it to hide additional commands.
    import re
    depth = 0
    code = []
    for token in re.split(r"(\(\*|\*\))", source):
        if token == "(*":
            depth += 1
            code.append(" ")
        elif token == "*)":
            if depth == 0:
                raise ValueError("unmatched comment terminator in JModel.ec")
            depth -= 1
        elif depth == 0:
            code.append(token)
    if depth:
        raise ValueError("unclosed comment in JModel.ec")
    if " ".join("".join(code).split()) != EXPORT:
        raise ValueError("JModel.ec must contain only: " + EXPORT)


def source_selftest():
    mutations = [
        EXPORT + "\naxiom forged : false.",
        EXPORT + "\nlemma forged : false. proof. admit. qed.",
        "pragma +implicits.\n" + EXPORT,
        EXPORT.replace("JModel_x86", "JWord"),
        EXPORT + "\n" + EXPORT,
        EXPORT + "\n(* unclosed comment",
        EXPORT + "\n*)",
    ]
    with tempfile.TemporaryDirectory(prefix="ntruplus-model-source-test-") as temporary:
        directory = Path(temporary)
        model = directory / "JModel.ec"
        model.write_text("(* outer (* nested *) comment *)\n" + EXPORT + "\n")
        check_source(directory)
        for mutation in mutations:
            model.write_text(mutation)
            try:
                check_source(directory)
            except ValueError:
                continue
            raise SystemExit("FAIL: compatibility source gate accepted a mutation")
        model.write_text(EXPORT)
        nested = directory / "nested"
        nested.mkdir()
        (nested / "JModel_x86.ec").write_text("axiom forged : false.")
        try:
            check_source(directory)
        except ValueError:
            pass
        else:
            raise SystemExit("FAIL: compatibility source gate accepted an extra model")
    print("PASS: compatibility source gate rejects eight model/assumption mutations")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--easycrypt", default="easycrypt")
    parser.add_argument("--source-only", action="store_true",
                        help="check the exact shim source without invoking EasyCrypt")
    parser.add_argument("--selftest", action="store_true")
    args = parser.parse_args()
    if args.selftest:
        source_selftest()
    try:
        check_source(SHIM)
    except ValueError as error:
        raise SystemExit("FAIL: " + str(error)) from error
    print("PASS: compatibility shim contains only the installed-model export")
    if args.source_only:
        return
    # Check every project's effective loader configuration, including projects
    # that previously overrode the installed model with Formosa's old model.
    projects = [ROOT] + sorted(
        p.parent for p in (ROOT / "ntruplus/proof/768/ref").glob("*/easycrypt.project")
    )
    for project in projects:
        result = subprocess.run(
            [args.easycrypt, "config"], cwd=project,
            capture_output=True, text=True, check=True,
        )
        config = result.stdout + result.stderr
        if "external/formosa-mlkem/jasmin/eclib" in config:
            raise SystemExit(f"FAIL: legacy Jasmin model remains in {project}")
        if "compat/jasmin" not in config:
            raise SystemExit(f"FAIL: compatibility model is unavailable in {project}")
    with tempfile.TemporaryDirectory(prefix="ntruplus-jasmin-model-") as temporary:
        probe = Path(temporary) / "ModelCompatibility.ec"
        probe.write_text(PROBE)
        command = [args.easycrypt, "compile", "-no-eco", "-p", "Z3",
                   "-timeout", "30", "-max-provers", "1",
                   "-I", f"Jasmin:{SHIM}"]
        for directory in ("ntruplus/proof/768/ref/basemul/extracted",
                          "external/formosa-mlkem/crypto-specs/common",
                          "external/formosa-mlkem/proof/eclib"):
            command += ["-I", str(ROOT / directory)]
        command.append(str(probe))
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        if result.returncode:
            raise SystemExit(result.stdout + result.stderr)
    print(f"PASS: {len(projects)} loader configurations exclude the legacy Jasmin model")
    print("PASS: pinned Formosa helpers and the installed x86 model share W16 types and operations")


if __name__ == "__main__":
    main()
