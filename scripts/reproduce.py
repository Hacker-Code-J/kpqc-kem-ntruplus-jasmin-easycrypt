#!/usr/bin/env python3
"""Public entry point for existing NTRU+768 verification scripts (Python 3.10+)."""

import argparse
import ast
from dataclasses import dataclass
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
PREFIX = "verify-ntruplus768-"


@dataclass(frozen=True)
class Target:
    script: Path
    options: frozenset


def targets(root=ROOT):
    """Read CLI declarations without importing or executing proof harnesses."""
    result = {}
    for script in sorted((root / "scripts").glob(PREFIX + "*.sh")):
        name = script.name[len(PREFIX) : -3]
        source = script.read_text()
        options = set()
        if "exec python3" in source:
            match = re.search(r'exec python3 "\$\w+/(tests/[^"\n]+\.py)" "\$@"', source)
            if match is None:
                raise ValueError(f"unrecognized Python wrapper: {script.name}")
            driver = root / match[1]
            if driver.name.startswith("test_ntruplus768_"):
                family = driver.stem.removeprefix("test_ntruplus768_")
                driver = (
                    root / "tests/ntruplus768" / family / ("verify_" + family + ".py")
                )
            tree = ast.parse(driver.read_text(), filename=str(driver))
            for node in ast.walk(tree):
                if (
                    isinstance(node, ast.Call)
                    and isinstance(node.func, ast.Attribute)
                    and node.func.attr == "add_argument"
                ):
                    options.update(
                        arg.value
                        for arg in node.args
                        if isinstance(arg, ast.Constant)
                        and isinstance(arg.value, str)
                        and arg.value.startswith("--")
                    )
        result[name] = Target(script, frozenset(options))
    if not result:
        raise ValueError("no verification scripts found")
    return result


def proof_commands(inventory, names, prior_evidence_root=None):
    """Prepare all commands first, so a missing input prevents partial launch."""
    if not names:
        raise ValueError("choose at least one proof target or --all")
    unknown = set(names) - inventory.keys()
    if unknown:
        raise ValueError("unknown target(s): " + ", ".join(sorted(unknown)))
    if "baseline" in names:
        raise ValueError("use the baseline command for the C/KAT test")
    needs_prior = [
        name for name in names if "--prior-evidence-root" in inventory[name].options
    ]
    if needs_prior and prior_evidence_root is None:
        raise ValueError(
            "--prior-evidence-root is required for "
            + ", ".join(needs_prior)
            + "; see docs/evidence.md"
        )
    if prior_evidence_root is not None:
        prior_evidence_root = Path(prior_evidence_root).expanduser().resolve()
        if not prior_evidence_root.is_dir():
            raise ValueError(
                "prior evidence root is not a directory: " + str(prior_evidence_root)
            )
    commands = []
    for name in names:
        command = ["bash", str(inventory[name].script)]
        if name in needs_prior:
            command += ["--prior-evidence-root", str(prior_evidence_root)]
        commands.append(command)
    return commands


def execute(commands, root=ROOT):
    for command in commands:
        if shutil.which(command[0]) is None:
            raise ValueError("missing required executable: " + command[0])
        print("RUN: " + shlex.join(command), flush=True)
        completed = subprocess.run(command, cwd=root, check=False)
        if completed.returncode:
            print(
                "FAILED: verifier exited with code " + str(completed.returncode),
                file=sys.stderr,
            )
            return completed.returncode if completed.returncode > 0 else 1
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser(
        "list", help="list the existing verify-ntruplus768 shell-script inventory"
    )
    commands.add_parser(
        "smoke", help="source-only compatibility shim and negative controls; no proofs"
    )
    commands.add_parser(
        "baseline",
        help="build C reference, functional test and byte-exact KAT comparison",
    )
    proof = commands.add_parser(
        "proof", help="run existing verifiers with their full default checks"
    )
    proof.add_argument("targets", nargs="*")
    proof.add_argument(
        "--all",
        action="store_true",
        help="run every listed verification script except baseline, sequentially",
    )
    proof.add_argument(
        "--prior-evidence-root",
        type=Path,
        help="explicit root of the hash-pinned historical evidence bundle",
    )
    proof.add_argument(
        "--dry-run", action="store_true", help="print commands without running checks"
    )
    args = parser.parse_args(argv)
    try:
        inventory = targets()
        if args.command == "list":
            for name, target in inventory.items():
                scope = (
                    "C functional/KAT"
                    if name == "baseline"
                    else "verifier default scope"
                )
                if "--prior-evidence-root" in target.options:
                    scope += "; requires --prior-evidence-root"
                print(name + "\t" + scope)
            print(
                "Inventory: shell entry points only, not all Make targets. "
                "See docs/claims.md."
            )
            return 0
        if args.command == "smoke":
            selected = [
                [
                    sys.executable,
                    str(
                        ROOT
                        / "tests/ntruplus768/toolchain/check_model_compatibility.py"
                    ),
                    "--source-only",
                    "--selftest",
                ]
            ]
        elif args.command == "baseline":
            if "baseline" not in inventory:
                raise ValueError("baseline script is missing")
            selected = [["bash", str(inventory["baseline"].script)]]
        else:
            if args.all and args.targets:
                raise ValueError("choose explicit targets or --all, not both")
            names = (
                [name for name in inventory if name != "baseline"]
                if args.all
                else args.targets
            )
            selected = proof_commands(inventory, names, args.prior_evidence_root)
            if args.dry_run:
                for command in selected:
                    print(shlex.join(command))
                print("DRY RUN ONLY: no verification performed.")
                return 0
        result = execute(selected)
        if result == 0:
            print(
                "Completed requested "
                + args.command
                + " commands; retain each verifier's scope and evidence."
            )
        return result
    except (OSError, ValueError, SyntaxError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    sys.exit(main())
