#!/usr/bin/env python3
"""Check the explicit policy of the fixed poly_basemul export.

Jasmin 2026.03.0 can infer an omitted SCT argument. This guard requires
all three pointer/content policies to be stated before invoking the checker.
It is a source-interface check, not a replacement for CT/SCT analysis.
"""

import argparse
import re
from pathlib import Path

ENTRY = "jade_ntruplus_ntruplus768_amd64_ref_poly_basemul"
INPUT = "{ptr:transient,val:secret}"
OUTPUT = "{ptr:public,val:secret}"


def compact(text):
    return re.sub(r"\s+", "", text).replace("×", "*").replace("→", "->")


def check(text):
    text = re.sub(r"/\*.*?\*/|//[^\n]*", "", text, flags=re.S)
    pattern = (
        r'#\[sct\s*=\s*"([^"]*)"\]\s*export\s+fn\s+'
        + ENTRY
        + r"\s*\(([^)]*)\)\s*->\s*reg\s+ptr\s+u16\[NTRUPLUS_N\]"
    )
    matches = re.findall(pattern, text, flags=re.S)
    if len(matches) != 1:
        raise ValueError("expected one explicit SCT policy on the poly_basemul export")
    policy, arguments = matches[0]
    expected_args = (
        "regmutptru16[NTRUPLUS_N]rp,"
        "regconstptru16[NTRUPLUS_N]ap,"
        "regconstptru16[NTRUPLUS_N]bp"
    )
    if compact(arguments) != expected_args:
        raise ValueError("poly_basemul pointer interface changed; review its security policy")
    if compact(policy) != "*".join([INPUT] * 3) + "->" + OUTPUT:
        raise ValueError("SCT policy must specify three transient pointers to secret data and a public return pointer to secret data")


def selftest():
    # Keep mutations independent of harmless formatting changes in the source.
    text = (
        f'#[sct="{INPUT}*{INPUT}*{INPUT}->{OUTPUT}"] export fn {ENTRY}('
        "reg mut ptr u16[NTRUPLUS_N] rp, "
        "reg const ptr u16[NTRUPLUS_N] ap, "
        "reg const ptr u16[NTRUPLUS_N] bp) -> reg ptr u16[NTRUPLUS_N]"
    )
    check(text)
    entry = INPUT + "*"
    mutations = {
        "missing input": text.replace(entry, "", 1),
        "extra input": text.replace(entry, entry + "\n" + entry, 1),
        "public input data": text.replace("val:secret", "val:public", 1),
        "changed return policy": text.replace("ptr:public", "ptr:transient", 1),
        "changed interface": text.replace("reg const ptr u16[NTRUPLUS_N] bp", "reg const ptr u16[NTRUPLUS_N] cp", 1),
    }
    for name, mutant in mutations.items():
        if mutant == text:
            raise ValueError("self-test mutation did not apply: " + name)
        try:
            check(mutant)
        except ValueError:
            continue
        raise ValueError("self-test accepted " + name)
    print("PASS: poly_basemul policy guard rejects five interface/policy mutations")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--selftest", action="store_true")
    args = parser.parse_args()
    try:
        text = args.source.read_text()
        check(text)
        if args.selftest:
            selftest()
    except (OSError, ValueError) as error:
        parser.exit(1, "FAIL: " + str(error) + "\n")
    print("PASS: poly_basemul explicit SCT policy matches all three arguments")


if __name__ == "__main__":
    main()
