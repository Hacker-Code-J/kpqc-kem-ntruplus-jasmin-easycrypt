#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


class VerificationError(RuntimeError):
    pass


EXPECTED_CHAIN = [
    ("t1", "a", "a"),
    ("t2", "t1", "t1"),
    ("t2", "t2", "t2"),
    ("t3", "t2", "t2"),
    ("t1", "t1", "t2"),
    ("t2", "t1", "t3"),
    ("t2", "t2", "t2"),
    ("t2", "t2", "a"),
    ("t1", "t1", "t2"),
    ("t2", "t2", "t2"),
    ("t2", "t2", "t2"),
    ("t2", "t2", "t2"),
    ("t2", "t2", "t2"),
    ("t2", "t2", "t2"),
    ("t2", "t2", "t2"),
    ("t2", "t2", "t1"),
    ("t2", "NTRUPLUS_RINV", "t2"),
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def strip_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    return re.sub(r"//.*", "", text)


def compact(text: str) -> str:
    return re.sub(r"\s+", " ", strip_comments(text)).strip()


def extract_body(text: str, name: str) -> str:
    matches = list(re.finditer(rf"\b{name}\s*\([^)]*\)[^{{;]*\{{", text, flags=re.S))
    require(len(matches) == 1, f"expected exactly one definition of `{name}`")
    start = matches[0].end() - 1
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1 : index]
    raise VerificationError(f"unterminated body for `{name}`")


def extract_c_define(text: str, name: str) -> int:
    matches = re.findall(
        rf"^\s*#\s*define\s+{name}\s+(-?\d+)\s*(?://.*)?$",
        text,
        flags=re.M,
    )
    require(len(matches) == 1, f"expected one C definition of {name}")
    return int(matches[0])


def extract_jasmin_param(text: str, name: str) -> int:
    matches = re.findall(
        rf"^\s*param\s+int\s+{name}\s*=\s*(-?\d+)\s*;\s*$",
        strip_comments(text),
        flags=re.M,
    )
    require(len(matches) == 1, f"expected one Jasmin parameter {name}")
    return int(matches[0])


def extract_chain(body: str, helper: str) -> list[tuple[str, str, str]]:
    pattern = rf"\b(t[123])\s*=\s*{helper}\s*\(\s*([^,()]+)\s*,\s*([^,()]+)\s*\)\s*;"
    return [
        (dst.strip(), left.strip(), right.strip())
        for dst, left, right in re.findall(pattern, strip_comments(body))
    ]


def verify_c_source(params_text: str, text: str) -> None:
    require(
        extract_c_define(params_text, "NTRUPLUS_Q") == 3457,
        "C q must remain 3457",
    )
    require(extract_c_define(text, "NTRUPLUS_QINV") == 12929, "C QINV must remain 12929")
    require(extract_c_define(text, "NTRUPLUS_RINV") == -682, "C RINV must remain -682")

    montgomery_body = compact(extract_body(text, "montgomery_reduce"))
    require(
        montgomery_body
        == "int16_t t; t = (int16_t)a * NTRUPLUS_QINV; "
        "t = (a - (int32_t)t * NTRUPLUS_Q) >> 16; return t;",
        "C montgomery_reduce body changed",
    )
    require(
        compact(extract_body(text, "fqmul"))
        == "return montgomery_reduce((int32_t)a * b);",
        "C fqmul body changed",
    )

    fqinv_body = extract_body(text, "fqinv")
    require(extract_chain(fqinv_body, "fqmul") == EXPECTED_CHAIN, "C fqinv chain changed")
    require(compact(fqinv_body).endswith("return t2;"), "C fqinv must return t2")


def verify_jasmin_source(text: str) -> None:
    require(extract_jasmin_param(text, "NTRUPLUS_Q") == 3457, "Jasmin q must remain 3457")
    require(
        extract_jasmin_param(text, "NTRUPLUS_QINV") == 12929,
        "Jasmin QINV must remain 12929",
    )
    require(
        extract_jasmin_param(text, "NTRUPLUS_RINV") == -682,
        "Jasmin RINV must remain -682",
    )

    require(
        compact(extract_body(text, "__mul_i16"))
        == "reg u32 ad; reg u32 bd; reg u32 c; ad = (32s) a; "
        "bd = (32s) b; c = ad * bd; return c;",
        "Jasmin __mul_i16 body changed",
    )
    require(
        compact(extract_body(text, "__montgomery_reduce"))
        == "reg u16 t; reg u32 q; reg u32 td; reg u32 r; "
        "q = NTRUPLUS_Q; td = (32s) a; td *= NTRUPLUS_QINV; t = td; "
        "td = (32s) t; r = (32s) a; td *= q; r -= td; r >>s= 16; "
        "t = r; return t;",
        "Jasmin __montgomery_reduce body changed",
    )
    require(
        compact(extract_body(text, "__fqmul"))
        == "reg u32 c; reg u16 r; c = __mul_i16(a, b); "
        "r = __montgomery_reduce(c); return r;",
        "Jasmin __fqmul body changed",
    )

    signature = re.search(
        r"export\s+fn\s+jade_ntruplus_ntruplus768_amd64_ref_fqinv\s*"
        r"\(\s*reg\s+u16\s+a\s*\)\s*->\s*reg\s+u16",
        strip_comments(text),
        flags=re.S,
    )
    require(signature is not None, "unexpected Jasmin fqinv export ABI")
    require(
        re.search(r'#\[ct\s*=\s*"secret\s*(?:→|->)\s*secret"\s*\]', text)
        is not None,
        "missing scalar CT annotation",
    )
    require("#[sct=" in text or "#[sct =" in text, "missing scalar SCT annotation")

    fqinv_body = extract_body(text, "jade_ntruplus_ntruplus768_amd64_ref_fqinv")
    require(
        extract_chain(fqinv_body, "__fqmul") == EXPECTED_CHAIN,
        "Jasmin fqinv chain changed",
    )
    require(compact(fqinv_body).endswith("return t2;"), "Jasmin fqinv must return t2")


def verify_all(params_text: str, c_text: str, jasmin_text: str) -> None:
    verify_c_source(params_text, c_text)
    verify_jasmin_source(jasmin_text)


def mutate_once(text: str, pattern: str, replacement: str, label: str) -> str:
    mutated, count = re.subn(pattern, replacement, text, count=1, flags=re.M)
    require(count == 1, f"could not construct mutation: {label}")
    return mutated


def expect_rejected(
    params_text: str, c_text: str, jasmin_text: str, label: str
) -> None:
    try:
        verify_all(params_text, c_text, jasmin_text)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(params_text: str, c_text: str, jasmin_text: str) -> int:
    verify_all(params_text, c_text, jasmin_text)
    mutations = [
        (
            mutate_once(
                params_text,
                r"(#\s*define\s+NTRUPLUS_Q\s+)3457",
                r"\g<1>3456",
                "C q",
            ),
            c_text,
            jasmin_text,
            "C q",
        ),
        (
            params_text,
            mutate_once(c_text, r"(#\s*define\s+NTRUPLUS_QINV\s+)12929", r"\g<1>12928", "C QINV"),
            jasmin_text,
            "C QINV",
        ),
        (
            params_text,
            mutate_once(c_text, r"(#\s*define\s+NTRUPLUS_RINV\s+)-682", r"\g<1>-681", "C RINV"),
            jasmin_text,
            "C RINV",
        ),
        (
            params_text,
            mutate_once(c_text, r"t2\s*=\s*fqmul\(t2,\s*a\);", "t2 = fqmul(t2, t1);", "C chain"),
            jasmin_text,
            "C chain",
        ),
        (
            params_text,
            mutate_once(c_text, r"return\s+t2;", "return t1;", "C return"),
            jasmin_text,
            "C return",
        ),
        (
            params_text,
            mutate_once(
                c_text,
                r"t\s*=\s*\(int16_t\)a\s*\*\s*NTRUPLUS_QINV;",
                "t = (int16_t)a * (NTRUPLUS_QINV - 1);",
                "C Montgomery multiplier",
            ),
            jasmin_text,
            "C Montgomery multiplier",
        ),
        (
            params_text,
            mutate_once(
                c_text,
                r"montgomery_reduce\(\(int32_t\)a\s*\*\s*b\)",
                "montgomery_reduce((int32_t)a + b)",
                "C fqmul operator",
            ),
            jasmin_text,
            "C fqmul operator",
        ),
        (
            params_text,
            c_text,
            mutate_once(jasmin_text, r"(param\s+int\s+NTRUPLUS_Q\s*=\s*)3457", r"\g<1>3456", "Jasmin q"),
            "Jasmin q",
        ),
        (
            params_text,
            c_text,
            mutate_once(jasmin_text, r"(param\s+int\s+NTRUPLUS_QINV\s*=\s*)12929", r"\g<1>12928", "Jasmin QINV"),
            "Jasmin QINV",
        ),
        (
            params_text,
            c_text,
            mutate_once(jasmin_text, r"(param\s+int\s+NTRUPLUS_RINV\s*=\s*)-682", r"\g<1>-681", "Jasmin RINV"),
            "Jasmin RINV",
        ),
        (
            params_text,
            c_text,
            mutate_once(jasmin_text, r"t2\s*=\s*__fqmul\(t2,\s*a\);", "t2 = __fqmul(t2, t1);", "Jasmin chain"),
            "Jasmin chain",
        ),
        (
            params_text,
            c_text,
            mutate_once(jasmin_text, r"return\s+t2;", "return t1;", "Jasmin return"),
            "Jasmin return",
        ),
        (
            params_text,
            c_text,
            mutate_once(
                jasmin_text,
                r"jade_ntruplus_ntruplus768_amd64_ref_fqinv",
                "jade_ntruplus_ntruplus768_amd64_ref_fqinv_bad",
                "Jasmin export",
            ),
            "Jasmin export",
        ),
        (
            params_text,
            c_text,
            mutate_once(jasmin_text, r"__fqmul", "__fqmul_bad", "Jasmin helper"),
            "Jasmin helper",
        ),
        (
            params_text,
            c_text,
            mutate_once(
                jasmin_text,
                r"c\s*=\s*ad\s*\*\s*bd;",
                "c = ad + bd;",
                "Jasmin signed multiply",
            ),
            "Jasmin signed multiply",
        ),
        (
            params_text,
            c_text,
            mutate_once(
                jasmin_text,
                r"r\s*-=\s*td;",
                "r += td;",
                "Jasmin Montgomery subtract",
            ),
            "Jasmin Montgomery subtract",
        ),
        (
            params_text,
            c_text,
            mutate_once(
                jasmin_text,
                r"c\s*=\s*__mul_i16\(a,\s*b\);",
                "c = __mul_i16(a, a);",
                "Jasmin fqmul operands",
            ),
            "Jasmin fqmul operands",
        ),
    ]

    for mutated_params, mutated_c, mutated_jasmin, label in mutations:
        expect_rejected(mutated_params, mutated_c, mutated_jasmin, label)
    return len(mutations)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Check the exact C/Jasmin fqinv seam")
    parser.add_argument("--params-source", required=True)
    parser.add_argument("--c-source", required=True)
    parser.add_argument("--jasmin-source", required=True)
    parser.add_argument("--self-check", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        params_text = Path(args.params_source).read_text(encoding="utf-8")
        c_text = Path(args.c_source).read_text(encoding="utf-8")
        jasmin_text = Path(args.jasmin_source).read_text(encoding="utf-8")
        if args.self_check:
            rejected = run_self_check(params_text, c_text, jasmin_text)
            print(f"fqinv seam self-check passed: {rejected} mutations rejected")
        else:
            verify_all(params_text, c_text, jasmin_text)
            print("fqinv C/Jasmin seam check passed")
    except (OSError, VerificationError) as err:
        print(f"FAILED: {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
