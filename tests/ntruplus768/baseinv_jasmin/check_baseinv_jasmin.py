#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True

BASEINV_CHECKER_DIR = Path(__file__).resolve().parents[1] / "baseinv"
sys.path.insert(0, str(BASEINV_CHECKER_DIR))

from check_baseinv import (  # noqa: E402
    VerificationError as CVerificationError,
    verify_ntt_source_text,
    verify_params_text,
)


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
    matches = list(
        re.finditer(rf"\b{name}\s*\([^)]*\)[^{{;]*\{{", text, flags=re.S)
    )
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


def extract_signature(text: str, name: str) -> str:
    match = re.search(
        rf"((?:inline\s+|export\s+)?fn\s+{name}\s*\([^)]*\)"
        rf"\s*(?:->\s*[^{{]+)?)\s*\{{",
        strip_comments(text),
        flags=re.S,
    )
    require(match is not None, f"could not find signature for `{name}`")
    return compact(match.group(1))


def extract_jasmin_param(text: str, name: str) -> int:
    matches = re.findall(
        rf"^\s*param\s+int\s+{name}\s*=\s*(-?\d+)\s*;\s*$",
        strip_comments(text),
        flags=re.M,
    )
    require(len(matches) == 1, f"expected one Jasmin parameter {name}")
    return int(matches[0])


def extract_chain(body: str) -> list[tuple[str, str, str]]:
    pattern = (
        r"\b(t[123])\s*=\s*__fqmul\s*\(\s*([^,()]+)\s*,"
        r"\s*([^,()]+)\s*\)\s*;"
    )
    return [
        (dst.strip(), left.strip(), right.strip())
        for dst, left, right in re.findall(pattern, strip_comments(body))
    ]


def verify_c_sources(params_text: str, c_text: str) -> None:
    try:
        verify_params_text(params_text)
        verify_ntt_source_text(c_text)
    except CVerificationError as err:
        raise VerificationError(str(err)) from err


def verify_jasmin_source(text: str) -> None:
    clean = strip_comments(text)

    require(extract_jasmin_param(text, "NTRUPLUS_Q") == 3457, "Jasmin q changed")
    require(
        extract_jasmin_param(text, "NTRUPLUS_QINV") == 12929,
        "Jasmin QINV changed",
    )
    require(
        extract_jasmin_param(text, "NTRUPLUS_RINV") == -682,
        "Jasmin RINV changed",
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

    fqinv_body = extract_body(text, "__fqinv")
    require(extract_chain(fqinv_body) == EXPECTED_CHAIN, "Jasmin fqinv chain changed")
    require(compact(fqinv_body).endswith("return t2;"), "Jasmin fqinv return changed")

    require(
        extract_signature(text, "__baseinv_pretrace")
        == "inline fn __baseinv_pretrace( reg u16 a0 a1 a2 a3 zeta) -> "
        "reg u16, reg u16, reg u16, reg u16",
        "unexpected Jasmin pretrace signature",
    )
    require(
        compact(extract_body(text, "__baseinv_pretrace"))
        == "reg u16 t0; reg u16 t1; reg u16 t2; reg u16 t3; "
        "reg u32 acc; reg u32 term; acc = __mul_i16(a2, a2); "
        "term = __mul_i16(a1, a3); term += term; acc -= term; "
        "t0 = __montgomery_reduce(acc); acc = __mul_i16(a3, a3); "
        "t1 = __montgomery_reduce(acc); acc = __mul_i16(a0, a0); "
        "term = __mul_i16(t0, zeta); acc += term; "
        "t0 = __montgomery_reduce(acc); acc = __mul_i16(a1, a1); "
        "term = __mul_i16(t1, zeta); acc += term; "
        "term = __mul_i16(a0, a2); term += term; acc -= term; "
        "t1 = __montgomery_reduce(acc); acc = __mul_i16(t1, zeta); "
        "t2 = __montgomery_reduce(acc); acc = __mul_i16(t0, t0); "
        "term = __mul_i16(t1, t2); acc -= term; "
        "t3 = __montgomery_reduce(acc); return t0, t1, t2, t3;",
        "Jasmin pretrace body changed",
    )

    require(
        extract_signature(text, "__baseinv_success")
        == "inline fn __baseinv_success( reg u16 a0 a1 a2 a3 t0 t1 t2 "
        "determinant) -> reg u16, reg u16, reg u16, reg u16",
        "unexpected Jasmin success-helper signature",
    )
    require(
        compact(extract_body(text, "__baseinv_success"))
        == "reg u16 r0; reg u16 r1; reg u16 r2; reg u16 r3; "
        "reg u16 invword; reg u32 acc; reg u32 term; "
        "acc = __mul_i16(a0, t0); term = __mul_i16(a2, t2); "
        "acc += term; r0 = __montgomery_reduce(acc); "
        "acc = __mul_i16(a3, t2); term = __mul_i16(a1, t0); "
        "acc += term; r1 = __montgomery_reduce(acc); "
        "acc = __mul_i16(a2, t0); term = __mul_i16(a0, t1); "
        "acc += term; r2 = __montgomery_reduce(acc); "
        "acc = __mul_i16(a1, t1); term = __mul_i16(a3, t0); "
        "acc += term; r3 = __montgomery_reduce(acc); "
        "invword = __fqinv(determinant); acc = __mul_i16(r0, invword); "
        "r0 = __montgomery_reduce(acc); acc = __mul_i16(r1, invword); "
        "r1 = __montgomery_reduce(acc); acc = __mul_i16(r2, invword); "
        "r2 = __montgomery_reduce(acc); acc = __mul_i16(r3, invword); "
        "r3 = __montgomery_reduce(acc); return r0, r1, r2, r3;",
        "Jasmin success-helper body changed",
    )

    require(
        extract_signature(text, "__baseinv_core")
        == "fn __baseinv_core( reg mut ptr u16[4] rp, reg const ptr u16[4] ap, "
        "reg u16 zeta) -> reg ptr u16[4], reg u64",
        "unexpected Jasmin proof-core ABI",
    )
    require(
        compact(extract_body(text, "__baseinv_core"))
        == "reg u16 a0; reg u16 a1; reg u16 a2; reg u16 a3; reg u16 t0; "
        "reg u16 t1; reg u16 t2; reg u16 t3; reg u16 r0; reg u16 r1; "
        "reg u16 r2; reg u16 r3; reg u64 status; _ = #init_msf(); "
        "a0 = ap[0]; a1 = ap[1]; a2 = ap[2]; a3 = ap[3]; "
        "t0, t1, t2, t3 = __baseinv_pretrace(a0, a1, a2, a3, zeta); "
        "if (t3 == 0) { status = 1; } else { r0, r1, r2, r3 = "
        "__baseinv_success(a0, a1, a2, a3, t0, t1, t2, t3); "
        "r1 = -r1; r3 = -r3; rp[0] = r0; rp[1] = r1; rp[2] = r2; rp[3] = r3; "
        "status = 0; } return rp, status;",
        "Jasmin proof-core branch, stores, or status changed",
    )

    export_name = "jade_ntruplus_ntruplus768_amd64_ref_baseinv"
    require(
        extract_signature(text, export_name)
        == "export fn jade_ntruplus_ntruplus768_amd64_ref_baseinv( "
        "reg mut ptr u16[4] rp, reg const ptr u16[4] ap, reg u16 zeta) -> "
        "(reg ptr u16[4], reg u64)",
        "unexpected Jasmin baseinv export ABI",
    )
    require(
        compact(extract_body(text, export_name))
        == "reg u64 status; rp, status = __baseinv_core(rp, ap, zeta); "
        "return rp, status;",
        "Jasmin export must return the mutable pointer and status projection",
    )

    require(len(re.findall(r"\bexport\s+fn\b", clean)) == 1, "unexpected extra export")
    require(
        len(re.findall(r"#\[\s*safety\s*=", clean)) == 2,
        "core and export must each have exactly one safety annotation",
    )
    require(
        len(re.findall(r"#\[\s*(?:ct|sct)\s*=", clean)) == 0,
        "baseinv branches on secret data and must not carry CT/SCT annotations",
    )


def verify_all(params_text: str, c_text: str, jasmin_text: str) -> None:
    verify_c_sources(params_text, c_text)
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
        (mutate_once(params_text, r"(NTRUPLUS_Q\s+)3457", r"\g<1>3456", "C q"), c_text, jasmin_text, "C q"),
        (params_text, mutate_once(c_text, r"if\s*\(t3\s*==\s*0\)\s*return\s+1;", "if (t3 == 0) return 0;", "C failure status"), jasmin_text, "C failure status"),
        (params_text, mutate_once(c_text, r"r\[3\]\s*=\s*-montgomery_reduce\(r\[3\]\*t3\);", "r[3] = montgomery_reduce(r[3]*t3);", "C output sign"), jasmin_text, "C output sign"),
        (params_text, c_text, mutate_once(jasmin_text, r"(NTRUPLUS_Q\s*=\s*)3457", r"\g<1>3456", "Jasmin q"), "Jasmin q"),
        (params_text, c_text, mutate_once(jasmin_text, r"(NTRUPLUS_QINV\s*=\s*)12929", r"\g<1>12928", "Jasmin QINV"), "Jasmin QINV"),
        (params_text, c_text, mutate_once(jasmin_text, r"(NTRUPLUS_RINV\s*=\s*)-682", r"\g<1>-681", "Jasmin RINV"), "Jasmin RINV"),
        (params_text, c_text, mutate_once(jasmin_text, r"c\s*=\s*ad\s*\*\s*bd;", "c = ad + bd;", "signed multiply"), "signed multiply"),
        (params_text, c_text, mutate_once(jasmin_text, r"r\s*-=\s*td;", "r += td;", "Montgomery subtract"), "Montgomery subtract"),
        (params_text, c_text, mutate_once(jasmin_text, r"t2\s*=\s*__fqmul\(NTRUPLUS_RINV,\s*t2\);", "t2 = __fqmul(NTRUPLUS_QINV, t2);", "fqinv final scale"), "fqinv final scale"),
        (params_text, c_text, mutate_once(jasmin_text, r"term\s*\+=\s*term;", "term -= term;", "pretrace doubling"), "pretrace doubling"),
        (params_text, c_text, mutate_once(jasmin_text, r"acc\s*-\=\s*term;\s*t3\s*=", "acc += term; t3 =", "determinant sign"), "determinant sign"),
        (params_text, c_text, mutate_once(jasmin_text, r"term\s*=\s*__mul_i16\(a2,\s*t2\);", "term = __mul_i16(a2, t0);", "success numerator"), "success numerator"),
        (params_text, c_text, mutate_once(jasmin_text, r"if\s*\(t3\s*==\s*0\)\s*\{\s*status\s*=\s*1;", "if (t3 == 0) { status = 0;", "failure status"), "failure status"),
        (params_text, c_text, mutate_once(jasmin_text, r"r1\s*=\s*-r1;", "r1 = r1;", "output sign"), "output sign"),
        (params_text, c_text, mutate_once(jasmin_text, r"r3\s*=\s*-r3;", "r3 = r3;", "last output sign"), "last output sign"),
        (params_text, c_text, mutate_once(jasmin_text, r"a3\s*=\s*ap\[3\];", "a3 = ap[2];", "input lane"), "input lane"),
        (params_text, c_text, mutate_once(jasmin_text, r"return\s+rp,\s*status;", "return ap, status;", "core pointer result"), "core pointer result"),
        (params_text, c_text, mutate_once(jasmin_text, r"return\s+rp,\s*status;", "return rp, rp;", "status projection"), "status projection"),
        (params_text, c_text, mutate_once(jasmin_text, r"jade_ntruplus_ntruplus768_amd64_ref_baseinv", "jade_ntruplus_ntruplus768_amd64_ref_baseinv_bad", "export name"), "export name"),
        (params_text, c_text, mutate_once(jasmin_text, r"#\[safety", '#[ct = "secret -> secret"]\n#[safety', "forbidden CT annotation"), "forbidden CT annotation"),
    ]

    for mutated_params, mutated_c, mutated_jasmin, label in mutations:
        expect_rejected(mutated_params, mutated_c, mutated_jasmin, label)
    return len(mutations)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Check the exact C/Jasmin baseinv seam")
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
            print(f"baseinv Jasmin seam self-check passed: {rejected} mutations rejected")
        else:
            verify_all(params_text, c_text, jasmin_text)
            print("baseinv C/Jasmin seam check passed")
    except (OSError, VerificationError) as err:
        print(f"FAILED: {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
