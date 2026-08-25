#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True

BASEINV_DIR = Path(__file__).resolve().parents[1] / "baseinv"
sys.path.insert(0, str(BASEINV_DIR))

from check_baseinv import VerificationError as CVerificationError  # noqa: E402
from check_baseinv import verify_all as verify_c_sources  # noqa: E402


class VerificationError(RuntimeError):
    pass


EXPECTED_ZETAS96 = (
    "223, 1138, 64477, 65139, 65353, 1655, 559, 63862, "
    "277, 933, 1723, 437, 64022, 242, 1640, 432, "
    "63953, 696, 774, 1671, 927, 514, 512, 489, "
    "297, 601, 1473, 1130, 1322, 871, 760, 1212, "
    "65224, 65184, 443, 943, 8, 1250, 65436, 1660, "
    "65505, 1206, 64195, 64289, 444, 235, 1364, 64327, "
    "361, 230, 673, 582, 1409, 1501, 1401, 251, "
    "1022, 64473, 1053, 1188, 417, 64145, 65509, 63910, "
    "1685, 65221, 1408, 64288, 400, 274, 63993, 32, "
    "63986, 1531, 64169, 65412, 1458, 1379, 64596, 63855, "
    "22, 1709, 65261, 1108, 354, 63808, 64568, 858, "
    "1221, 65318, 294, 64804, 64441, 892, 1588, 64757"
)


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


def verify_makefile_text(text: str) -> None:
    require(
        "-auto-spill-all" in text,
        "Makefile must pin jasminc -auto-spill-all for this source",
    )
    require(
        'SLICE := jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv' in text,
        "Makefile must build the poly_baseinv export slice",
    )
    require(
        '$(NTT_SOURCE)" "$(POLY_SOURCE)"' in text,
        "Makefile run targets must link both production C sources",
    )


def verify_jasmin_source(text: str) -> None:
    clean = strip_comments(text)

    require(
        re.search(r"param\s+int\s+NTRUPLUS_N\s*=\s*768\s*;", clean) is not None,
        "Jasmin NTRUPLUS_N changed",
    )
    zetas_match = re.search(
        r"u16\[96\]\s+NTRUPLUS_ZETAS96\s*=\s*\{.*?\};",
        clean,
        flags=re.S,
    )
    require(zetas_match is not None, "missing Jasmin NTRUPLUS_ZETAS96 table")
    require(
        compact(zetas_match.group(0))
        == compact(f"u16[96] NTRUPLUS_ZETAS96 = {{ {EXPECTED_ZETAS96} }};"),
        "Jasmin NTRUPLUS_ZETAS96 table changed",
    )

    require(
        extract_signature(text, "__poly_baseinv_block")
        == "fn __poly_baseinv_block( reg mut ptr u16[4] tr, reg const ptr u16[4] ta, reg u16 zeta) -> reg ptr u16[4], reg u64",
        "unexpected block helper ABI",
    )
    require(
        compact(extract_body(text, "__poly_baseinv_block"))
        == "reg u16 t0; reg u16 t1; reg u16 t2; reg u16 t3; reg u16 r0; reg u16 r1; reg u16 r2; reg u16 r3; reg u64 status; t0, t1, t2, t3 = BaseInv::__baseinv_pretrace(ta[0], ta[1], ta[2], ta[3], zeta); if (t3 == 0) { status = 1; } else { r0, r1, r2, r3 = BaseInv::__baseinv_success(ta[0], ta[1], ta[2], ta[3], t0, t1, t2, t3); r1 = -r1; r3 = -r3; tr[0] = r0; tr[1] = r1; tr[2] = r2; tr[3] = r3; status = 0; } return tr, status;",
        "block helper body changed",
    )

    require(
        extract_signature(text, "__poly_baseinv_apply")
        == "fn __poly_baseinv_apply( reg mut ptr u16[NTRUPLUS_N] rp, reg const ptr u16[NTRUPLUS_N] ap, reg u64 block, reg u16 zeta) -> reg ptr u16[NTRUPLUS_N], reg u64",
        "unexpected apply helper ABI",
    )
    require(
        compact(extract_body(text, "__poly_baseinv_apply"))
        == "stack u16[4] ta; stack u16[4] tr; reg mut ptr u16[4] trp; reg u64 off; reg u64 status; tr[0] = 0; tr[1] = 0; tr[2] = 0; tr[3] = 0; trp = tr[0:4]; off = block; off <<= 2; ta[0] = ap[off]; ta[1] = ap[off + 1]; ta[2] = ap[off + 2]; ta[3] = ap[off + 3]; trp, status = __poly_baseinv_block(trp, ta, zeta); if (status == 0) { rp[off] = trp[0]; rp[off + 1] = trp[1]; rp[off + 2] = trp[2]; rp[off + 3] = trp[3]; } return rp, status;",
        "apply helper body changed",
    )

    require(
        extract_signature(text, "__poly_baseinv_pair")
        == "fn __poly_baseinv_pair( reg mut ptr u16[NTRUPLUS_N] rp, reg const ptr u16[NTRUPLUS_N] ap, reg u64 i, reg u16 zeta) -> reg ptr u16[NTRUPLUS_N], reg u64",
        "unexpected pair helper ABI",
    )
    require(
        compact(extract_body(text, "__poly_baseinv_pair"))
        == "reg u64 block; reg u64 status; block = i; block <<= 1; rp, status = __poly_baseinv_apply(rp, ap, block, zeta); if (status != 1) { block += 1; zeta = -zeta; rp, status = __poly_baseinv_apply(rp, ap, block, zeta); } return rp, status;",
        "pair helper body changed",
    )

    require(
        extract_signature(text, "__poly_baseinv_zero")
        == "inline fn __poly_baseinv_zero( reg mut ptr u16[NTRUPLUS_N] rp) -> reg ptr u16[NTRUPLUS_N]",
        "unexpected zero helper ABI",
    )
    require(
        compact(extract_body(text, "__poly_baseinv_zero"))
        == "reg u64 j; j = 0; while (j < NTRUPLUS_N) { rp[j] = 0; j += 1; } return rp;",
        "zero helper body changed",
    )

    require(
        extract_signature(text, "__poly_baseinv_core")
        == "fn __poly_baseinv_core( reg mut ptr u16[NTRUPLUS_N] rp, reg const ptr u16[NTRUPLUS_N] ap) -> reg ptr u16[NTRUPLUS_N], reg u64",
        "unexpected core ABI",
    )
    require(
        compact(extract_body(text, "__poly_baseinv_core"))
        == "reg ptr u16[96] zetasp; reg u16 zeta; reg u64 i; reg u64 status; _ = #init_msf(); i = 0; status = 0; zetasp = NTRUPLUS_ZETAS96[0:96]; while (i < NTRUPLUS_N / 8) { zeta = zetasp[i]; rp, status = __poly_baseinv_pair(rp, ap, i, zeta); if (status == 1) { i = NTRUPLUS_N / 8; } else { i += 1; status = 0; } } if (status == 1) { rp = __poly_baseinv_zero(rp); } return rp, status;",
        "core body changed",
    )

    export_name = "jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv"
    require(
        extract_signature(text, export_name)
        == "export fn jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv( reg mut ptr u16[NTRUPLUS_N] rp, reg const ptr u16[NTRUPLUS_N] ap) -> (reg ptr u16[NTRUPLUS_N], reg u64)",
        "unexpected export ABI",
    )
    require(
        compact(extract_body(text, export_name))
        == "reg u64 status; rp, status = __poly_baseinv_core(rp, ap); return rp, status;",
        "export body changed",
    )

    require(len(re.findall(r"\bexport\s+fn\b", clean)) == 1, "unexpected extra export")
    require(
        clean.count("#[safety") == 4,
        "expected exactly four safety annotations",
    )
    require(
        len(re.findall(r"#\[\s*(?:ct|sct)\s*=", clean)) == 0,
        "poly_baseinv branches on secret data and must not carry CT/SCT annotations",
    )


def verify_all(
    params_text: str,
    ntt_header_text: str,
    poly_header_text: str,
    ntt_text: str,
    poly_text: str,
    kem_text: str,
    jasmin_text: str,
    makefile_text: str,
) -> None:
    try:
        verify_c_sources(
            params_text, ntt_header_text, poly_header_text, ntt_text, poly_text, kem_text
        )
    except CVerificationError as err:
        raise VerificationError(str(err)) from err
    verify_makefile_text(makefile_text)
    verify_jasmin_source(jasmin_text)


def mutate_once(text: str, old: str, new: str, label: str) -> str:
    mutated = text.replace(old, new, 1)
    require(mutated != text, f"could not construct mutation: {label}")
    return mutated


def expect_rejected(*payload: str, label: str) -> None:
    try:
        verify_all(*payload)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(
    params_text: str,
    ntt_header_text: str,
    poly_header_text: str,
    ntt_text: str,
    poly_text: str,
    kem_text: str,
    jasmin_text: str,
    makefile_text: str,
) -> int:
    verify_all(
        params_text,
        ntt_header_text,
        poly_header_text,
        ntt_text,
        poly_text,
        kem_text,
        jasmin_text,
        makefile_text,
    )

    mutations = [
        ("makefile", "-auto-spill-all", "", "auto-spill contract"),
        ("jasmin", "status != 1", "status == 1", "pair second-call gate"),
        ("jasmin", "zeta = -zeta;", "zeta = zeta;", "odd-block negation"),
        ("jasmin", "i < NTRUPLUS_N / 8", "i < NTRUPLUS_N / 4", "96-pair loop bound"),
        ("jasmin", "i = NTRUPLUS_N / 8;", "i = NTRUPLUS_N / 4;", "failure exit bound"),
        ("jasmin", "rp = __poly_baseinv_zero(rp);", "status = 1;", "failure zeroization"),
        (
            "jasmin",
            "rp, status = __poly_baseinv_core(rp, ap);",
            "rp, status = __poly_baseinv_core(rp, ap); status = 0;",
            "export status return",
        ),
        ("jasmin", "#[safety = { requires = is_arr_init(ap,0,2 * NTRUPLUS_N), ensures = true }]", "#[ct = true]", "CT annotation"),
        ("jasmin", "223, 1138", "224, 1138", "zeta table head"),
        ("jasmin", "block <<= 1;", "block <<= 2;", "pair block stride"),
    ]

    for target, old, new, label in mutations:
        payload = [params_text, ntt_header_text, poly_header_text, ntt_text, poly_text, kem_text, jasmin_text, makefile_text]
        if target == "makefile":
            payload[7] = mutate_once(makefile_text, old, new, label)
        else:
            payload[6] = mutate_once(jasmin_text, old, new, label)
        expect_rejected(*payload, label=label)

    print("poly_baseinv Jasmin checker self-check passed: 10 mutations rejected")
    return 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fail-closed checker for the NTRU+768 poly_baseinv Jasmin realization"
    )
    parser.add_argument("--params-source", required=True)
    parser.add_argument("--ntt-header", required=True)
    parser.add_argument("--poly-header", required=True)
    parser.add_argument("--ntt-source", required=True)
    parser.add_argument("--poly-source", required=True)
    parser.add_argument("--kem-source", required=True)
    parser.add_argument("--jasmin-source", required=True)
    parser.add_argument("--makefile", required=True)
    parser.add_argument("--self-check", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    params_text = Path(args.params_source).read_text(encoding="utf-8")
    ntt_header_text = Path(args.ntt_header).read_text(encoding="utf-8")
    poly_header_text = Path(args.poly_header).read_text(encoding="utf-8")
    ntt_text = Path(args.ntt_source).read_text(encoding="utf-8")
    poly_text = Path(args.poly_source).read_text(encoding="utf-8")
    kem_text = Path(args.kem_source).read_text(encoding="utf-8")
    jasmin_text = Path(args.jasmin_source).read_text(encoding="utf-8")
    makefile_text = Path(args.makefile).read_text(encoding="utf-8")

    if args.self_check:
        return run_self_check(
            params_text,
            ntt_header_text,
            poly_header_text,
            ntt_text,
            poly_text,
            kem_text,
            jasmin_text,
            makefile_text,
        )

    try:
        verify_all(
            params_text,
            ntt_header_text,
            poly_header_text,
            ntt_text,
            poly_text,
            kem_text,
            jasmin_text,
            makefile_text,
        )
    except VerificationError as err:
        print(f"FAIL: {err}", file=sys.stderr)
        return 1

    print("poly_baseinv Jasmin checker passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
