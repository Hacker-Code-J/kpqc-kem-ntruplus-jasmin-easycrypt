#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True

TEST_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TEST_ROOT / "baseinv"))
sys.path.insert(0, str(TEST_ROOT / "keygen_sampler"))
sys.path.insert(0, str(TEST_ROOT / "poly_baseinv_jasmin"))

from check_keygen_sampler import VerificationError as SamplerError  # noqa: E402
from check_keygen_sampler import verify_all as verify_sampler_sources  # noqa: E402
from check_baseinv import VerificationError as BaseinvCError  # noqa: E402
from check_poly_baseinv_jasmin import VerificationError as BaseinvError  # noqa: E402
from check_poly_baseinv_jasmin import verify_jasmin_source as verify_baseinv_jasmin_source  # noqa: E402
from check_baseinv import verify_all as verify_baseinv_c_sources  # noqa: E402


class VerificationError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def strip_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    return re.sub(r"//.*", "", text)


def compact(text: str) -> str:
    text = re.sub(r"\s+", " ", strip_comments(text)).strip()
    text = re.sub(r"\[\s+", "[", text)
    return re.sub(r"\s+\]", "]", text)


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


def extract_export_signature(text: str, name: str) -> str:
    match = re.search(
        rf"(export\s+fn\s+{name}\s*\([^)]*\)\s*->\s*[^{{]+)\{{",
        strip_comments(text),
        flags=re.S,
    )
    require(match is not None, f"could not find export signature for `{name}`")
    return compact(match.group(1))


def verify_kem_prefix(kem_text: str) -> None:
    body = compact(extract_body(kem_text, "crypto_kem_keypair_derand"))
    prefix = (
        "poly h, hinv; "
        "poly_basemul(&h, g, finv); "
        "poly_basemul(&hinv, f, ginv); "
        "poly_tobytes(pk, &h);"
    )
    require(
        body.count("poly_basemul(&h, g, finv);") == 1,
        "crypto_kem_keypair_derand() must contain exactly one poly_basemul(&h, g, finv)",
    )
    require(
        body.count("poly_basemul(&hinv, f, ginv);") == 1,
        "crypto_kem_keypair_derand() must contain exactly one poly_basemul(&hinv, f, ginv)",
    )
    require(
        prefix in body,
        "crypto_kem_keypair_derand() must keep the exact h then hinv poly_basemul prefix before serialization",
    )


def verify_poly_header(poly_header_text: str) -> None:
    require(
        re.search(
            r"^\s*void\s+poly_basemul\s*\(\s*poly\s*\*\s*r\s*,\s*const\s+poly\s*\*\s*a\s*,\s*const\s+poly\s*\*\s*b\s*\)\s*;\s*$",
            strip_comments(poly_header_text),
            flags=re.M,
        )
        is not None,
        "poly.h must declare the exact poly_basemul ABI",
    )


def verify_basemul_jasmin(text: str) -> None:
    export_name = "jade_ntruplus_ntruplus768_amd64_ref_poly_basemul"
    require(
        extract_export_signature(text, export_name)
        == "export fn jade_ntruplus_ntruplus768_amd64_ref_poly_basemul( reg mut ptr u16[NTRUPLUS_N] rp, reg const ptr u16[NTRUPLUS_N] ap, reg const ptr u16[NTRUPLUS_N] bp) -> reg ptr u16[NTRUPLUS_N]",
        "unexpected Jasmin poly_basemul export ABI",
    )
    require(
        len(re.findall(r"\bexport\s+fn\b", strip_comments(text))) == 1,
        "poly_basemul.jazz must keep exactly one export",
    )


def verify_makefile_text(text: str) -> None:
    clean = strip_comments(text)
    flat = compact(text)
    require("-auto-spill-all" in clean, "Makefile must pin -auto-spill-all")
    require(
        re.search(r"^all:\s+check selfcheck run ubsan\s*$", clean, flags=re.M)
        is not None,
        "Makefile must keep all: check selfcheck run ubsan",
    )
    require(
        re.search(
            r"^\s*SLICE_BASEINV\s*:=\s*jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv\s*$",
            clean,
            flags=re.M,
        )
        is not None,
        "Makefile must pin the poly_baseinv export slice",
    )
    require(
        re.search(
            r"^\s*SLICE_BASEMUL\s*:=\s*jade_ntruplus_ntruplus768_amd64_ref_poly_basemul\s*$",
            clean,
            flags=re.M,
        )
        is not None,
        "Makefile must pin the poly_basemul export slice",
    )
    require(
        '"$(DRIVER)" "$(NTT_SOURCE)" "$(POLY_SOURCE)"' in flat,
        "Makefile run target must link the driver with ntt.c and poly.c",
    )
    require(
        '"$(NTT_SOURCE)" "$(POLY_SOURCE)" "$(KEM_SOURCE)"' not in flat,
        "Makefile must not link kem.c into the keygen_h runtime driver",
    )
    require(
        '"$(OUTDIR)/poly_baseinv.o" "$(OUTDIR)/poly_basemul.o"' in flat,
        "Makefile run target must link both Jasmin objects",
    )
    require(
        '$(CFLAGS) $(SANFLAGS) "$(DRIVER)" "$(NTT_SOURCE)" "$(POLY_SOURCE)"' in flat,
        "Makefile UBSan target must link the driver with ntt.c and poly.c",
    )
    require(
        '"$(OUTDIR)/poly_baseinv_ubsan.o" "$(OUTDIR)/poly_basemul_ubsan.o"' in flat,
        "Makefile UBSan target must link both Jasmin UBSan objects",
    )
    require(
        re.search(
            r'^\t"\$\(OUTDIR\)/keygen_h_driver"\s*$', clean, flags=re.M
        )
        is not None,
        "Makefile run target must execute keygen_h_driver",
    )
    require(
        re.search(
            r'^\t"\$\(OUTDIR\)/keygen_h_driver_ubsan"\s*$', clean, flags=re.M
        )
        is not None,
        "Makefile UBSan target must execute keygen_h_driver_ubsan",
    )


def verify_all(
    params_text: str,
    ntt_header_text: str,
    poly_header_text: str,
    ntt_text: str,
    poly_text: str,
    kem_text: str,
    baseinv_jasmin_text: str,
    basemul_jasmin_text: str,
    makefile_text: str,
) -> None:
    try:
        verify_sampler_sources(params_text, poly_header_text, poly_text, kem_text)
    except SamplerError as err:
        raise VerificationError(str(err)) from err
    try:
        verify_baseinv_c_sources(
            params_text,
            ntt_header_text,
            poly_header_text,
            ntt_text,
            poly_text,
            kem_text,
        )
        verify_baseinv_jasmin_source(baseinv_jasmin_text)
    except (BaseinvCError, BaseinvError) as err:
        raise VerificationError(str(err)) from err
    verify_poly_header(poly_header_text)
    verify_kem_prefix(kem_text)
    verify_basemul_jasmin(basemul_jasmin_text)
    verify_makefile_text(makefile_text)


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
    baseinv_jasmin_text: str,
    basemul_jasmin_text: str,
    makefile_text: str,
) -> int:
    verify_all(
        params_text,
        ntt_header_text,
        poly_header_text,
        ntt_text,
        poly_text,
        kem_text,
        baseinv_jasmin_text,
        basemul_jasmin_text,
        makefile_text,
    )

    mutations = [
        (
            "kem",
            "poly_basemul(&h, g, finv);",
            "poly_basemul(&h, f, finv);",
            "h left operand",
        ),
        (
            "kem",
            "poly_basemul(&hinv, f, ginv);",
            "poly_basemul(&hinv, g, ginv);",
            "hinv left operand",
        ),
        (
            "kem",
            "    poly_basemul(&h, g, finv);\n    poly_basemul(&hinv, f, ginv);\n",
            "    poly_basemul(&hinv, f, ginv);\n    poly_basemul(&h, g, finv);\n",
            "keypair_derand order",
        ),
        (
            "poly_header",
            "void poly_basemul(poly *r, const poly *a, const poly *b);",
            "void poly_basemul(poly *r, poly *a, const poly *b);",
            "poly_basemul const ABI",
        ),
        (
            "basemul_jasmin",
            "export fn jade_ntruplus_ntruplus768_amd64_ref_poly_basemul",
            "export fn jade_ntruplus_ntruplus768_amd64_ref_poly_basemul_mut",
            "Jasmin basemul export name",
        ),
        (
            "basemul_jasmin",
            "reg const ptr u16[NTRUPLUS_N] bp) -> reg ptr u16[NTRUPLUS_N]",
            "reg mut ptr u16[NTRUPLUS_N] bp) -> reg ptr u16[NTRUPLUS_N]",
            "Jasmin basemul third ABI",
        ),
        (
            "makefile",
            "SLICE_BASEMUL := jade_ntruplus_ntruplus768_amd64_ref_poly_basemul",
            "SLICE_BASEMUL := jade_ntruplus_ntruplus768_amd64_ref_poly_basemul_mut",
            "Makefile basemul slice",
        ),
        (
            "makefile",
            '"$(OUTDIR)/poly_baseinv.o" "$(OUTDIR)/poly_basemul.o"',
            '"$(OUTDIR)/poly_baseinv.o"',
            "missing basemul object",
        ),
        (
            "makefile",
            '"$(NTT_SOURCE)" "$(POLY_SOURCE)"',
            '"$(NTT_SOURCE)" "$(POLY_SOURCE)" "$(KEM_SOURCE)"',
            "extra production source",
        ),
        (
            "makefile",
            "-auto-spill-all",
            "",
            "auto-spill pin",
        ),
        (
            "makefile",
            "all: check selfcheck run ubsan",
            "all: check selfcheck run",
            "UBSan all-target coverage",
        ),
        (
            "makefile",
            '\t"$(OUTDIR)/keygen_h_driver"\n',
            "\t@true\n",
            "normal driver execution",
        ),
        (
            "makefile",
            '\t"$(OUTDIR)/keygen_h_driver_ubsan"\n',
            "\t@true\n",
            "UBSan driver execution",
        ),
        (
            "kem",
            "poly_tobytes(pk, &h);",
            "poly_tobytes(pk, &hinv);",
            "pk serialization source",
        ),
        (
            "kem",
            "poly_basemul(&hinv, f, ginv);",
            "poly_basemul(&hinv, f, finv);",
            "hinv right operand",
        ),
    ]

    originals = {
        "params": params_text,
        "ntt_header": ntt_header_text,
        "poly_header": poly_header_text,
        "ntt": ntt_text,
        "poly": poly_text,
        "kem": kem_text,
        "baseinv_jasmin": baseinv_jasmin_text,
        "basemul_jasmin": basemul_jasmin_text,
        "makefile": makefile_text,
    }
    for target, old, new, label in mutations:
        payload = [
            params_text,
            ntt_header_text,
            poly_header_text,
            ntt_text,
            poly_text,
            kem_text,
            baseinv_jasmin_text,
            basemul_jasmin_text,
            makefile_text,
        ]
        changed = mutate_once(originals[target], old, new, label)
        index = {
            "params": 0,
            "ntt_header": 1,
            "poly_header": 2,
            "ntt": 3,
            "poly": 4,
            "kem": 5,
            "baseinv_jasmin": 6,
            "basemul_jasmin": 7,
            "makefile": 8,
        }[target]
        payload[index] = changed
        expect_rejected(*payload, label=label)
    return len(mutations)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fail-closed checker for the NTRU+768 keygen h poly_basemul seam",
    )
    parser.add_argument("--params-source", required=True)
    parser.add_argument("--ntt-header", required=True)
    parser.add_argument("--poly-header", required=True)
    parser.add_argument("--ntt-source", required=True)
    parser.add_argument("--poly-source", required=True)
    parser.add_argument("--kem-source", required=True)
    parser.add_argument("--baseinv-jasmin", required=True)
    parser.add_argument("--basemul-jasmin", required=True)
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
    baseinv_jasmin_text = Path(args.baseinv_jasmin).read_text(encoding="utf-8")
    basemul_jasmin_text = Path(args.basemul_jasmin).read_text(encoding="utf-8")
    makefile_text = Path(args.makefile).read_text(encoding="utf-8")

    try:
        if args.self_check:
            count = run_self_check(
                params_text,
                ntt_header_text,
                poly_header_text,
                ntt_text,
                poly_text,
                kem_text,
                baseinv_jasmin_text,
                basemul_jasmin_text,
                makefile_text,
            )
            print(f"keygen_h checker self-check passed: {count} mutations rejected")
        else:
            verify_all(
                params_text,
                ntt_header_text,
                poly_header_text,
                ntt_text,
                poly_text,
                kem_text,
                baseinv_jasmin_text,
                basemul_jasmin_text,
                makefile_text,
            )
            print("keygen_h checker passed")
    except (OSError, VerificationError) as err:
        print(f"keygen_h checker failed: {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
