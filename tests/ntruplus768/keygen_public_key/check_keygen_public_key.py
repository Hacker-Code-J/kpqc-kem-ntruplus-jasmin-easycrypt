#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True

TEST_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TEST_ROOT / "baseinv"))
sys.path.insert(0, str(TEST_ROOT / "keygen_h"))
sys.path.insert(0, str(TEST_ROOT / "poly_baseinv_jasmin"))
sys.path.insert(0, str(TEST_ROOT / "poly_frombytes"))
sys.path.insert(0, str(TEST_ROOT / "poly_tobytes"))

from check_baseinv import VerificationError as BaseinvCError  # noqa: E402
from check_baseinv import verify_all as verify_baseinv_c_sources  # noqa: E402
from check_keygen_h import VerificationError as KeygenHError  # noqa: E402
from check_keygen_h import verify_basemul_jasmin as verify_poly_basemul_jasmin  # noqa: E402
from check_keygen_h import verify_poly_header as verify_keygen_poly_header  # noqa: E402
from check_poly_baseinv_jasmin import VerificationError as BaseinvError  # noqa: E402
from check_poly_baseinv_jasmin import verify_jasmin_source as verify_baseinv_jasmin_source  # noqa: E402
from check_poly_frombytes import VerificationError as FromBytesError  # noqa: E402
from check_poly_frombytes import verify_poly_frombytes_text  # noqa: E402
from check_poly_tobytes import VerificationError as ToBytesError  # noqa: E402
from check_poly_tobytes import verify_c_text as verify_poly_tobytes_c_text  # noqa: E402
from check_poly_tobytes import verify_jasmin_text as verify_poly_tobytes_jasmin_text  # noqa: E402


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
        body.count("poly_tobytes(pk, &h);") == 1,
        "crypto_kem_keypair_derand() must contain exactly one poly_tobytes(pk, &h)",
    )
    require(
        prefix in body,
        "crypto_kem_keypair_derand() must keep the exact h then hinv poly_basemul prefix before pk serialization",
    )


def verify_tobytes_jasmin(text: str) -> None:
    export_name = "jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes"
    require(
        extract_export_signature(text, export_name)
        == "export fn jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes( reg mut ptr u8[NTRUPLUS_POLYBYTES] rp, reg const ptr u16[NTRUPLUS_N] ap) -> reg ptr u8[NTRUPLUS_POLYBYTES]",
        "unexpected Jasmin poly_tobytes export ABI",
    )
    require(
        len(re.findall(r"\bexport\s+fn\b", strip_comments(text))) == 1,
        "poly_tobytes.jazz must keep exactly one export",
    )


def verify_makefile_text(text: str) -> None:
    clean = strip_comments(text)
    flat = compact(text)
    logical = compact(text.replace("\\\n", " "))

    require("-auto-spill-all" in clean, "Makefile must pin -auto-spill-all")
    require(
        re.search(r"^all:\s+check selfcheck run ubsan\s*$", clean, flags=re.M) is not None,
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
        re.search(
            r"^\s*SLICE_TOBYTES\s*:=\s*jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes\s*$",
            clean,
            flags=re.M,
        )
        is not None,
        "Makefile must pin the poly_tobytes export slice",
    )
    require(
        '"$(DRIVER)" "$(NTT_SOURCE)" "$(POLY_SOURCE)"' in logical,
        "Makefile run target must link the driver with ntt.c and poly.c",
    )
    require(
        '"$(NTT_SOURCE)" "$(POLY_SOURCE)" "$(KEM_SOURCE)"' not in logical,
        "Makefile must not link kem.c into the runtime driver",
    )
    require(
        '"$(OUTDIR)/poly_baseinv.o" "$(OUTDIR)/poly_basemul.o" "$(OUTDIR)/poly_tobytes.o"'
        in logical,
        "Makefile run target must link all three Jasmin objects",
    )
    require(
        '"$(OUTDIR)/poly_baseinv_ubsan.o" "$(OUTDIR)/poly_basemul_ubsan.o" "$(OUTDIR)/poly_tobytes_ubsan.o"'
        in logical,
        "Makefile UBSan target must link all three Jasmin UBSan objects",
    )
    require(
        re.search(
            r'^\t"\$\(OUTDIR\)/keygen_public_key_driver"\s*$',
            clean,
            flags=re.M,
        )
        is not None,
        "Makefile run target must execute keygen_public_key_driver",
    )
    require(
        re.search(
            r'^\t"\$\(OUTDIR\)/keygen_public_key_driver_ubsan"\s*$',
            clean,
            flags=re.M,
        )
        is not None,
        "Makefile UBSan target must execute keygen_public_key_driver_ubsan",
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
    tobytes_jasmin_text: str,
    makefile_text: str,
) -> None:
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
        verify_keygen_poly_header(poly_header_text)
        verify_poly_basemul_jasmin(basemul_jasmin_text)
        verify_poly_tobytes_c_text(poly_text, kem_text)
        verify_poly_tobytes_jasmin_text(tobytes_jasmin_text)
        verify_poly_frombytes_text(poly_text)
    except (KeygenHError, BaseinvCError, BaseinvError, ToBytesError, FromBytesError) as err:
        raise VerificationError(str(err)) from err

    verify_kem_prefix(kem_text)
    verify_tobytes_jasmin(tobytes_jasmin_text)
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
    tobytes_jasmin_text: str,
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
        tobytes_jasmin_text,
        makefile_text,
    )

    mutations = [
        (
            "kem",
            "poly_basemul(&h, g, finv);",
            "poly_basemul(&h, f, finv);",
            "h product left operand",
        ),
        (
            "kem",
            "poly_basemul(&hinv, f, ginv);",
            "poly_basemul(&hinv, g, ginv);",
            "hinv product left operand",
        ),
        (
            "kem",
            "poly_basemul(&hinv, f, ginv);\n\n    poly_tobytes(pk, &h);",
            "poly_tobytes(pk, &h);\n    poly_basemul(&hinv, f, ginv);",
            "pk serialization order",
        ),
        (
            "kem",
            "poly_tobytes(pk, &h);",
            "poly_tobytes(pk, &hinv);",
            "pk serialization source",
        ),
        (
            "kem",
            "poly_tobytes(pk, &h);",
            "poly_tobytes(pk, &h); poly_tobytes(pk, &h);",
            "duplicate pk serialization",
        ),
        (
            "tobytes",
            "jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes",
            "jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes_bad",
            "poly_tobytes export name",
        ),
        (
            "makefile",
            "all: check selfcheck run ubsan",
            "all: check run ubsan",
            "all target missing selfcheck",
        ),
        (
            "makefile",
            "SLICE_TOBYTES := jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes",
            "SLICE_TOBYTES := jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes_alt",
            "poly_tobytes slice",
        ),
        (
            "makefile",
            '"$(DRIVER)" "$(NTT_SOURCE)" "$(POLY_SOURCE)"',
            '"$(DRIVER)" "$(NTT_SOURCE)" "$(POLY_SOURCE)" "$(KEM_SOURCE)"',
            "runtime kem link",
        ),
        (
            "makefile",
            '"$(OUTDIR)/poly_baseinv.o" "$(OUTDIR)/poly_basemul.o" \\\n\t  "$(OUTDIR)/poly_tobytes.o" $(LDFLAGS) \\',
            '"$(OUTDIR)/poly_baseinv.o" "$(OUTDIR)/poly_basemul.o" $(LDFLAGS) \\',
            "missing poly_tobytes object",
        ),
    ]

    for source_name, old, new, label in mutations:
        payload = {
            "params": params_text,
            "ntt_header": ntt_header_text,
            "poly_header": poly_header_text,
            "ntt": ntt_text,
            "poly": poly_text,
            "kem": kem_text,
            "baseinv": baseinv_jasmin_text,
            "basemul": basemul_jasmin_text,
            "tobytes": tobytes_jasmin_text,
            "makefile": makefile_text,
        }
        payload[source_name] = mutate_once(payload[source_name], old, new, label)
        expect_rejected(
            payload["params"],
            payload["ntt_header"],
            payload["poly_header"],
            payload["ntt"],
            payload["poly"],
            payload["kem"],
            payload["baseinv"],
            payload["basemul"],
            payload["tobytes"],
            payload["makefile"],
            label=label,
        )

    return len(mutations)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fail-closed checker for the NTRU+768 keygen public-key serialization seam",
    )
    parser.add_argument("--params-source", required=True)
    parser.add_argument("--ntt-header", required=True)
    parser.add_argument("--poly-header", required=True)
    parser.add_argument("--ntt-source", required=True)
    parser.add_argument("--poly-source", required=True)
    parser.add_argument("--kem-source", required=True)
    parser.add_argument("--baseinv-jasmin", required=True)
    parser.add_argument("--basemul-jasmin", required=True)
    parser.add_argument("--tobytes-jasmin", required=True)
    parser.add_argument("--makefile", required=True)
    parser.add_argument("--self-check", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        params_text = Path(args.params_source).read_text(encoding="utf-8")
        ntt_header_text = Path(args.ntt_header).read_text(encoding="utf-8")
        poly_header_text = Path(args.poly_header).read_text(encoding="utf-8")
        ntt_text = Path(args.ntt_source).read_text(encoding="utf-8")
        poly_text = Path(args.poly_source).read_text(encoding="utf-8")
        kem_text = Path(args.kem_source).read_text(encoding="utf-8")
        baseinv_jasmin_text = Path(args.baseinv_jasmin).read_text(encoding="utf-8")
        basemul_jasmin_text = Path(args.basemul_jasmin).read_text(encoding="utf-8")
        tobytes_jasmin_text = Path(args.tobytes_jasmin).read_text(encoding="utf-8")
        makefile_text = Path(args.makefile).read_text(encoding="utf-8")

        verify_all(
            params_text,
            ntt_header_text,
            poly_header_text,
            ntt_text,
            poly_text,
            kem_text,
            baseinv_jasmin_text,
            basemul_jasmin_text,
            tobytes_jasmin_text,
            makefile_text,
        )

        if args.self_check:
            rejected = run_self_check(
                params_text,
                ntt_header_text,
                poly_header_text,
                ntt_text,
                poly_text,
                kem_text,
                baseinv_jasmin_text,
                basemul_jasmin_text,
                tobytes_jasmin_text,
                makefile_text,
            )
            print(f"keygen_public_key checker self-check passed ({rejected} mutations rejected)")
        else:
            print("keygen_public_key checker passed")
        return 0
    except (OSError, VerificationError) as err:
        print(f"keygen_public_key checker failed: {err}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
