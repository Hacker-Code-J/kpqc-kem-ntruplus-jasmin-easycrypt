#!/usr/bin/env python3

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.dont_write_bytecode = True

TEST_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TEST_ROOT / "keygen_sampler"))
sys.path.insert(0, str(TEST_ROOT / "poly_baseinv_jasmin"))

from check_keygen_sampler import (  # noqa: E402
    VerificationError as SamplerVerificationError,
)
from check_keygen_sampler import verify_all as verify_sampler_sources  # noqa: E402
from check_poly_baseinv_jasmin import (  # noqa: E402
    VerificationError as PolyBaseInvVerificationError,
)
from check_poly_baseinv_jasmin import verify_jasmin_source  # noqa: E402


class VerificationError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def verify_makefile(text: str) -> None:
    require(
        "all: check selfcheck run ubsan" in text,
        "Makefile all target must retain normal and UBSan coverage",
    )
    require(
        "-auto-spill-all" in text,
        "Makefile must retain the poly_baseinv auto-spill contract",
    )
    require(
        "jade_ntruplus_ntruplus768_amd64_ref_poly_baseinv" in text,
        "Makefile must build the verified poly_baseinv export",
    )
    require(
        '"$(POLY_SOURCE)" "$(NTT_SOURCE)"' in text,
        "Makefile must link the production polynomial and NTT sources",
    )
    require(
        '"$(OUTDIR)/keygen_inverse_driver_ubsan"' in text and
        '\t"$(OUTDIR)/keygen_inverse_driver_ubsan"' in text,
        "Makefile must build and execute the UBSan composition binary",
    )


def verify_all(
    params: str,
    poly_header: str,
    poly_source: str,
    kem_source: str,
    jasmin_source: str,
    makefile: str,
) -> None:
    try:
        verify_sampler_sources(params, poly_header, poly_source, kem_source)
        verify_jasmin_source(jasmin_source)
    except (SamplerVerificationError, PolyBaseInvVerificationError) as exc:
        raise VerificationError(str(exc)) from exc
    verify_makefile(makefile)


def replace_once(text: str, old: str, new: str, label: str) -> str:
    changed = text.replace(old, new, 1)
    require(changed != text, f"could not construct mutation: {label}")
    return changed


def expect_rejected(payload: list[str], label: str) -> None:
    try:
        verify_all(*payload)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(
    params: str,
    poly_header: str,
    poly_source: str,
    kem_source: str,
    jasmin_source: str,
    makefile: str,
) -> int:
    values = [params, poly_header, poly_source, kem_source, jasmin_source, makefile]
    verify_all(*values)

    mutations = (
        (3, "shake256(buf, sizeof buf, coins, 32);", "shake256(buf, sizeof buf, coins, 31);", "f SHAKE input length"),
        (3, "f->coeffs[0] += 1;", "f->coeffs[0] += 0;", "f unit adjustment"),
        (3, "poly_ntt(f, f);", "poly_ntt(finv, f);", "f NTT destination"),
        (3, "return poly_baseinv(finv, f);", "return poly_baseinv(f, finv);", "f inverse arguments"),
        (3, "poly_ntt(g, g);", "poly_ntt(ginv, g);", "g NTT destination"),
        (3, "return poly_baseinv(ginv, g);", "return 0;", "g status propagation"),
        (4, "rp, status = __poly_baseinv_core(rp, ap);", "rp, status = __poly_baseinv_core(ap, rp);", "Jasmin export arguments"),
        (5, "-auto-spill-all", "", "auto-spill build contract"),
        (5, "all: check selfcheck run ubsan", "all: check selfcheck run", "UBSan all-target coverage"),
    )

    for index, old, new, label in mutations:
        payload = values.copy()
        payload[index] = replace_once(payload[index], old, new, label)
        expect_rejected(payload, label)

    print(f"keygen inverse checker self-check passed: {len(mutations)} mutations rejected")
    return 0


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Check the NTRU+768 keygen sampler-to-poly_baseinv composition seam"
    )
    parser.add_argument("--params-header", required=True)
    parser.add_argument("--poly-header", required=True)
    parser.add_argument("--poly-source", required=True)
    parser.add_argument("--kem-source", required=True)
    parser.add_argument("--jasmin-source", required=True)
    parser.add_argument("--makefile", required=True)
    parser.add_argument("--self-check", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        values = [
            Path(args.params_header).read_text(encoding="utf-8"),
            Path(args.poly_header).read_text(encoding="utf-8"),
            Path(args.poly_source).read_text(encoding="utf-8"),
            Path(args.kem_source).read_text(encoding="utf-8"),
            Path(args.jasmin_source).read_text(encoding="utf-8"),
            Path(args.makefile).read_text(encoding="utf-8"),
        ]
        if args.self_check:
            return run_self_check(*values)
        verify_all(*values)
        print("keygen inverse composition checker passed")
        return 0
    except (OSError, VerificationError) as exc:
        print(f"keygen inverse composition checker failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
