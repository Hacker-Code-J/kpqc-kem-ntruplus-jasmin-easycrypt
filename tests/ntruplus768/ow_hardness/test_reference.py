#!/usr/bin/env python3
"""Exact finite diagnostics of conditioning and the computational RLWE target.

Composite scalar rings expose nonunits explicitly. These are sanity checks,
not NTRU+ security proofs or evidence of cryptographic hardness.
"""
from collections import Counter
from fractions import Fraction as Q
from math import gcd
import json


def weighted_reduction(modulus):
    ring = range(modulus)
    psi = {modulus - 1: Q(1, 4), 0: Q(1, 2), 1: Q(1, 4)}
    unit = lambda x: gcd(x, modulus) == 1
    inverse = lambda x: pow(x, -1, modulus)
    scale = lambda x: 3 * x % modulus
    fshape = lambda x: (1 + 3 * x) % modulus
    alpha_f = sum(p for x, p in psi.items() if unit(fshape(x)))
    alpha_g = sum(p for x, p in psi.items() if unit(x))
    f_law = {fshape(x): p / alpha_f for x, p in psi.items() if unit(fshape(x))}
    g_law = {x: p / alpha_g for x, p in psi.items() if unit(x)}
    assert 0 < alpha_f <= 1 and 0 < alpha_g < 1
    assert sum(f_law.values()) == sum(g_law.values()) == 1
    assert Counter(scale(x) for x in ring) == Counter(ring)
    assert all(unit(scale(x)) == unit(x) for x in ring)
    assert any(not unit(x) for x in ring)
    assert {scale(x): p for x, p in psi.items()} != psi

    adversaries = {
        "zero": lambda h, c: 0,
        "one": lambda h, c: 1,
        "ciphertext": lambda h, c: c,
        "linear": lambda h, c: (h + c) % modulus,
        "double-ciphertext": lambda h, c: 2 * c % modulus,
        "key-dependent": lambda h, c: 1 if h == 3 else 0,
    }
    rows = []
    scale_counterexample = False
    nonunit_extra_success = False
    for name, attack in adversaries.items():
        def ow(h):
            return sum(pr * pm for r, pr in psi.items() for m, pm in psi.items()
                       if attack(h, (h * r + m) % modulus) == m)

        actual = sum(pf * pg * ow(scale(g * inverse(f) % modulus))
                     for f, pf in f_law.items() for g, pg in g_law.items())
        real = sum(pf * pg * ow(scale(g * inverse(f) % modulus))
                   for f, pf in f_law.items() for g, pg in psi.items() if unit(g))
        real_without_scale = sum(pf * pg * ow(g * inverse(f) % modulus)
                                 for f, pf in f_law.items() for g, pg in psi.items() if unit(g))
        one_shot = sum(pf * pg * ow(scale(g * inverse(fshape(f0)) % modulus))
                       for f0, pf in psi.items() for g, pg in psi.items()
                       if unit(fshape(f0)) and unit(g))
        uniform = sum(Q(1, modulus) * ow(scale(z)) for z in ring if unit(z))
        uniform_plain = sum(Q(1, modulus) * ow(h) for h in ring if unit(h))
        rlwe = Q(0)
        rlwe_unit = Q(0)
        for a in ring:
            for secret, ps in psi.items():
                for error, pe in psi.items():
                    b = (a * secret + error) % modulus
                    recovered = (inverse(a) * (b - attack(a, b)) % modulus) if unit(a) else 0
                    mass = Q(1, modulus) * ps * pe
                    rlwe += mass * (recovered == secret)
                    if unit(a):
                        rlwe_unit += mass * (recovered == secret)
        advantage_signed = real - uniform
        advantage_absolute = abs(advantage_signed)
        assert real == alpha_g * actual
        assert one_shot == alpha_f * alpha_g * actual
        assert uniform == uniform_plain == rlwe_unit
        assert alpha_g * actual == advantage_signed + uniform
        assert alpha_g * actual <= advantage_signed + rlwe
        assert alpha_g * actual <= advantage_absolute + rlwe
        assert actual <= (advantage_absolute + rlwe) / alpha_g
        scale_counterexample |= real_without_scale != real
        nonunit_extra_success |= rlwe > uniform
        rows.append({"adversary": name, "ow": str(actual), "weighted_ow": str(real),
                     "uniform_guarded": str(uniform), "ntru_signed": str(advantage_signed),
                     "rlwe": str(rlwe), "one_shot_f": str(one_shot)})
    assert nonunit_extra_success
    if modulus in (10, 14):
        assert alpha_f < 1 and scale_counterexample
    # A valid OW output is the RLWE error, not the secret itself.
    a, secret, error = 1, 1, 0
    b = (a * secret + error) % modulus
    recovered_error = adversaries["zero"](a, b)
    assert recovered_error == error and recovered_error != secret
    assert inverse(a) * (b - recovered_error) % modulus == secret
    # Conditioning uniform a on units would silently renormalize the mass.
    unit_mass = Q(sum(unit(a) for a in ring), modulus)
    assert 0 < unit_mass < 1
    assert Q(rows[0]["uniform_guarded"]) / unit_mass != Q(rows[0]["uniform_guarded"])
    return {"modulus": modulus, "alpha_f": str(alpha_f), "alpha_g": str(alpha_g),
            "unit_mass": str(unit_mass), "missing_scale_detected": scale_counterexample,
            "nonunit_fallback_can_succeed": nonunit_extra_success, "cases": rows}


def main():
    results = [weighted_reduction(m) for m in (10, 14, 35)]
    assert len({3 * x % 6 for x in range(6)}) < 6  # Scaling needs a unit scalar.
    checks = ["f-conditioned denominator", "g-unit conditioning weight", "one-shot f requires extra alpha_f",
              "weighted real-distinguisher identity", "signed NTRU orientation", "absolute NTRU upper bound",
              "full-ring uniform includes nonunits", "unit guard preserves unnormalized mass",
              "factor-three uniform permutation", "factor-three cannot be absorbed into psi",
              "missing factor-three detection", "nonunit scalar is not a permutation",
              "OW plaintext is RLWE error", "inverse converts recovered error to secret",
              "nonunit fallback gives inequality not unconditional equality", "division by positive acceptance mass"]
    print(json.dumps({"status": "PASS", "count": len(checks), "checks": checks,
                      "finite_composite_rings": results,
                      "scope": "Exact finite sanity checks only; no NTRU+ proof, lattice hardness claim, or PPT certification."}))


if __name__ == "__main__":
    main()
