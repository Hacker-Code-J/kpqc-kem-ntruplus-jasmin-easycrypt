#!/usr/bin/env python3
"""Exact finite checks of integer lifting, pair norms and weighted reduction.

Small rings deliberately include zero divisors. These diagnostics are not
security estimates, a proof for NTRU+, or a worst-case Ring-SIS theorem.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from math import gcd
import json


def signed16(value):
    value %= 1 << 16
    return value if value < 1 << 15 else value - (1 << 16)


def integer_lift_and_norms():
    cases = 0
    for a, b in product((-1, 0, 1), repeat=2):
        decoded = signed16(a) - signed16(b)
        assert decoded == a - b and -2 <= decoded <= 2
        cases += 1
    assert signed16(1) - signed16(65535) == 2
    assert 1 - 65535 != 2  # Unsigned lifting changes the intended difference.
    assert signed16(-32768) - signed16(32767) == -65535
    assert signed16(-32768 - 32767) == 1  # Word subtraction is a different operation.

    norms = []
    for n in (1, 2, 4, 768):
        # With a=1, the two honest input pairs (m,r)=(-1,1),(1,-1)
        # both encrypt to zero. Their signed differences saturate 8*n.
        v, w = [2] * n, [-2] * n
        nv = sum(x * x for x in v)
        nw = sum(x * x for x in w)
        assert all(x + y == 0 for x, y in zip(v, w))
        assert max(map(abs, v + w)) == 2
        assert nv == nw == 4 * n and nv + nw == 8 * n
        assert nv + nw > 4 * n
        norms.append({"n": n, "first_squared_norm": nv, "second_squared_norm": nw,
                      "concatenated_squared_norm": nv + nw})
    q = 3457
    nonzero_integer = [q, 0]
    assert any(nonzero_integer) and not any(x % q for x in nonzero_integer)
    assert not all(-2 <= x <= 2 for x in nonzero_integer)
    for xs in product(range(-2, 3), repeat=3):
        assert (all(x % q == 0 for x in xs)) == (not any(xs))
    return {"trit_pairs": cases, "norm_witnesses": norms,
            "integer_nonzero_and_modular_nonzero_distinguished": True}


def scalar_collision(q, h, out):
    m0, m1, r0, r1 = out
    return (all(x in (-1, 0, 1) for x in out)
            and (m0, r0) != (m1, r1)
            and (h * r0 + m0 - h * r1 - m1) % q == 0)


def find_collision(q, h):
    pairs = tuple(product((-1, 0, 1), repeat=2))
    for (m0, r0), (m1, r1) in product(pairs, repeat=2):
        out = (m0, m1, r0, r1)
        if scalar_collision(q, h, out):
            return out
    return (0, 0, 0, 0)


def short_win(q, h, v, w):
    return -2 <= v <= 2 and -2 <= w <= 2 and (v != 0 or w != 0) and (h * v + w) % q == 0


def weighted_injectivity(q):
    values = range(q)
    psi = {q - 1: Q(1, 4), 0: Q(1, 2), 1: Q(1, 4)}
    unit = lambda x: gcd(x, q) == 1
    inverse = lambda x: pow(x, -1, q)
    shape = lambda x: (1 + 3 * x) % q
    scale = lambda x: 3 * x % q
    alpha_f = sum(p for x, p in psi.items() if unit(shape(x)))
    alpha_g = sum(p for x, p in psi.items() if unit(x))
    f_law = {shape(x): p / alpha_f for x, p in psi.items() if unit(shape(x))}
    g_law = {x: p / alpha_g for x, p in psi.items() if unit(x)}
    assert Counter(scale(x) for x in values) == Counter(values)
    attacks = {
        "first-collision": lambda h: find_collision(q, h),
        "only-three": lambda h: find_collision(q, h) if h == 3 else (0, 0, 0, 0),
        "only-one": lambda h: find_collision(q, h) if h == 1 else (0, 0, 0, 0),
        "duplicate": lambda h: (1, 1, -1, -1),
        "invalid-domain": lambda h: (2, 2, 0, 0),
    }
    rows = []
    missing_scale = signed_negative = extra_f_factor = False
    for name, attack in attacks.items():
        win = lambda h: scalar_collision(q, h, attack(h))
        actual = sum(pf * pg * win(scale(g * inverse(f) % q))
                     for f, pf in f_law.items() for g, pg in g_law.items())
        real = sum(pf * pg * win(scale(g * inverse(f) % q))
                   for f, pf in f_law.items() for g, pg in psi.items() if unit(g))
        wrong_scale = sum(pf * pg * win(g * inverse(f) % q)
                          for f, pf in f_law.items() for g, pg in psi.items() if unit(g))
        one_shot = sum(pf * pg * win(scale(g * inverse(shape(f0)) % q))
                       for f0, pf in psi.items() for g, pg in psi.items()
                       if unit(shape(f0)) and unit(g))
        uniform = sum(Q(1, q) * win(scale(h)) for h in values if unit(scale(h)))
        solver = Q(0)
        for a in values:
            out = attack(a) if unit(a) else (0, 0, 0, 0)
            pair = (out[2] - out[3], out[0] - out[1]) if scalar_collision(q, a, out) and unit(a) else (0, 0)
            solver += Q(1, q) * short_win(q, a, *pair)
        gap = real - uniform
        assert real == alpha_g * actual
        assert one_shot == alpha_f * alpha_g * actual
        assert uniform == solver
        assert alpha_g * actual == gap + solver
        assert actual <= (abs(gap) + solver) / alpha_g
        signed_negative |= gap < 0
        missing_scale |= wrong_scale != real
        extra_f_factor |= one_shot != real
        rows.append({"attack": name, "actual_INJ": str(actual), "real": str(real),
                     "uniform": str(uniform), "signed_NTRU_gap": str(gap), "short_solver": str(solver)})
    if q == 8:
        assert missing_scale and extra_f_factor
    if q == 7:
        assert signed_negative
    unit_mass = Q(sum(unit(a) for a in values), q)
    assert unit_mass < 1
    nonzero = next((Q(row["uniform"]) for row in rows if Q(row["uniform"])), None)
    if nonzero is not None:
        assert nonzero / unit_mass != nonzero
    return {"modulus": q, "alpha_f": str(alpha_f), "alpha_g": str(alpha_g),
            "missing_scale_detected": missing_scale, "extra_f_conditioning_detected": extra_f_factor,
            "signed_negative_gap_exercised": signed_negative, "attacks": rows}


def mul_phi6(a, b, q):
    # In Z_q[X]/(X^2-X+1), X^2=X-1.
    return ((a[0] * b[0] - a[1] * b[1]) % q,
            (a[0] * b[1] + a[1] * b[0] + a[1] * b[1]) % q)


def nonunit_difference_counterexample():
    q = 7
    ring = tuple(product(range(q), repeat=2))
    unit = lambda a: any(mul_phi6(a, b, q) == (1, 0) for b in ring)
    v, w = (2, 1), (-2, -1)
    assert not unit(v)
    matches = [a for a in ring if all((x + y) % q == 0 for x, y in zip(mul_phi6(a, v, q), w))]
    unit_matches = [a for a in matches if unit(a)]
    assert len(matches) == 7 and len(unit_matches) == 6
    assert Q(len(unit_matches), q * q) > Q(1, q * q)
    return {"ring": "F_7[X]/(X^2-X+1)", "v": v, "w": w,
            "all_solution_mass": str(Q(len(matches), q * q)),
            "unit_guarded_solution_mass": str(Q(len(unit_matches), q * q)),
            "incorrect_field_bound": str(Q(1, q * q))}


def main():
    lift = integer_lift_and_norms()
    weights = [weighted_injectivity(q) for q in (7, 8, 10)]
    nonunit = nonunit_difference_counterexample()
    checks = ["signed-word integer lift", "unsigned-lift counterexample", "word-wrap counterexample",
              "nonzero integer witness", "modular zero does not define integer nonzero",
              "bounded lifts cannot wrap modulo 3457", "both component norm bounds",
              "concatenated norm 8n versus erroneous 4n", "actual collision saturates pair bound",
              "raw g versus conditioned g mass", "f conditioning remains explicit", "factor-three mapping",
              "checked collision-to-short-relation solver", "whole uniform ring includes nonunits",
              "unit guard is not distribution conditioning", "signed NTRU orientation",
              "absolute advantage relaxation", "invalid/duplicate collision outputs rejected",
              "nonunit difference defeats q^-n even with unit-key guard"]
    print(json.dumps({"status": "PASS", "count": len(checks), "checks": checks,
                      "integer_norm_diagnostics": lift, "weighted_scalar_models": weights,
                      "nonunit_difference": nonunit,
                      "scope": "Finite diagnostics only; no NTRU+ hardness, statistical no-relation, iid Ring-SIS or worst-case lattice claim."}))


if __name__ == "__main__":
    main()
