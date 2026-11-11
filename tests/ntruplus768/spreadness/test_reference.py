#!/usr/bin/env python3
"""Exact tiny-ring diagnostics, not proofs for the cryptographic parameters.

Use F_5[x]/(x^2-1), two CBD1 coefficients, and a fixed two-bit message.
The G-average calculation enumerates each single-entry marginal exactly;
it does not replace an expectation by a statement about every realized G.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product
import json

TRITS = (-1, 0, 1)
POLYS = tuple(product(TRITS, repeat=2))
PADS = tuple(product((0, 1), repeat=4))
H = (2, 1)

def mul(a, b):
    return ((a[0]*b[0]+a[1]*b[1])%5, (a[0]*b[1]+a[1]*b[0])%5)

def enc(m, r, h=H):
    hr = mul(h, r)
    return tuple((m[i]+hr[i])%5 for i in range(2))

def center(x):
    return (x+2)%5-2

def cbd_mass():
    counts = Counter((bits[0]-bits[1], bits[2]-bits[3])
                     for bits in product((0, 1), repeat=4))
    return {r: F(count, 16) for r, count in counts.items()}

def encode(msg, pad):
    return tuple((pad[2*i] ^ msg[i])-pad[2*i+1] for i in range(2))

def test_CBD1_exact_mass_comes_from_two_uniform_bits():
    counts = Counter(a-b for a, b in product((0, 1), repeat=2))
    assert counts == {-1: 1, 0: 2, 1: 1}
    assert max(F(n, 4) for n in counts.values()) == F(1, 2)

def test_independent_fresh_CBD_vector_has_product_point_mass():
    mass = cbd_mass()
    single = {-1: F(1, 4), 0: F(1, 2), 1: F(1, 4)}
    assert set(mass) == set(POLYS)
    assert all(mass[r] == single[r[0]]*single[r[1]] for r in POLYS)
    assert max(mass.values()) == F(1, 4) and sum(mass.values()) == 1

def test_unit_public_key_is_injective_for_each_fixed_message():
    assert mul(H, (4, 3)) == (1, 0)
    mass = cbd_mass()
    for m in POLYS:
        pushed = Counter()
        for r, probability in mass.items():
            pushed[enc(m, r)] += probability
        assert len(pushed) == len(POLYS) and max(pushed.values()) == F(1, 4)

def test_nonunit_nonzero_public_key_does_not_give_injectivity():
    nonunit = (1, 1)
    assert nonunit != (0, 0) and mul(nonunit, (1, -1)) == (0, 0)
    mass_at_zero = sum(p for r, p in cbd_mass().items() if enc((0, 0), r, nonunit) == (0, 0))
    assert mass_at_zero == F(3, 8) > F(1, 4)

def test_injectivity_cannot_allow_the_message_to_change_with_randomness():
    m0, r0 = (1, 1), (0, 0)
    m1, r1 = (-1, 0), (1, 0)
    assert m0 in POLYS and m1 in POLYS and r0 != r1
    assert enc(m0, r0) == enc(m1, r1)

def test_G_averaged_point_bound_is_not_a_bound_for_every_fixed_G():
    mass = cbd_mass()
    msg = (0, 0)
    averaged = Counter()
    for r, probability in mass.items():
        for pad in PADS:
            averaged[enc(encode(msg, pad), r)] += probability/F(16)
    assert max(averaged.values()) <= F(1, 4)
    assert averaged[(0, 0)] == F(9, 128)
    # Fix a G table whose entries align three randomness values at zero.
    fixed_G = {}
    for r in POLYS:
        desired = tuple(center(-x) for x in mul(H, r))
        fixed_G[r] = next((p for p in PADS if encode(msg, p) == desired), (0, 0, 0, 0))
    realized = sum(p for r, p in mass.items() if enc(encode(msg, fixed_G[r]), r) == (0, 0))
    assert realized == F(3, 8) > F(1, 4) > averaged[(0, 0)]

def main():
    tests = sorted((name, value) for name, value in globals().items() if name.startswith('test_'))
    for _, test in tests:
        test()
    print(json.dumps({'status': 'PASS', 'count': len(tests),
                      'scope': 'independent exact finite diagnostics, not cryptographic proof',
                      'cases': [name for name, _ in tests]}))

if __name__ == '__main__':
    main()
