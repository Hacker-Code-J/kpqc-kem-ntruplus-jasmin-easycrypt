#!/usr/bin/env python3
"""Exact small-ring diagnostics; these do not prove NTRU+ unit or Gen-law theorems."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import json

Q = 7
RING = tuple(product(range(Q), repeat=2))
ZERO, ONE = (0, 0), (1, 0)


def reduce_poly(p, n=2):
    result = [0]*n
    for i, x in enumerate(p):
        result[i % n] = (result[i % n]+x) % Q
    return tuple(result)


def mul(a, b):
    assert len(a) == len(b)
    result = [0]*(2*len(a)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i+j] += x*y
    return reduce_poly(result, len(a))


def scale(c, a):
    return tuple(c*x % Q for x in a)


def shape_f(a):
    result = list(scale(3, a))
    result[0] = (result[0]+1) % Q
    return tuple(result)


# Unit is an independent existential specification, not a status predicate.
INVERSES = {a: tuple(b for b in RING if mul(a, b) == ONE) for a in RING}


def unit(a):
    return bool(INVERSES[a])


def inverse_core(a):
    determinant = (a[0]*a[0]-a[1]*a[1]) % Q
    if determinant == 0:
        return ZERO, 1
    d = pow(determinant, -1, Q)
    return ((a[0]*d) % Q, (-a[1]*d) % Q), 0


def transform(a):
    return ((a[0]+a[1]) % Q, (a[0]-a[1]) % Q)


def inverse_transform(a):
    half = pow(2, -1, Q)
    return ((a[0]+a[1])*half % Q, (a[0]-a[1])*half % Q)


def public_solutions(f, g):
    return tuple(h for h in RING if mul(h, f) == scale(3, g))


def gen_key(f, g):
    solutions = public_solutions(f, g)
    return (solutions[0] if solutions else ZERO, f)


def pack(a):
    return (a[0] | (a[1] << 12)).to_bytes(3, 'little')


def unpack(b):
    if len(b) != 3:
        return None
    value = int.from_bytes(b, 'little')
    a = value & 4095, value >> 12
    return a if all(x < Q for x in a) else None


def byte_key(f0, g0, tag):
    fhat, ghat = transform(shape_f(f0)), transform(scale(3, g0))
    assert all(fhat)
    hhat = tuple(ghat[i]*pow(fhat[i], -1, Q) % Q for i in range(2))
    # Only the first secret-key block encodes f; the suffix is separate data.
    return pack(hhat), pack(fhat)+bytes((tag,))


def decode_key(key):
    pk, sk = key
    hhat, fhat = unpack(pk), unpack(sk[:3])
    assert hhat is not None and fhat is not None
    return inverse_transform(hhat), inverse_transform(fhat)


def push(d, fn):
    result = defaultdict(F)
    for x, mass in d.items():
        result[fn(x)] += mass
    return dict(result)


def condition(d, pred):
    mass = sum((p for x, p in d.items() if pred(x)), F(0))
    assert mass > 0
    return {x: p/mass for x, p in d.items() if pred(x)}


def product_law(p, q):
    return {(x, y): px*qy for x, px in p.items() for y, qy in q.items()}


def ec_degree(coefficients):
    return max((i+1 for i, c in enumerate(coefficients) if c % Q), default=0)


def main():
    checks = []

    def check(name, condition):
        assert condition, name
        checks.append(name)

    check('existential-unit-agrees-with-independent-determinant-status',
          all((inverse_core(a)[1] == 0) == unit(a) for a in RING))
    check('successful-status-produces-a-real-multiplicative-inverse',
          all(mul(a, inverse_core(a)[0]) == ONE for a in RING if inverse_core(a)[1] == 0))
    check('whole-inverse-core-rejection-has-status-one-and-zero-output',
          all(inverse_core(a) == (ZERO, 1) for a in RING if not unit(a)))
    left, right = (Q-1, 1), (1, 1)
    check('nonzero-polynomial-is-not-equivalent-to-a-unit',
          left != ZERO and right != ZERO and mul(left, right) == ZERO
          and not unit(left) and not unit(right))
    quartic_left, quartic_right = (Q-1, 0, 1, 0), (1, 0, 1, 0)
    check('quartic-blocks-also-have-nonzero-zero-divisors',
          mul(quartic_left, quartic_right) == (0, 0, 0, 0)
          and quartic_left != (0, 0, 0, 0) and quartic_right != (0, 0, 0, 0))
    check('finite-ring-unit-count-is-smaller-than-nonzero-element-count',
          sum(unit(a) for a in RING) == 36 < len(RING)-1)
    check('multiplication-by-a-unit-is-an-injective-and-surjective-endomap',
          all((len({mul(a, b) for b in RING}) == len(RING)) == unit(a) for a in RING))
    check('larger-codomain-invalidates-finite-injection-to-surjection',
          len({0, 1, 2}) == 3 and {0, 1, 2} < {0, 1, 2, 3})
    check('canonical-transform-is-a-bijection-on-the-same-carrier',
          {transform(a) for a in RING} == set(RING)
          and all(inverse_transform(transform(a)) == a for a in RING))
    check('all-terminal-factors-must-be-invertible',
          any(a != ZERO and (0 in transform(a)) and not unit(a) for a in RING))
    check('scaling-g-by-three-preserves-unit-acceptance',
          all(unit(scale(3, a)) == unit(a) for a in RING))
    check('three-scaling-remains-essential-in-the-public-key-equation',
          gen_key(ONE, ONE)[0] == (3, 0) != ONE)
    check('f-constant-one-cannot-be-dropped-from-the-shape',
          shape_f(ZERO) == ONE and unit(shape_f(ZERO)) and not unit(scale(3, ZERO)))
    check('valid-unit-f-gives-existence-and-uniqueness-of-canonical-h',
          all(len(public_solutions(f, g)) == 1 for f in RING if unit(f) for g in RING))
    check('nonunit-f-can-make-the-public-equation-unsatisfiable',
          not public_solutions(left, ONE))
    check('nonunit-f-can-make-the-public-equation-nonunique',
          len(public_solutions(left, ZERO)) > 1)
    high_alias = (ONE[0]-1, ONE[1], 1)
    check('quotient-equality-alone-does-not-fix-a-polynomial-representative',
          reduce_poly(high_alias) == ONE and high_alias != ONE and ec_degree(high_alias) > 2)
    check('coefficient-list-degree-bound-includes-the-highest-basis-monomial',
          ec_degree(ZERO) == 0 and ec_degree(ONE) == 1 and ec_degree((0, 1)) == 2)

    bit_difference = {Q-1: F(1, 4), 0: F(1, 2), 1: F(1, 4)}
    cbd = product_law(bit_difference, bit_difference)
    df, dg = condition(cbd, lambda a: unit(shape_f(a))), condition(cbd, unit)
    check('acceptance-conditions-the-whole-polynomial',
          all(unit(g) for g in dg) and sum(dg.values(), F(0)) == 1)
    g0, g1 = push(dg, lambda a: a[0]), push(dg, lambda a: a[1])
    check('accepted-coordinates-can-keep-CBD-marginals-while-losing-independence',
          g0 == g1 == bit_difference and dg != product_law(g0, g1))
    check('product-of-accepted-coordinate-marginals-can-reintroduce-nonunits',
          sum(p for a, p in product_law(g0, g1).items() if not unit(a)) == F(1, 2))
    separate = product_law(df, dg)
    joint = condition(product_law(cbd, cbd), lambda fg: unit(shape_f(fg[0])) and unit(fg[1]))
    check('separate-rejection-stages-give-independent-whole-conditioned-polynomials', joint == separate)
    figure_law = push(separate, lambda fg: gen_key(shape_f(fg[0]), fg[1]))
    decoded_law = push(separate, lambda fg: decode_key(byte_key(fg[0], fg[1], 0)))
    check('public-byte-API-decoded-hf-law-matches-independent-Gen-choice', decoded_law == figure_law)
    terminal_law = push(separate, lambda fg: (unpack(byte_key(fg[0], fg[1], 0)[0]),
                                             unpack(byte_key(fg[0], fg[1], 0)[1][:3])))
    check('forgetting-inverse-NTT-changes-the-key-projection-law', terminal_law != figure_law)
    check('secret-suffix-is-excluded-from-the-hf-projection-not-erased',
          all(decode_key(byte_key(f0, g, 0)) == decode_key(byte_key(f0, g, 1))
              and byte_key(f0, g, 0)[1] != byte_key(f0, g, 1)[1] for f0, g in separate))
    check('canonical-byte-decoder-rejects-mod-q-aliases',
          unpack(pack((Q+1, 0))) is None and unpack(pack(ONE)) == ONE)
    # Programmed table writes do not change the accepted sampled polynomials.
    programmed_joint = {}
    for (f0, g), mass in separate.items():
        key = decode_key(byte_key(f0, g, 1))
        programmed_joint[(key, ((0, f0), (1, g)))] = mass
    check('programmed-table-installation-preserves-the-hf-marginal',
          push(programmed_joint, lambda s: s[0]) == figure_law)
    recover_fg = lambda key: (scale(pow(3, -1, Q), ((key[1][0]-1) % Q, key[1][1])),
                              scale(pow(3, -1, Q), mul(key[0], key[1])))
    check('programmed-key-and-table-remain-correlated-after-marginal-equality',
          all(recover_fg(key) == (dict(table)[0], dict(table)[1]) for key, table in programmed_joint)
          and sum(mass*mass for mass in separate.values()) < 1)
    iid_pair = product_law({0: F(1, 2), 1: F(1, 2)}, {0: F(1, 2), 1: F(1, 2)})
    cached_pair = {(0, 0): F(1, 2), (1, 1): F(1, 2)}
    check('actual-ROM-repeated-seed-law-is-not-the-independent-fresh-law', cached_pair != iid_pair)
    trits = (-1, 0, 1)
    check('ternary-shaping-needs-no-signed-word-overflow',
          all(-32768 <= 3*x+c < 32768 for x in trits for c in (0, 1)))
    integer = 3*32767+1
    word = integer % 65536
    signed = word if word < 32768 else word-65536
    check('dropping-the-trit-range-can-break-shaped-integer-field-equality',
          signed != integer and signed % 3457 != integer % 3457)
    check('real-modulus-three-is-a-unit-but-packing-modulus-is-not-the-field',
          (3*pow(3, -1, 3457)) % 3457 == 1 and 3457 % 4096 != 0)
    print(json.dumps({'status': 'PASS', 'count': len(checks), 'checks': checks,
                      'scope': 'Exact finite quotient-ring diagnostics; not the NTRU+ unit iff, byte-level Gen theorem, or an oracle independence proof.',
                      'toy_modulus': Q, 'toy_ring_elements': len(RING),
                      'toy_accepted_key_pairs': len(figure_law)}))


if __name__ == '__main__':
    main()
