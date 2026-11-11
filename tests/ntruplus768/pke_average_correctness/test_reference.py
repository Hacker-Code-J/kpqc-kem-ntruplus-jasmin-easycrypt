#!/usr/bin/env python3
"""Exact degree-2 ring and distribution diagnostics, not a PKE proof."""
from fractions import Fraction as F
from itertools import product
import json

Q = 7
TRITS = tuple(product((-1, 0, 1), repeat=2))


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def scale(n, a):
    return tuple(n*x for x in a)


def mul(a, b):
    # Integer quotient Z[X]/(X^2-X+1): X^2=X-1.
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]+a[1]*b[1]


def long_product(a, b):
    coefficients = [0]*3
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            coefficients[i+j] += x*y
    high = coefficients.pop()
    coefficients[1] += high
    coefficients[0] -= high
    return tuple(coefficients)


def mod(a):
    return tuple(x % Q for x in a)


def inverse(a):
    for b in product(range(Q), repeat=2):
        if mod(mul(a, b)) == (1, 0):
            return b
    return None


def canonical(a):
    return len(a) == 2 and all(0 <= x < Q for x in a)


def encrypt(h, m, r):
    return mod(add(mul(h, r), m)) if canonical(h) else None


def decrypt(ct, f):
    if not canonical(ct) or not canonical(f):
        return None
    centered = tuple((x+Q//2) % Q-Q//2 for x in mul(f, ct))
    return tuple((x+1) % 3-1 for x in centered)


def weight(a):
    return F((2 if a[0] == 0 else 1)*(2 if a[1] == 0 else 1), 16)


def main():
    checks = []
    def check(label, condition):
        assert condition, label
        checks.append(label)

    check('quotient-reduction-signs-match-independent-long-division',
          all(mul(a, b) == long_product(a, b) for a, b in product(TRITS, repeat=2)))
    check('degree-two-monomial-has-negative-constant', mul((0, 1), (0, 1)) == (-1, 1))
    check('CBD-message-law-is-normalized-and-not-uniform-on-trits',
          sum(map(weight, TRITS)) == 1 and weight((0, 0)) == F(1, 4) and weight((1, 1)) == F(1, 16))
    joint = {(m, r): weight(m)*weight(r) for m, r in product(TRITS, repeat=2)}
    check('message-and-randomness-are-independent-before-key-conditioning',
          sum(joint.values()) == 1 and joint[((0, 0), (1, 1))] == F(1, 64))
    check('reusing-message-as-randomness-changes-joint-law',
          joint[((0, 0), (1, 1))] > 0 and joint[((0, 0), (0, 0))] != weight((0, 0)))

    fshape = lambda a: (1+3*a[0], 3*a[1])
    finverses = {a: inverse(fshape(a)) for a in TRITS}
    ginverses = {a: inverse(scale(3, a)) for a in TRITS}
    check('scaled-g-and-unscaled-g-have-identical-unit-events',
          all((inverse(g) is None) == (ginverses[g] is None) for g in TRITS))
    check('scaled-g-inverse-requires-inverse-three-factor',
          all(ginverses[g] == mod(scale(pow(3, -1, Q), inverse(g)))
              for g in TRITS if inverse(g) is not None))
    check('unscaled-inverse-cannot-substitute-scaled-inverse',
          ginverses[(1, 0)] != inverse((1, 0)))

    accepted_f = {a: weight(a) for a in TRITS if finverses[a] is not None}
    accepted_g = {a: weight(a) for a in TRITS if ginverses[a] is not None}
    pf, pg = sum(accepted_f.values()), sum(accepted_g.values())
    p0 = sum(w for a, w in accepted_f.items() if a[0] == 0)/pf
    p1 = sum(w for a, w in accepted_f.items() if a[1] == 0)/pf
    together = accepted_f[(0, 0)]/pf
    check('whole-key-acceptance-correlates-coordinates', together != p0*p1)
    check('accepted-f-and-g-use-product-of-whole-conditional-laws',
          sum(wf*wg/(pf*pg) for wf in accepted_f.values() for wg in accepted_g.values()) == 1)

    nowrap_cases = 0
    bad_mass = F(0)
    raw_intersection_mass = F(0)
    valid_keys = 0
    for f0, g0 in product(accepted_f, accepted_g):
        f, g = fshape(f0), scale(3, g0)
        h = mod(mul(g, finverses[f0]))
        check_key = mod(mul(h, f)) == mod(g)
        assert check_key
        valid_keys += 1
        for m, r in product(TRITS, repeat=2):
            ct = encrypt(h, m, r)
            recovered = decrypt(ct, mod(f))
            lift = add(mul(f, m), mul(g, r))
            assert lift == add(m, scale(3, add(mul(f0, m), mul(g0, r))))
            if all(abs(x) <= Q//2 for x in lift):
                assert recovered == m
                nowrap_cases += 1
            if recovered != m:
                raw = weight(f0)*weight(g0)*weight(m)*weight(r)
                raw_intersection_mass += raw
                bad_mass += raw/(pf*pg)
    check('valid-key-no-wrap-recovery-holds-on-all-enumerated-cases', valid_keys > 0 and nowrap_cases > 0)
    check('average-failure-is-whole-buffer-conditioned-intersection',
          0 < bad_mass < 1 and bad_mass == raw_intersection_mass/(pf*pg))
    f0 = g0 = m = r = (-1, -1)
    f = fshape(f0); h = mod(mul(scale(3, g0), finverses[f0]))
    ct = encrypt(h, m, r)
    check('without-no-wrap-recovered-message-can-differ-from-input',
          decrypt(ct, mod(f)) == (-1, 0) and decrypt(ct, mod(f)) != m)
    check('canonical-ciphertext-alias-is-rejected-not-reduced', decrypt((ct[0]+Q, ct[1]), mod(f)) is None)
    check('noncanonical-secret-encoding-is-rejected', decrypt(ct, (mod(f)[0]+Q, mod(f)[1])) is None)
    check('noncanonical-public-key-is-rejected', encrypt((h[0]+Q, h[1]), m, r) is None)
    check('zero-recovered-message-is-a-successful-value', decrypt((0, 0), (1, 0)) == (0, 0))
    check('wrong-key-breaks-recovery-even-with-small-coefficients', decrypt((1, 0), (2, 0)) != (1, 0))
    check('no-wrap-alone-does-not-recover-a-nonternary-plaintext',
          decrypt(encrypt((3, 0), (2, 0), (0, 0)), (1, 0)) != (2, 0))

    check('actual-noise-threshold-575-is-inside-centered-range', 1+3*575 <= 1728)
    check('actual-noise-threshold-576-can-wrap-in-both-directions',
          1+3*576 > 1728 and -1-3*576 < -1728)
    check('noise-576-is-necessary-tail-bound-not-certain-failure', 3*576 == 1728)

    # A two-key, two-message failure matrix separates the expectation orders.
    failures = {(key, message): F(key == message) for key, message in product((0, 1), repeat=2)}
    average = sum(failures.values())/4
    max_after_mean = max(sum(failures[k, m] for k in (0, 1))/2 for m in (0, 1))
    mean_after_max = sum(max(failures[k, m] for m in (0, 1)) for k in (0, 1))/2
    check('average-correctness-does-not-imply-key-dependent-worst-message-bound',
          average == max_after_mean == F(1, 2) and mean_after_max == 1)
    print(json.dumps({'status':'PASS','count':len(checks),'checks':checks,
                      'toy_valid_keys':valid_keys,'toy_no_wrap_cases':nowrap_cases,
                      'toy_average_failure':str(bad_mass),
                      'scope':'Exact degree-2 quotient-ring surrogate over F7 and finite distribution counterexamples. Not NTRU+ parameter correctness, actual-call execution, worst-case correctness, or cryptographic proof.'}))


if __name__ == '__main__':
    main()
