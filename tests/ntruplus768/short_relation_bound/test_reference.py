#!/usr/bin/env python3
"""Finite semantic diagnostics; none of these computations proves the theorem."""
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from math import isqrt


def reduced_product(a, b):
    n = len(a)
    half = n // 2
    assert n == len(b) and n == 2 * half
    coeffs = [0] * (2 * n - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            coeffs[i + j] += x * y
    for degree in range(len(coeffs) - 1, n - 1, -1):
        value = coeffs[degree]
        coeffs[degree - half] += value
        coeffs[degree - n] -= value
        coeffs[degree] = 0
    return coeffs[:n]


def block_entry(v, k, j):
    half = len(v) // 2
    i = j % half
    p = (k - i) % half
    if k < half:
        if i <= k:
            return v[p] if j < half else -v[p + half]
        return -v[p + half] if j < half else -(v[p] + v[p + half])
    if i <= k - half:
        return v[p + half] if j < half else v[p] + v[p + half]
    return v[p] + v[p + half] if j < half else v[p]


def main():
    records = []
    for n in (2, 4, 6):
        vectors = [tuple([0] * n), tuple([2] * n), tuple([-2] * n),
                   tuple(2 if i % 2 else -2 for i in range(n))]
        vectors.extend(tuple(2 if i == k else 0 for i in range(n)) for k in range(n))
        for v in vectors:
            for j in range(n):
                basis = [int(i == j) for i in range(n)]
                expected = reduced_product(basis, v)
                assert expected == [block_entry(v, k, j) for k in range(n)]
            assert all(sum(block_entry(v, k, j) ** 2 for j in range(n)) <= 16 * n
                       for k in range(n))
        records.append({'case': 'quotient-matrix-' + str(n), 'result': 'PASS',
                        'vectors': len(vectors)})
    for q in (3, 5):
        checked = 0
        for a, b, c, d in product(range(-2, 3), repeat=4):
            determinant = a * d - b * c
            if not determinant:
                continue
            fibers = Counter(((a * x + b * y) % q, (c * x + d * y) % q)
                             for x, y in product(range(q), repeat=2))
            assert max(fibers.values()) <= abs(determinant)
            checked += 1
        records.append({'case': 'all-small-matrix-fibers-mod-' + str(q),
                        'result': 'PASS', 'nonsingular_integer_matrices': checked})
    # A nonzero integer determinant need not give an invertible mod-q matrix.
    q = 7
    fibers = Counter((0, y) for x, y in product(range(q), repeat=2))
    assert fibers[(0, 0)] == 7
    assert Fraction(7, 49) > Fraction(1, 49)
    records.append({'case': 'nonunit-difference-rejects-q-to-minus-n', 'result': 'PASS'})
    n, q = 768, 3457
    numerator = 25 ** n * 12288 ** 384
    denominator = q ** n
    assert numerator * 2 ** 244 < denominator
    assert numerator * 2 ** 245 >= denominator
    assert Fraction(7680000, 11950849) < Fraction(9, 14)
    assert 9 ** 96 * 2 ** 61 < 14 ** 96
    assert all(q % divisor for divisor in range(2, isqrt(q) + 1))
    records.extend({'case': name, 'result': 'PASS'} for name in (
        'exact-coarse-bound-below-2-to-minus-244',
        'coarse-bound-does-not-justify-2-to-minus-245',
        'exact-rational-power-certificate', 'prime-3457-diagnostic'))
    print(json.dumps({'status': 'PASS', 'count': len(records), 'records': records,
                      'scope': 'Finite diagnostics only; no replacement for kernel-checked algebra or probability proofs.'}))


if __name__ == '__main__':
    main()
