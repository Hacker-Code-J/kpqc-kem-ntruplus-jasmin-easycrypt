#!/usr/bin/env python3
"""Exact finite diagnostics for joint setup and partial continuation; not a security proof."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import json


def weight(d):
    return sum(d.values(), F(0))


def push(d, fn):
    result = defaultdict(F)
    for x, mass in d.items():
        result[fn(x)] += mass
    return dict(result)


def bind(d, kernel):
    result = defaultdict(F)
    for x, mass in d.items():
        for y, chance in kernel(x).items():
            result[y] += mass*chance
    return dict(result)


def sdist(p, q):
    # Supremum over events for finite subdistributions, retaining mass loss.
    differences = [p.get(x, F(0))-q.get(x, F(0)) for x in p.keys() | q.keys()]
    return max(sum((x for x in differences if x > 0), F(0)),
               sum((-x for x in differences if x < 0), F(0)))


def normalize(d):
    assert weight(d) > 0
    return {x: mass/weight(d) for x, mass in d.items()}


def joint_setup(independent_tables=False):
    """Toy key=(E answer,F answer), with F indexed by the first key component."""
    result = defaultdict(F)
    bits = 4 if independent_tables else 2
    for values in product((0, 1), repeat=bits):
        e, f = values[:2]
        te, tf = values[2:] if independent_tables else (e, f)
        state = ((e, f), ((0, te),), ((e, tf),))
        result[state] += F(1, 2**bits)
    return dict(result)


def probe_joint(state):
    key, e, f = state
    return {dict(e)[0] == key[0] and dict(f)[key[0]] == key[1]: F(1)}


def erase_and_probe(state, erased):
    key, e, f = state
    result = defaultdict(F)
    for fresh in (0, 1):
        em, fm = dict(e), dict(f)
        if erased == 'E':
            em = {0: fresh}
        else:
            fm = {key[0]: fresh}
        result[em[0] == key[0] and fm[key[0]] == key[1]] += F(1, 2)
    return dict(result)


def paired_proposals(n):
    real, programmed = defaultdict(F), defaultdict(F)
    bad, mismatch = F(0), F(0)
    good_agreement = True
    for s0, s1, b0, b1 in product(range(n), range(n), (0, 1), (0, 1)):
        mass = F(1, n*n*4)
        re = {s0: b0}
        second = re.setdefault(s1, b1)
        pe = {s0: b0}
        pe[s1] = b1  # Independent second answer, including overwrite on a hit.
        r = ((b0, second), tuple(sorted(re.items())))
        p = ((b0, b1), tuple(sorted(pe.items())))
        real[r] += mass
        programmed[p] += mass
        bad += mass*(s0 == s1)
        mismatch += mass*(r != p)
        if s0 != s1:
            good_agreement &= r == p
    return dict(real), dict(programmed), bad, mismatch, good_agreement


def birthday(n, initial_size, queries):
    good = F(1)
    for i in range(queries):
        good *= F(max(0, n-initial_size-i), n)
    return 1-good


def stopped_script(qf, qg, draws, initial_e=None):
    """One shared count/table, accepting f=1 and g=0; all draws are specified."""
    e, counters = dict(initial_e or {}), [0, 0]
    iterator = iter(draws)
    f = None
    for phase, cap in enumerate((qf, qg)):
        accepted = None
        for _ in range(max(0, cap)):
            seed, answer = next(iterator)
            e[seed] = answer
            counters[phase] += 1
            if answer == (1 if phase == 0 else 0):
                accepted = answer
                break
        if accepted is None:
            return None, tuple(counters), e
        if phase == 0:
            f = accepted
    return (f, accepted), tuple(counters), e


def cached_retry_step(state):
    phase, cached_answer = state
    if phase == 0 and cached_answer == 1:
        return (1, cached_answer)
    if phase == 1 and cached_answer == 0:
        return None
    return state


class ToyOracles:
    """Toy tags/lengths are deliberately unrelated to NTRU+ byte encodings."""
    def __init__(self, e, f, entropy):
        self.tables = {b'E': dict(e), b'F': dict(f)}
        self.suffixes, self.other = {}, {}
        self.entropy, self.draws = iter(entropy), 0

    def draw(self):
        self.draws += 1
        return next(self.entropy)

    def typed(self, tag, key):
        table = self.tables[tag]
        if key not in table:
            table[key] = self.draw()
        return table[key]

    def raw(self, encoded, length):
        assert 0 <= length <= 2
        if len(encoded) == 2 and encoded[:1] in self.tables:
            prefix = self.typed(encoded[:1], encoded[1])
            if encoded not in self.suffixes:
                self.suffixes[encoded] = self.draw()
            result = bytes((prefix, self.suffixes[encoded]))
        else:
            if encoded not in self.other:
                self.other[encoded] = bytes((self.draw(), self.draw()))
            result = self.other[encoded]
        return result[:length]


def main():
    checks = []

    def check(name, condition):
        assert condition, name
        checks.append(name)

    joint, independent = joint_setup(), joint_setup(True)
    check('key-marginals-alone-cannot-detect-independent-setup-tables',
          sdist(push(joint, lambda x: x[0]), push(independent, lambda x: x[0])) == 0)
    check('joint-key-and-EF-law-retains-observable-correlation',
          sdist(joint, independent) == F(3, 4))
    check('same-continuation-distinguishes-the-lost-joint-correlation',
          bind(joint, probe_joint).get(True, 0) == 1
          and bind(independent, probe_joint).get(True, 0) == F(1, 4))
    check('erasing-E-after-keygen-breaks-repeat-query-consistency',
          bind(joint, lambda x: erase_and_probe(x, 'E')).get(True, 0) == F(1, 2))
    check('erasing-F-after-keygen-breaks-repeat-query-consistency',
          bind(joint, lambda x: erase_and_probe(x, 'F')).get(True, 0) == F(1, 2))

    real, programmed, bad, mismatch, good_equal = paired_proposals(4)
    check('no-collision-coupling-preserves-key-and-entire-table', good_equal)
    check('repeated-seed-can-change-the-programmed-key-and-table',
          bad == F(1, 4) and mismatch == F(1, 8))
    check('joint-distance-is-bounded-by-the-collision-event',
          sdist(real, programmed) == mismatch <= bad)
    old_table = {0: 0}
    real_answer = old_table[0]
    programmed_table = dict(old_table)
    programmed_answer = 1
    programmed_table[0] = programmed_answer
    check('programmed-hit-overwrites-with-the-latest-independent-answer',
          real_answer == 0 and programmed_table[0] == programmed_answer == 1)
    check('a-real-hit-is-deterministic-not-a-fresh-uniform-answer',
          sdist({old_table[0]: F(1)}, {0: F(1, 2), 1: F(1, 2)}) == F(1, 2))
    check('birthday-count-includes-collisions-across-f-and-g-phases',
          birthday(4, 0, 2) == F(1, 4)
          and birthday(4, 0, 1)+birthday(4, 0, 1) == 0)
    check('birthday-bound-retains-initial-cache-size-and-combined-query-count',
          all(birthday(n, a, q) <= min(F(1), F(a*q, n)+F(q*(q-1), 2*n))
              for n in range(1, 6) for a in range(n+1) for q in range(7)))
    result, counts, table = stopped_script(1, 2, ((0, 1), (1, 1), (2, 0)))
    check('g-rejection-retains-the-accepted-f-and-shared-table',
          result == (1, 0) and counts == (1, 2) and table == {0: 1, 1: 1, 2: 0})
    check('zero-f-budget-makes-no-proposal-and-preserves-existing-E',
          stopped_script(0, 2, (), {3: 1}) == (None, (0, 0), {3: 1}))
    check('zero-g-budget-retains-only-the-completed-f-draw',
          stopped_script(1, 0, ((0, 1),)) == (None, (1, 0), {0: 1}))
    # With one seed, cached 0 traps f forever; cached 1 traps g forever.
    trapped = [cached_retry_step((0, answer)) for answer in (0, 1)]
    check('real-ROM-repeated-seed-can-trap-an-unlimited-retry-stage',
          trapped == [(0, 0), (1, 1)]
          and all(cached_retry_step(state) == state for state in trapped))
    check('independent-programmed-retries-have-nonzero-finite-prefix-success',
          all((1-F(1, 2)**q)**2 > 0 for q in (1, 2, 4)))

    o = ToyOracles({0: 1}, {1: 0}, (0, 1, 0, 1, 0, 1))
    check('typed-E-query-uses-the-keygen-installed-entry', o.typed(b'E', 0) == 1 and o.draws == 0)
    raw_e = o.raw(b'E\x00', 2)
    check('typed-then-raw-E-query-shares-the-installed-prefix', raw_e[:1] == b'\x01' and o.draws == 1)
    check('raw-E-repeat-preserves-prefix-suffix-and-entropy-consumption',
          o.raw(b'E\x00', 1) == raw_e[:1] and o.raw(b'E\x00', 2) == raw_e and o.draws == 1)
    check('raw-then-typed-F-query-uses-the-same-installed-F-entry',
          o.raw(b'F\x01', 1) == b'\x00' and o.typed(b'F', 1) == 0)
    before = dict(o.tables[b'E'])
    o.raw(b'E\x00extra', 1)
    check('typed-tag-prefix-with-wrong-length-is-not-the-typed-input', o.tables[b'E'] == before)

    eps = F(1, 16)
    p, q = {'a': eps, 'c': 1-eps}, {'b': eps, 'c': 1-eps}
    kernel = lambda x: {0: F(1)} if x == 'a' else {1: F(1)} if x == 'b' else {}
    pp, qq = bind(p, kernel), bind(q, kernel)
    check('partial-continuation-retains-subdistribution-distance-and-missing-mass',
          sdist(pp, qq) == sdist(p, q) == eps and weight(pp) == weight(qq) == eps)
    check('conditioning-on-adversary-termination-can-amplify-distance-to-one',
          sdist(normalize(pp), normalize(qq)) == 1 > eps)
    check('missing-setup-mass-is-visible-even-with-identical-conditional-keys',
          sdist({'key': 1-eps}, {'key': F(1)}) == eps
          and sdist(normalize({'key': 1-eps}), {'key': F(1)}) == 0)
    check('returning-false-is-distinct-from-not-returning',
          sdist({False: F(1, 2)}, {}) == F(1, 2))
    grid = [{0: a, 1: b} for a, b in product((F(0), F(1, 2), F(1)), repeat=2) if a+b <= 1]
    contractions = 0
    for p, q, k0, k1 in product(grid, repeat=4):
        k = lambda x: k0 if x == 0 else k1
        assert sdist(bind(p, k), bind(q, k)) <= sdist(p, q)
        contractions += 1
    check('all-small-partial-kernels-contract-event-supremum-distance', contractions == 1296)
    check('data-processing-requires-the-same-continuation-in-both-worlds',
          sdist({0: F(1)}, {0: F(1)}) == 0
          and sdist(bind({0: F(1)}, lambda _: {0: F(1)}),
                    bind({0: F(1)}, lambda _: {1: F(1)})) == 1)
    delta, tau = F(512*511//2, 2**256), F(2, 2**256)
    check('selected-256-per-phase-coarse-budget-is-below-two-to-minus-239',
          delta+tau == F(130818, 2**256) < F(1, 2**239))
    print(json.dumps({'status': 'PASS', 'count': len(checks), 'checks': checks,
                      'scope': 'Exact toy diagnostics for joint-state and partial-law trust mistakes; not a cryptographic setup proof or IND-CCA reduction.',
                      'partial_kernel_cases': contractions,
                      'toy_joint_distance': str(sdist(joint, independent)),
                      'toy_key_marginal_distance': '0'}))


if __name__ == '__main__':
    main()
