#!/usr/bin/env python3
"""Exact finite diagnostics for E erasure; no toy result is a security proof."""
from fractions import Fraction as F
from itertools import product
import json

MAX_OUTPUT = 224
WITNESS = bytes((165,))*192  # A specified typed fallback, not a failure option.


def seed(i):
    return bytes((i,))+bytes(31)


def effective_raw_e(data, outlen):
    return data if len(data) == 32 and 0 <= outlen <= MAX_OUTPUT else None


class Backend:
    def __init__(self, initial=None):
        self.e_table = dict(initial or {})
        self.calls = []

    def e(self, s):
        assert len(s) == 32
        self.calls.append(('e', s))
        self.e_table.setdefault(s, bytes((s[0] ^ 90,))*192)
        return self.e_table[s]

    def raw(self, data, outlen):
        self.calls.append(('raw', data, outlen))
        if not 0 <= outlen <= MAX_OUTPUT:
            return None
        if len(data) == 32:
            return (self.e(data)+bytes(32))[:outlen]
        return bytes((119,))*outlen

    def other(self, name, data):
        self.calls.append((name, data))
        return name, data


class Port:
    def __init__(self, backend, cap, used=(), capped=True):
        self.backend, self.limit, self.used = backend, max(0, cap), tuple(used)
        self.capped = capped
        self.requests = self.forwarded = 0
        self.queries = []
        self.overflow = self.bad = False

    def request(self):
        allowed = self.requests < self.limit
        self.requests += 1
        self.overflow |= not allowed
        return allowed

    def forward(self, s):
        self.forwarded += 1
        self.queries.insert(0, s)
        self.bad |= s in self.used

    def e(self, s):
        allowed = self.request()
        if self.capped and not allowed:
            return WITNESS
        self.forward(s)
        return self.backend.e(s)

    def raw(self, data, outlen):
        s = effective_raw_e(data, outlen)
        allowed = True if s is None else self.request()
        if self.capped and not allowed:
            return None
        if s is not None:
            self.forward(s)
        return self.backend.raw(data, outlen)

    def other(self, name, data):
        return self.backend.other(name, data)


def programmed_trace(pool, answers, qf, qg, initial=None):
    table, used = dict(initial or {}), []
    cursor, counts = 0, [0, 0]
    accepted = [None, None]
    for phase, cap in enumerate((qf, qg)):
        for _ in range(cap):
            s, answer = pool[cursor], answers[cursor]
            cursor += 1
            counts[phase] += 1
            used.insert(0, s)
            table[s] = answer
            if answer == (1 if phase == 0 else 0):
                accepted[phase] = answer
                break
        if accepted[phase] is None:
            return None, tuple(counts), used, table
    return tuple(accepted), tuple(counts), used, table


def hit(pool, queries):
    return any(q in pool for q in queries)


def hit_probability(n, size, queries):
    return sum((F(1, n**size) for pool in product(range(n), repeat=size)
                if hit(pool, queries)), F(0))


def main():
    checks = []

    def check(name, condition):
        assert condition, name
        checks.append(name)

    s0, s1 = seed(0), seed(1)
    check('effective-raw-E-is-exactly-32-bytes-at-valid-output-lengths',
          all(effective_raw_e(s0, n) == s0 for n in (0, 1, 192, 224)))
    check('invalid-output-lengths-are-not-effective-E',
          all(effective_raw_e(s0, n) is None for n in (-1, 225)))
    check('tag-prefixes-and-nearby-input-lengths-do-not-create-extra-E-dispatch',
          all(effective_raw_e(data, 1) is None for data in (s0[:-1], s0+b'\x00', b'E'+s0)))
    backend = Backend()
    port = Port(backend, 3, (s0,))
    first = port.e(s0)
    zero = port.raw(s0, 0)
    repeat = port.raw(s0, 192)
    check('typed-repeat-and-zero-output-raw-E-share-one-counter',
          (port.requests, port.forwarded) == (3, 3) and zero == b'' and repeat == first)
    check('forwarded-query-log-retains-repetitions-and-hit-latch',
          port.queries == [s0, s0, s0] and port.bad)
    before = list(backend.calls), dict(backend.e_table)
    check('over-cap-typed-E-returns-witness-without-backend-call',
          port.e(s1) == WITNESS and (backend.calls, backend.e_table) == before)
    check('over-cap-raw-E-returns-None-without-backend-call',
          port.raw(s1, 0) is None and (backend.calls, backend.e_table) == before)
    check('blocked-E-attempts-still-increment-requests-not-forwarded',
          (port.requests, port.forwarded, port.overflow) == (5, 3, True))
    old_count = port.requests, port.forwarded, list(port.queries), port.bad
    invalid = port.raw(s1, -1)
    other = port.raw(b'other', 2)
    passthrough = port.other('g', b'input')
    check('invalid-and-non-E-requests-preserve-E-monitor-state',
          (port.requests, port.forwarded, port.queries, port.bad) == old_count
          and invalid is None and other == b'ww' and passthrough == ('g', b'input'))
    empty_backend = Backend()
    empty_cap = Port(empty_backend, -4)
    check('negative-budget-clamps-to-zero-and-forwards-no-E',
          empty_cap.e(s0) == WITNESS and empty_cap.raw(s0, 0) is None
          and empty_backend.calls == [] and empty_cap.forwarded == 0)
    observed_backend = Backend()
    counted = Port(observed_backend, 1, capped=False)
    counted.e(s0)
    counted.raw(s0, 0)
    check('counting-wrapper-observes-overflow-without-enforcing-the-cap',
          counted.requests == counted.forwarded == 2 and counted.overflow
          and len([call for call in observed_backend.calls if call[0] == 'e']) == 2)
    p0, p1 = Port(Backend(), 3, (s0,)), Port(Backend(), 3, (s1,))
    replies0 = p0.e(s0), p0.raw(s0, 2), p0.other('h', b'x')
    replies1 = p1.e(s0), p1.raw(s0, 2), p1.other('h', b'x')
    check('hidden-log-and-hit-latch-do-not-change-observable-replies-or-queries',
          replies0 == replies1 and p0.queries == p1.queries
          and p0.backend.calls == p1.backend.calls and p0.bad != p1.bad)

    pool = (0, 2, 0, 3, 1, 1)
    out, counts, used, table = programmed_trace(pool, (0, 1, 1, 0), 3, 3, {1: 9})
    check('setup-log-includes-rejected-and-accepted-seeds-in-reverse-order',
          out == (1, 0) and counts == (2, 2) and used == [3, 0, 2, 0])
    check('all-attempt-log-length-is-sum-of-f-and-g-counts-with-duplicates',
          len(used) == sum(counts) == 4 and len(set(used)) == 3)
    check('logging-only-accepted-seeds-misses-observable-rejected-seed-hits',
          0 in used and 0 not in (2, 3) and table[0] == 1)
    check('unused-pool-padding-is-never-programmed-over-an-existing-entry',
          used == list(reversed(pool[:sum(counts)])) and table[1] == 9)
    check('erased-model-must-preserve-nonempty-initial-E-outside-used-seeds',
          1 not in used and table[1] == 9 and {}.get(1) != table[1])
    reject = programmed_trace((0, 1), (0, 0), 2, 0)
    check('aborted-prefix-still-retains-every-rejected-attempt',
          reject[0] is None and reject[1] == (2, 0) and reject[2] == [1, 0])

    n, size = 4, 2
    check('iid-seed-pool-allows-duplicates',
          sum(F(1, n**size) for xs in product(range(n), repeat=size) if xs[0] == xs[1]) == F(1, n))
    check('union-hit-bound-allows-duplicate-queries-and-pool-entries',
          all(hit_probability(n, size, queries) <= F(size*len(queries), n)
              for count in range(3) for queries in product(range(n), repeat=count)))
    check('pure-hit-bound-also-allows-a-partial-independent-query-kernel',
          F(1, 3)*hit_probability(n, size, (0,)) == F(7, 48) <= F(size, n))
    # The visible tuple includes key, F state, retry count and fresh oracle coin.
    check('independent-pool-hit-bound-holds-conditionally-on-complete-visible-state',
          all(hit_probability(n, size, ((key+ftag+count+coin) % n,)) <= F(size, n)
              for key, ftag, count, coin in product(range(2), range(2), range(3), range(2))))
    check('key-only-independence-does-not-cover-F-state-that-leaks-the-seed',
          sum(F(1, n) for hidden in range(n) if hit((hidden,), (hidden,))) == 1 > F(1, n))
    count_leak = sum((F(1, n*n) for xs in product(range(n), repeat=2)
                      if hit(xs[:1+xs[0] % 2], (xs[0] % 2,))), F(0))
    check('retry-count-leakage-can-break-the-independent-query-kernel-bound',
          count_leak == F(9, 16) > F(size, n))
    no_hit_pools = [xs for xs in product(range(n), repeat=size) if not hit(xs, (0,))]
    check('conditioning-on-no-hit-does-not-preserve-the-original-iid-law',
          no_hit_pools and all(xs[0] != 0 for xs in no_hit_pools) and F(1, n) > 0)

    # A queries once, returns iff its answer matches a visible setup value,
    # and otherwise enters a no-query self-loop. It respects a cap of one.
    value_count = 4
    programmed_win = erased_win = returned_bad = reaching_hit = F(0)
    for hidden, visible_value, response in product(range(n), range(value_count), range(value_count)):
        mass = F(1, n*value_count*value_count)
        is_hit = hidden == 0
        p_response = visible_value if is_hit else response
        programmed_win += mass*(p_response == visible_value)
        erased_win += mass*(response == visible_value)
        returned_bad += mass*(is_hit and response == visible_value)
        reaching_hit += mass*is_hit
    check('a-query-cap-does-not-prevent-divergence-after-the-last-query',
          erased_win == F(1, 4) < 1)
    check('returned-bad-underestimates-game-distance-when-hit-branches-diverge',
          programmed_win-erased_win == F(3, 16) > returned_bad == F(1, 16))
    check('reaching-hit-probability-remains-larger-than-returned-bad',
          reaching_hit == F(1, 4) > returned_bad)

    def adaptive(p):
        answer = p.e(s0)
        return p.e(s1) if answer == bytes((1,))*192 else answer

    initial0 = {s0: bytes(192), s1: bytes((2,))*192}
    initial1 = {s0: bytes((1,))*192, s1: bytes((2,))*192}
    counted0, capped0 = Port(Backend(initial0), 1, capped=False), Port(Backend(initial0), 1)
    check('cap-removal-agrees-when-the-complete-counted-query-contract-holds',
          adaptive(counted0) == adaptive(capped0) and counted0.requests <= 1)
    counted1, capped1 = Port(Backend(initial1), 1, capped=False), Port(Backend(initial1), 1)
    check('a-query-contract-for-only-one-backend-state-is-insufficient',
          adaptive(counted1) != adaptive(capped1) and counted1.requests == 2 > 1)
    print(json.dumps({'status': 'PASS', 'count': len(checks), 'checks': checks,
                      'scope': 'Exact small-domain diagnostics; not an E-erasure game-hop proof or IND-CCA reduction.',
                      'hit_then_diverge': {'game_probability_difference': str(programmed_win-erased_win),
                                           'returned_bad_probability': str(returned_bad),
                                           'hit_reach_probability': str(reaching_hit)},
                      'count_leak_hit_probability': str(count_leak)}))


if __name__ == '__main__':
    main()
