#!/usr/bin/env python3
"""Small exact API counterexamples; diagnostics, not a cryptographic proof."""
from fractions import Fraction as F
import json


def status_reply(key, status):
    return ('Some', key) if status == 0 else None


def decode(raw):
    if len(raw) == 32:
        return 'E', raw
    if len(raw) == 1153 and raw[0] in (0, 1):
        return ('F' if raw[0] == 0 else 'G'), raw[1:]
    if len(raw) == 129 and raw[0] == 2:
        return 'H', raw[1:]
    return None


def coefficients(raw):
    return tuple(x for i in range(0, 1152, 3) for x in
                 (raw[i] + 256 * (raw[i+1] % 16), raw[i+1] // 16 + 16 * raw[i+2]))


class Gate:
    """Only models the exclusion gate; backend deliberately rejects every query."""
    def __init__(self, challenge):
        self.challenge, self.requests, self.backend = challenge, 0, 0
        self.tables = ({'cached': b'value'}, {}, {}, {})

    def decap(self, ct):
        self.requests += 1
        if self.challenge is not None and self.challenge == ct:
            return None
        self.backend += 1
        return None


class StreamReference:
    """Single deterministic tape per raw input; no random-oracle distribution claim."""
    def __init__(self):
        self.streams = {}

    def raw(self, query, length):
        if not 0 <= length <= 224:
            return None
        if query not in self.streams:
            offset = len(self.streams)
            self.streams[query] = bytes((i + offset) % 256 for i in range(224))
        return self.streams[query][:length]

    def typed(self, query):
        kind, _ = decode(query)
        return self.raw(query, {'E': 192, 'F': 32, 'G': 192, 'H': 224}[kind])


class BudgetReference:
    def __init__(self, limit, max_input):
        self.limit, self.max_input = max(0, limit), max(0, max_input)
        self.attempts = self.forwarded = 0
        self.core = StreamReference()

    def get(self, query, length):
        self.attempts += 1
        if self.attempts <= self.limit and len(query) <= self.max_input and 0 <= length <= 224:
            self.forwarded += 1
            return self.core.raw(query, length)
        return None


def complete_distribution(returned):
    # Missing mass has no dictionary entry, so the fallback cannot execute there.
    completed = {True: F(0), False: F(0)}
    for outcome, weight in returned.items():
        for fallback in (False, True):
            completed[fallback if outcome is None else outcome] += weight / 2
    return completed


def main():
    checks = []
    def check(label, condition):
        assert condition, label
        checks.append(label)

    zero = bytes(32)
    check('successful-zero-key-is-Some-not-None', status_reply(zero, 0) == ('Some', zero))
    check('failure-status-rejects-even-nonzero-key', status_reply(bytes([1])*32, 1) is None)
    check('nonzero-status-is-not-success', status_reply(zero, 2**32-1) is None)
    ct = bytes(1152)
    alias = bytes([129, 13]) + bytes(1150)  # coefficient 3457 is 0 only after reduction modulo q.
    check('noncanonical-alias-has-equal-residues-but-different-bytes',
          alias != ct and coefficients(alias)[0] == 3457 and
          tuple(x % 3457 for x in coefficients(alias)) == coefficients(ct))
    gate = Gate(ct)
    before = repr(gate.tables)
    check('exact-challenge-counted-without-backend-or-hash-effects',
          gate.decap(ct) is None and gate.requests == 1 and gate.backend == 0 and repr(gate.tables) == before)
    check('noncanonical-alias-is-forwarded-before-backend-rejection',
          gate.decap(alias) is None and gate.requests == 2 and gate.backend == 1)
    gate.decap(ct[:-1] + b'\1')
    check('challenge-exclusion-compares-last-byte', gate.backend == 2 and gate.requests == 3)
    absent = Gate(None); absent.decap(ct)
    check('absent-challenge-does-not-block-zero-ciphertext', absent.backend == 1)

    queries = {'E': bytes(32), 'F': b'\0'+ct, 'G': b'\1'+ct, 'H': b'\2'+bytes(128)}
    check('honest-tags-and-lengths-are-disjoint', all(decode(q)[0] == k for k, q in queries.items()))
    malformed = (b'\2'+ct, b'\0'+bytes(128), b'\0'+ct[:-1], b'\1'+ct+b'\0')
    check('wrong-tag-or-length-is-untyped-not-peeled', all(decode(q) is None for q in malformed))
    reference = StreamReference()
    for kind, query in queries.items():
        natural = reference.typed(query)
        full = reference.raw(query, 224)
        check('typed-then-raw-shared-prefix-'+kind, full[:len(natural)] == natural)
    reference = StreamReference()
    for kind, query in queries.items():
        full = reference.raw(query, 224)
        natural = reference.typed(query)
        check('raw-then-typed-shared-prefix-'+kind, full[:len(natural)] == natural)
    check('repeated-short-long-query-prefix-consistency', reference.raw(queries['F'], 13) == reference.raw(queries['F'], 224)[:13])
    before = dict(reference.streams)
    check('out-of-range-output-length-no-cache-effects',
          reference.raw(b'new', -1) is None and reference.raw(b'new', 225) is None and reference.streams == before)
    check('zero-output-is-empty-success-and-installs-stream', reference.raw(b'new', 0) == b'' and b'new' in reference.streams)
    check('maximum-output-length-is-224', len(reference.raw(b'new', 224)) == 224)
    reference.raw(malformed[0], 224); reference.raw(malformed[1], 224)
    check('malformed-inputs-preserve-complete-distinct-cache-keys', malformed[0] in reference.streams and malformed[1] in reference.streams)

    budget = BudgetReference(3, 32)
    check('invalid-output-consumes-attempt-without-forwarding',
          budget.get(bytes(32), 225) is None and budget.attempts == 1 and budget.forwarded == 0 and not budget.core.streams)
    check('oversized-input-consumes-attempt-without-forwarding',
          budget.get(bytes(33), 224) is None and budget.attempts == 2 and budget.forwarded == 0)
    check('budget-last-allowed-request-is-forwarded',
          budget.get(bytes(32), 224) is not None and budget.attempts == 3 and budget.forwarded == 1)
    before = dict(budget.core.streams)
    check('repeated-query-after-budget-is-rejected-without-cache-effects',
          budget.get(bytes(32), 1) is None and budget.attempts == 4 and budget.forwarded == 1 and budget.core.streams == before)
    check('zero-budget-forwards-no-requests', BudgetReference(0, 32).get(bytes(32), 0) is None)
    check('core-input-domain-remains-unbounded-by-optional-wrapper',
          StreamReference().raw(bytes(1154), 224) is not None)

    # A returned None gets a fair fallback; a diverging run returns no fallback.
    win, lose, abort = F(1, 8), F(1, 4), F(1, 8)
    mass = win + lose + abort
    completed = complete_distribution({True: win, False: lose, None: abort})
    completed_win = completed[True]
    check('fallback-preserves-subdistribution-return-mass', sum(completed.values()) == mass == F(1, 2))
    check('fallback-only-adds-half-returned-abort-mass', completed_win == F(3, 16))
    check('centering-at-return-mass-has-exact-signed-identity', completed_win-mass/2 == (win-lose)/2)
    check('centering-at-one-half-without-losslessness-is-false', completed_win-F(1, 2) != (win-lose)/2)
    check('divergence-does-not-become-fair-fallback', complete_distribution({}) == {True: 0, False: 0})
    check('returned-certain-setup-abort-completes-to-fair-bit',
          complete_distribution({None: F(1)}) == {True: F(1, 2), False: F(1, 2)})
    print(json.dumps({'status':'PASS','count':len(checks),'checks':checks,
                      'scope':'Finite deterministic API examples and exact rational subdistribution identities; not EasyCrypt or cryptographic proof.'}))


if __name__ == '__main__':
    main()
