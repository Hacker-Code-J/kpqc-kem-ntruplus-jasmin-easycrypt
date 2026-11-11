#!/usr/bin/env python3
"""Finite adapter/history diagnostics; not an adaptive security proof."""
from itertools import product
import json


class Store:
    def __init__(self):
        self.rows = []
        self.context = None

    def init(self, pk, suffix, star):
        self.rows = []
        self.context = (pk, suffix, star)

    def record(self, key, value):
        self.rows = [(key, value)] + [(k, v) for k, v in self.rows if k != key]


class Backend:
    def __init__(self):
        self.h_cache = {}
        self.calls = []

    def h(self, key):
        self.calls.append(("h", key))
        if key not in self.h_cache:
            self.h_cache[key] = bytes([len(self.h_cache) % 256]) * 224
        return self.h_cache[key]

    def raw(self, input, length):
        self.calls.append(("raw", input, length))
        return None if not 0 <= length <= 224 else bytes(length)

    def g(self, key, value):
        self.calls.append(("g", key))
        return "target" if value[0] == 1 else "other"


def typed_h(store, backend, key):
    value = backend.h(key)
    store.record(key, value)
    return value


def raw(store, backend, query, length):
    kind, key = query
    if 0 <= length <= 224 and kind == "H":
        return typed_h(store, backend, key)[:length]
    return backend.raw(query, length)


def decap(store, backend, ciphertext):
    _pk, suffix, star = store.context
    if ciphertext == star:
        return None
    for key, value in list(store.rows):
        if key[1] == suffix and backend.g(key, value) == ciphertext:
            return value[:32]
    return None


def main():
    records = []
    key = ("message", "suffix")
    cases = 0
    for length, kind in product((-1, 0, 1, 32, 223, 224, 225), ("H", "E", "F", "G", "malformed")):
        store, backend = Store(), Backend();store.init("pk", "suffix", "challenge")
        answer = raw(store, backend, (kind, key), length)
        if kind == "H" and 0 <= length <= 224:
            assert len(store.rows) == 1 and len(store.rows[0][1]) == 224
            assert len(answer) == length and backend.calls == [("h", key)]
        else:
            assert not store.rows and backend.calls == [("raw", (kind, key), length)]
        assert store.context == ("pk", "suffix", "challenge")
        cases += 1
    records.append({"case": "full-H-record-before-prefix-including-zero-and-invalid-forwarding", "inputs": cases, "result": "PASS"})
    store, backend = Store(), Backend();store.init("pk", "suffix", "challenge")
    ranks = []
    for mode in ("typed", "raw0", "raw224", "typed"):
        answer = typed_h(store, backend, key) if mode == "typed" else raw(store, backend, ("H", key), int(mode[3:]))
        ranks.append(len(store.rows))
        assert len(answer) in (0, 224)
    assert ranks == [1, 1, 1, 1] and len(backend.calls) == 4
    assert len(store.rows[0][1]) == 224
    records.append({"case": "repeat-calls-execute-backend-but-distinct-rank-does-not-grow", "result": "PASS"})
    other = ("second", "suffix");typed_h(store, backend, other)
    assert store.rows[0][0] == other and len(store.rows) == 2
    before = list(backend.calls)
    assert decap(store, backend, "challenge") is None and backend.calls == before
    assert decap(store, backend, "target") == bytes([1]) * 32
    assert backend.calls[-1] == ("g", other)
    records.append({"case": "persistent-list-challenge-block-and-internal-G-through-backend", "result": "PASS"})
    # Equal answers do not imply equal G transcripts: a failing row may be scanned first.
    left, right = Store(), Store();left.init("pk", "suffix", "challenge");right.init("pk", "suffix", "challenge")
    rows = [(key, bytes(224)), (other, bytes([1]) * 224)]
    left.rows = rows;right.rows = rows[::-1]
    b0, b1 = Backend(), Backend()
    assert decap(left, b0, "target") == decap(right, b1, "target")
    assert b0.calls == [("g", key), ("g", other)] and b1.calls == [("g", other)]
    records.append({"case": "same-reply-different-G-transcript-prevents-old-transcript-reuse", "result": "PASS"})
    # Distinct adapter instances have independent history despite sharing a backend.
    independent = Store();independent.init("pk2", "suffix2", "star2")
    typed_h(independent, backend, ("private2", "suffix2"))
    assert independent.context != store.context and len(independent.rows) == 1 and len(store.rows) == 2
    records.append({"case": "fresh-store-instance-separation", "result": "PASS"})
    print(json.dumps({"status": "PASS", "count": len(records), "records": records,
        "scope": "Finite reference diagnostics only; raw tags are abstract fixtures, compiler scope is checked separately, and no adaptive security, original-CCA, PPT or full runtime result follows from these tests."}))


if __name__ == "__main__":
    main()
