#!/usr/bin/env python3
"""Small executable-history diagnostics; no mathematical or runtime proof claim."""
from itertools import product
import json


def byte_equal(left, right):
    assert len(left) == len(right)
    same = True
    comparisons = 0
    for a, b in zip(left, right):
        equal = a == b
        same = same and equal
        comparisons += 1
    return same, comparisons


def get(table, key):
    visits = comparisons = 0
    for candidate, value in table:
        match, count = byte_equal(candidate, key)
        visits += 1
        comparisons += count
        if match:
            return value, visits, comparisons
    return None, visits, comparisons


def put(table, key, value):
    reversed_kept = []
    comparisons = 0
    for candidate, old in table:
        match, count = byte_equal(candidate, key)
        comparisons += count
        if not match:
            reversed_kept.insert(0, (candidate, old))
    kept = []
    for entry in reversed_kept:
        kept.insert(0, entry)
    return [(key, value)] + kept, len(table) + len(kept), comparisons


def candidate_lookup(table, suffix, ciphertext, encrypt):
    visits = calls = 0
    for key, value in table:
        visits += 1
        if key[-1] == suffix:
            calls += 1
            if encrypt(key, value) == ciphertext:
                return value, visits, calls
    return None, visits, calls


def main():
    records = []
    key = bytes(128)
    for index in (0, 95, 96, 127):
        changed = bytearray(key); changed[index] = 1
        assert byte_equal(key, changed) == (False, 128)
    assert byte_equal(key, key) == (True, 128)
    for size in (32, 1152):
        left = bytes(size);right = bytearray(left);right[0] = 1
        assert byte_equal(left, right) == (False, size)
        assert byte_equal(left, left) == (True, size)
    records.append({"case": "key-boundaries-and-full-scan-after-mismatch", "result": "PASS"})
    alphabet = [bytes([x]) * 128 for x in range(3)]
    cases = 0
    for length in range(5):
        for trace in product(range(3), repeat=length):
            table, reference = [], {}
            for time, item in enumerate(trace):
                before = len(table)
                table, visits, comparisons = put(table, alphabet[item], time)
                reference[alphabet[item]] = time
                assert visits == before + len(table) - 1 and comparisons == 128 * before
                assert before <= visits <= 2 * before
                assert len(table) == len(reference) and len(table) <= before + 1
                assert len({key for key, _ in table}) == len(table)
                assert dict(table) == reference
            for query in alphabet:
                answer, visits, comparisons = get(table, query)
                assert answer == reference.get(query)
                assert 0 <= visits <= len(table) and comparisons == 128 * visits
            cases += 1
    records.append({"case": "empty-repeated-put-get-and-exact-counts", "traces": cases, "result": "PASS"})
    table = [(alphabet[0], 1), (alphabet[0], 2), (alphabet[1], 3)]
    updated, visits, comparisons = put(table, alphabet[0], 9)
    assert updated == [(alphabet[0], 9), (alphabet[1], 3)]
    assert visits == 4 and comparisons == 384
    records.append({"case": "put-removes-all-old-copies-and-preserves-other-order", "result": "PASS"})
    a, b = bytes([0, 7]), bytes([1, 7])
    table = [(a, 11), (b, 22)]
    forward = candidate_lookup(table, 7, b"ct", lambda _key, _value: b"ct")
    backward = candidate_lookup(table[::-1], 7, b"ct", lambda _key, _value: b"ct")
    assert forward[0] == 11 and backward[0] == 22 and forward[0] != backward[0]
    records.append({"case": "same-map-different-scan-order-can-change-answer", "result": "PASS"})
    good = [(a, 11), (b, 11)]
    assert candidate_lookup(good, 7, b"ct", lambda _k, _v: b"ct")[0] == candidate_lookup(good[::-1], 7, b"ct", lambda _k, _v: b"ct")[0]
    assert candidate_lookup(table, 9, b"ct", lambda _k, _v: b"ct")[1:] == (2, 0)
    records.append({"case": "agreement-needs-matching-payload-condition-suffix-skips-counted", "result": "PASS"})
    # Persistent tables process every input; overwrites do not grow the table.
    table = []; total_visits = total_bytes = 0
    for value in range(8):
        table, visits, count = put(table, alphabet[0], value)
        total_visits += visits; total_bytes += count
    assert len(table) == 1 and total_visits == 7 and total_bytes == 896
    records.append({"case": "repeated-builder-queries-and-table-growth", "result": "PASS"})
    for q in range(10):
        table = []; visits = comparisons = 0
        for value in range(q):
            table, v, c = put(table, bytes([value]) * 128, value)
            visits += v; comparisons += c
        assert visits == q * (q - 1) and comparisons == 64 * q * (q - 1)
    records.append({"case": "all-fresh-builder-visits-and-byte-count-upper-bounds", "result": "PASS"})
    for q in range(10):
        build_visits, build_bytes = q * (q - 1), 64 * q * (q - 1)
        for visits in range(q + 1):
            for encrypted in range(visits + 1):
                lookup_bytes = 1152 + 32 * visits + 1152 * encrypted
                assert build_visits + visits <= q * q
                assert build_bytes + lookup_bytes <= build_bytes + 1184 * q + 1152
                assert encrypted <= q
    records.append({"case": "public-build-plus-lookup-profile-composition", "result": "PASS"})
    print(json.dumps({"status": "PASS", "count": len(records), "records": records,
        "scope": "Finite diagnostics only. Python dict/slicing are reference specifications, not claims about the EasyCrypt implementation, all ROM tables, constant time, PPT or full security."}))


if __name__ == "__main__":
    main()
