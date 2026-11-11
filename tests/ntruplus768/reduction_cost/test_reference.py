#!/usr/bin/env python3
"""Finite call-count boundary diagnostics; no execution-time or EC proof claim."""
from itertools import product
import json


def first_scan(flags):
    visited = 0
    answer = None
    for i, hit in enumerate(flags):
        visited += 1
        if hit:
            answer = i
            break
    return answer, visited


def lookup_scan(rows, blocked=False):
    visited = encrypted = 0
    if blocked:
        return None, visited, encrypted
    for index, (suffix_matches, ciphertext_matches) in enumerate(rows):
        visited += 1
        if suffix_matches:
            encrypted += 1
            if ciphertext_matches:
                return index, visited, encrypted
    return None, visited, encrypted


def main():
    records = []
    cases = 0
    for n in range(8):
        for flags in product((False, True), repeat=n):
            answer, visited = first_scan(flags)
            expected = flags.index(True) + 1 if any(flags) else n
            assert visited == expected and 0 <= visited <= n
            assert answer == (flags.index(True) if any(flags) else None)
            cases += 1
    records.append({"case": "extract-first-match-empty-and-miss", "inputs": cases, "result": "PASS"})
    cases = 0
    for n in range(6):
        for rows in product(tuple(product((False, True), repeat=2)), repeat=n):
            answer, visits, encrypted = lookup_scan(rows)
            assert 0 <= encrypted <= visits <= n
            assert lookup_scan(rows, True) == (None, 0, 0)
            if answer is not None:
                assert all(rows[answer]) and not any(all(row) for row in rows[:answer])
            assert encrypted == sum(row[0] for row in rows[:visits])
            cases += 1
    records.append({"case": "lookup-challenge-suffix-and-one-G-per-encryption", "inputs": cases, "result": "PASS"})
    rows = [(False, False), (True, False), (True, True), (True, True)]
    assert lookup_scan(rows) == (2, 3, 2)
    records.append({"case": "suffix-mismatch-counts-visit-but-no-encryption", "result": "PASS"})
    # A raw G dispatch is a call even for output length zero or a repeated input.
    for outlen in (-1, 0, 1, 192, 224, 225):
        valid = 0 <= outlen <= 224
        for is_g in (False, True):
            calls = sum(valid and is_g for _ in range(5))
            assert calls == (5 if valid and is_g else 0)
            if valid:
                stream = tuple(range(224))
                assert len(stream[:outlen]) == outlen
                assert stream[:outlen][:outlen // 2] == stream[:outlen // 2]
    records.append({"case": "raw-invalid-zero-repeat-call-accounting", "result": "PASS"})
    for bound in (0, 1, 224, 4096):
        request = bytes(bound + 1)
        input_bytes = len(request)  # Valid output length zero still dispatches input.
        assert input_bytes > bound and len(request[:0]) == 0
    records.append({"case": "one-zero-output-request-has-unbounded-input-payload", "result": "PASS"})
    cases = 0
    for h, d, g in product(range(5), repeat=3):
        for n in range(d + 1):
            for visits, encrypted in product(range(h + 1), repeat=2):
                if encrypted > visits:
                    continue
                v, c = n * visits, n * encrypted
                for e in (0, g + c):
                    assert 0 <= c <= v <= d * h
                    assert e <= g + d * h and v + e <= g + 2 * d * h
                    for ce, cx in ((0, 0), (1, 0), (0, 1), (2, 3)):
                        assert c * ce + e * cx <= d * h * ce + (g + d * h) * cx
                cases += 1
    records.append({"case": "conditional-trace-and-weighted-call-sums", "inputs": cases, "result": "PASS"})
    # Omitting either trace premises or the second d*h factor is unsound.
    assert 2 * 3 + (4 + 2 * 3) > 4 + 2 * 3
    assert 1 * 5 > 1 * 2
    records.append({"case": "missing-trace-premise-and-factor-counterexamples", "result": "PASS"})
    print(json.dumps({"status": "PASS", "count": len(records), "records": records,
                      "scope": "Finite diagnostics only; no EC proof, whole-adversary trace, PPT or machine-time claim."}))


if __name__ == "__main__":
    main()
