#!/usr/bin/env python3
"""Exact finite consistency diagnostics, not exhaustive NTRU+ security tests."""
from fractions import Fraction
from itertools import product
import json


def recovery_partition(n):
    # This finite encryption is intentionally collision-rich across different
    # randomness values; fixing r still uniquely determines the message.
    domain = range(n)

    def encrypt(m, r):
        return (m + r) % n if m in domain and r in domain else None

    def decode(query):
        tag, r = query
        return r if tag == 1 and r in domain else None

    def candidate(ct, query):
        r = decode(query)
        if r is None or ct not in domain:
            return None
        return ((ct - r) % n, r)

    def first(ct, queries, excluded=None):
        for query in queries:
            value = candidate(ct, query)
            if value is not None and (excluded is None or value[1] != excluded):
                return value
        return None

    def inj_win(w):
        m, m2, r, r2 = w
        return (all(x in domain for x in w) and (m, r) != (m2, r2)
                and encrypt(m, r) is not None and encrypt(m, r) == encrypt(m2, r2))

    invalid = ((0, 0), (1, n))
    alphabet = tuple((1, r) for r in domain) + invalid
    cases = hits = collisions = one_way = 0
    duplicate_cases = first_mismatch_witnesses = 0
    for m, r in product(domain, repeat=2):
        ct = encrypt(m, r)
        for length in range(4):
            for queries in product(alphabet, repeat=length):
                hit = (1, r) in queries
                bad2 = any((value := candidate(ct, q)) is not None and value[1] != r for q in queries)
                collision_candidate = first(ct, queries, excluded=r)
                collision = ((m, m, r, r) if collision_candidate is None
                             else (m, collision_candidate[0], r, collision_candidate[1]))
                ow_candidate = first(ct, queries)
                answer = 0 if ow_candidate is None else ow_candidate[0]
                assert (collision_candidate is not None) == bad2
                assert not bad2 or inj_win(collision)
                assert not (hit and not bad2) or answer == m
                assert int(hit) <= int(inj_win(collision)) + int(answer == m)
                assert all(candidate(ct, q) is None for q in invalid)
                if len(set(queries)) < len(queries):
                    duplicate_cases += 1
                if hit and answer != m:
                    # An earlier colliding candidate can defeat naive first
                    # match inversion; this is exactly the INJ branch.
                    assert bad2 and inj_win(collision)
                    first_mismatch_witnesses += 1
                cases += 1
                hits += hit
                collisions += inj_win(collision)
                one_way += answer == m
        assert first(ct, ()) is None and not inj_win((m, m, r, r))
        assert candidate(n, (1, r)) is None
    assert not inj_win((n, n + 1, 0, 0))  # None = None is not a collision.
    assert not inj_win((0, 1, 0, 0))      # Unequal ciphertexts do not win.
    assert first_mismatch_witnesses > 0 and duplicate_cases > 0
    assert Fraction(hits, cases) <= Fraction(collisions, cases) + Fraction(one_way, cases)
    return {"size": n, "cases": cases, "duplicate_query_cases": duplicate_cases,
            "first_match_collision_witnesses": first_mismatch_witnesses,
            "hit_mass": str(Fraction(hits, cases)), "inj_mass": str(Fraction(collisions, cases)),
            "ow_mass": str(Fraction(one_way, cases))}


def adaptive_g_history():
    target = bytes(1152)
    other = bytes([1]) + bytes(1151)
    third = bytes([2]) + bytes(1151)
    table, queries = {}, []
    hit = False

    def physical_get(payload):
        if payload not in table:
            table[payload] = bytes((sum(payload) + i) % 256 for i in range(192))
        return table[payload]

    def logged_get(payload):
        nonlocal hit
        hit = hit or payload == target
        queries.insert(0, payload)
        return physical_get(payload)

    def raw(encoded, length):
        if not 0 <= length <= 224:
            return None
        if len(encoded) == 1153 and encoded[0] == 1:
            return (logged_get(encoded[1:]) + bytes(32))[:length]
        return bytes(length)

    def internal_lookup(candidates):
        for payload, matches in candidates:
            logged_get(payload)
            if matches:
                break

    challenge_pad = physical_get(target)
    assert target in table and not queries and not hit
    encoded = bytes([1]) + target
    assert raw(encoded, -1) is None and raw(encoded, 225) is None
    assert not queries and not hit
    assert raw(encoded, 0) == b"" and queries == [target] and hit
    assert raw(encoded, 16) == challenge_pad[:16] and queries == [target, target]
    assert logged_get(target) == challenge_pad and len(queries) == 3
    raw(bytes([0]) + target, 0)
    raw(encoded[:-1], 0)
    assert len(queries) == 3
    internal_lookup([(other, False), (target, True), (third, False)])
    assert queries == [target, other, target, target, target]
    assert third not in queries and third not in table
    assert hit == (target in queries)
    assert physical_get(target) == challenge_pad
    assert len(queries) > len(set(queries))
    # A fresh phase starts with no hit even though the physical target is cached.
    queries.clear()
    hit = False
    assert target in table and not queries and not hit
    logged_get(other)
    assert not hit and queries == [other]
    logged_get(target)
    assert hit and queries == [target, other]
    logged_get(other)
    assert hit and queries == [other, target, other]
    return {"challenge_query_excluded": True, "cached_target_reply_preserved": True,
            "raw_zero_logged": True, "internal_lookup_G_logged": True,
            "duplicates_retained": True, "hit_latched": True}


def main():
    partition = [recovery_partition(n) for n in (2, 3)]
    history = adaptive_g_history()
    checks = ["target-hit partitions into collision or recovery", "first-match recovery under no collision",
              "first-match counterexample when collision exists", "collision witness has distinct input pairs",
              "None-None and unequal outputs excluded from collision", "invalid G payload skipped",
              "failed recovery skipped", "empty scan returns no candidate", "duplicate query lists retained",
              "exact finite probability inequality", "challenge G query excluded from adaptive log",
              "raw zero-output G request logged", "internal lookup G calls logged",
              "invalid raw requests do not query G", "cached G answer never resampled", "hit remains latched"]
    print(json.dumps({"status": "PASS", "count": len(checks), "checks": checks,
                      "partition": partition, "adaptive_G_history": history,
                      "scope": "Exact finite diagnostics only; not an exhaustive NTRU+ security test or a replacement for EasyCrypt proofs."}))


if __name__ == "__main__":
    main()
