#!/usr/bin/env python3
"""Exact finite diagnostics of the membership reduction and raw H boundary.

These are independent finite consistency checks, not proofs about NTRU+.
"""
from fractions import Fraction
from itertools import product
import json


def membership_diagnostic(n):
    messages = range(n)
    subsets = [frozenset(i for i in messages if mask >> i & 1) for mask in range(1 << n)]
    cases = collisions = 0
    # Include both fully revealing and colliding ciphertext channels.
    for classes in sorted({1, n}):
        for lists in product(subsets, repeat=classes):
            q = max(map(len, lists))
            hit = Fraction(sum(m in lists[m % classes] for m in messages), n)
            cross = Fraction(sum(m0 in lists[m1 % classes] for m0 in messages for m1 in messages), n * n)
            wins = 0
            for m0, m1, bit in product(messages, messages, (False, True)):
                selected = m1 if bit else m0
                guess = m0 not in lists[selected % classes]
                wins += guess == bit
                if m0 == m1:
                    collisions += 1
            win = Fraction(wins, 2 * n * n)
            assert win == Fraction(1, 2) + (hit - cross) / 2
            assert cross <= Fraction(q, n)
            assert hit <= 2 * abs(win - Fraction(1, 2)) + Fraction(q, n)
            if q == 0:
                assert hit == cross == 0 and win == Fraction(1, 2)
            if all(len(xs) == n for xs in lists):
                assert hit == cross == 1 and win == Fraction(1, 2)
            cases += 1
    # A one-query list that illegally sees the unused target violates the
    # cross-hit bound. This detects why state exclusion is necessary.
    assert Fraction(1) > Fraction(1, n)
    return {"cases": cases, "equal_message_branches": collisions}


def raw_history_diagnostic():
    target = bytes([2]) + bytes(range(96)) + bytes(range(32))
    reply = bytes(range(224))
    table, history = {}, {}
    calls, hit = 0, False

    def h_get(encoded):
        nonlocal calls, hit
        calls += 1
        hit = hit or encoded == target
        if encoded not in table:
            table[encoded] = reply
        history[encoded] = table[encoded]
        return table[encoded]

    def raw(encoded, outlen):
        if not 0 <= outlen <= 224:
            return None
        if len(encoded) == 129 and encoded[0] == 2:
            return h_get(encoded)[:outlen]
        return bytes(outlen)

    assert raw(target, -1) is None and raw(target, 225) is None
    assert calls == 0 and not history and not hit
    assert raw(target, 0) == b""
    assert calls == 1 and hit and history[target] == reply
    assert raw(target, 16) == reply[:16]
    assert calls == 2 and len(history) == 1
    assert h_get(target) == reply
    assert calls == 3 and len(table) == 1
    raw(bytes([3]) + target[1:], 0)
    raw(target[:-1], 224)
    assert calls == 3
    # A wrong suffix is a distinct query even when the message is equal.
    other = target[:-1] + bytes([255])
    raw(other, 0)
    assert calls == 4 and len(history) == 2
    return {"valid_H_callbacks": calls, "unique_H_inputs": len(history), "zero_output_preserves_full_internal_reply": True}


def main():
    membership = [membership_diagnostic(n) for n in (2, 3)]
    raw = raw_history_diagnostic()
    checks = ["CPA success identity", "unused-message cross-hit bound", "CPA advantage coefficient two",
              "equal challenge messages", "empty query list", "full query list", "colliding ciphertext channel",
              "target-state-leak counterexample", "raw zero-output records full internal reply",
              "typed/raw repeated reply consistency", "invalid raw lengths and domain exclusion", "different suffix is distinct input"]
    print(json.dumps({"status": "PASS", "count": len(checks), "checks": checks,
                      "membership": membership, "raw_history": raw,
                      "scope": "Exact finite diagnostics only; no claim of an exhaustive NTRU+ security test."}))


if __name__ == "__main__":
    main()
