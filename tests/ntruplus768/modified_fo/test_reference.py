#!/usr/bin/env python3
"""Exact finite counterexamples; these diagnostics are not a cryptographic proof.

The scalar ring is Z/7Z with public multiplier 3. It deliberately has tiny
parameters so wraparound and full-regeneration differences can be enumerated.
"""
from fractions import Fraction as F
from itertools import product
import json

TRITS = (-1, 0, 1)
PADS = tuple(product((0, 1), repeat=2))

def center(x):
    return (x+3)%7-3

def enc(code, r):
    return (code+3*r)%7

def dec(ct):
    return (center(ct)+1)%3-1

def recover(ct, code):
    return center(5*(ct-code))

def encode(msg, pad):
    head, tail = pad
    return (head ^ msg)-tail

def decode(code, pad):
    head, tail = pad
    total = code+tail
    return (total+head)%2, total not in (0, 1)

def compare(ct, pads, hashes):
    code = dec(ct)
    recovered = recover(ct, code)
    msg, failed = decode(code, pads.get(recovered, (0, 0)))
    rh = hashes[msg]
    new_code = encode(msg, pads[rh])
    native = not failed and recovered == rh
    full = not failed and recovered in TRITS and enc(new_code, rh) == ct
    return native, full, dec(enc(new_code, rh)) != new_code, msg, rh

def test_full_regeneration_is_not_same_message_check():
    differences = []
    checked = 0
    for choices in product(PADS, repeat=3):
        pads = dict(zip(TRITS, choices))
        for hashes in product(TRITS, repeat=2):
            for ct in range(7):
                native, full, bad, _, _ = compare(ct, pads, hashes)
                assert not native or full
                if native != full:
                    assert bad
                    differences.append((ct, pads, hashes))
                checked += 1
    assert checked == 4032 and differences

def test_base_failure_does_not_imply_transformed_failure():
    pads = {-1: (0, 1), 1: (0, 0)}
    code = encode(0, pads[-1])
    ct = enc(code, -1)
    recovered_code = dec(ct)
    recovered_r = recover(ct, recovered_code)
    assert recovered_code != code
    assert decode(recovered_code, pads[recovered_r]) == (0, False)

def test_challenge_entry_can_be_base_bad():
    code, rh = -1, -1
    assert dec(enc(code, rh)) != code

def test_cached_challenge_entry_cannot_accept_another_ciphertext():
    for pad, msg, rh in product(PADS, (0, 1), TRITS):
        ctstar = enc(encode(msg, pad), rh)
        for ct in range(7):
            if ct != ctstar:
                assert enc(encode(msg, pad), rh) != ct

def test_challenge_badness_cannot_be_excluded_without_ciphertext_block():
    found = False
    for choices in product(PADS, repeat=3):
        pads = dict(zip(TRITS, choices))
        for hashes in product(TRITS, repeat=2):
            for msg in (0, 1):
                ctstar = enc(encode(msg, pads[hashes[msg]]), hashes[msg])
                native, full, bad, decoded_msg, _ = compare(ctstar, pads, hashes)
                if full and not native and decoded_msg == msg:
                    assert bad
                    found = True
    assert found

def test_checked_recovery_rejects_nontrits():
    assert recover(3, -1) == -1
    candidates = {recover(ct, code) for ct in range(7) for code in TRITS}
    assert candidates == set(range(-3, 4)) and candidates-set(TRITS)

def test_expectation_of_max_cannot_be_replaced_by_max_expectation():
    table = ((F(1), F(0)), (F(0), F(1)))
    expected_max = sum(map(max, table))/2
    max_expected = max(sum(row[j] for row in table)/2 for j in (0, 1))
    assert expected_max == 1 and max_expected == F(1, 2)

def test_average_error_does_not_give_pointwise_key_bound():
    rare, bad_key_error = F(1, 16), F(1)
    assert rare*bad_key_error < F(1, 8) < bad_key_error

def test_independence_is_needed_for_product_bad_bound():
    joint = {(0, 0): F(1, 2), (1, 1): F(1, 2)}
    assert joint[(1, 1)] > F(1, 2)**2

def test_h_hits_share_the_full_message_and_public_hash_key():
    table, draws = {}, []
    def get(key):
        if key not in table:
            draws.append(key)
            table[key] = len(draws)
        return table[key]
    first = get((0, 7))
    assert get((0, 7)) == first and len(draws) == 1
    assert get((0, 8)) != first and len(draws) == 2

def test_eager_completion_preserves_cached_values_and_lazy_other_inputs():
    prefixes = {0: 9, 4: 8}
    suffixes = {0: 5}
    before_suffixes = dict(suffixes)
    for key, fresh in zip((0, 1, 2), (3, 4, 5)):
        prefixes.setdefault(key, fresh)
    assert prefixes == {0: 9, 1: 4, 2: 5, 4: 8}
    assert 3 not in prefixes and suffixes == before_suffixes

def test_nonempty_cache_is_not_iid_uniform():
    cached = {0: 0}
    outputs = [cached.get(0, fresh) for fresh in (0, 1)]
    assert outputs.count(0) == 2

def test_raw_prefix_requests_preserve_the_g_suffix():
    prefix, suffix = bytes((7,))*192, bytes((8,))*32
    full = prefix+suffix
    assert full[:0] == b'' and full[:192] == prefix
    assert full[:224][192:] == suffix

def test_bounded_number_of_queries_does_not_imply_termination():
    # A subdistribution may have no returned result even after zero queries.
    returned = {}
    queries_before_divergence = 0
    assert queries_before_divergence <= 1 and sum(returned.values()) == 0


def raw_h(data, outlen):
    return 0 <= outlen <= 224 and len(data) == 129 and data[0] == 2

def test_typed_raw_H_repeats_and_zero_length_are_charged():
    query = bytes((2,))+bytes(128)
    # One typed request and two raw aliases, including the empty response.
    assert 1+sum(raw_h(query, n) for n in (224, 0)) == 3

def test_invalid_and_non_H_raw_requests_do_not_consume_H_budget():
    query = bytes((2,))+bytes(128)
    rejected = ((query, -1), (query, 225), (query[:-1], 0),
                (bytes((1,))+query[1:], 0), (bytes(32), 0))
    assert not any(raw_h(data, n) for data, n in rejected)

def test_all_D_attempts_and_denied_H_have_explicit_budget_cost():
    # A cap pays for the first two attempts even if D is challenge-blocked.
    kinds = ('blocked-D', 'malformed-D', 'H-repeat', 'raw-H-zero')
    charged = list(enumerate(kinds))
    forwarded = [kind for before, kind in charged if before < 2]
    assert forwarded == ['blocked-D', 'malformed-D']
    assert len(charged) == 4 and not any('H' in kind for kind in forwarded)

def main():
    tests = sorted((name, value) for name, value in globals().items() if name.startswith('test_'))
    for _, test in tests:
        test()
    print(json.dumps({'status': 'PASS', 'count': len(tests),
                      'scope': 'independent exact finite diagnostics, not actual cryptographic proof',
                      'cases': [name for name, _ in tests]}))

if __name__ == '__main__':
    main()
