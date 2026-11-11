#!/usr/bin/env python3
"""Small exact diagnostics for history/cache distinctions, not a security proof."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
import json

class LazyH:
    def __init__(self, coins=(bytes((7,))*224, bytes((9,))*224), initial=None):
        self.table = dict(initial or {})
        self.coins = iter(coins)
        self.draws = 0

    def get(self, key):
        if key not in self.table:
            self.table[key] = next(self.coins)
            self.draws += 1
        return self.table[key]

class PublicH:
    def __init__(self, backend):
        self.backend = backend
        self.history = {}

    def typed(self, key):
        full = self.backend.get(key)
        self.history[key] = full
        return full

    def raw(self, data, outlen):
        if not 0 <= outlen <= 224:
            return None
        if len(data) == 129 and data[0] == 2:
            return self.typed((data[1:97], data[97:]))[:outlen]
        # Only H effects matter in this diagnostic, not other oracle outputs.
        return bytes(outlen)


def first_match(history, suffix, ct, star):
    """Public candidate fixtures; this function makes no encryption claim."""
    if ct == star:
        return None
    for (_, recorded_suffix), (candidate_ct, key) in history.items():
        if recorded_suffix == suffix and candidate_ct == ct:
            return key
    return None


def test_public_history_absence_does_not_imply_physical_freshness():
    backend = LazyH()
    public = PublicH(backend)
    hidden = (b'internal', b'Fpk')
    out = backend.get(hidden)
    assert hidden in backend.table and hidden not in public.history
    assert public.typed(hidden) == out and backend.draws == 1


def test_raw_zero_returns_empty_but_records_full_private_reply():
    public = PublicH(LazyH())
    query = bytes((2,))+bytes(128)
    assert public.raw(query, 0) == b''
    assert len(public.history[(bytes(96), bytes(32))]) == 224


def test_typed_raw_repeats_reuse_the_same_physical_entry():
    public = PublicH(LazyH())
    key = (bytes(96), bytes(32))
    full = public.typed(key)
    query = bytes((2,))+bytes(128)
    assert public.raw(query, 32) == full[:32]
    assert public.raw(query, 224) == full and public.backend.draws == 1


def test_invalid_and_non_H_raw_requests_do_not_record_H():
    public = PublicH(LazyH())
    query = bytes((2,))+bytes(128)
    assert public.raw(query, 225) is None
    assert public.raw(bytes((1,))+query[1:], 0) == b''
    assert public.history == {} and public.backend.table == {}


def test_hidden_sampling_erasure_preserves_later_repeat_query_distribution():
    eager, deferred = Counter(), Counter()
    for hidden in (0, 1):
        eager[(hidden, hidden)] += F(1, 2)
    for later in (0, 1):
        deferred[(later, later)] += F(1, 2)
    assert eager == deferred == {(0, 0): F(1, 2), (1, 1): F(1, 2)}
    resample_on_hit = Counter({pair: F(1, 4) for pair in product((0, 1), repeat=2)})
    assert resample_on_hit != eager


def test_erasure_cannot_clear_a_preexisting_cached_reply():
    original = {1: F(1)}
    unchanged_by_omitting_hidden_sample = {1: F(1)}
    erased_and_resampled = {0: F(1, 2), 1: F(1, 2)}
    assert original == unchanged_by_omitting_hidden_sample != erased_and_resampled


def test_fresh_acceptance_bound_does_not_apply_to_an_unlogged_cache_hit():
    fresh_accept = sum(F(1, 2) for value in (0, 1) if value == 1)
    cached_accept = F(1)  # A hidden physical entry can already contain 1.
    public_history = {}
    assert not public_history and cached_accept > fresh_accept


def test_averaged_error_is_not_a_bound_for_a_selected_fixed_setup():
    setups = ((F(1, 8), F(1)), (F(7, 8), F(0)))
    expected = sum(probability*error for probability, error in setups)
    assert expected == F(1, 8) < setups[0][1]


def test_lookup_uses_public_history_suffix_and_exact_challenge_exclusion():
    history = {('wrong', 9): (4, 7), ('right', 3): (4, 0)}
    assert first_match(history, 3, 4, 5) == 0  # Successful zero key is not None.
    assert first_match(history, 3, 4, 4) is None
    assert first_match({}, 3, 4, 5) is None


def test_arbitrary_candidates_need_not_have_order_independent_answers():
    entries = [(('m0', 3), (4, 7)), (('m1', 3), (4, 8))]
    assert first_match(dict(entries), 3, 4, 5) != first_match(dict(reversed(entries)), 3, 4, 5)


def main():
    tests = sorted((name, value) for name, value in globals().items() if name.startswith('test_'))
    for _, test in tests:
        test()
    print(json.dumps({'status': 'PASS', 'count': len(tests),
                      'scope': 'independent exact diagnostics, not cryptographic proof or a whole-game theorem',
                      'cases': [name for name, _ in tests]}))

if __name__ == '__main__':
    main()
