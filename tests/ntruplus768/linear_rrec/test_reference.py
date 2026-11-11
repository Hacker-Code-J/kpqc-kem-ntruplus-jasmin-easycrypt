#!/usr/bin/env python3
"""Small exact diagnostics, not a proof of NTRU+ or whole FO equivalence."""
from itertools import product
import json


Q = 7
FIELD = tuple(product(range(Q), repeat=2))
TRITS = tuple(product((-1, 0, 1), repeat=2))
H = (2, 3)
HINV = (4, 5)


def forward(v):
    x, y = v
    return ((x + 2*y) % Q, (3*x + y) % Q)


def inverse(v):
    x, y = v
    return ((4*x + 6*y) % Q, (2*x + 4*y) % Q)


def pack(v):
    """Two canonical coefficients use all three bytes of a 12-bit codec."""
    return (v[0] | (v[1] << 12)).to_bytes(3, 'little')


def checked_decode(b):
    if len(b) != 3:
        return None
    w = int.from_bytes(b, 'little')
    v = (w & 4095, w >> 12)
    return v if all(x < Q for x in v) else None


def encrypt(m, r):
    fm, fr = forward(m), forward(r)
    return tuple((H[i]*fr[i] + fm[i]) % Q for i in range(2))


def terminal_candidate(ct, m, stored_inverse=HINV):
    fm = forward(m)
    return tuple(stored_inverse[i]*(ct[i]-fm[i]) % Q for i in range(2))


def linear_recover(ciphertext, m):
    ct = checked_decode(ciphertext)
    if ct is None or m not in TRITS:
        return None
    residues = inverse(terminal_candidate(ct, m))
    centered = tuple(x if x <= Q//2 else x-Q for x in residues)
    return centered if centered in TRITS else None


def main():
    checks = []

    def check(name, condition):
        assert condition, name
        checks.append(name)

    # Exhaust every pair of maps on the same three-element finite carrier.
    maps = tuple(product(range(3), repeat=3))
    left_pairs = [(f, g) for f in maps for g in maps
                  if all(g[f[x]] == x for x in range(3))]
    check('finite-same-carrier-left-inverse-forces-right-inverse',
          len(left_pairs) == 6 and all(all(f[g[y]] == y for y in range(3))
                                      for f, g in left_pairs))
    f, g = (0, 1, 2), (0, 1, 2, 0)
    check('larger-terminal-carrier-invalidates-left-to-right-inference',
          all(g[f[x]] == x for x in range(3)) and f[g[3]] != 3)
    check('finite-linear-transform-covers-all-terminal-values',
          len({forward(x) for x in FIELD}) == len(FIELD))
    check('inverse-then-forward-covers-arbitrary-terminal-not-just-trit-images',
          all(forward(inverse(y)) == y for y in FIELD)
          and len({forward(r) for r in TRITS}) < len(FIELD))
    check('wrong-inverse-scale-is-detected',
          any(forward(tuple(2*x % Q for x in inverse(y))) != y for y in FIELD))
    check('canonical-codec-is-injective-on-entire-field-domain',
          len({pack(x) for x in FIELD}) == len(FIELD)
          and all(checked_decode(pack(x)) == x for x in FIELD))
    check('mod-q-equivalent-noncanonical-alias-is-rejected',
          checked_decode(pack((Q, 0))) is None and pack((Q, 0)) != pack((0, 0)))
    check('rejecting-option-decoder-is-not-injective-on-malformed-ciphertexts',
          checked_decode(pack((Q, 0))) == checked_decode(pack((Q+1, 0)))
          and pack((Q, 0)) != pack((Q+1, 0)))
    check('byte-prefix-agreement-does-not-establish-full-serialization-equality',
          pack((0, 0))[:1] == pack((0, 1))[:1] and pack((0, 0)) != pack((0, 1)))
    check('canonical-serialization-equality-only-implies-mod-q-word-equality',
          (-1, 0) != (Q-1, 0)
          and pack(tuple(x % Q for x in (-1, 0))) == pack((Q-1, 0)))
    check('short-and-overlong-ciphertexts-are-not-canonical',
          checked_decode(pack((0, 0))[:2]) is None
          and checked_decode(pack((0, 0)) + b'\x00') is None)
    # Every canonical ciphertext is considered, including those whose unique
    # linear preimage lies outside the allowed ternary randomness domain.
    candidates = [(ct, m, inverse(terminal_candidate(ct, m)))
                  for ct in FIELD for m in TRITS]
    check('unrestricted-linear-candidate-reencrypts-every-canonical-ciphertext',
          all(encrypt(m, r) == ct for ct, m, r in candidates))
    check('trit-domain-recovery-acceptance-exactly-matches-unique-ternary-preimage',
          all((linear_recover(pack(ct), m) is not None)
              == any(encrypt(m, r) == ct for r in TRITS)
              for ct in FIELD for m in TRITS))
    check('accepted-linear-recovery-needs-no-extra-reencryption-guard',
          all(encrypt(m, r) == ct for ct in FIELD for m in TRITS
              if (r := linear_recover(pack(ct), m)) is not None))
    check('arbitrary-canonical-ciphertext-can-reject-outside-trit-domain',
          linear_recover(pack((1, 0)), (0, 0)) is None
          and checked_decode(pack((1, 0))) == (1, 0))
    check('forward-correctness-holds-for-every-ternary-message-and-randomness',
          all(linear_recover(pack(encrypt(m, r)), m) == r
              for m in TRITS for r in TRITS))
    check('zero-ciphertext-and-zero-recovered-randomness-remain-success',
          linear_recover(pack((0, 0)), (0, 0)) == (0, 0))
    check('message-domain-rejection-is-preserved',
          linear_recover(pack((0, 0)), (2, 0)) is None)
    # Compare the native terminal r2 bytes against NTT(rH), at the very same m.
    check('native-full-byte-comparison-equals-reencryption-comparison-at-same-message',
          all((pack(terminal_candidate(ct, m)) == pack(forward(rh)))
              == (encrypt(m, rh) == ct)
              for ct in FIELD for m in FIELD for rh in TRITS))
    rh, m = (1, 1), (0, 0)
    ct = encrypt(m, rh)
    check('native-terminal-match-does-not-require-terminal-coefficients-to-be-trits',
          terminal_candidate(ct, m) == forward(rh)
          and forward(rh) not in {tuple(x % Q for x in r) for r in TRITS})
    check('changing-the-decoded-message-invalidates-the-comparison-identity',
          pack(terminal_candidate(ct, m)) == pack(forward(rh))
          and encrypt((1, 0), rh) != ct)
    check('stored-inverse-agreement-is-required-for-public-inverse-comparison',
          pack(terminal_candidate(ct, m, (0, 0))) != pack(forward(rh))
          and encrypt(m, rh) == ct)
    check('singular-key-admits-no-public-multiplicative-inverse',
          any(all(h*x % Q != 1 for x in range(Q)) for h in (0, H[1])))
    # These are exact codec/word arithmetic sanity checks with the real q and
    # width, not execution of the cryptographic implementation's normalizer.
    q = 3457
    signed = lambda w: w if w < 32768 else w-65536
    canonical = lambda w: signed(w) % q
    check('signed-16-bit-normalization-differs-from-unsigned-reduction',
          canonical(65535) == q-1 and canonical(65535) != 65535 % q)
    check('normalization-uses-q-not-the-12-bit-packing-modulus',
          q % q == 0 and q % 4096 != 0)
    check('real-q-aliases-are-distinct-byte-strings-before-canonical-checking',
          pack((1, 0)) != pack((1+q, 0)) and (1+q) % q == 1)
    print(json.dumps({'status': 'PASS', 'count': len(checks), 'checks': checks,
                      'scope': 'Exact small finite-domain diagnostics; not NTRU+ correctness, a security reduction, or whole modified-FO/native equivalence.',
                      'finite_field': Q, 'arbitrary_terminal_points': len(FIELD),
                      'same_message_comparison_cases': len(FIELD)**2*len(TRITS)}))


if __name__ == '__main__':
    main()
