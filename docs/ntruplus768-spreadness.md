# NTRU+768 ciphertext spreadness with explicit oracle scope

**Full replay PASS**, 2026-10-15: 8 mains / 92 lemmas,
8 semantic EOF probes and 8 own-main unfinished-proof rejections.
The replay passed 38 structural/trust controls
and 6 finite diagnostics.
All 902 source inputs and 300 external inputs matched
before/after hashes. Source pins: 892; imported EC files: 697,
linked to 16 prior PASS records rather than counted as fresh main replays.

This family proves ciphertext-concentration bounds for the actual array
encryption calls. The bounds use distinct probability spaces and must not
be substituted for one another.

| Experiment or property | Proved bound |
|---|---|
| Base PKE, every valid generated key and fixed trit message/ciphertext | `2^-768`, attained by the zero-randomness ciphertext |
| Transformed PKE, fixed key/message/ciphertext, averaged over independently sampled G | `2^-768` |
| Transformed PKE, fixed valid key and arbitrary fixed G, maximum over messages/ciphertexts | `2^-768 + fo_error(key,G)` |
| Expected maximum under the actual fresh-key/F/G setup | `< 2^-768 + 2^-353 < 2^-352` |
| Actual transformed call after a fixed finite G cache T and a new independent r draw | `(fsize(T)+1)*2^-768` |

## Base PKE and actual calls

`SpreadCBD` proves the maximum atom of the actual unconditioned CBD1
distribution, its zero-vector equality and corresponding polynomial
statements. Each coefficient has masses 1/4,1/2,1/4; accepted key
coefficients are not assumed independent.

`SpreadBase` uses the existing keyed randomness-recovery contract to
show that a fixed-message ciphertext has at most one trit randomness
preimage. Actual key validity is essential. Canonical public-key bytes
alone do not imply the needed inverse. The proof adds no decryption
correctness or coefficient no-wrap premise.

`SpreadProcedures` connects an independent uniform192 buffer to the
extracted CBD kernel and existing PKE array kernels. `SpreadGenerated`
uses the existing **public** KeyGen result and proves the validity
predicate for its returned public key. Its initialized actual-ROM
experiment has returned `Some(ciphertext)` mass at most `2^-768`, without
assuming ROM-KeyGen losslessness or normalizing by return. Fresh KeyGen
losslessness is a separate proved statement.

## G averaging, maximum and the correctness envelope

For fixed key K, message mu, function g and ciphertext c, define

```
p(K,g,mu,c) = Pr_r[Enc(pk,SOTPEncode(mu,g(r));r) = Some c].
```

`SpreadTransfer` proves `E_G p(K,G,mu,c) <= 2^-768` with the actual finite
G-pad law and SOTP hiding. It fixes mu and c before averaging. This matches
the marginal averaging calculation in specification Theorem 3.8.

`SpreadWeak` separately bounds `max_mu,c p(K,g,mu,c)` **before** averaging.
When base decryption succeeds, its output code is fixed by c, so that
part of the ciphertext event is at most `2^-768`. The failed part is at
most the existing `fo_error(K,g)` envelope. The symbolic finite maximum
uses all message bytes and the ciphertext image of all trit code/randomness
pairs. Ciphertexts outside that image have zero mass, and
`spread_cipher_max_upper_iff` connects the finite expression to every
message and ciphertext.

The final `spread_weak_setup_max_352` theorem takes this literal maximum
inside the expectation under the exact `FOSetupSource` law: actual fresh
accepted keys, retained F table and independent G pads. The prior error
expectation gives `<2^-768+2^-353<2^-352`, a conservative weak-spreadness
parameter of 352. It does not assume or prove a fixed-G `2^-768` bound,
swap maximum and expectation, or replace this fresh-key law by the actual
cached-ROM KeyGen law.

## Existing caches and concrete oracle correspondence

`SpreadCache` samples a new r independently of the initial table T.
Actual G-input injectivity and the CBD atom bound give a cache-hit
probability at most `fsize(T)*2^-768`. Existing answers are reused.
The remaining independent-pad ciphertext event is at most `2^-768`.
The proved intermediate bound is `p_hit + 2^-768`; the family does not
claim the stronger `p_hit+(1-p_hit)*2^-768` intermediate formula.

`SpreadCalls` relates the actual CBD/G-preparation/SOTP/PKE caller to
this experiment while preserving the **complete G map**. A distinct
`SpreadFreshG` experiment explicitly initializes G and gives `2^-768`.
For an already prepared table satisfying `acwc2_cache_matches`, the
actual caller probability equals `p(K,g,mu,c)` exactly. That equality is
not a numerical bound for arbitrary fixed G.

The cache contract permits inputs chosen from past observations, provided
the new r is independent of that state. Using it within the existing FO
game additionally requires a fresh H input and the G table **after** the
preceding `DecapMessage` query. A cached H output is not a new independent
draw. A query-count bound must account for typed/raw and internal G calls;
the old H/Decaps budget alone does not supply it. An analysis-only fully
prepared table must not be mistaken for a revealed-query cache.

The [public H-history simulation](ntruplus768-fo-simulation.md) uses the
fresh-H bound `2^-768 + fo_error(key,G)` in a selected-query argument.
It removes the first hidden G query by adaptive sampling erasure and
does not replace a fixed-G ciphertext mass by its G-average. Its actual
fresh-game comparison costs `qD/2^768 + (qH+qD)/2^353` under explicit
termination and query contracts.

## Reproduction and scope

```
./scripts/verify-ntruplus768-spreadness.sh
./scripts/verify-ntruplus768-spreadness.sh --check-only
```

The full runner checks all new mains with semantic EOF probes and each
main's own unfinished-proof negative. All negative copies are generated
and hashed in preflight, preserving declarations after the final proof.
It also checks structural/trust controls and small finite diagnostics.
The finite examples distinguish G-average from fixed-G claims; they are
not proofs or attacks on NTRU+.

Strict settings are `-no-eco`, `Proofs:check`, Z3, timeout60/max-provers1
and `OCAMLRUNPARAM=o=20`. Default `EC_JOBS=2` uses two isolated processes;
`EC_JOBS=1` is serial. Source-only checks never receive a full proof PASS.
Imported theories are hash-linked to prior evidence and are not counted
as newly replayed mains. Evidence is in the thesis workspace under
`handoff/verification/ntruplus-spreadness-20261015/`.

This family changes no C/Jasmin implementation, native API or extraction
and reruns no native, Safety or CT/SCT test. The remaining IND-CPA
embedding and hardness reductions, HAETAE UF-CMA and separate QROM goal
remain to be completed.
