# Expected worst-message correctness for the NTRU+768 ACWC2 composition

This proof-only development composes the existing PKE, public checked
randomness recovery and SOTP procedures. The proved bound is

```text
E_key E_G [ max_message Pr_r[transformed decryption fails] ] < 2^-353.
```

The key has the actual fresh acceptance-conditioned KeyGen law. The
96-byte message is maximized after the key and the entire G function are
fixed; r has the implemented CBD1 distribution. G has independent
uniform 192-byte entries on the finite ternary randomness domain. The
expectations and maximum stay in this order. This is not a bound on each
fixed key, nor a maximum taken outside the expectation over G.

The concrete endpoint is `acwc2_fresh_worst_actual_calls` in
[`NTRUPlus768ACWC2WorstCase.ec`](../ntruplus/proof/768/ref/acwc2_correctness/NTRUPlus768ACWC2WorstCase.ec).
It uses the actual KeyGen output distribution
`mk(fun out => Pr[KeygenSource(FreshExpand).guess(witness): res = out])`
and states the bound directly for

```text
E_actual_key E_pads [ max_message
  Pr[ACWC2FixedOracleTrial.run(pads,pk,sk,message): failure] ] < 2^-353.
```

Here `pads` has `acwc2_gpads_law`: one independent answer per ternary
randomness input. The inner probability samples fresh encryption
randomness and runs the actual array procedures. It does not sample a
new G for each candidate message.

**Final replay: PASS (2026-10-14).** All 16 new mains and 183 lemmas
passed strict `-no-eco` / `Proofs:check`, including 16 semantic EOF
obligations and 16 isolated unfinished-proof rejections. The runner
passed 79 structural/trust controls and 30 exact finite diagnostics.
It recorded 39 command logs, 32 isolated source copies, 798
pinned sources, 810 runtime inputs and 294 external inputs, with unchanged
before/after hashes. The 607 imported EasyCrypt files are linked to prior
PASS evidence and are not counted as new main replays.

The full report is in the companion thesis directory at
`handoff/verification/ntruplus-acwc2-correctness-20261014/final-replay/summary.json`.
Finite diagnostics supplement the proofs; they are not security proofs.

The preceding [PKE average result](ntruplus768-pke-average.md) and
[RR/SOTP/G contracts](ntruplus768-acwc2-contracts.md) supply the concrete
interfaces. This continuation concerns the checked array composition;
it is not an IND-CCA reduction or a new native API.

## Actual transformed encryption and decryption

[`NTRUPlus768ACWC2Procedures.ec`](../ntruplus/proof/768/ref/acwc2_correctness/NTRUPlus768ACWC2Procedures.ec)
defines the following calls with a common G port:

| Procedure | Inputs and computation |
| --- | --- |
| `ACWC2Enc(G).run` | Public key, 96-byte message and ternary r; query G(r), run actual SOTP encoding, then actual PKE encryption. |
| `ACWC2Dec(G).run` | Public key, complete 2336-byte secret key and ciphertext; run PKE decryption using the serialized f component, public checked RRec, G on the recovered randomness, then guarded SOTP decoding. |
| `ACWC2RoundTrip(G).run` | Run both procedures and return failure for encryption rejection, decryption rejection or a different recovered message. |

The decoder receives no original message or original encryption
randomness. The public RRec helper computes its inverse from the public
key, uses the existing linear arithmetic and inverse NTT, checks the
ternary candidate and performs one actual PKE reencryption comparison.
It has no secret inverse input. These are compositions of the existing
extracted kernels and explicit array-model guards. The later
[linear-RRec continuation](ntruplus768-linear-rrec.md) proves that removing
the helper's reencryption call preserves its option result for all
inputs. This guide's recorded experiment and proof sources retain the
checked helper used in their original replay.
The additional proof-only ACWC2 caller using `LinearRRec` is proved
equivalent with equal result and G state, without a functional or
losslessness premise on G. `linear_acwc2_fresh_worst_actual_calls`
transfers the same `2^-353` bound with the original fresh-key law, chosen
G pads and message maximum unchanged. The
[linear-RRec guide](ntruplus768-linear-rrec.md) records the exact caller
contracts and that continuation's final replay status.

[`NTRUPlus768ACWC2Recovery.ec`](../ntruplus/proof/768/ref/acwc2_correctness/NTRUPlus768ACWC2Recovery.ec)
proves functional and lossless connections to the fixed-G specifications.
When the underlying PKE decryption recovers its encoded message, the
no-wrap-free honest RRec contract returns the original r and the SOTP
roundtrip returns the original 96-byte message. Thus transformed failure
is included in underlying PKE failure. The direct actual-G recovery
contract reuses the established cache entry for r and preserves the
whole G table.

## Finite G law and the shared actual cache

The ternary randomness domain is the complete finite support of
`pke_psi1`. The proof enumerates that support symbolically; it does not
execute an exhaustive search. For every r in the domain, G(r) is one
independent `uniform192` sample. The exact joint observation law is a
finite product, not just a collection of uniform marginals.

[`NTRUPlus768ACWC2Oracle.ec`](../ntruplus/proof/768/ref/acwc2_correctness/NTRUPlus768ACWC2Oracle.ec)
defines this law as `acwc2_eager_g_law` and proves
`acwc2_g_independent_observations`. Its cache uses the actual injective
1152-byte `rr_G_input(r)` keys. `ACWC2EagerOracle.init` explicitly clears G,
samples the finite list and installs the corresponding entries.
The separate `prepare` operation preserves every existing entry; it does
not silently replace an arbitrary cache by independent answers.

`acwc2_prepared_roundtrip_correct` connects the fixed-G specification to
`ACWC2RoundTrip(ACWC2HashG)` under the complete-cache consistency invariant.
The actual NTT/input preparation and `SHAKEGROM`/`ROG` calls remain in the
caller. Repeated queries use the same pad and the prepared table is
unchanged. The earlier G bridge supplies the exact tag-1 1153-byte raw
query and its typed classification.

[`NTRUPlus768ACWC2Execution.ec`](../ntruplus/proof/768/ref/acwc2_correctness/NTRUPlus768ACWC2Execution.ec)
then makes the conditional failure probability an actual randomized
call. `ACWC2FixedOracleTrial` first clears G and deterministically installs
the already selected `pads`. It draws a new `uniform192` buffer, invokes
the actual checked CBD1 kernel and runs `ACWC2ROMRoundTrip`. There is no G
resampling in this procedure. `acwc2_fixed_oracle_trial_error` identifies
its failure probability exactly with `acwc2_message_error` for the fixed
function `acwc2_gfun(pads)`. Each counterfactual message therefore uses
the same previously chosen oracle answers, while its probability averages
over fresh encryption randomness.

The worst-message analysis samples the complete finite G function before
choosing the message. A full eager table and an initially empty lazy
table are different states. This result does not claim equality of those
global states, arbitrary adaptive-context equivalence with empty lazy G,
or an iid law for an arbitrary preexisting G cache. The prior fresh-query
and repeated-query contracts retain their separate premises.

## The independent variables and their mean

For fixed key w, message msg and randomness r, define

```text
B_r(pad) = underlying PKE fails on
           code = SOTPEncode(msg,pad), randomness = r
w_r      = Pr[pke_psi1 = r]
X(G)     = sum_r w_r * 1[B_r(G(r))].
```

The actual transformed error is at most X(G). Each B_r reads only G(r),
so these are the coordinates to which independence applies. Transformed
decryption can query G at a different recovered r; its failure events are
not asserted to be independent.

[`NTRUPlus768ACWC2Mean.ec`](../ntruplus/proof/768/ref/acwc2_correctness/NTRUPlus768ACWC2Mean.ec)
uses the actual fixed-message SOTP law to show that the mean of X is
`acwc2_base_mean(w)`, the underlying PKE error averaged over independent
CBD1 code and randomness. This mean is independent of msg. It can vary
with w. The numerical input is the average over actual fresh generated
keys, below `2^-354`; there is no assumption that every key's mean has
that bound. Whole-buffer acceptance conditioning is retained, and no
independence of accepted key coefficients is assumed.

[`NTRUPlus768ACWC2KeyMean.ec`](../ntruplus/proof/768/ref/acwc2_correctness/NTRUPlus768ACWC2KeyMean.ec)
connects this outer mean to `PKEAverage(FreshExpand)` exactly. Its contracts
establish normalization and generated-key validity of the actual reified
KeyGen law, the average identity and the bound below `2^-354`. The final
instantiation leaves no average-error, validity or independence hypothesis
for a caller to supply.

The centered coordinate is
`w_r * (1[B_r(G(r))] - Pr_pad[B_r(pad)])`. Its expectation is zero and its
absolute value is at most w_r. The code proves its complete independent
joint law, finite support and normalization before applying the moment
theorem.

## Concentration and numerical combination

[`NTRUPlus768ACWC2Domains.ec`](../ntruplus/proof/768/ref/acwc2_correctness/NTRUPlus768ACWC2Domains.ec)
and
[`NTRUPlus768ACWC2Collision.ec`](../ntruplus/proof/768/ref/acwc2_correctness/NTRUPlus768ACWC2Collision.ec)
retain the biased CBD1 weights. Each coefficient has probabilities
`1/4, 1/2, 1/4` for `-1, 0, 1`, and

```text
sum_r w_r^2 = (3/8)^768.
```

The actual centered variables satisfy the hypotheses of the finite
independent eighth-moment theorem in
[`NTRUPlus768ACWC2Moment.ec`](../ntruplus/proof/768/ref/acwc2_correctness/NTRUPlus768ACWC2Moment.ec):

```text
E_G[(X(G) - base_mean(w))^8] <= 105 * (sum_r w_r^2)^4.
```

The finite-message argument unions over all `2^768` messages and then
bounds their expected maximum. It does not require independent bad
events for different messages. With `epsilon = 2^-356`, the conservative
certificate uses `105 <= 2^16` and bounds the union contribution by
`2^-592`. The arithmetic in
[`NTRUPlus768ACWC2Numerical.ec`](../ntruplus/proof/768/ref/acwc2_correctness/NTRUPlus768ACWC2Numerical.ec)
combines the key-averaged base error, epsilon and this contribution to
obtain the target `2^-353` scale. The key average remains outside the
expectation of the message maximum.

## Reproduction and scope

Run from the repository root:

```sh
./scripts/verify-ntruplus768-acwc2-correctness.sh \
  --prior-evidence-root /path/to/thesis \
  --output /path/to/new-evidence-directory
```

The output directory must be new or empty and outside the checkout.
Sources are in
[`ntruplus/proof/768/ref/acwc2_correctness/`](../ntruplus/proof/768/ref/acwc2_correctness/).
The runner checks new mains, semantic EOF obligations, isolated
unfinished-proof negatives, source controls and exact finite diagnostics.
Imported theories are bound to prior evidence by hashes; they are not
all new main replays. The declared setting is September 2026
EasyCrypt/Why3 with Z3, `-no-eco`, `Proofs:check`, one prover and
`OCAMLRUNPARAM=o=20`. `--check-only` is a source check, not a proof replay.

The bound uses the actual fresh accepted-key distribution and the
independently sampled finite G function. It does not transfer itself to
unrestricted cached-ROM KeyGen or to an adversarial continuation. The
earlier initialized honest-KEM returned-failure-plus-missing-mass bound
below `2^-238` is unchanged and concerns a separate experiment.

The [linear-RRec continuation](ntruplus768-linear-rrec.md) separately
proves redundancy of the public helper's extra check and connects the
existing serialized-R2 comparison to reencryption using the same decoded
m1, with result, clearing and separated G/H state preserved. It also
proves total terminal representability and inverse-to-forward congruence.
Full FO reencryption forms a new SOTP code and retains the correctness-loss
reasoning of Theorem 4.3.

The [Gen-law continuation](ntruplus768-keygen-gen-law.md) establishes the
acceptance/unit equivalence and exact fresh Gen projection. The
[modified FO continuation](ntruplus768-modified-fo.md) connects the actual
adaptive shared-oracle game to partial eager G preparation and proves the
full reencryption correctness-loss transition. It uses the stronger
intermediate base-PKE error envelope, rather than inferring it from the
transformed failure event. The [spreadness continuation](ntruplus768-spreadness.md)
separates the G-average bound from the actual expected maximum and
proves a conservative weak-spreadness bound using the same base-error
envelope. Their remaining game-level use and hardness reductions are
still needed for the full security result.
No IND-CCA bound, concrete SHAKE-to-ROM theorem or QROM result follows.
No C/Jasmin implementation, extraction or native API is changed, and no
new native, Safety, CT or SCT replay is claimed.
