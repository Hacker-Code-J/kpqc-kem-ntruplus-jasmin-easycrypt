# NTRU+768 reduction to base-PKE injectivity and one-wayness

This family reduces the concrete ACWC2 CPA attacker constructed in the
preceding KEM proof to computational injectivity and one-way experiments
for the base PKE. The final theorem `sec_original_inj_ow` in
[`NTRUPlus768SecFinal.ec`](../ntruplus/proof/768/ref/kem_acwc2_security/NTRUPlus768SecFinal.ec)
composes that result with the original KEM experiment:

```text
|Pr[CCAOriginalGame(A).run(): win] - 1/2|
  <= 2 (pINJ + pOW)
     + (130820 + 512 qE) / 2^256
     + (q0 + qH,S + d) / 2^353
     + (qC + d) / 2^768,

pINJ = Pr[SecBaseINJGame(SecINJAuxAdapter(SecINJReducer(A))).run(): win],
pOW  = Pr[SecBaseOWGame(SecOWAuxAdapter(SecOWReducer(A))).run(): win].
```

The KEM advantage uses absolute deviation from one half. `pINJ` and `pOW`
are success probabilities, not deviations from one half. The intermediate
`sec_cpa_base` theorem bounds the absolute CPA bias of
`CPAGame(CPAReduction(A))` by `pINJ + pOW`. This is the particular attacker
from the preceding reduction; its message-selection phase makes no G
query. It is not a general theorem for arbitrary CPA attackers with
prechallenge G queries.

The classical-ROM route follows Theorem 3.6 of the pinned official
NTRU+ specification (`ntruplus-spec-20260710` in the thesis bibliography).
The present development gives explicit array procedures, oracle-state
comparisons, finite extractors and base-challenger adapters. It does not
assert an INJ, OW-CPA, NTRU or RLWE hardness assumption. The subsequent
[one-wayness reduction](ntruplus768-ow-hardness.md) bounds the OW term by
explicit conditioned-NTRU and computational RLWE experiments, retaining
the key-acceptance factor. The INJ hardness reduction remains open.

## Public message recovery

For a ternary base-PKE plaintext `M` and randomness `r`, encryption has
polynomial form `c = h*r + M`. The public procedure `MRec(pk,r,c)` computes
`c-h*r` in the serialized NTT representation, normalizes before the
inverse transform, and accepts a ternary result. It checks canonical
public-key/ciphertext encodings and the randomness domain. The procedure
composes existing extracted kernels and checking loops; it is not a newly
exported native API.

The `MRec` sources establish the model, exact recovery properties,
actual-call contracts and checked decoding of G payloads. In particular:

- An accepted recovery result reencrypts to the supplied ciphertext
  (arbitrary-ciphertext message recovery, AC-MR).
- A ciphertext encrypting a valid `(M,r)` under a canonical public key
  recovers that exact `M` (valid-ciphertext message recovery, VC-MR).
- A G payload decodes to `r` exactly when `r` is in the ternary domain and
  its verified serialization is that payload.

No secret key, enumeration of the ternary space, reencryption test or new
decryption-failure premise is used by recovery. This does not give an
attacker the hidden encryption randomness: the security proof charges
executions that query its encoding.

## G programming and the adaptive transcript

`SecPhase` passes one G port to both `SimOracles` and `SimLookup`.
`SecGLogged` records each input before invoking that port. The transcript
therefore includes direct queries, valid raw G requests with output length
zero, repeated requests and G evaluations performed internally by public
decapsulation lookup. The honest challenge evaluation is excluded.
The log is a list, so duplicates are retained. Invalid raw lengths do not
invoke G. A syntactically valid G payload may still fail the ternary
randomness decoder during extraction.

The challenge entry is represented explicitly in the physical G table.
`SecGMarked` records whether an adaptive call reaches its private target.
The programmed and unprogrammed tables are coupled outside that target;
outputs and transcript states are required to agree only until a hit.
After a hit, only the appropriate bad-event relation is retained. Cached
answers are never replaced by fresh samples.

The exact SOTP hiding law converts the unprogrammed challenge to
independent `M,r <- psi1`. The bit then has no influence on the adaptive
view, giving winning probability one half under the robust termination
contract. The change is bounded by the returned target-query probability.
The proof does not reinterpret a returned hit event as an ever-hit event
for a possibly diverging attacker.

## Finite extraction

`SecExtract` visits only payloads that actually occurred in the adaptive
G list. `MRecDecode` rejects invalid encodings; `MRec` rejects unsuccessful
recovery candidates. The scan preserves its explicit first-match order.

The collision reducer knows the pair `(M*,r*)` that it sampled. If a
recovered candidate has `r' != r*`, exact recovery soundness gives two
distinct domain-valid encryption input pairs with the same nonfailure
ciphertext. `sec_inj_win` checks all four domain conditions, distinct
pairs, ciphertext equality and a result different from `None`.
This is computational injectivity as a collision-finding objective; it is
not a proof of mathematical injectivity of the complete encryption map.
The failure default repeats the honest pair and does not win INJ.

The one-way reducer receives only the public key and challenge ciphertext.
If the target randomness was queried and no other-randomness candidate
exists, the first accepted plaintext is the challenge plaintext by VC-MR.
It returns that plaintext. This partitions the hit event into an INJ
witness or successful one-way recovery.

No additional G-query factor appears in the success-probability bound:
the reducer scans the finite recorded list rather than guessing a query
index. The fixed-size recovery calls and terminating scan are explicit,
but a running-time/PPT bound for the complete reduction is not mechanized.

## Base challengers contain no oracle access

`SecBaseKeygen` returns the public key of the actual fresh key generator
with `SecZeroF` in place of the F backend. F contributes only to the unused
KEM secret-key suffix. The proof connects this public projection exactly
to the actual public-key law, then moves the independent F response to the
attacker's auxiliary setup. It does not remove an arbitrary existing F
cache or replace a cached response under an unjustified independence claim.

`SecBaseINJGame` generates that public key and checks the attacker's
collision output. `SecBaseOWGame` generates the public key, samples
independent base message and randomness from `psi1`, and tests message
recovery. Neither challenger initializes or calls a ROM.

`SecINJAuxAdapter` and `SecOWAuxAdapter` internally implement the auxiliary
E/F/G/H/raw simulation and establish `F(pk)` before invoking their concrete
reducers. Exact experiment equalities preserve success probabilities while
moving these auxiliary interfaces out of the challenger. Neither adapter
receives the challenge secret key.

## Contracts and remaining scope

The final composition retains the earlier private-state restrictions and
robust losslessness for all permitted lossless typed/raw and Decaps
backends. It additionally excludes the G transcript and target flag from
the underlying attacker. The earlier contracts keep their original scopes:

- `qE`: effective E requests with the specified initial E-counter state.
- `q0`: combined H-plus-Decaps requests in each native and full-FO backend.
- `d = max(0, SimSelectedBudget.budget)`: the universal Decaps bound.
- `qH,S`: public H requests in the concrete Known backend.
- `qC`: distinct public H records in the concrete CPA phase, from every
  initial phase state.

A bound for one backend is not substituted for another. No query or retry
cap is added to the original interfaces. Probabilities are not conditioned
on return, and termination of the original unlimited cached-ROM KeyGen
is not assumed. Fresh KeyGen losslessness is an existing proved result.
The formal statement concerns classical ROM queries. HAETAE unforgeability,
QROM, native SHAKE/RNG correspondence and C memory/ABI correspondence remain
separate work.

## Reproduction

```sh
./scripts/verify-ntruplus768-acwc2-security.sh
./scripts/verify-ntruplus768-acwc2-security.sh --check-only
```

An explicit reviewed manifest fixes every new main, its hash and final
semantic theorem. Each positive copy contains a semantic EOF check.
Each isolated negative leaves its own final proof unfinished and must
fail at that proof, not while importing a different theory. Source controls
check the G routing, collision predicate, base sampling and extraction
interfaces. Exact finite diagnostics exercise the hit/collision/recovery
partition, first-match behavior, invalid payloads, duplicate queries and
raw/internal G logging. They are not exhaustive tests of NTRU+ security.

The runner uses `compile -no-eco -pragmas Proofs:check -p Z3 -timeout 60
-max-provers 1` with `OCAMLRUNPARAM=o=20` and `EC_JOBS=2` by default (one is
also permitted). `--output` must select a new or empty evidence directory
outside the checkout; `--prior-evidence-root` locates the thesis evidence.
Source and external tool/configuration/theory hashes are audited before
and after replay. Imported EC theories are linked to the preceding
IND-CPA reduction PASS and are not counted as new main checks.
`--check-only` reports `SOURCE_CHECK_ONLY`; freezing an inventory does not
produce a proof PASS.

The evidence directory is
`handoff/verification/ntruplus-acwc2-security-20261018/` in the thesis
workspace. This family does not modify native C/Jasmin sources or rerun
native tests, extraction, Safety, CT or SCT.
