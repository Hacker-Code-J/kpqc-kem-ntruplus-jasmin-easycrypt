# Erasing programmed KeyGen E entries in the NTRU+768 CCA game

All 15 mains (254 lemmas) have completed individual strict verification.
**Full replay PASS**, 2026-10-15: 15 mains / 254 lemmas,
15 semantic EOF probes and 15 own-main unfinished-proof rejections.
The replay also passed 49 structural/trust controls
and 30 exact finite diagnostics, with
850 source pins and 863 audited source inputs.
All 298 external tool/configuration/theory/driver/prior-evidence inputs
and all source inputs matched before/after hashes. The 652 imported EC files
are linked to 14 prior PASS records, not counted as newly replayed mains.
The report contains 37 command logs and 30 checked proof copies.
A separate portable check resolves the prior records under another evidence
root; that quick check is labeled SOURCE_CHECK_ONLY. Evidence belongs to
`handoff/verification/ntruplus-e-erasure-20261015/`.

This proof-only continuation compares a game whose fresh KeyGen proposals
are recorded in E with one whose KeyGen uses independent fresh buffers and
leaves E empty. The actual key generation, challenge encapsulation,
challenge-excluding decapsulation, typed/raw oracle interfaces and F/G/H
state remain in the experiment. The new step bounds the chance that the
adversary queries a hidden KeyGen seed.

The [earlier CCA setup theorem](ntruplus768-cca-setup.md) already compares
actual cached-ROM KeyGen with programmed fresh setup, without assuming
adversary termination. Its error below `2^-239` is for that preceding hop.
It is not the cost of erasing the programmed E entries. The erasure
composition here has explicit adversary-termination and query-budget
conditions and an additional error term.

The subsequent [modified FO comparison](ntruplus768-modified-fo.md)
adds `Q/2^353` for Q H/Decaps requests under separate native/full backend
count contracts and robust adversary losslessness. It retains this E
bound and gives an actual-game comparison, not the final IND-CCA advantage.

## Games, effective queries and assumptions

[`NTRUPlus768ErasureGames.ec`](../ntruplus/proof/768/ref/kem_e_erasure/NTRUPlus768ErasureGames.ec)
defines three games using the analysis wrapper `CappedA(A)`:

| Game | Setup expansion |
|---|---|
| `ErasureOriginalGame(A)` | Actual unrestricted `ExpandROM`. |
| `ErasureProgrammedGame(A)` | Independent fresh buffers recorded at their sampled seeds in E. |
| `ErasureIndependentGame(A)` | `FreshExpand`, which leaves the initially empty E table untouched. |

`EBudgetState` is configured with a nonnegative qE before these games.
The cap is an explicit analysis policy, not a new limit on the original
implementation. In
[`NTRUPlus768ErasureBudget.ec`](../ntruplus/proof/768/ref/kem_e_erasure/NTRUPlus768ErasureBudget.ec),
`CountEPort` forwards every original request while recording a private count.
`CapEPort` forwards at most qE effective E requests. Later typed E requests
return the fixed witness buffer; later raw E requests return `None`, without
calling the backend. Other requests retain their original behavior.

An effective request is either a typed E call or a raw call with exactly
32 input bytes and a valid output length in `0..224`. Raw E inputs are
untagged. Repeated requests count again, including cached queries, and a
valid output length of zero still counts because the actual raw procedure
calls E. Invalid raw lengths and requests in other domains are not E
requests. KeyGen's own setup calls are separate from this adversarial qE
count.

The game-erasure argument requires two distinct conditions:

- **Robust adversary losslessness.** For every permitted extended oracle
  port H and decapsulation port D, losslessness of H.e, H.f, H.g, H.h,
  H.raw and D.decap implies losslessness of `A(H,D).guess`. The usual module
  restrictions also prevent A from reading the private seed log, pool,
  hit flag, budget state or analysis tape directly.
- **A universal initial-state query bound for cap removal.** The observed
  `CountedA(A,SharedCCAExtendedOracles,CCADecapOracle).guess` makes at most
  qE effective requests from zero counters, limit qE, a false overflow flag
  and an empty query log. This Hoare condition ranges over the remaining
  initial state and input values; it is not a bound measured in one run or
  an expected query count. The capped-game bound uses the cap itself; the
  separate count contract is needed to recover the uncapped games.

The robust termination condition concerns the adversary phase. It does not
assume that actual unrestricted cached-ROM KeyGen terminates. A query cap
alone does not imply termination: an adversary may loop after a hit. A
return-time `bad` probability would then omit that hit's nonreturning mass.
The full erasure transition is therefore not claimed here for arbitrary
nonterminating A. Separate subdistribution hit-averaging helpers do not
remove this game-level premise.

## Every attempted seed, and the independent full pool

[`NTRUPlus768ErasureModel.ec`](../ntruplus/proof/768/ref/kem_e_erasure/NTRUPlus768ErasureModel.ec)
records a seed before each expansion. Accepted and rejected attempts are
both retained, and repeated seeds remain repeated list entries. Programmed
expansion overwrites E when a seed repeats; the erased expansion samples
the same fresh buffer without that table write.

The coupling in
[`NTRUPlus768ErasureSetup.ec`](../ntruplus/proof/768/ref/kem_e_erasure/NTRUPlus768ErasureSetup.ec)
preserves the actual result, F table and whole used-seed list. The E tables
agree outside that list. This is a relation between complete states, not an
output-only event comparison and not equality of the two entire E tables.
The [Prefix contracts](../ntruplus/proof/768/ref/kem_e_erasure/NTRUPlus768ErasurePrefix.ec)
prove `size used = initial_size + nf + ng`, preserve joint-state events on
the successful finite prefix and reuse the fresh retry-tail bound.

For nonnegative retry budgets qf and qg, let `Q=qf+qg` and `N=nf+ng` in the
stopped setup. Then `N<=Q`. The exact bridge in
[`NTRUPlus768ErasureSeedPool.ec`](../ntruplus/proof/768/ref/kem_e_erasure/NTRUPlus768ErasureSeedPool.ec),
`erasure_padded_postsample`, moves sampling of a full Q-entry uniform32 pool
after the visible setup output, F table and counts. Thus the full pool is
independent of those observations. The actual used log is

```text
used = rev(take N pool).
```

N depends on the acceptance history. The used log has length N and is not
independent of N; no independence of the variable-length used log from the
whole setup is asserted. Every used seed belongs to the full pool, which
is sufficient for the hit bound. The unused padding entries are private
analysis samples: they are never programmed into E and do not add real
KeyGen attempts.

[`NTRUPlus768ErasureSeedTape.ec`](../ntruplus/proof/768/ref/kem_e_erasure/NTRUPlus768ErasureSeedTape.ec)
connects online draws with the pre-sampled tape by moving refreshes of only
the unread suffix. Its normalization makes the generic eager rule total;
on the valid states of the actual setup it is the identity. The raw/normalized
sampler contracts preserve the sampling and cap behavior used by this bridge.

Both game bodies initialize E to empty. Consequently the erased setup
leaves an empty E table available to later queries, while preserving actual
F-cache updates. This is not a theorem that clearing an arbitrary nonempty
initial table preserves its old answers.

## Adaptive queries and the finite-prefix error

[`NTRUPlus768ErasureQueryKernel.ec`](../ntruplus/proof/768/ref/kem_e_erasure/NTRUPlus768ErasureQueryKernel.ec)
keeps the actual challenge and adaptive oracle/decapsulation continuation.
Its observation contains the attempt count and forwarded E-query list.
Private pool samples can be moved after this observation in the independent
game. For a query list of length at most qE,
[`NTRUPlus768ErasureHitBound.ec`](../ntruplus/proof/768/ref/kem_e_erasure/NTRUPlus768ErasureHitBound.ec)
gives

```text
hit(Q,qE) = Q*qE / 2^256.
```

Neither list must contain distinct entries. The used-prefix hit event is
contained in the full-pool hit event. The actual-game connection is composed
in [`NTRUPlus768ErasureActualHit.ec`](../ntruplus/proof/768/ref/kem_e_erasure/NTRUPlus768ErasureActualHit.ec)
and the oracle/adversary coupling files. Their good-event relations preserve the shared F/G/H, raw-stream,
decapsulation and adversary state, with E agreement outside the hidden list.

Write

```text
tau(qf,qg) = (1-p_f)^qf + (1-p_g)^qg
          <= (3/8)^qf + (3/8)^qg,
delta(0,Q) = Q*(Q-1)/(2*2^256).
```

The proved bound between the two capped, unrestricted-retry programmed and
independent games is

```text
|Pr[ErasureProgrammedGame(A): win]
 - Pr[ErasureIndependentGame(A): win]| <= hit(Q,qE) + tau(qf,qg).
```

The common-tail interval argument charges one retry tail for this hop.
Composing the preceding actual-ROM-to-programmed setup comparison adds
`delta(0,Q)+tau(qf,qg)`, giving the proved total

```text
actual ROM -> independent: delta(0,Q) + 2*tau(qf,qg) + hit(Q,qE).
```

For qf=qg=256, the arithmetic contract bounds this expression by
`(130820+512*qE)/2^256`. The stated `<2^-238` specialization fixes qE=256;
that numerical conclusion is not asserted for an arbitrary query budget.
The budgets qf and qg bound analysis prefixes and do not impose retry limits
on the unrestricted implementation. All probabilities are returned-win
probabilities without conditioning on return.

## Cap removal, reproduction and remaining scope

[`NTRUPlus768ErasureCapRemoval.ec`](../ntruplus/proof/768/ref/kem_e_erasure/NTRUPlus768ErasureCapRemoval.ec)
separates the observational counter from the enforcing cap. Robust
adversary losslessness and the universal count bound rule out overflow.
The final composition removes the cap on both the original and independent
sides without adding error. The private monitor starts at zero; the two
endpoints retain the original uncapped attacker interface.

[`NTRUPlus768ErasureSecurity.ec`](../ntruplus/proof/768/ref/kem_e_erasure/NTRUPlus768ErasureSecurity.ec)
provides the final endpoints:

| Endpoint | Proved comparison |
|---|---|
| `erasure_programmed_independent_distance` | Capped programmed versus independent games: `hit + tau`. |
| `erasure_original_independent_capped_distance` | Capped actual-ROM versus independent games: `delta + 2*tau + hit`. |
| `erasure_original_independent_distance` | Original `CCAOriginalGame(A)` versus `CCASharedSetupGame(FreshExpand,A)`, after both caps are removed under the universal count contract. |
| `erasure_original_independent_256` | The same uncapped endpoints with qf=qg=256: `(130820+512*qE)/2^256`. |

Combining `erasure_original_independent_distance` with
`erasure_error_256_queries_238` gives the stated `<2^-238` specialization
at qf=qg=qE=256. The robust adversary and query
conditions remain part of this numerical conclusion.

Run the family from the repository root:

```sh
./scripts/verify-ntruplus768-e-erasure.sh \
  --prior-evidence-root /path/to/thesis \
  --output /path/to/new-evidence-directory
```

Use a new or empty output directory outside the checkout. The runner's
shell syntax and `--help` interface have been checked. The completed report,
logs and matching source hashes determine the full replay result. Controls
are in [`tests/ntruplus768/e_erasure/`](../tests/ntruplus768/e_erasure/), with
sources in [`ntruplus/proof/768/ref/kem_e_erasure/`](../ntruplus/proof/768/ref/kem_e_erasure/).
`--check-only` does not execute a proof replay. The declared configuration
uses September 2026 EasyCrypt/Why3, Z3, `-no-eco`, `Proofs:check`, one prover
and `OCAMLRUNPARAM=o=20`.

The [Gen-law result](ntruplus768-keygen-gen-law.md) retains its exact
Figure 18 `(h,f)` marginal statement, and the preceding CCA setup theorem
retains its broader partial-adversary scope. This continuation completes
neither the full IND-CCA bound nor the FO or hardness reductions. It makes
no QROM claim and changes or newly replays no C/Jasmin implementation,
extraction, native API, Safety, CT or SCT result.
