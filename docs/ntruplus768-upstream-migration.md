# NTRU+768 upstream compatibility and paper-target decision

## Closed costs for actual word-array reductions (2026-10-21)

The [runtime-bound proof](ntruplus768-runtime-bound.md) gives the same
three concrete word-array witnesses the original IND-CCA inequality and
closed fixed-768 costs in a source-calibrated primitive model. The actual
persistent history, G transcript, extraction, arithmetic, array copies
and fixed reduction setup are included.

With Q counting all public callbacks, B the total raw-input byte volume,
and t_A a separate reserve for A's own work excluding oracle bodies:

```text
Cost_R(t_A) <= t_A + 10909917*Q^2 + 32450882*Q + 64*B + C_R,
C_DI=17679874, C_DO=10492283, C_CO=18463740.
```

Repeats and zero-output raw requests count toward Q; Q is not the
security theorem's distinct-H bound qC. The cost frontend and its
source-pricing rules are part of the stated trust boundary. Ideal ROM
operations and unit-cost integer arithmetic remain model primitives.
No CPU-cycle, bit-complexity or general parameter-family PPT theorem is
claimed. The original security assumptions, signed hardness terms,
acceptance factor and loss terms are unchanged.

```sh
./scripts/verify-ntruplus768-runtime-bound.sh
```

## Adaptive persistent list reduction (2026-10-20)

The [adaptive history proof](ntruplus768-adaptive-history.md)
connects the concrete H list to the full adaptive attacker and its actual
G transcript. The original CCA game is bounded by three concrete
list-based NTRU/RLWE reduction attackers, with additional loss
`2*qC/2^353` outside `alpha_g`. Here qC is the original distinct-H bound.

The original adversary restrictions and all existing termination,
initial-state and query contracts are preserved. Fresh local storage is
created after the original adversary declaration; the actual reduction
witnesses are fixed before all initial memories and query budgets. The
final export is independently type-checked. The subsequent runtime-bound
proof closes the costs of the same word-array witnesses in its explicit
fixed-768 model. General PPT, native correspondence, HAETAE UF-CMA and
QROM remain separate objectives.

```sh
./scripts/verify-ntruplus768-adaptive-history.sh
```

## Concrete public histories and lookup-order bound (2026-10-20)

The [history refinement](ntruplus768-history-refinement.md) implements
H-history retrieval/update and public lookup with explicit list and byte
loops. It proves the map representation, exact per-operation counts and
aggregate history costs for Q fixed H requests followed by one lookup:
node visits <=Q^2, explicit comparisons <=64Q(Q-1)+1184Q+1152.

The actual old/list lookup reply distributions differ by at most
Q*fo_error(w,g); the existing fresh key/G setup gives Q/2^353. Repeated H
requests reuse their cache. The public implementation receives no secret
key or error function. All pointwise error and setup-support premises are
proved for these actual finite-history experiments.

This fixed-query result alone does not replace the adaptive backend.
The subsequent adaptive-history proof above connects persistent state,
the changed G trace and extraction. The runtime-bound proof then closes
the source-calibrated fixed-768 costs, with A's own work reserved separately.

```sh
./scripts/verify-ntruplus768-history-refinement.sh
```

## Local reduction resource bounds and preserved probability (2026-10-19)

The [resource accounting proof](ntruplus768-reduction-cost.md) counts
actual public-lookup visits, internal encryptions, candidate calls and raw
payload bytes. Local counters preserve original results and state. The
three resulting hardness attackers have the same success probabilities,
so the original IND-CCA inequality and all adversary contracts are retained.

For an explicit finite measurement list, at most d lookups of snapshot
size at most h give total visits <=d*h and encryptions K<=d*h. Extraction
from a G list of length g+K makes at most g+d*h candidate calls. These are
local/finite-trace counts. Subsequent history/adaptive refinement and
the runtime-bound proof connect the actual execution and close its stated
fixed-768 source-calibrated costs; general PPT remains outside that result.
Raw outputs are at most224bytes, but one valid zero-output request can
supply arbitrarily many input bytes. Query budgets alone do not bound
input volume. The three final attackers contain no KeyGen retry loop.

```sh
./scripts/verify-ntruplus768-reduction-cost.sh
```

## Uniform short relations bounded below 2^-244 (2026-10-18)

The [statistical bound](ntruplus768-short-relation-bound.md) proves
`deltaSR < 2^-244` without a short-relation hardness assumption. The actual
integer quotient multiplication matrix, rational irreducibility of
`X^768-X^384+1`, Hadamard's inequality and a Smith-normal-form fiber bound
cover nonunit differences modulo3457. A concrete finite union bound and
exact rational arithmetic close the existing entire-ring existence event.

The original classical-ROM KEM advantage is consequently bounded by

```text
AdvCCAOriginal(A) <= 2*(DeltaNTRU(D_I)+DeltaNTRU(D_O)+epsRLWE(C_O)+2^-244)/alpha_g
 + (130820+512*qE)/2^256 + (q0+qH,S+d)/2^353 + (qC+d)/2^768.
```

Both signed NTRU gaps, the accepted-key factor and all original termination,
initial-state and query contracts are preserved. Coq8.20.1/MathComp2.2
checks the algebraic helpers through native EasyCrypt goals, including a
separate kernel check against the proposition captured before helper imports.
No new algebraic axiom is inserted into EasyCrypt. Full reduction complexity,
HAETAE UF-CMA, QROM and native memory/ABI correspondence remain separate.

```sh
./scripts/verify-ntruplus768-short-relation-bound.sh
```

## Collisions reduced to uniform short relations (2026-10-18)

The [collision reduction](ntruplus768-inj-hardness.md) extracts a nonzero pair of signed
integer differences satisfying h*v+w=0, with coefficients in [-2,2].
Each squared coefficient norm is at most 3072; their sum is at most 6144.
The exact probability bounds are

```text
epsINJ <= (DeltaNTRU(D_I)+epsSR(C_I))/alpha_g;
epsSR(C_I) <= deltaSR = Pr[a <- uniform R_q : a short nonzero relation exists].
```

The original KEM bound is composed with these results and the preceding
OW reduction. The two NTRU distinguishers retain the specified denominator
conditioning and g-acceptance factor. The short-relation challenge uses
the row [a,1] with a uniform over the entire ring. No iid Ring-SIS
equivalence or numerical negligibility of deltaSR is assumed.
The subsequent [statistical bound](ntruplus768-short-relation-bound.md)
proves deltaSR < 2^-244 and composes it into the same original game.

```sh
./scripts/verify-ntruplus768-inj-hardness.sh
```

## One-wayness reduced to explicit NTRU and computational RLWE (2026-10-18)

The [one-wayness reduction](ntruplus768-ow-hardness.md) preserves the actual key-acceptance
factor and proves

```text
epsOW <= (DeltaNTRU(D) + epsRLWE(C)) / alpha_g, alpha_g >= 5/8.
AdvCCAOriginal(A) <= 2*epsINJ + 2*(DeltaNTRU(D)+epsRLWE(C))/alpha_g
  + (130820 + 512*qE)/2^256
  + (q0 + qH,S + d)/2^353 + (qC + d)/2^768.
```

The NTRU denominator is explicitly conditioned to be a unit; its numerator
is unconditioned. Uniform challenges cover the whole ring, including
nonunits. The RLWE solver recovers the secret from a correctly recovered
error using checked public inversion. The byte codec and actual key law
connect these experiments to the preceding base-PKE attacker.
The subsequent [collision reduction](ntruplus768-inj-hardness.md) exposes an explicit
uniform short-relation term, now bounded by the subsequent statistical proof.
The complete PPT/time theorem remains open.

```sh
./scripts/verify-ntruplus768-ow-hardness.sh
```

## Original IND-CCA game reduced to base-PKE INJ and OW-CPA (2026-10-18)

The [base-PKE reduction](ntruplus768-acwc2-security.md) constructs concrete collision-finding and
one-way attackers and proves

```text
AdvCCAOriginal(A) <= 2 (Pr[base INJ success] + Pr[base OW-CPA success])
  + (130820 + 512 qE)/2^256
  + (q0 + qH,S + d)/2^353 + (qC + d)/2^768.
```

The KEM advantage is absolute winning-probability bias. The two base
terms are success probabilities in challengers with no random-oracle
calls or initialization. Their concrete attackers simulate the auxiliary
E/F/G/H/raw interfaces. Public MRec and G-input decoding use the existing
extracted kernels; only the actual finite G transcript is scanned.
Private-state, robust termination and the distinct query contracts are
retained. This step adds no G-query multiplier to the probability bound.
The subsequent [one-wayness reduction](ntruplus768-ow-hardness.md) bounds the OW term
by explicit conditioned-NTRU and computational RLWE experiments.
INJ hardness, a complete PPT/time theorem, QROM, HAETAE and native
memory/ABI remain separate obligations.

```sh
./scripts/verify-ntruplus768-acwc2-security.sh
```

## Original IND-CCA game reduced to concrete ACWC2 IND-CPA (2026-10-18)

The [IND-CPA reduction](ntruplus768-indcpa-reduction.md) constructs `CPAReduction(A)` and proves

```text
AdvCCAOriginal(A) <= 2 AdvCPAGame(CPAReduction(A))
  + (130820 + 512 qE)/2^256
  + (q0 + qH,S + d)/2^353 + (qC + d)/2^768.
```

Advantages are absolute winning-probability deviations from one half.
The stated private-state, robust termination and separate query contracts
are retained. The CPA challenge and public simulator share G, and the
auxiliary E/F/raw states are preserved. This completes the explicit
original-game-to-CPA probability reduction. The subsequent
[base-PKE reduction](ntruplus768-acwc2-security.md) bounds that CPA term by concrete INJ and
OW-CPA success; the NTRU/RLWE hardness reductions remain open. Runtime/PPT accounting,
HAETAE unforgeability, QROM and native memory/ABI obligations remain separate.

```sh
./scripts/verify-ntruplus768-indcpa-reduction.sh
```

## Public H-history simulation of full modified FO (2026-10-16)

The [public-history simulation](ntruplus768-fo-simulation.md) compares the actual fresh full-FO
game with an uncapped simulator whose Decaps port uses only public key
data and logged H replies. Under robust adversary termination, a universal
Decaps count contract and the Known-backend public-H count contract,

```
|Pr[FOFreshReencryptGame(A): win] - Pr[SimPublicFreshGame(A): win]|
  <= qD/2^768 + (qH+qD)/2^353.
```

Here qD is the nonnegative persistent hybrid budget. Typed/raw H repeats
and valid zero-output requests count. Hidden H/G evaluations are removed
through adaptive private-sampling equalities; public history is never
identified with the full physical cache. The earlier original/native-to-
full-FO comparison keeps its separate hypotheses and bound. The later
[IND-CPA reduction](ntruplus768-indcpa-reduction.md) composes this result with a concrete CPA
attacker; the hardness reductions remain separate.

```sh
./scripts/verify-ntruplus768-fo-simulation.sh
```

## Ciphertext spreadness with explicit oracle scope (2026-10-15)

The [spreadness continuation](ntruplus768-spreadness.md) proves a tight
`2^-768` base-PKE ciphertext bound from actual CBD sampling, valid generated
keys and randomness recovery. The public-KeyGen/initialized-ROM experiment
retains that returned-event upper bound without assuming ROM termination.

For SOTP encryption, the fixed-message/ciphertext G-average is at most
`2^-768`. A separate correctness-based argument proves the actual expected
maximum `<2^-768+2^-353<2^-352` under fresh-key/F/G setup. An existing lazy
cache costs at most `(fsize(cache)+1)*2^-768` for a new independent r draw.
The actual caller preserves its whole G table. These statements retain
their different quantifiers and do not complete the FO hardness reduction.

```sh
./scripts/verify-ntruplus768-spreadness.sh
```

## Actual decapsulation and full modified FO comparison (2026-10-15)

The [modified FO continuation](ntruplus768-modified-fo.md) connects
actual decapsulation to a new SOTP encoding and full reencryption, with
explicit recovered-randomness domain checks and preserved failure-side
hash calls. The actual shared G context is linked to finite preparation,
and the challenge H entry is excluded by a separate rejection argument.

For a robustly terminating adversary satisfying both native/full backend
request contracts, Q H/Decaps requests cost at most `Q/2^353`. Adding the
preceding E-erasure contract yields the actual uncapped-game comparison
`(130820+512*qE)/2^256 + Q/2^353`. Actual ROM KeyGen termination is not
assumed. The subsequent spreadness bounds supply a further ingredient; remaining
security-game and hardness reductions are needed for the complete IND-CCA bound.

```sh
./scripts/verify-ntruplus768-modified-fo.sh
```

## Programmed E-entry erasure (2026-10-15)

The [E-erasure continuation](ntruplus768-e-erasure.md) proves the next
adaptive game transition, with an explicit robust adversary-termination
condition and an effective E-query cap. It includes accepted/rejected and
repeated setup seeds, and counts repeated typed/raw E requests, including
valid raw requests with output length zero. A full Q-entry uniform seed
pool is independent of the visible setup output, F cache and counts; the
used N-prefix remains dependent on N, and unused padding is never programmed.

The two capped fresh games have error at most `Q*qE/2^256 + tau`. The combined
actual-ROM-to-independent bound is `delta + 2*tau + Q*qE/2^256`, bounded by
`(130820+512*qE)/2^256` at qf=qg=256. The `<2^-238` specialization uses qE=256.
The uncapped endpoint also needs the universal initial-state CountedA query
contract, which removes both caps and restores the original attacker
interface at both endpoints. Actual ROM KeyGen termination is not assumed. The earlier CCA
setup theorem below retains its separate partial-adversary scope and error.

See the new guide for the current contracts and full replay status; use
`scripts/verify-ntruplus768-e-erasure.sh`. This proof-only step changes no
native, Safety or CT/SCT result and does not complete IND-CCA, FO, hardness
or QROM reductions.

## Actual acceptance and the Figure 18 Gen law (2026-10-15)

The [Gen-law continuation](ntruplus768-keygen-gen-law.md) proves the
acceptance/Gen identification left open by the PKE distribution work. It connects actual
inverse status to terminal inverse existence, then to quotient-ring units
using injectivity and surjectivity on finite canonical terminal arrays.
An independently defined canonical h satisfies `h*f=3*g0`; supported
existence and uniqueness connect this relation to the returned byte keys.

The exact laws equate every `(h,f)` projection event of actual fresh and
programmed KeyGen with the corresponding event of `Figure18Gen.run()`,
which executes the two polynomial rejection loops. They distinguish Figure 18's polynomial keys from
Algorithm 11's packed NTT keys, inverse-h block and F suffix. The separate
cached-ROM marginal distance is below `2^-239` with empty initial E and
possible nonreturn. Programmed E/key correlation and actual F-cache updates
are retained. The subsequent [E-erasure continuation](ntruplus768-e-erasure.md)
proves E removal under stronger adversary/query assumptions. The full FO
reduction remains separate.
All eight mains have completed individual strict verification. The guide
records full replay status and the official pinned specification record;
the runner is `scripts/verify-ntruplus768-keygen-gen-law.sh`. Earlier family
counts and correctness/security scopes below are unchanged.

## Shared-state CCA setup comparison (2026-10-14)

The [CCA setup continuation](ntruplus768-cca-setup.md) compares the actual
unrestricted ROM KeyGen with independent expansion samples programmed
into its shared E table. The observation includes the keygen witness,
cleared workspace and final E/F tables. Its proved distance is
`delta + tau`; the setup comparison retains possible ROM nonreturn.

The distribution-level argument passes that complete state to the actual
challenge-first CCA continuation. Typed and raw queries keep the same
tables, including the latest recorded answer at each programmed E input.
The actual game winning-probability difference is at most `130818/2^256`,
strictly below `2^-239`, without requiring A to terminate. This does not
assert a small missing mass for either full game; a separate full-game
returned-mass comparison is not stated.

Fresh proposal buffers are independent, while the generated key and final
E table are correlated. There is no adversarial query during KeyGen and
no table erasure afterward, so this transfer needs no additional term
for subsequent E-query count. Replacing the table by an independent
PKE/FO oracle requires the separate hit/query-budget step in
[the E-erasure continuation](ntruplus768-e-erasure.md), whose robust
adversary-termination premise is not needed by this setup comparison. The
[Gen-law continuation](ntruplus768-keygen-gen-law.md) identifies the
fresh/programmed returned-key `(h,f)` marginal with Figure 18 Gen. The public-key-dependent FO argument and hardness reductions
remain open.
The guide records final verification status; reproduction uses
`scripts/verify-ntruplus768-cca-setup.sh`. No C/Jasmin or CT/SCT result is
changed by this proof-only continuation.

## Linear public randomness recovery (2026-10-14)

The [linear-RRec continuation](ntruplus768-linear-rrec.md) removes the
public helper's explicit reencryption call while preserving its encoding,
public-inverse and ternary-domain guards. Its complete option result is
proved equal to checked RRec on every input. Its proved
transform foundation supplies a representative for every terminal array
and inverse-to-forward congruence on the supported q-range; these are no
longer missing existence premises.

A separate actual-caller proof equates the existing CompleteDecaps
serialized-R2 comparison with PKE reencryption using the same decoded m1,
for valid keys and every ciphertext. It preserves result, cleared
workspace and the G/H states under the explicit generic `H{-G}` state
restriction; the concrete separate G/H ROM tables discharge that
restriction. No functional hash or hash-call losslessness premise is used.
The native path does not run R2 inverse NTT or the helper's trit check.
The ACWC2 caller using `LinearRRec` inherits the same `2^-353` bound in the
original fresh-key, finite-G experiment. Full FO instead re-encodes the
decoded message using the newly derived randomness; Theorem 4.3 retains
a correctness-error loss. See the new guide for the caller contracts and
final replay status. This continuation
changes no C/Jasmin implementation or native API, and does not discharge
paper-Gen identification, the full acceptance/unit equivalence or the
security reductions. The later [Gen-law continuation](ntruplus768-keygen-gen-law.md)
discharges the first two obligations for the returned `(h,f)` projection
under fresh or programmed expansion.

## Expected worst-message ACWC2 correctness (2026-10-14)

The new array composition connects actual PKE encryption/decryption,
public checked RRec and SOTP to a fixed G function and the corresponding
prepared actual G cache. The proved bound is
`E_key E_G max_message Pr_r[failure] < 2^-353`, under the actual fresh
accepted-key law and independent uniform G entries on the complete finite
ternary randomness domain. The message maximum stays inside both
expectations.

The concrete endpoint `acwc2_fresh_worst_actual_calls` maximizes actual
`ACWC2FixedOracleTrial` failure probabilities. Each trial deterministically
installs the previously selected G answers before the actual uniform
buffer draw, checked CBD1 and transformed kernel calls. It does not draw
a different G for each message.

The concentration variables are underlying PKE failure indicators, each
reading only one G(r), with the actual biased CBD1 randomness weights.
They contain transformed failure; transformed decoder failures themselves
are not assumed independent. Fixed-message SOTP hiding identifies their
mean with the per-key PKE average, and only the outer key average is bounded
by `2^-354`. Eighth moments and a finite-message union give the proved numerical
bound. See [the ACWC2 correctness guide](ntruplus768-acwc2-correctness.md)
for the final integration/replay status and run
`scripts/verify-ntruplus768-acwc2-correctness.sh`.

This changes no native API and does not identify a prepared eager G table
with an initially empty lazy table in arbitrary adversarial contexts.
The public-helper and existing-byte-comparison connections are addressed
separately by the [linear-RRec guide](ntruplus768-linear-rrec.md).
Public-key-dependent FO and hardness reductions remain separate. The
[Gen-law continuation](ntruplus768-keygen-gen-law.md) proves the full
acceptance/unit equivalence and the exact Figure 18 `(h,f)` law under fresh
or programmed expansion.
The existing initialized honest-KEM bound below `2^-238` keeps its original
experiment.

## Public RR, SOTP and G-input contracts (2026-10-14)

The public checked RR helper computes its inverse from the checked public
key, retains the actual DecapR2 and inverse-NTT calls, and adds explicit
centering, trit validation and one PKE reencryption check. Its honest
forward contract covers all ternary message/randomness pairs for valid
generated keys without the no-wrap event. For arbitrary ciphertexts,
success returns randomness whose actual PKE encryption reproduces the
complete ciphertext bytes.

The SOTP wrappers establish roundtrip, successful-decode rigidity and the
fixed-message CBD1 law under an independent uniform pad. The G bridge
uses the actual NTT and preparation calls to produce an injective
1152-byte payload and tag-1 1153-byte query on the ternary domain. Cached
queries reuse their pad; the uniform law requires a fresh serialized
input in the current G table.

This proof-only helper is not a new native Figure 18 RRec implementation.
The later [linear-RRec development](ntruplus768-linear-rrec.md) proves
redundancy of its extra consistency check on arbitrary ciphertexts and
supplies the separate existing-caller comparison contract. This contract
family alone supplies no worst-case-message estimate or IND-CCA reduction;
the ACWC2 continuation above uses its interfaces. The
existing PKE/KEM average bounds and native boundaries remain unchanged.
The full replay passed. See [the ACWC2 contract guide](ntruplus768-acwc2-contracts.md)
for its checked scope and counts, and run
`scripts/verify-ntruplus768-acwc2-contracts.sh`.

## Underlying PKE average correctness (2026-10-14)

The new proof-only PKE procedures compose the existing extracted checked
decoder, NTT, basemul, centered addition, serialization and candidate
kernels. The average experiment keeps actual fresh KeyGen, its Finish and
clearing calls, and independent checked-CBD1 samples for message and
randomness. Its failure bound is below `2^-354` under the implementation's
whole-array acceptance-conditioned key law. A separate experiment with
initially empty E/F tables and unrestricted cached-ROM KeyGen bounds returned
failure plus missing mass below `2^-238`. It uses the stateless no-wrap
observer transfer and includes no adversarial continuation.

The polynomial distribution bridge proves the unconditioned iid CBD1 law,
whole-array conditioning and scalar-three unit equivalence. It does not
identify the actual acceptance predicate with the paper's quotient-ring
unit test in both directions. The earlier general ring-encryption theorem
has an explicit terminal-representation premise; the
[linear-RRec continuation](ntruplus768-linear-rrec.md) now supplies total
terminal representability. The generated-key c*f identity already required
no assumed public-key representative or no-wrap condition.

The [Gen-law continuation](ntruplus768-keygen-gen-law.md) now proves the
full acceptance/unit equivalence and identifies the fresh/programmed
returned-key `(h,f)` law with Figure 18 Gen. Hardness/FO security reductions
remain open.
The ACWC2 continuation above addresses
the expected worst-message step for fresh keys and finite independent G;
its guide records the final verification status. The earlier `2^-238` initialized honest-KEM correctness
bound and native boundaries are unchanged. See
[the PKE average guide](ntruplus768-pke-average.md) and run
`scripts/verify-ntruplus768-pke-average.sh`; the completed runner report and
matching hashes determine the replay result.

## Classical-ROM IND-CCA game/API layer (2026-10-14)

The proof-only game layer connects the actual KeyGen, randomized Encaps and
CompleteDecaps callers to a challenge-first adversary interface. Typed
E/F/G/H queries share the honest tables. Raw requests classify the complete
input and use persistent prefixes with an output bound of 224 bytes,
including requests beyond the usual typed output length.

The status adapter returns `Some(ss)` on status zero, including an all-zero
key. The private decapsulation oracle counts every request, blocks the exact
1152-byte challenge before any Decaps/hash call, and forwards every other
ciphertext to the actual guard. No query-count cap is imposed. The partial
game records nonreturn; finite setup exhaustion is completed with an
independent fair bit, with adversary losslessness stated separately.

This adds game definitions, API projections and probability identities.
It supplies no IND-CCA security bound and does not extend the existing
honest correctness estimate to adversarial executions. The ACWC2 result
uses a separate prepared finite-G experiment; its connection to this
adversarial game, the public-key-dependent FO reduction, hardness assumptions
and native boundaries remain open. See [the game guide](ntruplus768-kem-indcca-game.md)
and `scripts/verify-ntruplus768-kem-indcca-game.sh`. The completed runner
report and matching source hashes establish the replay result.

## Numerical honest-ROM correctness (2026-10-14)

The numerical continuation connects the actual initialized
`KEMROMCorrectness(UniformKEMRNG)` experiment to a total returned-failure plus
missing-mass bound below `2^-238`. Its independent uniform 32-byte seeds and
96-byte coins, empty E/F/G/H tables and one honest Encaps--Decaps execution
are explicit. The actual callers and their clearing operations remain intact.

The proof chain uses the implemented CBD1 product law, disjoint four-trit
blocks for each coefficient, a no-wrap threshold of at least 576, and
whole-buffer key conditioning. The raw ideal tail is below `2^-356`, the
accepted-key ideal tail below `2^-354`, and the prior empty-cache KeyGen
error below `2^-239` is charged once through successful-return mass.
Different coefficient failure events need not be independent.

This averaged honest-ROM bound does not establish IND-CCA or worst-case-message
correctness by itself. The game/API layer above supplies the adversarial
interface, and the separate ACWC2 continuation addresses its stated
fresh-key, finite-G expected worst-message quantity. Their security-game
connection and a quantitative public-key-dependent FO reduction remain
obligations. Native primitive, C/ABI and
leakage boundaries are unchanged. See [the numerical DFR guide](ntruplus768-kem-numerical-dfr.md)
for the final verification status, event/state scope and
[`verify-ntruplus768-kem-numerical-dfr.sh`](../scripts/verify-ntruplus768-kem-numerical-dfr.sh).

## Fresh KeyGen acceptance and concrete ROM error (2026-10-13)

The actual fresh-buffer f/g predicates now have acceptance lower bounds of
5/8, proved from the quadratic rejection cover and disjoint head-bit XOR
translates. These bounds normalize the whole-buffer accepted-pair law and
discharge the fresh termination premises in the stopped-ROM comparison.
They do not supply a per-call lower bound for cached ROM answers.

For 256 attempts per phase and at most `a` initial E entries, the public
KeyGen output-event error is at most `(512*a+130818)/2^256`; it is below
`2^-239` for an empty initial E cache. The bound also controls late-return
and missing mass, without assuming unrestricted real-ROM termination.
It is not a numerical DFR or IND-CCA bound. The independent uniform seeds,
standalone-query scope and native boundaries are retained. See
[the acceptance contract](ntruplus768-keygen-acceptance.md) and run
`scripts/verify-ntruplus768-keygen-acceptance.sh` for the replay scope.

## Stopped ROM transfer for actual KeyGen (2026-10-13)

The proof-only continuation connects the existing unrestricted ROM and fresh
KeyGen callers using finite f/g prefixes. Independent uniform seeds, a bounded
initial E cache and positive fresh acceptance masses yield an output-event
difference bounded by the seed-collision term plus the geometric retry tails.
Missing mass and late returns satisfy the same bound; real-ROM losslessness
is not assumed. The actual fresh accepted-buffer pair has the product of its
whole-buffer conditional laws. Finite tails remain valid at zero acceptance
mass, and the pair law then remains a subdistribution statement.

The standalone model permits no interleaved external E queries. The numerical
continuation above supplies the subsequent honest-KEM distribution and tail
argument. IND-CCA and native correspondence remain open. See [the stopped-KeyGen contract](ntruplus768-stopped-rom.md) and
run `scripts/verify-ntruplus768-stopped-rom.sh` for the declared replay scope.

## Symbolic correctness-failure bound (2026-10-13)

The actual array callers now have a public correctness experiment and a
private observation of the integer no-wrap condition. A projection proof
preserves the failure result and module states, including a shared stateful
RNG. Under the declared hash contracts and separation, failure probability
is at most the no-wrap violation probability. IID termination and transfer
of any separately proved epsilon bound are established in their explicit
specialization. Four new mains and21lemmas passed coherent replay.

This was a symbolic proof-only addition. The subsequent numerical continuation
above specializes its failure implication to the initialized uniform-RNG ROM
experiment. IND-CCA and the existing native primitive and C correspondence
boundaries remain separate obligations. See
[the probability contract](ntruplus768-kem-failure-bound.md).

## Complete mixed KeyGen and conditional three-procedure agreement (2026-10-13)

The native KeyGen path and actual array calls now derive the successful-key
relations, key encodings and stored HashF suffix used by Encaps--Decaps.
Fixed iid32-byte seed proposals, deterministic SHAKE expansion and positive
f/g acceptance masses give probability-one termination and the exact
conditioned-seed pushforward law. Generic RNG termination alone is insufficient.
The generated-key agreement theorem retains the sufficient integer no-wrap
condition; no failure-probability bound or IND-CCA reduction follows yet.

The new arithmetic certificate covers the larger triple/plus-one KeyGen
input domain and the official fqinv chain. Full replay passed31mains and87new
lemmas, four helperSafety/CT/SCT checks and normal/UBSan full API comparisons.
Inverse branches, native SHAKE/RNG, C orchestration and memory/ABI conditions
retain their explicit boundaries. See [the KeyGen contract](ntruplus768-keygen-complete.md).

## Complete mixed Encaps and conditional agreement (2026-10-13)

The complete deterministic and randomized Encaps entry points now call the
actual Jasmin guard, hashing-input preparation, CBD1, NTT, SOTP encoder,
multiplication, addition, serialization and key-copy procedures. Randomized
Encaps consumes 96 external RNG bytes before validation, including on invalid
public keys. Both paths clear the 13634-byte caller workspace; the randomized
wrapper also clears its local 96-byte coin buffer.

The official fused multiply-add and the separate Jasmin multiplication/addition
can have different raw words. A source-bound integer certificate establishes
their bounds and congruence, after which canonical serialization gives equal
ciphertext bytes. This is distinct from a C-AST equivalence theorem. The
reused trit-input NTT certificate applies to both CBD1 and SOTP outputs.

The full replay passed 54 EasyCrypt mains, 84 new lemmas, six slice
safety/CT/SCT checks and normal/UBSan native comparisons. This includes the
deterministic caller, generic RNG state/distribution results and conditional
key agreement. Agreement uses explicit successful-key arithmetic,
serialization, stored HashF and no-wrap premises, without assuming successful
Decaps. Native SHAKE/RNG, C orchestration and memory/ABI behavior remain
external conditions. No numerical failure bound, unconditional KeyGen
correctness, full mixed-API CT/SCT or IND-CCA result is claimed. See
[the detailed contract](ntruplus768-encap-complete.md) and replay with
`scripts/verify-ntruplus768-encap-complete.sh`.

## Complete mixed Decaps entry point (2026-10-12)

`ntruplus768_decaps` now supplies the complete native Decaps call sequence
using the actual Jasmin kernels and official C SHAKE256. New Jasmin exports
prepare `0x02 || msg96 || sk[2304..2335]`, sample CBD1 from the 192-byte hash
tail, compare serialized values while retaining SOTP failure, select the
32-byte shared secret, and clear the caller's 13506-byte workspace on every
path. A SOTP failure does not skip HashH or regeneration.

The complete array model covers arbitrary 1152-byte ciphertexts and
2336-byte secret keys, including malformed encodings. The full replay passed
39 EasyCrypt mains and 61 new lemmas, exact fresh extraction, four slice
safety/CT/SCT checks, and normal/UBSan native and independent-oracle tests.
SHAKE functional/termination contracts remain external for C, together with
native memory and ABI behavior. The cleanup theorem for a designated array
does not prove C struct mapping or
register/spill/nested-call erasure. Full-API CT/SCT, complete KEM correctness
and IND-CCA remain outside this milestone. See
[the detailed contract](ntruplus768-decap-complete.md) and replay with
`scripts/verify-ntruplus768-decap-complete.sh`.

## Decaps message continuation (2026-10-12)

The native continuation now calls Jasmin serialization/prefix preparation,
official `3991b2a` C SHAKE256, and the existing Jasmin SOTP decoder. It preserves
the 1152 serialized bytes and returns the candidate message and SOTP status.
The actual SHAKE call consumes `0x01 || serialized` (1153 bytes) and produces
192 bytes. The C glue clears its private input and pad buffers; this source
fact does not establish formal erasure.

The new EasyCrypt composition requires a functional and lossless external
SHAKE module. Instantiating it with mathematical SHAKE256 proves only that
model's contract. Native C SHAKE, memory and ABI correctness remain external
conditions; slice CT/SCT results do not establish whole mixed-API CT/SCT.
Native ordinary/UBSan tests cover message-only and combined
guard/candidate/r2/message replacements. The full replay passed the actual
preparation/SOTP proofs, conditional composition and caller proofs, fresh
extraction, default safety, CT/SCT and normal/UBSan native comparisons.
See [the detailed contract](ntruplus768-decap-message.md). That milestone stops
before HashH, regeneration, final comparison and shared-secret selection;
the complete Decaps work above addresses those subsequent calls.

## Decaps r2 computation and trit-input NTT correspondence (2026-10-12)

`decap_r2.jazz` connects the actual NTT, subtraction and multiplication calls
to compute `BaseMul(c-NTT(m1),hinv)`. Its extracted proof and caller discharge
arithmetic premises from accepted decoded arrays and the preceding ternary
candidate. The four native buffers are disjoint and aligned; private arrays
are statically initialized. Default exported-array initialization in the
safety checker remains an explicit model assumption.

The existing NTT schedule is retained. Official3991b2a moves radix-2 Barrett
reductions to a final sweep; source tokens, constants and an integer interval
certificate establish the restricted trit-input correspondence. Official raw
outputs lie in [-14821,14821], and both schedules finish with the unique
centered representative. This is not an EasyCrypt C-AST equivalence or a
migration of every NTT caller. Native ordinary/UBSan comparisons and KATs
exercise r2 alone and the combined guard/candidate/r2 replacements; the rest
of Decaps remains C. Reproduce with
`scripts/verify-ntruplus768-decap-r2-comp.sh`; details are in
`ntruplus768-decap-r2.md`.

## Decaps first normal-path calculation (2026-10-12)

`decap_candidate.jazz` composes the existing multiplication, inverse NTT and
centered mod-three kernels into a callable procedure. Its actual extraction
is linked to their word contracts and termination proofs; canonical decoder
outputs discharge the arithmetic ranges and imply ternary results. The
EasyCrypt caller connects accepted guard outputs to this computation.

For these calls the official target preserves the arithmetic formulas;
its in-place API and intermediate-storage changes do not require changing
the reused kernels. Forward-NTT reduction migration is not covered here.
Differential execution tests replace only the corresponding three-call
block, also testing the combined Jasmin guard/candidate. The rest of the
API and cleanup remains official C. No C-AST theorem, unconditional original
message recovery or IND-CCA reduction is claimed. Internal candidate scratch
erasure is also outside the present contract. Replay with
`scripts/verify-ntruplus768-decap-candidate.sh`; the detailed contract is in
`ntruplus768-decap-candidate.md`.

## Decaps entry-guard migration step (2026-10-12)

The official validation boundary is now represented by `decap_guard.jazz`:
ct/f/hinv checked decoding in short-circuit order, skipped-output
preservation and zero shared secret on early rejection. The existing checked
decoder and its actual-procedure proof are reused. The native interface uses
the contiguous 2304-byte secret-polynomial prefix, leaving the stored hash
outside this slice. Array specifications and native memory conditions remain
distinct obligations.

The caller model invokes a continuation only after guard acceptance and
propagates its final status as well as its shared-secret output. It allows
later rejection; it is not the extracted full Decaps program. Native tests
replace only the validation block in the pinned C, retaining its original
normal body and cleanup. The source/reference/extraction pins and semantic
EOF proof guards are part of the dedicated replay.

The CT/SCT policy discloses two encoding-validity bits, not key contents.
Both bits are proved zero on canonical secret-key encodings. This conditional
policy does not establish no-disclosure CT for malformed secret keys or full
KEM leakage security. See `ntruplus768-decap-guard.md` and run
`scripts/verify-ntruplus768-decap-guard.sh`.

The complete callers, actual KeyGen relations and conditional agreement are
tracked above. The numerical continuation above handles honest-ROM correctness;
remaining full-KEM obligations include external-call conditions, stronger
correctness notions and the classical-ROM security reduction. The old
arithmetic baseline stays separately pinned until the full migration exit
criteria pass.

Audit date: 2026-08-26

## Encaps entry-guard migration step (2026-10-11)

The checked decoder now feeds `encap_guard.jazz`, which clears all ciphertext
and shared-secret bytes on rejection and preserves those buffers on acceptance.
`ntruplus/proof/768/ref/encap_guard/` proves the actual extracted guard contract
and termination. A separate caller model proves that rejection does not invoke
an arbitrary success continuation. The native integration harness substitutes
this guard for only the corresponding block of official `3991b2a` `kem.c`;
all subsequent encapsulation calculations remain in the original C body.
The public C API still samples coins before this guard.

Replay with `scripts/verify-ntruplus768-encap-guard.sh`. The reference manifest
pins the official source and KAT used for the mixed implementation tests.
Public-key-dependent rejection is public under the guard's CT policy.
CT/SCT run after inlining the reused decoder. Under SCT, key bytes are
`transient` (normal public, speculative secret), and the source protects the
validation status before branching. The existing decoder policy is unchanged.
Disjoint buffers and the recorded native memory contract remain prerequisites;
only public-key initialization is required, since output buffers are not read.
This step establishes a verified entry guard and tests its C caller connection;
it is not a full-Jasmin Encaps, a C-AST equivalence theorem, or an IND-CCA proof.
Decaps rejection/clearing is covered by its entry guard; the complete Decaps
composition is tracked separately above.

## Checked-decoder migration step (2026-10-11)

The research target now includes NTRU+ IND-CCA security in the classical ROM,
using the official hardened implementation at `3991b2a`. The initial standalone
slice is the checked `poly_frombytes` decoder:

- `ntruplus/jasmin/768/ref/poly_frombytes.jazz` implements its 384 iterations,
  exact decoded values and uint32 status computation, including rejected inputs.
- `ntruplus/proof/768/ref/poly_frombytes_checked/` connects the freshly extracted
  procedure to the existing arithmetic and canonical-validation specifications.
  The contract establishes termination, exact output and status, the 0/1 flag,
  success iff all 768 coefficients are below 3457, and the canonical serialization
  round trip.
- `tests/ntruplus768/poly_frombytes_checked/reference/` preserves the official
  C oracle and its required headers/license with exact commit/file provenance.
- `scripts/verify-ntruplus768-poly-frombytes-checked.sh` is the strict standalone
  replay entry point, covering fresh extraction, proof completion, native safety
  and information-flow checks, and normal/UBSan differential execution.

This result does not switch the full `NTRU+/NTRU+768` reference tree or complete
its KEM caller proofs. The decoder retains decoded coefficients even on failure;
propagating its status and clearing public outputs is a caller obligation.
The native contract uses disjoint 1536-byte writable u16-aligned output and
1152 initialized readable input bytes. The EasyCrypt result is for the extracted
Jasmin procedure; the C oracle is tied by source review and differential execution,
not a C-AST equivalence proof. The remaining API/trace migrations and the IND-CCA
reduction below are still open. The original decision and audit are retained as
historical context; Encaps caller progress is described above.

## Decision

The functional-correctness paper remains pinned to the already verified
NTRU+768 reference baseline:

```text
38201624477a7dbb2f46d1ae7686ae5ceee4eb80
```

The local tree differs from that upstream commit by one tracked,
documentation-only patch:

```text
patches/ntruplus768-3820162-comment-fix.patch
```

It corrects the `baseinv` `fqinv(t3)` Montgomery annotation from `R^5` to
`R^3`; it does not change executable C.  The current official migration target
is pinned separately as:

```text
3991b2ae08d6f0008d37e41b8aceaaab27b4ec89
```

That commit was both `HEAD` and `refs/heads/main` of the official NTRU+
repository at audit time.  It is not imported into this repository and is not
covered by the current Jasmin/EasyCrypt claims.  The paper and artifact must
name the verified baseline commit explicitly and must not describe it as the
current upstream implementation.

This freeze keeps the high-level ring-semantics and valid-ciphertext recovery
work on the critical paper path.  Migration to the hardened target proceeds on
a separate track and must complete the exit criteria below before the source
pin changes.

## Reproduction

Run the immutable source/KAT audit:

```sh
./scripts/audit-ntruplus768-upstream.sh
```

It verifies all of the following:

- the local reference tree equals upstream `3820162` plus the tracked
  comment-only patch;
- the local KAT tree byte-matches upstream `3820162`;
- exactly 15 NTRU+768 reference files changed between the two commits;
- the NTRU+768 KAT tree did not change;
- candidate `3991b2a` builds, reports zero functional-test failures, and
  regenerates the committed response file byte-for-byte;
- the candidate contains the expected canonical-decoding, invalid-input,
  in-place-ABI, reduction-placement, `fqinv`, declassification, and clearing
  changes.

Run the bounded fail-closed checker impact audit:

```sh
./scripts/audit-ntruplus768-checker-impact.sh
```

This checks only the `check` and `selfcheck` targets.  It deliberately avoids
EasyCrypt compilation, Jasmin safety/CT analysis, differential execution, and
UBSan.

## Measured results

The candidate preserves the KAT response SHA-256:

```text
22c72039845361ff142273150a59785bada5146c04018ce0a8b67b99a647eaa8
```

The source delta is 15 files, 319 insertions, and 611 deletions under
`Reference_Implementation/NTRU+768`.  No file under `KAT/NTRU+768` changes.

The bounded checker matrix counts individual targets, not directories:

The repository-side checker tree is frozen at verified commit
`d2cb239d262fb4f656992d6bd7e6220dc82748b4` so the audit remains reproducible
after later migration work changes the main branch.

| Source tree | PASS | FAIL | SKIP |
| --- | ---: | ---: | ---: |
| Verified baseline | 88 | 0 | 4 |
| Candidate `3991b2a` | 6 | 82 | 4 |

The four skipped targets are `check` and `selfcheck` in `basemul` and
`poly_basemul`, whose Makefiles expose neither target.  Only these candidate
directories pass both targets:

- `tests/ntruplus768/decap_verify`
- `tests/ntruplus768/invntt_final`
- `tests/ntruplus768/ntt_schedule`

The 82 failures are expected fail-closed detections.  They demonstrate that a
pin-only update would be unsound; they do not imply that the candidate C code
is functionally incorrect.

## Compatibility classification at the initial audit

| Candidate change | Class | Current impact | Reuse assessment |
| --- | --- | --- | --- |
| `poly_frombytes` returns failure for coefficients `>= q` | Semantic + ABI | Decoder signature/body and every unconditional caller seam fail | Pure decode arithmetic and canonical round-trip lemmas remain useful; return-value and reject-path proofs are new |
| Encapsulation rejects invalid `pk` and zeros `ct`/`ss` | Semantic control flow | Existing encap proofs cover only the valid branch | Valid-branch ring algebra is reusable; invalid-key return/zeroization needs a new theorem and tests |
| Decapsulation rejects invalid `ct`, `f`, or `hinv` before arithmetic | Semantic control flow | Existing decap chain assumes all three decoders continue | Established valid-branch seams are reusable behind a validity premise; early failure/cleanup must be composed separately |
| NTT, InvNTT, triple, and `crepmod3` become in-place APIs | ABI + trace | Exact signatures, wrapper forwarding, and caller-order checks fail | Alias-value algebra is largely reusable; extracted procedures and caller checkers need rebinding |
| Forward NTT defers Barrett reduction to one final sweep | Word trace/range | Current staged word proofs and source checker pin per-layer reduction | Root schedule and abstract transform goal remain reusable; word bounds and stage composition require new proofs |
| Inverse NTT removes the initial two-buffer copy | ABI + wrapper trace | Whole-wrapper checker/proof no longer matches | In-place stage algebra and final layer remain useful; wrapper theorem must be replaced |
| `fqinv` uses a different 15-step addition chain | Exact arithmetic trace | C/Jasmin exact-chain checkers fail | Prime-field inverse theorem is reusable; exact word trace and C/Jasmin coupling require refresh or chain equivalence |
| `basemul` and `basemul_add` use local temporaries | Source shape | Exact-body checkers fail | Four-lane quotient-ring formulas are unchanged and should be reused |
| `secure_clear`, declassification, visibility macros, SHAKE workspace changes | Hardening + source shape | KEM/hash source checkers and cleanup order fail | Hash value specifications remain reusable; cleanup/declassification are separate implementation properties |

## Malformed-input requirements identified by the initial audit

The initial baseline suite lacked dedicated regressions for the new
malformed-input behavior. The checked-decoder and entry-guard milestones
above now cover the rejection and public-output cases below. Whole-API
cleanup and information-flow guarantees remain separate obligations.
The audit identified these required behaviors:

1. A public key containing a decoded coefficient `>= q` makes encapsulation
   return `1` and zero both ciphertext and shared secret.
2. A non-canonical ciphertext, serialized `f`, or serialized `hinv` makes
   decapsulation return failure and zero the shared secret.
3. Canonical encodings retain the existing valid-input values and KAT.
4. Cleanup does not alter returned public outputs, and retry-status
   declassification remains explicit.

## Proof reuse map from the initial audit

Likely reusable with small adapters:

- NTRU+ root order, factor schedule, and terminal-root lemmas;
- four-coefficient quotient-ring multiplication and inverse identities;
- canonical serialization/round-trip mathematics for valid inputs;
- SOTP encode/decode value algebra;
- `hash_f`, `hash_g`, and `hash_h` domain-separated value specifications;
- valid-branch terminal failure/mask Boolean algebra.

Requires procedure- or trace-level repair:

- `fqinv`, `baseinv`, and `poly_baseinv` exact C/Jasmin trace coupling;
- forward NTT stages and whole-wrapper bounds after reduction relocation;
- inverse NTT whole-wrapper composition after copy removal;
- every caller checker that pins two-buffer transform/triple/`crepmod3` APIs;
- `poly_frombytes` status and all new malformed-input branches;
- KEM cleanup/declassification/source-order checks.

## Migration order

1. Prove and test the fallible canonical decoder, including malformed public
   key and ciphertext behavior.
2. Rebind one-buffer APIs and prove equivalence to the existing valid-input
   array specifications.
3. Refresh the forward/inverse NTT word-level traces while reusing the root
   schedule and high-level ring target.
4. Refresh `fqinv` and helper-body C/Jasmin coupling; reuse the field and
   quotient-ring algebra.
5. Add hardening/cleanup/declassification source and runtime checks.
6. Run the complete EasyCrypt, Jasmin safety/CT, differential, UBSan, and KAT
   chains before changing `THIRD_PARTY.md`'s imported source commit.

## Pin-change exit criteria

Do not replace the verified baseline until all conditions hold:

- candidate reference and KAT trees are imported with exact provenance;
- all 88 bounded checker targets pass against the candidate;
- new malformed-input and zeroization tests pass under normal and UBSan builds;
- every affected tracked Jasmin extraction is refreshed and reviewed;
- strict EasyCrypt proof chains pass without holes or stale assumptions;
- the paper's theorem statements distinguish valid-input correctness from
  malformed-input rejection and name the exact target commit.

## Classical-ROM caller contracts

The proof-only classical-ROM continuation keeps the actual candidate array
callers and uses realized cache entries rather than fixed mathematical SHAKE
values in their contracts. Four lazy typed domains preserve repeated-query
consistency and honest tagged-input encodings. The public failure bound,
fresh-G SOTP component law and uniform-seed completed-run collision bound are
separate results; see [the ROM scope](ntruplus768-classical-rom.md).
The stopped-KeyGen continuation above adds the fresh accepted-buffer joint law
and the unrestricted ROM/fresh event comparison with explicit missing mass.
These additions change no C/Jasmin source, extraction or native checkpoint.
Unconditional ROM rejection-loop termination, the IND-CCA reduction and
native memory/ABI correspondence remain outside this initial milestone.
The later numerical correctness and game/API continuations are described
above; neither changes these native or security boundaries.
