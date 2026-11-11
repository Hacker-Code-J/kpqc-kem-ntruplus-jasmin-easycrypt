# Numerical honest-ROM correctness for NTRU+768

This proof-only continuation connects the actual KeyGen, randomized Encaps
and CompleteDecaps array callers to a numerical correctness bound. The final
endpoint is `numerical_rom_dfr_total` in
[`NTRUPlus768NumericalDFR.ec`](../ntruplus/proof/768/ref/kem_numerical_dfr/NTRUPlus768NumericalDFR.ec):

```text
Pr[KEMROMCorrectness(UniformKEMRNG).run(): returned failure]
  + (1 - Pr[KEMROMCorrectness(UniformKEMRNG).run(): returns])
  < 2^-238.
```

The new proof mains, including the closed numerical endpoint, have passed
their standalone strict checks. Use a completed runner report for the
full-suite result and counts; standalone main checks do not by themselves
claim a full frozen-source replay.

## Experiment and observations

`UniformKEMRNG` makes independent uniform 32-byte KeyGen seed draws and one
uniform 96-byte Encaps coin draw. `KEMROMCorrectness` initializes all four
classical lazy random-oracle tables, E, F, G and H, to empty before calling
the existing unrestricted KeyGen, Encaps and Decaps programs. There are no
interleaved external queries. Repeated queries retain their cached answers.
The retry budgets used in the analysis do not change the implementation's
loops.

The returned boolean is true when Encaps or Decaps returns a nonzero status
or the two shared secrets differ. Missing mass is the probability that the
experiment does not return. The bound therefore also gives the separate
returned-failure and missing-mass bounds, and successful-return probability
greater than `1-2^-238`. It does not require unrestricted ROM KeyGen to be
lossless and supplies no wall-clock timeout guarantee.

The original random-byte, hash, arithmetic, coin-clear and workspace-clear
calls remain in the actual callers. Private proof observations retain the
accepted f/g buffers and read H/G cache entries already inserted by the real
Encaps call. They add no hash queries. The existing public/private projection
preserves the returned failure bit and the RNG/oracle states. Subsequent
reductions preserve their stated no-wrap observation and return mass; the
final theorem concerns these probability events, rather than arbitrary
readers of the final keys, ciphertexts or oracle tables. The separate
[IND-CCA game/API layer](ntruplus768-kem-indcca-game.md) supplies adversarial
hash and decapsulation interfaces. This numerical theorem does not bound
their adversarial executions or arbitrary continuations reading final state.

## Actual calls and the four-buffer law

In the independent-fresh-expansion comparison experiment, KeyGen's
accepted buffers have the established whole-buffer law

```text
dcond uniform192 keygen_f_accept
  * dcond uniform192 keygen_g_accept.
```

The previous [acceptance development](ntruplus768-keygen-acceptance.md)
proves `p_f,p_g >= 5/8` for the actual inverse predicates. Conditioning each
entire buffer retains dependencies among its accepted coefficients. The
comparison with cached ROM expansion is accounted for separately below.

KeyGen stores `F(pk)` in its secret-key suffix and F table. Honest Encaps
reads that cached value and queries `H(coins96,F(pk))`. The H and G tables
are still empty at the start of this single Encaps call. Its H answer is
uniform over 224 bytes; the actual final 192 bytes supply the r sampler.
The following G query uses the actual serialization computed from that H
answer. Its fresh 192-byte answer supplies the SOTP pad. XOR with the fixed
96-byte coins in the actual SOTP preparation preserves the uniform buffer
law. Thus the r and m sampling buffers have independent `uniform192` laws,
also for each fixed accepted key and fixed coins.

`NTRUPlus768HashPayloadSampling.ec` and `NTRUPlus768EncapFreshBridge.ec`
establish these laws through the actual hash preparation, CBD1, NTT,
serialization and SOTP calls. `NTRUPlus768ROMDFRObservation.ec` connects
their private observation to the original initialized three-caller experiment.
The existing no-wrap agreement contract supplies the Decaps success case
using the actual cached H/G answers.

## Integer noise and its tail

For an unconditioned `uniform192` buffer, the implemented CBD1 layout uses
disjoint pairs of fair bits. `NTRUPlus768CBDDistribution.ec` proves its full
768-coefficient product law with probabilities
`Pr[-1]=1/4`, `Pr[0]=1/2`, `Pr[1]=1/4`, and connects it to the actual
`poly_cbd1_spec` word array.

Write the shaped key polynomials as `f=1+3*f0` and `g=3*g0`. For each
coefficient k, the existing integer lift has the form `m_k+3*S_k`, where
`S=g0*r+m*f0` in the integer quotient by `X^768-X^384+1`. Since
`|m_k|<=1`, a no-wrap violation implies `|S_k|>=576` for some k. The proof
retains this inclusive threshold and the dependence of m on S.

For each fixed k, each product is partitioned into 384 disjoint blocks of
four CBD1 coefficients, ordered `((a,c),(b,d))`. The two products together
give 768 independent blocks in the unconditioned four-buffer experiment.
Depending on the quotient reduction, a block contributes one of

```text
ab-cd,  -(ad+cb+cd),  ad+cb+cd,  ab+ad+cb.
```

For both signs, the exact exponential moment `E[2^(+X)]` or `E[2^(-X)]`
is `289/256` for the first form and `K=1237/1024` for the other forms.
The independent-block product and two-sided Markov bounds, followed by a
union bound over 768 coefficients, give

```text
Pr_raw[no-wrap violation] <= 1536*K^768/2^576 < 2^-356.
```

The factor 1536 accounts for both signs and all coefficients. Different
coefficient failure events may share inputs; their independence is not used.
`NTRUPlus768NoiseDecomposition.ec`, `NTRUPlus768NoiseNoWrap.ec`,
`NTRUPlus768NoiseMGF.ec` and `NTRUPlus768NoiseTail.ec` contain the integer
decomposition, threshold, exact moments and tail calculation.

`NTRUPlus768ConditionalBufferLaw.ec` conditions the joint four-buffer law
on acceptance of f and g. For any event B,

```text
Pr_accepted[B] <= Pr_raw[B]/(p_f*p_g) <= (64/25)*Pr_raw[B].
```

Consequently the accepted-key ideal no-wrap violation probability is below
`2^-354`. This step uses whole-buffer conditioning, without treating accepted
coefficients as iid.

## Transfer to unrestricted ROM KeyGen

The [stopped-ROM proof](ntruplus768-stopped-rom.md) and its numerical
acceptance specialization supply
`epsilon_KG = 130818/2^256 < 2^-239` for an initially empty E table.
`NTRUPlus768KEMROMTransfer.ec` applies statistical-distance contraction to
the explicit stateless two-buffer no-wrap observer.

The proof transfers the probability of a successful no-wrap return. Its
complement already consists of returned bad executions plus missing mass,
so `epsilon_KG` is charged once. Combining it with the accepted ideal tail
and the existing actual failure-implies-bad theorem yields

```text
returned failure + missing mass < 2^-354 + 2^-239 <= 2^-238.
```

## Reproduction and scope

Run from the repository root:

```sh
./scripts/verify-ntruplus768-kem-numerical-dfr.sh \
  --prior-evidence-root /path/to/thesis \
  --output /path/to/new-evidence-directory
```

The output directory must be new or empty and outside the checkout. Sources
are in [`ntruplus/proof/768/ref/kem_numerical_dfr/`](../ntruplus/proof/768/ref/kem_numerical_dfr/),
and controls are in [`tests/ntruplus768/kem_numerical_dfr/`](../tests/ntruplus768/kem_numerical_dfr/).
The runner selects September 2026 EasyCrypt/Why3 with Z3, `-no-eco`,
`Proofs:check`, one prover and `OCAMLRUNPARAM=o=20`. It checks the new mains,
their semantic EOF theorems and isolated unfinished-proof negatives, together
with source/diagnostic controls and before/after input hashes. Unchanged
imports are linked to prior evidence by exact hashes. Use the completed
run's `summary.json` and logs for its actual status and counts.
`--check-only` validates sources and controls without claiming a proof replay.

This is an honest classical-ROM correctness and nonreturn bound, averaged
over generated keys, honest uniform coins and oracle answers. IND-CCA,
worst-case-message or ACWC2-style correctness, and QROM security remain
separate goals. The [game/API continuation](ntruplus768-kem-indcca-game.md)
defines the challenge experiment, exact status projection, shared hash
queries and challenge-blocking decapsulation interface. It keeps partial
return mass explicit and fairly completes finite setup exhaustion. These
definitions and identities do not supply an IND-CCA bound. The remaining
steps include the average-to-worst correctness argument, a quantitative
public-key-dependent FO reduction and the required hardness assumptions.

The development changes no C/Jasmin implementation and establishes no
concrete SHAKE-to-ROM theorem. Native SHAKE/RNG, C memory/ABI correspondence,
binary execution and full-API leakage retain their existing boundaries.
No new extraction, native, Safety or CT/SCT replay is claimed here.
