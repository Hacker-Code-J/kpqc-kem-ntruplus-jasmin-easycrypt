# Stopped ROM transfer for actual NTRU+768 KeyGen

This development connects the existing unrestricted array KeyGen to an
independent fresh-buffer experiment through finite retry prefixes. It bounds
every output-event probability difference and the real ROM's nonreturning
mass, without assuming that the unrestricted ROM KeyGen terminates. It also
identifies the joint law of the two accepted buffers in the fresh experiment.

## Experiments and assumptions

The real experiment uses `Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM)` and the
fresh experiment uses `Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM)`. Each
attempt draws an independent uniform 32-byte seed. `ExpandROM` consults the
lazy E table, preserving cached answers; `FreshExpand` samples an independent
uniform 192-byte buffer on every call. The actual attempt, finish and workspace
clear procedures remain in both caller paths. Both experiments start from the
same F-table state.

The E table present before the first attempt is an explicit `m0`, with at most
`a` distinct seed keys. The standalone KeyGen has no interleaved external
queries or writes to E. This initial-cache bound differs from the earlier
observer's budget for initial and externally marked inputs. The hypotheses
do not assert that concrete SHAKE behaves as a random oracle, or that an
arbitrary shared-state RNG supplies independent seeds.

Let `U = uniform192`. The predicates `A_f = keygen_f_accept` and
`A_g = keygen_g_accept` test the actual shaped/NTT candidate's inversion
success. Set `p_f = mu U A_f` and `p_g = mu U A_g`. These are symbolic masses;
the original stopped-ROM theorem leaves their positivity as premises. The
subsequent [acceptance analysis](ntruplus768-keygen-acceptance.md) proves both
actual fresh masses are at least 5/8, discharging those premises without
assuming any per-call acceptance rate for cached ROM answers.

## Finite retry prefixes

`StoppedKeygen` gives f and g separate budgets `q_f` and `q_g`. It returns
`None` if either phase exhausts its budget, and otherwise calls the same
finish and clear procedures as KeyGen. These guards belong to the analysis
model; the public implementation retains its unrestricted rejection loops.
`CountedKeygen` records private attempt counts, and erasing those counts
recovers the existing caller. Prefix/resume proofs connect these two models
without assuming that a remaining unrestricted suffix terminates.

For every nonnegative budget `q`, the actual fresh f/g retry failure
probability is exactly `(1-p_f)^q` or `(1-p_g)^q`. Finite retries terminate
even when an acceptance mass is zero; a nonpositive budget performs no draw.
Consequently the fresh stopped KeyGen's abort probability is at most

```text
tau(q_f,q_g) = (1-p_f)^q_f + (1-p_g)^q_g.
```

The finite ROM and fresh proposal paths are coupled until a seed repeats or
hits the initial E table. With `Q = q_f+q_g`, the bound is

```text
delta(a,Q) = a*Q/2^256 + Q*(Q-1)/(2*2^256).
```

The stopped output-event difference is at most `delta(a,Q)`. This uses the
unnormalized agreement before a collision. It does not identify the fresh
law conditioned on a collision-free execution with the original fresh law.

## Transfer to unrestricted KeyGen

Assume nonnegative `a`, `q_f`, `q_g`, the initial-cache condition above, and
`p_f>0`, `p_g>0`. Positivity makes the fresh unrestricted experiment lossless.
For every event `B` on the actual public `(pk,sk)` output,

```text
|Pr[Keygen_ROM returns an output in B]
 - Pr[Keygen_fresh returns an output in B]|
  <= delta(a,q_f+q_g) + tau(q_f,q_g).
```

The same bound holds for events on the instrumented key witness and cleared
workspace. The relevant endpoints are `keygen_public_rom_fresh_distance` and
`keygen_rom_fresh_distance` in `NTRUPlus768StoppedROMBound.ec`. They refer to
the pre-existing unrestricted procedures, not just a substitute sampler.

Nontermination is retained as missing subdistribution mass. In the private
counting model, the proof also establishes

```text
Pr[ROM returns outside either retry budget] + (1-Pr[ROM returns])
  = 1-Pr[ROM returns within both budgets]
  <= delta(a,q_f+q_g) + tau(q_f,q_g).
```

In particular, `keygen_rom_missing_mass` bounds `1-Pr[ROM Keygen returns]`.
It does not replace this quantity by zero. The event and complementary-event
argument supplies both directions of the probability comparison despite
possible divergence in the real experiment. This resolves, for this symbolic
standalone KeyGen comparison, the earlier limitation of a collision bound
observed only on completed runs: such a bound alone could not account for
divergence after a collision.

## Joint accepted-buffer law

For the actual fresh KeyGen and any event on its accepted `(fbuf,gbuf)`,
`fresh_keygen_buffer_pair_probability` identifies the returned-event law as

```text
dcond U A_f  *  dcond U A_g
```

where `*` is the product of the two entire-buffer distributions. The theorem
is valid as a subdistribution statement even if an acceptance mass is zero;
positive masses make both factors, and hence the product, normalized.
Acceptance retains dependencies among the coefficients within each buffer.
The result establishes independence between the two accepted buffer factors
in the fresh experiment, not iid accepted coefficients or an exact product
law for the real ROM experiment.

For the actual fresh predicates, the acceptance continuation establishes that
both masses are positive and the product above is normalized. It also gives
the concrete 256-attempt-per-phase ROM comparison error
`(512*a+130818)/2^256`, below `2^-239` when the initial E cache is empty. The
general conditional statements above are retained, including their treatment
of missing mass. These numerical errors concern KeyGen, not DFR or IND-CCA.

## Subsequent shared-state CCA setup comparison

The subsequent [CCA setup development](ntruplus768-cca-setup.md) retains
the final E/F tables together with the actual KeyGen output. It uses a
fresh expansion port that programs each sample at its actual seed in E,
and strengthens the proposal coupling to preserve that complete state
before a collision. The earlier output-event bound alone is not used as
an adversarial continuation theorem.

The new joint-state bound is `delta + tau`, followed by statistical-distance
contraction through the actual typed/raw CCA continuation without an
attacker-losslessness premise. The actual initialized CCA games' winning
probabilities differ by at most `130818/2^256`, strictly below `2^-239`.
Fresh buffers keep their independent law,
but the key and programmed E table remain correlated. The table is kept
for subsequent queries. An additional hidden-input hit and query-budget
argument is needed before erasing it or replacing it by an independent
PKE/FO oracle. The linked guide records that continuation's separate
final verification status; the historical replay scope below is unchanged.

## Reproduction and remaining scope

Run the proof-only entry point from the repository root:

```sh
./scripts/verify-ntruplus768-stopped-rom.sh \
  --prior-evidence-root /path/to/thesis \
  --output /path/to/new-evidence-directory
```

The evidence directory must be new or empty and outside the checkout. The
runner uses the September 2026 EasyCrypt/Why3 installation, Z3, `-no-eco`,
`Proofs:check`, a 60-second prover timeout, one prover and `OCAMLRUNPARAM=o=20`.
Its scope is 14 new mains containing 152 lemmas, one semantic EOF check and
one isolated unfinished-proof rejection per main, and 109 source/trust/
diagnostic controls. The 57 finite-domain diagnostics include 2,450 exact
subdistribution-transfer cases; they check small counterexamples and formulas
and are not NTRU+ probability proofs.

The manifest pins 712 source files; the before/after audit covers 722 replay
inputs. The 535 imported prior EasyCrypt sources are linked to earlier
evidence by exact hashes and are not counted as freshly checked mains. Tools,
configurations, installed theories and prover drivers are audited separately.
Use the completed run's `summary.json` and logs for its actual result;
`--check-only` reports `SOURCE_CHECK_ONLY` and does not run the proof mains.

Sources are in `ntruplus/proof/768/ref/kem_stopped_rom/`, and the reproduction
controls are in `tests/ntruplus768/stopped_rom/`. The development introduces
no new local axioms or admitted proofs; imported theories retain their
existing trust boundaries. This milestone changes no C/Jasmin implementation
and reruns no native, extraction, Safety or CT/SCT checks. Native SHAKE/RNG,
C memory/ABI correspondence and full-API leakage security remain external.
Exact acceptance masses, a numerical no-wrap/DFR bound, further Encaps/Decaps
distribution transitions, classical-ROM IND-CCA and QROM remain open. The
fresh acceptance lower bounds are supplied by the linked continuation.
