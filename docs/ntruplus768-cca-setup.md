# Shared-state KeyGen comparison for the NTRU+768 CCA game

**PASS**, 2026-10-14: all 9 new mains (87 lemmas), 9 semantic
end-of-file probes and 9 isolated unfinished-proof rejections. The runner
passed 56 structural/trust controls and
29 exact finite diagnostics. It
verified 823 source pins and before/after hashes for
835 runtime inputs and
296 external tool/configuration/theory/driver
and prior-evidence inputs. The 635
imported EC files remain hash-linked prior evidence, not new main replays.
The companion thesis record is
`handoff/verification/ntruplus-cca-setup-20261014/final-replay/summary.json`,
with 25 command logs and 18 checked proof copies.

This continuation compares the actual unrestricted ROM KeyGen with fresh
expansion samples that are also recorded in the shared E table. The
comparison retains the returned key, cleared workspace and final E/F
tables together. It proves a joint setup distance at most `delta + tau`
and transfers it to the winning-probability difference between
`CCAOriginalGame(A)` and `CCAProgrammedFreshGame(A)`. For their initialized
empty-table setup, that difference is below `2^-239`.

The continuation uses statistical distance between subdistributions, so
the final observer need not terminate. It does not replace an arbitrary
attacker by a stateless output predicate or assume attacker losslessness.
It is a setup transition inside the actual challenge-first game, not a
complete IND-CCA security reduction.

## Fresh proposals recorded in the actual E table

[`NTRUPlus768CCASetupState.ec`](../ntruplus/proof/768/ref/kem_cca_setup/NTRUPlus768CCASetupState.ec)
defines the comparison expansion port:

```text
ProgrammedFreshExpand.shake(seed):
  y <$ uniform192
  ROE.m[seed] <- y
  return y
```

Each attempt still draws a fresh uniform 32-byte seed. Its expansion is
an independent uniform 192-byte buffer even if that seed was used before.
Repeated seeds therefore overwrite E during the comparison setup; each
seed's final entry contains its latest recorded answer. Earlier answers
at that same seed are not all retained. The
real `ExpandROM` instead reuses the cached answer. Their first discrepancy
is covered by the seed-collision bad event. Programming is private to this
analysis experiment; the adversary's interface has query procedures only.

[`NTRUPlus768CCASetupProgrammed.ec`](../ntruplus/proof/768/ref/kem_cca_setup/NTRUPlus768CCASetupProgrammed.ec)
connects the programmed attempts, retries and complete actual KeyGen to
the earlier `FreshExpand` caller. The output and final F table have the
same joint law in that projection. The original arithmetic, rejection,
Finish and clearing calls remain. The established fresh acceptance bounds
supply termination and retry-tail bounds.

This projection does not make the final E table independent of the key.
The attempt buffers determine the key and are written at their sampled
seed keys in E; a repeated seed can replace an earlier value. The comparison
deliberately retains this correlation. It also retains the F table
populated by actual key finishing.

## The joint setup observation

The private proof observation has type

```text
cca_setup_state = keygen_output * cca_e_table * cca_f_table
keygen_output  = keygen_witness * cleared_workspace
```

`JointSetup(E).run` calls the actual instrumented KeyGen and returns its
output together with the final `ROE.m` and `ROF.m`. `JointSetupSource(E)`
initializes E/F and runs that setup; the game comparison uses its
`guess(witness)` law. These witnesses and tables are not passed to A.

The finite analysis gives the f and g retry phases budgets qf and qg,
with one proposal counter across both phases. Let `Q = qf + qg`, and let
the initial E table contain at most a seed keys. For nonnegative budgets,

```text
delta(a,Q) = a*Q/2^256 + Q*(Q-1)/(2*2^256)
tau(qf,qg) = (1-p_f)^qf + (1-p_g)^qg.
```

Here p_f and p_g are the actual inversion-acceptance masses under a fresh
uniform192 buffer. Their established lower bounds are both 5/8. These
are not lower bounds for acceptance after arbitrary cached-ROM queries.

[`NTRUPlus768CCASetupProgrammedBridge.ec`](../ntruplus/proof/768/ref/kem_cca_setup/NTRUPlus768CCASetupProgrammedBridge.ec)
identifies the actual programmed E table with `FreshProposal.m`, including
the same overwrite behavior after a repeated seed. The strengthened
proposal coupling in
[`NTRUPlus768CCASetupSwitch.ec`](../ntruplus/proof/768/ref/kem_cca_setup/NTRUPlus768CCASetupSwitch.ec)
keeps the final tables in its good-event relation. Its stopped comparison
therefore applies to events on the entire joint observation.

[`NTRUPlus768CCASetupPrefix.ec`](../ntruplus/proof/768/ref/kem_cca_setup/NTRUPlus768CCASetupPrefix.ec)
and
[`NTRUPlus768CCASetupBound.ec`](../ntruplus/proof/768/ref/kem_cca_setup/NTRUPlus768CCASetupBound.ec)
carry that observation through the unrestricted prefix/resume argument.
The proved joint bound, for every event B, is

```text
|Pr[JointSetup_ROM returns in B]
 - Pr[JointSetup_programmed returns in B]| <= delta(a,Q) + tau(qf,qg).
```

The actual ROM setup remains a subdistribution. The proof does not assume
that its unrestricted suffix terminates, and the analysis budgets do not
change the implementation's retry loops. Fresh setup is lossless. A
complementary-event argument uses its normalized law to account for the
real setup's missing mass. This extends the earlier
[output-event stopped-ROM result](ntruplus768-stopped-rom.md) by retaining
the state that later oracle calls can observe.

## From the joint law to the actual adversary

[`NTRUPlus768CCASetupDistribution.ec`](../ntruplus/proof/768/ref/kem_cca_setup/NTRUPlus768CCASetupDistribution.ec)
reifies each actual setup procedure as a subdistribution on the joint
state and converts the all-event bound into `sdist`. The subsequent
`SDist.adv_sdist` step bounds any probabilistic observer's distinguishing
probability, including an observer that may not return.

[`NTRUPlus768CCASetupGame.ec`](../ntruplus/proof/768/ref/kem_cca_setup/NTRUPlus768CCASetupGame.ec)
defines `CCAProgrammedFreshGame(A)` by changing only the expansion port
inside KeyGen. It retains the original randomized challenge encapsulation,
challenge-key choice and `CCAChallengeOriginal(A)` continuation. The
decapsulation oracle still blocks the exact challenge ciphertext and
forwards every other ciphertext to the actual guard and caller.

The private `CCASetupObserver(A)` installs the sampled E/F snapshot,
initializes G/H, raw suffix caches and decapsulation state, and invokes
the same continuation. Moving these initializations after setup preserves
the execution because KeyGen uses only E/F and no adversarial call occurs
during KeyGen. A still receives only the public key, challenge ciphertext
and selected challenge key. Its mutable local state and the usual module
restrictions against direct access to private tables are retained.

The exact reification contracts are `cca_setup_game_reified_rom` for
`ExpandROM` and `cca_setup_game_reified_programmed` for
`ProgrammedFreshExpand`. They connect these two concrete setup paths to
the same private observer. They are not a claim for an unrestricted
generic expansion module with arbitrary access to the other globals.

Typed E/F/G/H queries and raw XOF queries subsequently share those exact
tables. The raw suffix caches preserve the existing 224-byte output
interface. The E table is neither erased nor replaced by an unrelated
table after setup. Consequently this transfer needs no additional qE
term for the number of subsequent E queries: the full state difference is
already covered by the joint setup distance.

[`NTRUPlus768CCASetupSecurity.ec`](../ntruplus/proof/768/ref/kem_cca_setup/NTRUPlus768CCASetupSecurity.ec)
provides the actual game endpoints:

| Theorem | Bound on the absolute winning-probability difference |
| --- | --- |
| `cca_original_programmed_setup_distance` | `delta(0,qf+qg) + tau(qf,qg)` for nonnegative qf and qg. |
| `cca_original_programmed_setup_distance_256` | `130818/2^256`, using analysis budgets qf=qg=256. |
| `cca_original_programmed_setup_distance_239` | Strictly less than `2^-239`. |

Each theorem compares `Pr[CCAOriginalGame(A).run(): res]` with
`Pr[CCAProgrammedFreshGame(A).run(): res]`, under the existing adversarial
module restrictions. There is no attacker-losslessness hypothesis.
These are returned-win probabilities without conditioning on return.
The same numerical setup bound first holds for every event on the joint
key/E/F observation; the game theorem follows from `SDist.adv_sdist`.

## Nontermination and the next reduction step

There is no attacker-losslessness premise in the proved game transfer.
An attacker that loops can leave missing mass in both games, even though
the programmed setup itself terminates. A bound on winning-probability
difference is not an upper bound on either full game's missing mass.
This development states the game endpoint for the returned-win event;
it includes no separate theorem about the difference of the full games'
returned masses. The standalone setup missing-mass statement has a
different scope.

This game still exposes a programmed E table correlated with the key.
Erasing that table to reach a key-only PKE/FO experiment with an independent
oracle requires another argument: identify the hidden programmed inputs,
bound the probability of hitting them, and state the relevant adversarial
query budgets. That transition is not supplied by the present setup bound.
The subsequent [E-erasure continuation](ntruplus768-e-erasure.md) proves it
under robust adversary losslessness and an effective typed/raw E-query
budget. Its universal count contract removes both analysis caps. The
additional hit and retry-tail costs are distinct from this page's
`<2^-239` comparison. The present
setup theorem continues to allow partial adversaries.

The [linear-RRec result](ntruplus768-linear-rrec.md) remains a separate
actual-caller connection. The subsequent [Gen-law continuation](ntruplus768-keygen-gen-law.md)
proves that the `(h,f)` projection of fresh/programmed returned byte keys
has exactly the output law of the two-loop `Figure18Gen.run()` procedure.
It also gives a separate actual-ROM approximation with initially empty E.
This marginal identification retains the E/key correlation and F-cache
behavior; it does not supply the independent-oracle transition above.
Public-key-dependent FO correctness-loss and security arguments and hardness
reductions remain further obligations. The earlier honest-KEM bound below `2^-238`
and ACWC2 bound below `2^-353` retain their own experiments. No complete
IND-CCA bound, concrete SHAKE-to-ROM theorem or QROM claim follows here.

## Reproduction

Run from the repository root:

```sh
./scripts/verify-ntruplus768-cca-setup.sh \
  --prior-evidence-root /path/to/thesis \
  --output /path/to/new-evidence-directory
```

Use a new or empty output directory outside the checkout. The sources are
in [`ntruplus/proof/768/ref/kem_cca_setup/`](../ntruplus/proof/768/ref/kem_cca_setup/).
The runner's completed report records main proofs, semantic EOF checks,
isolated unfinished-proof negatives, source controls and finite diagnostics.
Imported theories remain linked to prior evidence by source hashes; they
are not all new main replays. `--check-only` does not run a proof replay.

The declared proof setting is September 2026 EasyCrypt/Why3 with Z3,
`-no-eco`, `Proofs:check`, one prover and `OCAMLRUNPARAM=o=20`. No C/Jasmin
implementation, extraction or native API is changed. Native execution,
Safety, CT/SCT, C-memory/ABI and leakage boundaries are unchanged.
