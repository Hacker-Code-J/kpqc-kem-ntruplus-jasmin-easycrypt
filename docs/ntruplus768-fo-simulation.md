# NTRU+768 full modified-FO simulation from public H history

**Full replay PASS**, 2026-10-16 (KST): 39 mains / 517 lemmas,
39 semantic EOF probes and 39 own-main unfinished-proof rejections.
The replay passed 50 structural/trust controls
and 10 finite diagnostics.
All 944 source inputs and 301 external inputs matched
before/after hashes. Source pins: 933; 705 imported EC files are
linked to 17 prior PASS records and are not counted as fresh main replays.

This family removes the secret key from the Decaps interface of the
fresh-expansion full modified-FO game. The public simulator scans externally
triggered H records and calls the actual encryption procedures. The final
theorem `sim_fo_public_distance` in
[`NTRUPlus768SimFinal.ec`](../ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimFinal.ec)
proves

```
|Pr[FOFreshReencryptGame(A).run(): win]
 - Pr[SimPublicFreshGame(A).run(): win]|
  <= qD/2^768 + (qH+qD)/2^353,
```

where `qD = max(0, SimSelectedBudget.budget)` and `qH >= 0`. The budget is
the persistent EasyCrypt hybrid parameter. It is not a runtime retry cap.
Both endpoint games use the uncapped adversary interfaces.

The earlier [modified-FO result](ntruplus768-modified-fo.md) separately
compares the actual original CCA game with `FOFreshReencryptGame`, using
its E-erasure and native/full request contracts. This theorem starts at
the fresh full-FO endpoint and keeps its own query contracts explicit.
This theorem itself compares those two games. The subsequent
[IND-CPA reduction](ntruplus768-indcpa-reduction.md) composes it with a concrete
CPA attacker and bounds the original IND-CCA advantage; the hardness
reduction remains open.

## Adversary and request contracts

The final theorem requires the listed private-state restrictions and:

- Robust adversary losslessness for every permitted collection of
  lossless typed/raw hash and Decaps ports. A finite query count alone
  does not imply termination.
- A universal `FOCountedA` Decaps contract: for every permitted H/D
  backend that cannot access the private budget state, `nD=0` implies
  returned `nD <= qD`. This is stronger than a bound for one original
  backend. The counting wrapper forwards every request.
- The `SimPublicCountedA` public-H contract for the concrete Known
  backend, starting with zero H count, limit qH and no overflow. Its
  returned count must be at most qH. No separate Ghost or Lookup count
  contract is needed for this step.

Every public Decaps request counts, including challenge ciphertexts and
malformed inputs. Public H requests include typed H and valid raw H
dispatches: a 129-byte input with tag 2 and output length 0..224.
Repetitions and zero-output requests count. Internal H evaluations in
Decaps are handled by the selected-query argument, not as public H records.

The losslessness premise is used for the two-sided up-to-bad comparison
and removal of the analysis caps. Exact projection and private-sampling
equalities retain their separate partial-execution scope. The theorem
does not normalize probabilities by return or assume unrestricted actual
ROM KeyGen termination.

## Public history and the actual lookup

[`SimGames`](../ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimGames.ec)
uses the existing fresh KeyGen and actual Encaps. Its public challenge
passes pk, the public F(pk) suffix and cstar to the simulator. The
[`SimLookup`](../ntruplus/proof/768/ref/kem_fo_simulation/NTRUPlus768SimLookup.ec)
port reads these public values, the H history and G; it does not receive
or read sk. Diagnostic comparison kernels retain a secret witness, which
is not part of the simulator interface.

The history records the full H reply when an external typed/raw H request
occurs. A raw caller still receives only its requested prefix, possibly
zero bytes. The record is not a claim that the adversary received all
224 bytes. Repeated requests reuse the cached value. The physical H table
also contains the challenge and private Decaps evaluations, so absence
from public history alone does not establish freshness.

Lookup filters records by the public suffix and uses actual CBD, G
preparation, SOTP encoding and PKE encryption to find a matching
ciphertext. It blocks cstar exactly and preserves the distinction between
rejection and a successful all-zero key. The challenge H entry is handled
separately: its full reencryption is cstar, so it cannot accept a permitted
different ciphertext, even when its base-PKE correctness event is bad.

## Hidden evaluations and the selected query

Before the selected unknown-answer call, the hybrid returns None on
earlier unknown calls. Its physical H table is covered by public history
and the challenge entry. Actual prepare contracts then show that the
selected input is fresh. After that call, Real answers can create unlogged
entries, so the cover invariant is explicitly released. The private
selection counter proves at most one selected call; it does not prove
that a partial adversary terminates.

The selected fresh-H acceptance probability is bounded by
`2^-768 + fo_error(key,G)`. The atom term comes from the actual CBD1 law.
The error term uses the existing base-PKE correctness envelope for a
fixed key and prepared G. This is not an arbitrary fixed-G ciphertext
bound of `2^-768`. In the Known phase, public H correctness failures
contribute `qH * fo_error(key,G)`; the selected hybrid contributes
`qD * (2^-768 + fo_error(key,G))`.

Hidden H results that are discarded can be replaced by a private oracle
sample and then removed using the installed PROM theorem. The actual
first G lookup in `DecapMessage` may lie outside the prepared trit image.
After connecting Known to an actual-prefix-plus-Lookup intermediate game,
its result is unused and the same get/sample/skip argument removes it.
The regeneration G call is on CBD trit randomness and is already prepared.
These are adaptive oracle-context equalities, including later repeated
queries; they do not assert equality of the final latent G/H maps.

## Shared setup and averaging

The exact `FOSetupSource` law retains the actual fresh accepted key and
its F table, followed by independent pads on the finite trit G image.
Key/F correlation and whole-buffer acceptance conditioning are preserved.
Other G inputs remain lazy. No accepted-coefficient independence or
fixed-key numerical error claim is added.

The actual observed setup establishes the challenge, history and prepared
cache conditions. A proof-only ready guard is checked once before the
phase and is removed by an exact equality after that setup. It does not
stop an execution when a later bad event occurs. The sequential-distance
lemma lifts the pointwise bound through the same randomized setup using
its probability-one postcondition and explicit setup/phase losslessness.

Finally, `E[fo_error(key,G)] < 2^-353` under the exact joint source law
gives the displayed uncapped-game bound. The proof does not exchange a
maximum with an expectation or substitute an output-only key law for
the complete shared setup state.

## Reproduction and scope

```sh
./scripts/verify-ntruplus768-fo-simulation.sh
./scripts/verify-ntruplus768-fo-simulation.sh --check-only
```

The full runner checks each new main with a semantic EOF probe and an
own-main unfinished-proof rejection. It also checks structural/trust
controls and finite diagnostics. `--check-only` reports
`SOURCE_CHECK_ONLY`; it does not rerun EasyCrypt proofs or receive a full
proof PASS. Finite diagnostics are supporting examples, not substitutes
for the symbolic proofs.

The default `EC_JOBS=2` uses two isolated checker processes; `EC_JOBS=1`
selects serial verification. Strict settings are `-no-eco`, `Proofs:check`,
Z3, timeout 60, max-provers 1 and `OCAMLRUNPARAM=o=20`. `--output` requires
a new or empty directory outside the checkout. A relocated checkout can
use `--prior-evidence-root` to locate the thesis's earlier evidence.
Imported EC files are hash-linked to prior PASS records and are not
counted as newly replayed mains.

Evidence is retained in the thesis workspace under
`handoff/verification/ntruplus-fo-simulation-20261015/`. This family changes
no native C/Jasmin code, extraction or API and reruns no native, Safety or
CT/SCT test. Fixed SHAKE/ROM correspondence, C memory/ABI, the remaining
hardness reduction, HAETAE UF-CMA and QROM retain their separate
obligations. The IND-CPA embedding is supplied by the linked continuation.
