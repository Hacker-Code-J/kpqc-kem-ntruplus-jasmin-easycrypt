# NTRU+768 actual decapsulation and modified FO comparison

**Full replay PASS**, 2026-10-15: 30 mains,
401 lemmas, 30 semantic EOF probes and
30 own-main unfinished-proof rejections.
The replay passed 49 structural/trust controls
and 17 finite diagnostics.
All 893 source and 299 external inputs
matched their before/after hashes. The 882 source pins
include imported dependencies linked to prior PASS evidence.
The complete report is retained in the thesis evidence directory.

This proof-only continuation bounds the returned-win probability difference
between the existing actual CCA game and a game using full modified FO
reencryption. It composes the completed E-erasure comparison with the
correctness-loss transition. It does not establish the complete IND-CCA
advantage bound or the NTRU/RLWE hardness reduction.

## Endpoints and exact behavior

The final theorem `fo_original_full_distance_256` in
[`NTRUPlus768FOSecurity.ec`](../ntruplus/proof/768/ref/kem_modified_fo/NTRUPlus768FOSecurity.ec)
compares `CCAOriginalGame(A).run()` and `FOFreshReencryptGame(A).run()`.
Both use the original uncapped adversary interfaces. The latter uses the
existing fresh-expansion KeyGen and actual Encaps. Its Decaps port checks
the exact challenge ciphertext before entering the computation.

[`NTRUPlus768FOProcedures.ec`](../ntruplus/proof/768/ref/kem_modified_fo/NTRUPlus768FOProcedures.ec)
uses actual recovery, hash preparation, CBD, SOTP encoding, PKE encryption,
output masking and workspace clearing. It checks `LinearRRec.run` for
`Some` membership in the prescribed trit domain. It also checks SOTP
decoding, derives r from the H tail, calls G on the actual serialized r
input, reencodes the message, encrypts the new code, and compares the
ciphertext. This is not a same-decoded-polynomial reencryption check.

The native order GuardedR2, G, SOTPDecode, H is retained. SOTP failure
still calls H; an entry-guard rejection skips G/H. The comparison's
additional G call is handled through the same shared oracle. Returned
status and shared key retain the original option interpretation, including
successful zero keys; the exposed workspace is cleared. No new C/Jasmin
implementation or native erasure claim is introduced.

## Correctness envelope and challenge exception

`fo_base_bad` is the **base PKE** error for the code
`SOTPEncode(msg,G(r))` encrypted with r. It is not the transformed ACWC2
failure event. `fo_error` maximizes its probability over messages, with
the actual CBD1 r law. The intermediate weighted bound from the earlier
ACWC2 proof establishes the expected envelope below `2^-353`.

Native acceptance implies full-FO acceptance. The reverse implication
holds when the corresponding base-PKE error does not occur. If the full
reencryption differs from the query ciphertext, both reject regardless
of that error. For the cached challenge H entry, full reencryption equals
the challenge ciphertext; hence every permitted different ciphertext is
rejected by both. The challenge entry is therefore excluded from the bad
monitor without a separate correctness term.

Only a fresh nonchallenge H insertion can newly set bad. Repeated typed
or raw queries retain their cached values. The actual H-prefix/tail law
supplies the CBD error distribution; no adaptive cache answer is treated
as a new independent sample.

## Shared setup and G distribution

The private setup observation retains the actual key result and its
final F table. `FOSetupKeySource` initializes F and runs the existing
instrumented fresh KeyGen. It does not replace an arbitrary F cache with
an independent uniform suffix. G pads are then sampled independently on
the finite serialized image of trit randomness. The input encoding is
injective on that domain. Other arbitrary G inputs remain lazy.

The installed PROM eager/lazy theorem, a private completion loop and the
actual query adapters establish equality with the original lazy G game.
The ordinary raw G suffix cache stays separate. The completed equality
is for the actual adversary context; it is not inferred merely from
pointwise oracle output distributions. The setup distributional
composition and kernel averaging preserve initial adversary state and
the joint key/F correlation.

## Request contracts and bound

Let Q = qH + qD. An H request is a typed H call or a valid raw H dispatch:
129-byte input, tag 2, output length 0..224. Repeated requests and output
length zero count. Every Decaps request counts, including an exact
challenge request or malformed ciphertext. Other raw requests do not
use the H budget.

The final theorem explicitly requires:

- The original interface/private-state access restrictions, including
  the proof-only context, bad flag, budgets and private eager-oracle state.
- Robust adversary losslessness against every permitted collection of
  lossless oracle ports. A finite cap alone does not imply termination.
- Separate universal initial-state `FOCountedA` contracts for the actual
  native plain backend and the full-reencryption plain backend. Each
  forwards all requests and returns with total H/Decaps count at most Q
  from zero counters, limit Q and no overflow.
- For the actual-ROM composition, the preceding E-erasure universal
  effective-request contract with qE, and its private-state restrictions.
- Nonnegative qE and Q and the corresponding private initial budget
  values. The endpoint games do not expose these analysis variables.

The generic adaptive bad-event bound itself does not assume A_LL.
Robust A_LL is used to turn the up-to-bad coupling into returned-win
distance and to remove the analysis caps. KeyGen's actual unrestricted
ROM termination is never assumed. Probabilities are not conditioned on
return, and no arbitrary outcome is assigned to nontermination.

The fixed-setup error is at most `Q * fo_error(key,G)`. Averaging the
proved envelope gives `Q/2^353`. The final uncapped comparison is

```
|Pr[CCAOriginalGame(A): win] - Pr[FOFreshReencryptGame(A): win]|
  <= (130820 + 512*qE)/2^256 + Q/2^353.
```

The constants use qf=qg=256 in the prior retry analysis, not an
implementation retry cap. This envelope is not asserted definitionally
equal to the specification's logarithmic delta-prime formula.

## Reproduction and remaining work

```
./scripts/verify-ntruplus768-modified-fo.sh
./scripts/verify-ntruplus768-modified-fo.sh --check-only
```

Full verification runs every new main with semantic EOF checks, each
main's own unfinished-proof rejection, structural/trust controls and
small finite diagnostics. `--check-only` verifies inputs and controls;
it does not rerun proofs. `EC_JOBS=1` selects serial verification and
the default `EC_JOBS=2` uses two independent isolated checker processes.
The strict settings are `-no-eco`, `Proofs:check`, Z3, timeout 60,
max-provers 1 and `OCAMLRUNPARAM=o=20`. Imported EC files are pinned to
prior PASS evidence; they are not counted as newly replayed mains.

Evidence is in the thesis workspace under
`handoff/verification/ntruplus-modified-fo-20261015/`. Developmental
failures and `--llm` diagnostics are not final verification results.
The [spreadness continuation](ntruplus768-spreadness.md) establishes
base-PKE concentration, a quantifier-safe transformed expected maximum,
and a lazy-cache call bound. The subsequent
[public H-history simulation](ntruplus768-fo-simulation.md) now compares
this fresh full-FO endpoint with a simulator without a secret-key Decaps
interface, at cost `qD/2^768 + (qH+qD)/2^353`. Its universal Decaps and
Known-backend public-H contracts are stated separately from this family's
native/full contracts. IND-CPA embedding and hardness reductions remain,
followed by HAETAE UF-CMA and separately QROM.
Native SHAKE/RNG correspondence, C memory/ABI and whole mixed-API CT/SCT
retain their existing boundaries; none is newly verified by this family.
