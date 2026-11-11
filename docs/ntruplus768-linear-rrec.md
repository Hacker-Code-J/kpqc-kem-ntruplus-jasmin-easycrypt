# Linear public randomness recovery for NTRU+768

This continuation removes the extra PKE reencryption call from the public
checked randomness-recovery helper. `LinearRRec.run(pk,m,ct)` keeps the
checked encodings, public inverse calculation, existing R2/inverse-NTT
arithmetic, coefficient centering and ternary-domain check. It has the
same three public inputs as `RRec.run` and calls no `RRecVerify` procedure.

Final family replay and evidence record: **PASS**, 2026-10-14. The complete replay checked all 12 new
mains (120 lemmas), 12 semantic end-of-file probes and 12 isolated
unfinished-proof rejections. It passed 62 structural/trust controls and
26 exact finite-domain diagnostics. All 812 source pins, 825 runtime
inputs and 295 external tool/configuration/theory/driver/prior-evidence
files matched their recorded before/after hashes. The 623 imported EC
files are hash-linked prior evidence, not newly replayed mains. The
companion thesis record is
`handoff/verification/ntruplus-linear-rrec-20261014/final-replay/summary.json`.
It contains 31 command logs and 24 checked proof copies.

The complete option-valued result is proved equal for every public key,
message array and ciphertext, including rejected inputs. The actual-call
contracts are in
[`NTRUPlus768RRecLinearProof.ec`](../ntruplus/proof/768/ref/linear_rrec/NTRUPlus768RRecLinearProof.ec).
The public-helper, transform, decapsulation-comparison and ACWC2 caller
proofs passed both individual strict checks and the final complete replay.
This is a proof-only composition of existing kernels and array-model glue.
It adds no native export and changes no C or Jasmin implementation.

## Public procedure and arbitrary ciphertexts

The procedure in
[`NTRUPlus768RRecLinearProcedures.ec`](../ntruplus/proof/768/ref/linear_rrec/NTRUPlus768RRecLinearProcedures.ec)
performs these steps:

1. Check the 1152-byte public key and compute its inverse using the actual
   BaseInv core. Serialize and check-decode the inverse to canonical form.
2. Check the 1152-byte ciphertext and the supplied ternary message array.
3. Compute the existing R2 expression, apply inverse NTT, center its
   coefficients modulo 3457 and check the recovered candidate is ternary.
4. Return that candidate as `Some(r)`, or `None` if a check failed.

Neither a secret key nor a stored inverse is an input. The internal
`LinearRRecUsingInverse` procedure receives only the inverse already
computed from the public key. Rejection covers malformed encodings,
non-ternary messages, failed public inversion and non-ternary candidates.

The proved algebraic endpoint `rrec_linear_candidate_reencrypt` concerns an
arbitrary canonical ciphertext. If the public inverse succeeds, the
message is ternary and the computed candidate is ternary, then

```text
pke_enc_spec(pk, m, candidate) = Some(ct).
```

It has no honest-ciphertext or no-wrap premise. The proved
`rrec_linear_checked_equivalence` and `linear_rrec_actual_equiv` contracts
therefore remove the check for all inputs: positive branches pass it by
algebra, while negative branches return `None` in both procedures.
`linear_rrec_event_probability` states equality for every event on the
option result. The honest generated-key specialization still recovers
every ternary r without the no-wrap condition used for message decryption.

## The reverse transform and serialization arguments

[`NTRUPlus768RRecCanonical.ec`](../ntruplus/proof/768/ref/linear_rrec/NTRUPlus768RRecCanonical.ec)
defines coefficientwise canonicalization C into `[0,3457)`. Its domain S
is finite, canonicalization preserves coefficients modulo q and the
associated input polynomial, and globally congruent canonical arrays are
equal. The finiteness proof is symbolic; it does not enumerate `3457^768`
arrays during verification.

[`NTRUPlus768RRecTransform.ec`](../ntruplus/proof/768/ref/linear_rrec/NTRUPlus768RRecTransform.ec)
sets `F = C ∘ forwardNTT` and `I = C ∘ inverseNTT` on S. Existing transform
semantics give `I(F(x)) = x`. An explicit finite-set argument then proves
`F(I(y)) = y`. Consequently:

- `rrec_terminal_represented` supplies a global polynomial representative
  for every word-valued terminal array.
- `rrec_inverse_forward_mod` proves that forward NTT after inverse NTT is
  coefficientwise congruent to any input in the inverse NTT's q-range.
- `rrec_inverse_forward_trit` connects a centered ternary inverse-NTT
  candidate to the original terminal input under the same range premise.

[`NTRUPlus768RRecTerminal.ec`](../ntruplus/proof/768/ref/linear_rrec/NTRUPlus768RRecTerminal.ec)
provides the local uniqueness step: terminal arrays representing the same
polynomial have equal coefficients modulo q. It uses the degree bounds
of a block polynomial and its terminal quartic. Total representability
and the reverse transform are derived here, rather than assumed as a
CRT or surjectivity premise.

[`NTRUPlus768RRecSerialization.ec`](../ntruplus/proof/768/ref/linear_rrec/NTRUPlus768RRecSerialization.ec)
proves injectivity of `decoded_poly`, the raw 12-bit unpacking of all
1152 bytes, and canonical decode-then-encode roundtrip. The rejecting
option-valued checked decoder is not claimed to be injective. Together with public inverse cancellation,
these results turn coefficient congruence into exact ciphertext-byte
equality. They resolve the earlier missing representation/existence and
reverse-transform steps. They do not identify actual KeyGen acceptance
with quotient-ring unit rejection in both directions, or equate the
accepted key distribution with the paper's Gen distribution.

## Connection to the existing decapsulation comparison

The existing `CompleteDecaps` path uses the secret key's stored inverse
and compares the serialized R2 transform with the serialized NTT of the
randomness regenerated from H. It does not apply inverse NTT to R2 or run
the new public helper's ternary-candidate check.

Under `pke_key_relation w`, the comparison is proved equivalent to PKE
reencryption using the **same decoded message polynomial m1** and
regenerated randomness, for ciphertexts passing the existing entry checks.
The byte-level relation is in
[`NTRUPlus768RRecNativeComparison.ec`](../ntruplus/proof/768/ref/linear_rrec/NTRUPlus768RRecNativeComparison.ec).
The proof-facing composition `ReencryptDecaps(G,H).run(pk,ct,sk,workspace)` in
[`NTRUPlus768RRecNativeProcedures.ec`](../ntruplus/proof/768/ref/linear_rrec/NTRUPlus768RRecNativeProcedures.ec)
retains the existing guard, G/H preparation, hash, verification, masking
and clearing calls.

[`NTRUPlus768RRecNativeProof.ec`](../ntruplus/proof/768/ref/linear_rrec/NTRUPlus768RRecNativeProof.ec)
connects that composition to the existing `CompleteDecaps(G,H)` caller
for every ciphertext, including early rejection by the existing entry checks.
`native_reencrypt_decaps` proves equal returned shared keys, statuses,
workspaces and post-call oracle states from equal initial workspace and
oracle states. On return, the workspace is `clear_zero_spec`. The generic theorem
requires the module-state restriction `H<:CompleteSHAKEH{-G}`: H cannot
access G's state. It assumes neither a functional hash specification nor
hash-call losslessness, and needs no no-wrap or honest-ciphertext premise.
It is a relational equivalence, including potentially nonreturning hash
calls, rather than an unconditional termination claim.

The concrete endpoint `native_reencrypt_rom_decaps` instantiates
`SHAKEGROM` and `SHAKEHROM`, whose separate `ROG.m` and `ROH.m` tables satisfy
the state restriction. Its postcondition preserves the complete result,
`ROG.m` and `ROH.m`, with the returned workspace cleared. No corresponding
claim is made for an arbitrary mutable backend shared by both ports.
This caller proof is separate from the public helper's option equality.

## ACWC2 caller substitution

[`NTRUPlus768RRecACWC2Bridge.ec`](../ntruplus/proof/768/ref/linear_rrec/NTRUPlus768RRecACWC2Bridge.ec)
proves that `LinearACWC2Dec(G)` and the existing `ACWC2Dec(G)` have equal
results and G state after substituting `LinearRRec` for `RRec`. This holds
for any G port without a functional or losslessness premise. Encryption,
PKE/SOTP/CBD calls, query order and option-rejection behavior are retained.
The random trial and `LinearACWC2FixedOracleTrial` also have the same
result and post-call `ROG` state as the earlier callers.

The endpoint `linear_acwc2_fresh_worst_actual_calls` transfers the bound
below `2^-353` to the actual caller without the redundant RRec verification.
It uses the same reified `KeygenSource(FreshExpand)` law, the same
`acwc2_gpads_law` and the same maximum over all 96-byte messages. It adds
no average-error or oracle-law assumption to the existing result, and
retains the order `E_key E_G max_message Pr_r[failure]`.

This variant retains the ACWC2 array composition's inverse-NTT and trit
check. It does not add those operations to native CompleteDecaps or
identify the public helper with that native instruction path.

## Distinction from full FO reencryption

The pinned official specification defines linear RRec in Figure 18 as
`(c-m)h^-1`. Its RR definition concerns arbitrary ciphertexts: a returned
randomness in the declared domain must reencrypt to the ciphertext. The
public helper's option result makes that domain test explicit; the
honest forward theorem also rules out a vacuous always-rejecting helper.

Figures 12--14 use a different comparison in the full FO transformation.
After decoding the 96-byte message and obtaining new randomness from H,
FO forms a new encoded polynomial
`M'' = SOTPEncode(decoded_message, G(regenerated_randomness))` before
reencrypting. That polynomial is not assumed equal to the earlier
decoded m1 on every ciphertext. Theorem 4.3 compares the security games
with a correctness-error term `(q_H + q_D) * delta'`; it is not an
unconditional perfect equivalence of the full FO decapsulators.

The official text used for these distinctions is the pinned local
`research/ntruplus-specification.txt` in the companion evidence directory
`handoff/verification/ntruplus-classical-rom-20261013/` (RR definition,
Figure 18 and Section 4.2/Theorem 4.3). No IND-CCA advantage bound or
correctness-loss game hop is claimed by this linear-RRec layer.

## Subsequent CCA setup transfer

The [shared-state CCA setup development](ntruplus768-cca-setup.md) addresses
a different connection: actual ROM KeyGen versus fresh expansion samples
recorded in the shared E table, followed by the actual CCA adversary.
It retains the final E/F tables in the comparison and proves a
`delta + tau` winning-probability distance without assuming attacker
termination. For the initialized actual games, the difference is at most
`130818/2^256`, strictly below `2^-239`. Its family replay status is
recorded separately in that guide.

This setup transfer keeps the correlation between the key and programmed
E entries. It does not erase that table, replace the full FO comparison by
the same-m1 comparison above, or discharge the FO correctness-loss and
hardness arguments. It also does not claim that an arbitrary full CCA game
has small missing mass. The completed linear-RRec contracts and historical
replay record in this document are unchanged.

## Reproduction and retained boundaries

Run from the repository root:

```sh
./scripts/verify-ntruplus768-linear-rrec.sh \
  --prior-evidence-root /path/to/thesis \
  --output /path/to/new-evidence-directory
```

Use a new or empty output directory outside the checkout. The sources
are in
[`ntruplus/proof/768/ref/linear_rrec/`](../ntruplus/proof/768/ref/linear_rrec/)
and controls in
[`tests/ntruplus768/linear_rrec/`](../tests/ntruplus768/linear_rrec/).
The runner uses September 2026 EasyCrypt/Why3 with Z3, `-no-eco`,
`Proofs:check`, one prover and `OCAMLRUNPARAM=o=20`. Imported dependencies
are tied to prior evidence; source checks and finite diagnostics do not
replace a proof replay.

The prior [ACWC2 expected worst-message bound](ntruplus768-acwc2-correctness.md)
below `2^-353` and initialized honest-KEM bound below `2^-238` retain their
original experiments. The [Gen-law continuation](ntruplus768-keygen-gen-law.md)
identifies actual accepted keys with the paper's Gen projection. The
[modified FO continuation](ntruplus768-modified-fo.md) proves the adaptive
lazy/eager connection and full reencryption correctness-loss transition.
Spreadness, remaining hardness reductions, concrete SHAKE-to-ROM
correspondence and QROM analysis remain separate work. No new native execution, extraction, Safety,
CT/SCT, C-memory or ABI theorem is asserted here.
