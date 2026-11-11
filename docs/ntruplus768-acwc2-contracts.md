# Public randomness recovery, SOTP and G-input contracts for NTRU+768

This proof-only layer connects three concrete interfaces needed after the
[underlying PKE average-correctness result](ntruplus768-pke-average.md): public
randomness recovery, the SOTP encoding/decoding properties, and the exact
bytes queried to G. It keeps the existing extracted arithmetic and SOTP
calls and adds explicit array-model checks where stated below.

**Final replay: PASS (2026-10-14).** All 11 new mains and 117 lemmas
passed strict `-no-eco` / `Proofs:check`, including 11 semantic EOF
obligations and 11 isolated unfinished-proof rejections. The runner also
passed 58 structural/trust controls and 29 exact finite diagnostics. It
recorded 29 command logs, 22 isolated source copies, 780 pinned
sources, 792 runtime inputs and 293 external inputs, with unchanged
before/after hashes. The 596 imported EasyCrypt files remain linked to
prior PASS evidence; they are not counted as new main replays.

The full report is retained in the companion thesis directory at
`handoff/verification/ntruplus-acwc2-contracts-20261014/final-replay/summary.json`.
The small finite diagnostics exercise selected failure cases and do not
replace the EasyCrypt proofs.

The family name records its role in the ACWC2 proof path. These contracts
alone do not establish a worst-case-message correctness bound, the
average-to-worst theorem, or an IND-CCA reduction. The subsequent
[ACWC2 correctness development](ntruplus768-acwc2-correctness.md) composes
them in the actual fresh-key, independently sampled finite-G experiment;
its guide records the separate final integration and replay status.
The earlier fresh PKE
average bound below `2^-354` and initialized ROM bounds below `2^-238`
retain their stated experiments and scope.

## Public checked randomness recovery

`RRec.run(pk,m,ct)` receives exactly three public values: a 1152-byte public
key, a 768-coefficient message array and a 1152-byte ciphertext. Its
implementation is in
[`NTRUPlus768RRecProcedures.ec`](../ntruplus/proof/768/ref/acwc2_contracts/NTRUPlus768RRecProcedures.ec).
It performs the following operations:

1. Check the public-key encoding and compute its inverse with the actual
   `poly_baseinv` core. Serialize and check-decode a successful inverse so
   the following multiplication receives canonical coefficients.
2. Check the ciphertext encoding and require the supplied message to be
   ternary.
3. Use the existing DecapR2 arithmetic to subtract the transformed message
   and multiply by the public inverse. Apply the existing inverse NTT,
   center the coefficients modulo 3457 and check that the candidate is
   ternary.
4. Run the actual `PKEEnc` composition once on that candidate and compare
   the complete resulting ciphertext bytes with ct. Return `Some(r)` only
   when that check succeeds; otherwise return `None`.

There is no randomness search or enumeration. The top-level procedure
receives no secret key, supplied inverse or honest-encryption witness.
Internal scratch arrays are destinations for existing kernels. The
normalization and trit-check loops are explicit EasyCrypt array-model
glue, and the reencryption step is a single public consistency check.

[`NTRUPlus768RRecPublicInverse.ec`](../ntruplus/proof/768/ref/acwc2_contracts/NTRUPlus768RRecPublicInverse.ec)
connects the actual inverse/serialization/decoder calls to their exact
option-valued result. Its companion
[`NTRUPlus768RRecInverseAlgebra.ec`](../ntruplus/proof/768/ref/acwc2_contracts/NTRUPlus768RRecInverseAlgebra.ec)
proves actual BaseInv success, on the checked decoder's input range,
from an inverse in every terminal block. The proof makes each determinant
nonzero and establishes uniqueness modulo q=3457. Canonical inverses are
exactly equal. A generated key's inverse may be used as a logical
witness in this proof; it is not an input to the recovery algorithm. This
argument uses the terminal quartic blocks and needs no total CRT theorem.

The actual-call contracts in
[`NTRUPlus768RRecCallProof.ec`](../ntruplus/proof/768/ref/acwc2_contracts/NTRUPlus768RRecCallProof.ec)
give both directions:

- For a valid generated key and every ternary m and r, recovery on the
  honest `pke_ciphertext(pk,m,r)` returns `Some(r)` with probability one.
  The more general public-key theorem requires a canonical key whose
  computed public inverse succeeds. Neither statement requires the
  secret-product no-wrap condition used in PKE message decryption.
- For arbitrary pk, m and ct, a returned `Some(r)` implies that both m and
  r are ternary and `PKEEnc(pk,m,r)` returns exactly `Some(ct)`. This
  direction requires no generated-key relation or honest-ciphertext
  premise. Rejection is represented by `None`.

The forward direction follows from public cancellation and the transform
roundtrip; the final check accepts the recovered honest r. The reverse
direction uses the explicit reencryption check. The contract is for this
checked helper. The later [linear-RRec continuation](ntruplus768-linear-rrec.md)
proves that removing that call preserves the option result for every
input, retaining the encoding and ternary-domain guards. It also proves
the previously missing total terminal representability and reverse-transform
foundation. The new guide records the distinct actual CompleteDecaps
comparison theorem with the same decoded m1, cleared workspace and
separated G/H state, and the ACWC2 caller substitution carrying `2^-353`.
The full FO security-game connection retains its correctness-error loss. No native RRec export is introduced.

## Three properties of the actual SOTP calls

[`NTRUPlus768SOTPContracts.ec`](../ntruplus/proof/768/ref/acwc2_contracts/NTRUPlus768SOTPContracts.ec)
wraps the existing extracted SOTP encode/decode kernels. Messages are
96 bytes, pads are 192 bytes and encodings are 768-coefficient arrays.
`SOTPDecode` first calls the explicit trit-domain checker, then accepts the
raw decoder exactly when its status is zero. Thus a successfully decoded
all-zero message is `Some(zero)`, not rejection. The extra domain guard is
array-model glue; it is not asserted to be a check in the original native
decoder.

The procedure contracts establish:

| Property | Exact scope |
| --- | --- |
| Roundtrip | Encoding any message with any pad and decoding with the same pad returns `Some(message)`. |
| Rigidity | If decoding a code with a pad succeeds, encoding the recovered message with that same pad reconstructs the entire original code. |
| Fixed-message hiding | For every fixed message, an independent `uniform192` pad makes the actual encoded array have exactly the `pke_psi1` distribution. |

The rigidity argument is connected to the implemented coefficient and
byte layout in
[`NTRUPlus768SOTPRigidity.ec`](../ntruplus/proof/768/ref/acwc2_contracts/NTRUPlus768SOTPRigidity.ec).
The hiding law is the CBD1 product distribution, with trit probabilities
`1/4, 1/2, 1/4` for `-1, 0, 1`; it is not uniform over ternary polynomials.
The pad must
have the stated independent uniform law. The G contracts below distinguish
newly sampled answers from cached ones.

## Serialized randomness and the actual G query

The codec defines

```text
rr_G_input(r) = serialize(NTT(r))              : 1152 bytes
rr_G_query(r) = 0x01 || rr_G_input(r)           : 1153 bytes
```

[`NTRUPlus768RRecCodec.ec`](../ntruplus/proof/768/ref/acwc2_contracts/NTRUPlus768RRecCodec.ec)
proves that the 1152-byte payload is injective on the ternary randomness
domain. The transform and centered-recovery lemmas justify this statement
through the actual serialized representation. A successful RRec result
satisfies this ternary-domain premise, so its G-input encoding is unambiguous.

[`NTRUPlus768ACWC2HashG.ec`](../ntruplus/proof/768/ref/acwc2_contracts/NTRUPlus768ACWC2HashG.ec)
connects the existing extracted NTT and message-preparation calls to both
arrays. It proves the tag, lengths and injectivity of the full raw query,
and explicitly connects the byte list to the existing total raw classifier:

```text
decode_typed(to_list(rr_G_query(r))) = Some(G(rr_G_input(r))).
```

The `acwc2_g_query_typed` identity uses that classifier's complete tag and
length check. The procedure connection relates `ACWC2HashG.run(r)` through
`SHAKEGROM` to `ROG.get(rr_G_input(r))` with the same result and G-table state.

A cached payload returns its stored 192-byte pad and leaves the whole G
table unchanged. Every old entry is preserved. The exact uniform law
`mu uniform192 event` holds when `rr_G_input(r)` is absent from the current
table and r is in the ternary domain. This freshness condition supplies
the distribution required for a fresh G pad; query encoding injectivity
does not assert that distinct G outputs never collide. The connection is
to the declared classical ROM, not a concrete SHAKE-to-ROM theorem.

## Reproduction and remaining proof path

Run from the repository root:

```sh
./scripts/verify-ntruplus768-acwc2-contracts.sh \
  --prior-evidence-root /path/to/thesis \
  --output /path/to/new-evidence-directory
```

The output directory must be new or empty and outside the checkout.
Sources are in
[`ntruplus/proof/768/ref/acwc2_contracts/`](../ntruplus/proof/768/ref/acwc2_contracts/),
with controls in
[`tests/ntruplus768/acwc2_contracts/`](../tests/ntruplus768/acwc2_contracts/).
The runner uses September 2026 EasyCrypt/Why3 with Z3, `-no-eco`,
`Proofs:check`, one prover and `OCAMLRUNPARAM=o=20`. It checks the selected
new mains, their semantic EOF obligations, source controls and isolated
unfinished-proof negatives. Imported theories are bound to prior evidence
by hashes; they are not all claimed as fresh main replays.
`--check-only` does not establish a proof replay.

The proof path has an actual PKE average experiment and concrete RR,
SOTP and G-input contracts. The subsequent
[ACWC2 correctness guide](ntruplus768-acwc2-correctness.md) describes their
composition, independent finite-G law and proved expected worst-message bound
below `2^-353`. Its prepared-cache caller connection does not assert
arbitrary-context equivalence with an initially empty lazy G table.
Public-key-dependent FO and adversarial oracle reasoning, and the hardness
reduction, remain further work. Exact identification of the
implementation's accepted Gen law with the paper's unit-conditioned law
and the full acceptance-predicate/unit-test equivalence remain explicit
obligations. Total terminal representability and inverse-to-forward
congruence are supplied by the [linear-RRec continuation](ntruplus768-linear-rrec.md);
its exact results do not stand in for the remaining distribution or
security reductions.

No C/Jasmin implementation or exported native API is changed. The new
array-model helper does not itself prove correspondence with a native
Figure 18 routine. Native SHAKE/RNG, C memory/ABI, binary execution and
full-API leakage retain their existing boundaries. No new extraction,
native, Safety, CT or SCT replay is claimed here.
