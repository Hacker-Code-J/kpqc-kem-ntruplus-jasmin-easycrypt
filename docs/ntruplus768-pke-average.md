# Underlying PKE average correctness for NTRU+768

This proof-only development composes the existing extracted arithmetic and
checked-decoder kernels into PKE encryption and decryption procedures. Its
average experiment generates a key with the implementation's fresh-expansion
KeyGen, then independently samples the message and encryption randomness
from the implemented CBD1 law. The numerical endpoint is
`pke_fresh_average_correctness` in
[`NTRUPlus768PKEAverageCorrectness.ec`](../ntruplus/proof/768/ref/pke_average_correctness/NTRUPlus768PKEAverageCorrectness.ec):

```text
Pr[PKEAverage(FreshExpand).run(): returned failure] < 2^-354.
```

The fresh experiment is lossless. Its failure event includes encryption
rejection, decryption rejection and a recovered polynomial different from
the sampled message. This result concerns the actual acceptance-conditioned
fresh key law. The existing initialized honest-KEM ROM bound,
`returned failure + missing mass < 2^-238`, remains a separate result; see
[the numerical KEM guide](ntruplus768-kem-numerical-dfr.md).

## Actual procedures and domains

The compositions are in
[`NTRUPlus768PKEProcedures.ec`](../ntruplus/proof/768/ref/pke_average_correctness/NTRUPlus768PKEProcedures.ec),
with their functional contracts in
[`NTRUPlus768PKECallProof.ec`](../ntruplus/proof/768/ref/pke_average_correctness/NTRUPlus768PKECallProof.ec).

`PKEEnc.run(pk,m,r)` takes a 1152-byte serialized public key and two
768-coefficient word arrays. The functional encryption contract requires
both arrays to contain ternary coefficients. It runs the existing checked
public-key decoder, forward NTT on r and m, polynomial basemul, centered
addition and serialization. A failed public-key decode returns `None`;
otherwise it returns `Some(ct)`. The ternary-domain requirement is a proof
premise, not a new runtime input check.

`PKEDec.run(ct,fbytes)` takes two 1152-byte arrays. It checks the ciphertext
and serialized f component with the existing decoder. If both are
canonical, the existing candidate procedure performs multiplication by f,
inverse NTT and centered reduction modulo three; otherwise it returns
`None`. Decryption computes its candidate without receiving the original
message as an argument. Its functional option-valued contract applies to
arbitrary input byte arrays.

The PKE secret contains only f's serialized transform. It does not include
the KEM inverse-h block or HashF suffix. The underlying PKE procedures make
no F/G/H query and perform no SOTP or FO reencryption check. Key generation
still uses the actual instrumented KeyGen, including its existing Finish
and workspace-clear calls. That Finish call computes the KEM HashF suffix;
the PKE projection does not consume it.

These are EasyCrypt compositions of existing extracted kernels. They are
not newly exported native PKE functions or changes to the C/Jasmin API.

## Key, message and randomness distributions

[`NTRUPlus768PKEKeyDistribution.ec`](../ntruplus/proof/768/ref/pke_average_correctness/NTRUPlus768PKEKeyDistribution.ec)
connects a uniform 192-byte buffer to `pke_psi1`: 768 independent integer
trits with probabilities `1/4, 1/2, 1/4` for `-1, 0, 1`. It proves that
the word encoding preserves those coefficients and that their field
polynomial has the corresponding iid-trit pushforward law.

The implemented acceptance predicates factor through the entire CBD array:
shape f as `1+3*f0` or g as `3*g0`, run the actual forward-NTT specification,
and apply the existing block-inversion success predicate. Conditioning
commutes with this array projection. Thus the accepted f0/g0 pair has law

```text
dcond pke_psi1 pke_f_accept_array
  * dcond pke_psi1 pke_g_accept_array.
```

The earlier acceptance lower bounds normalize both factors. The two
accepted arrays are independent of one another; coefficients within either
accepted array need not be independent. The actual f-then-g retry law,
Finish and clearing contracts establish the same pair law for the returned
KeyGen witness.

Two subsequent independent uniform 192-byte buffers pass through the
actual checked CBD1 procedure to produce r and m. Their joint law is
`pke_psi1 * pke_psi1`, independently of the accepted key pair. The full
projection theorem retains this joint law, without replacing accepted
coefficients by iid samples. The fresh experiment and these projections
do not require a fresh initial F cache.

In `Rq = F_3457[X]/(X^768-X^384+1)`, the implemented shapes are exactly
`f=1+3*f0` and `g_actual=3*g0`. The field-key projection records `(f,g0)`;
the implemented public-key numerator is `3*g0`. A separate quotient-ring
lemma proves that multiplication by 3 preserves and reflects invertibility,
using the nonzero field element 3 and its inverse.

This average-correctness development does not itself identify the NTT/baseinv
acceptance predicate with the quotient-ring-unit test. The subsequent
[Gen-law continuation](ntruplus768-keygen-gen-law.md) proves that equivalence
and equates the `(h,f)` projection of fresh/programmed returned byte keys
with the output law of the two-loop `Figure18Gen.run()` procedure. A separate
cached-ROM approximation applies with initially empty E. The average
experiment and its bound already hold under actual acceptance and do not
assume this later identification.

## Polynomial semantics and the failure implication

The general encryption theorem in
[`NTRUPlus768PKEAlgebra.ec`](../ntruplus/proof/768/ref/pke_average_correctness/NTRUPlus768PKEAlgebra.ec)
proves that the decoded ciphertext transform represents `H*r+m`, under an
explicit premise that the decoded public-key transform represents H.
General decryption similarly assumes terminal representations for the
decoded ciphertext and f. The independent `pke_ring_decodes` relation
selects centered coefficients modulo q and then ternary residues modulo 3;
its definition contains no NTT program or supplied message.

For generated valid keys, `pke_valid_key_cf_semantics` proves the actual
ciphertext-times-f identity

```text
c*f = (3*g0)*r + m*(1+3*f0)  in Rq.
```

This statement uses the generated-key relation and ternary m/r domains.
It needs neither an assumed public-key representative H nor a no-wrap
premise. A sufficient integer no-wrap condition is used only in the next
step, which identifies the result of centered reduction modulo three with
m. The average experiment discharges its key and domain premises through
the actual KeyGen and CBD1 contracts.

The failure implication connects the actual PKE return event to the same
integer no-wrap event used by the numerical KEM development. Its
unconditioned four-buffer probability is below `2^-356`. Conditioning the
whole f/g buffers costs at most `1/(p_f*p_g) <= 64/25`, yielding the
`2^-354` accepted-key bound. The proof uses a union bound across coefficient
failures; it assumes no independence between those failure events.

## Separate cached-ROM key generation experiment

`PKEAverageROM.run()` initializes E and F to empty, uses the actual
unrestricted KeyGen with cached ROM expansion, and then runs the same PKE
trial with independent CBD1 message and randomness. The separate endpoint
`pke_rom_average_total` in
[`NTRUPlus768PKEAverageROM.ec`](../ntruplus/proof/768/ref/pke_average_correctness/NTRUPlus768PKEAverageROM.ec)
states

```text
Pr[PKEAverageROM.run(): returned failure]
  + (1 - Pr[PKEAverageROM.run(): returns]) < 2^-238.
```

The proof transfers the stateless no-wrap observation and return mass.
It adds the earlier KeyGen comparison error below `2^-239` once to the
accepted-key no-wrap bound. It does not assume unrestricted cached-ROM
KeyGen is lossless. This experiment has no adversarial oracle or
decapsulation continuation. Its message and randomness are independent
CBD1 samples; the earlier honest KEM experiment instead retains actual
Encaps and CompleteDecaps and has its own `2^-238` theorem.

## Reproduction and remaining scope

Run from the repository root:

```sh
./scripts/verify-ntruplus768-pke-average.sh \
  --prior-evidence-root /path/to/thesis \
  --output /path/to/new-evidence-directory
```

The output directory must be new or empty and outside the checkout.
Sources are in
[`ntruplus/proof/768/ref/pke_average_correctness/`](../ntruplus/proof/768/ref/pke_average_correctness/),
with controls in
[`tests/ntruplus768/pke_average_correctness/`](../tests/ntruplus768/pke_average_correctness/).
The runner uses September 2026 EasyCrypt/Why3, Z3, `-no-eco`, `Proofs:check`,
one prover and `OCAMLRUNPARAM=o=20`. Use its completed `summary.json`, logs
and matching source hashes to determine the full replay result and counts.
Individual main checks or `--check-only` do not establish a full-suite PASS.

The subsequent [RR/SOTP/G development](ntruplus768-acwc2-contracts.md)
supplies a public checked randomness-recovery helper, the three SOTP
properties and the exact serialized G-query interface. Honest RR recovery
covers all ternary message/randomness pairs for valid generated keys
without a no-wrap premise. Arbitrary-ciphertext success is checked by one
actual PKE reencryption. The later
[linear-RRec continuation](ntruplus768-linear-rrec.md) proves that removing
that call preserves the public helper's option result for every input,
with the encoding and ternary-domain guards retained.

The result on this page remains an average failure bound for the stated
PKE Gen, message and randomness experiment. The subsequent
[ACWC2 correctness development](ntruplus768-acwc2-correctness.md) proves
the expected worst-message bound below `2^-353` in its fresh-key, finite-G
experiment. The [linear-RRec development](ntruplus768-linear-rrec.md)
supplies total terminal representability and inverse-to-forward
congruence, and transfers the same ACWC2 bound to the actual caller with
its redundant RRec check removed. Its separate CompleteDecaps comparison
uses the same decoded m1 and preserves result, clearing and the separated
G/H states. The [Gen-law continuation](ntruplus768-keygen-gen-law.md) supplies
the acceptance/unit equivalence and exact fresh/programmed Figure 18
`(h,f)` law while retaining E/key correlation and F-cache behavior. Public-key-dependent FO, IND-CCA and
hardness reductions remain separate obligations.
The [CCA game/API layer](ntruplus768-kem-indcca-game.md)
retains its own adversarial-query and partial-probability scope.

No C/Jasmin implementation, native API or extraction is changed by this
development. Native SHAKE/RNG, concrete SHAKE-to-ROM correspondence, C
memory/ABI, binary execution and full-API leakage retain their existing
boundaries. No new native, Safety, CT or SCT replay is claimed.
