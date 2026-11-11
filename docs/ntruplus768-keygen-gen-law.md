# Actual KeyGen acceptance and the Figure 18 Gen law for NTRU+768

**Full replay PASS**, 2026-10-15: all 8 new mains (94 lemmas),
8 semantic end-of-file probes and 8 isolated unfinished-proof rejections.
The runner passed 53 structural/trust controls
and 32 exact finite diagnostics.
It verified 833 source pins and before/after hashes for
846 runtime inputs and
299 external tool/configuration/theory/driver,
prior-evidence and specification inputs. The
644 imported EC files remain hash-linked
prior evidence, not new main replays. The companion record is
`handoff/verification/ntruplus-keygen-gen-law-20261014/final-replay/summary.json`,
with 23 command logs and 16 checked proof copies.
The evidence directory retains the milestone's 2026-10-14 start date.

This proof-only continuation connects the implementation's inversion test
to invertibility in `Rq = F_3457[X]/(X^768-X^384+1)`, then identifies the
polynomial `(h,f)` projection of its returned byte keys with Figure 18's Gen
law under independent fresh expansion. The programmed-expansion version
keeps the same marginal while recording proposal buffers in E. The cached-ROM
version has a separate approximate marginal law; it is not an exact fresh
sampling law.

## Official target and the observed key

The companion evidence record
`handoff/verification/ntruplus-keygen-gen-law-20261014/specification-contract.json`
pins the official specification text by SHA256, Figure 18 lines 1509–1519
and Algorithm 11 lines 2184–2204. The directory keeps the milestone's start
date. Figure 18 samples f0 from the CBD1 polynomial law until `f=1+3*f0`
is a unit in Rq, independently samples g0 from that law until g0 is a unit,
and returns `(h,f)` with `h=3*g0/f` in Rq. CBD1 coefficients have masses
`1/4, 1/2, 1/4` at `-1, 0, 1`; this is not uniform sampling of trits.

Algorithm 11 shapes its second polynomial as `g_actual=3*g0`, tests that
polynomial for invertibility, and serializes terminal NTT representations:

```text
pk = Encodeq(NTT(h))
sk = Encodeq(NTT(f)) || Encodeq(NTT(h^-1)) || F(pk).
```

Its 1152-byte public key and 2336-byte secret key therefore have different
types and contents from Figure 18's two polynomials. The observation
`gen_serialized_core(pk,sk)` decodes the public bytes and the secret key's
first 1152 bytes, applies the existing inverse-transform specification, and
returns their coefficient polynomials `(h,f)`. It reads the returned byte
arrays; private sampler buffers are used only to prove the bridge.
The inverse-h block and F suffix remain in the actual procedure and are
excluded from this observation.

## From the actual status to a ring unit

[`NTRUPlus768KeygenTerminalUnit.ec`](../ntruplus/proof/768/ref/keygen_gen_law/NTRUPlus768KeygenTerminalUnit.ec)
defines `gen_terminal_unit a` by existence of a word-array inverse whose
192 terminal block products are the identity. Under the existing q-range
precondition, `gen_inverse_status_iff` connects this predicate in both
directions to `keygen_inverse_status a = W64.zero`.
`gen_inverse_core_correct` combines the actual PolyBaseInv core's exact
result and losslessness with that equivalence, successful inverse products
and complete-output zeroization on rejection. Scalar BaseInv alone retains
its output buffer on failure; the zeroization contract belongs to the
complete PolyBaseInv core.

The theorem `gen_terminal_unit_iff_rq` in
[`NTRUPlus768KeygenGlobalUnit.ec`](../ntruplus/proof/768/ref/keygen_gen_law/NTRUPlus768KeygenGlobalUnit.ec)
adds `terminal_represents a p` and identifies the terminal predicate with
`pke_rq_unit p`. The reverse implication uses the finite set of canonical
terminal arrays: multiplication by a unit is an injective endomap, hence
surjective, so the identity has a preimage. Finiteness is symbolic; the proof
does not enumerate `3457^768` arrays or assume a CRT isomorphism.

[`NTRUPlus768GenAcceptance.ec`](../ntruplus/proof/768/ref/keygen_gen_law/NTRUPlus768GenAcceptance.ec)
proves the equivalence for the exact f/g rejection predicates. Since 3 is a nonzero field
element, `unit(3*g0)` and `unit(g0)` are equivalent. This connects the two
notations in the official algorithms without changing the sampled g0 law.

## A public-key definition independent of the implementation

[`NTRUPlus768GenModel.ec`](../ntruplus/proof/768/ref/keygen_gen_law/NTRUPlus768GenModel.ec)
defines `gen_public_relation f g h` by the quotient equation `h*f = 3*g`
and a canonical representative bound. Its `NTRUPoly.deg h <= 768` uses the
library's coefficient-list-size convention and means ordinary mathematical
degree less than 768. `gen_public_key` chooses this representative; its
definition contains no NTT or implementation-derived h.

Uniqueness follows from cancellation by the unit f. Existence is required
and established on the supported generated-key law, so the explicit zero
default of the choice operator is unused there. The projection theorems
in [`NTRUPlus768GenKeyProjection.ec`](../ntruplus/proof/768/ref/keygen_gen_law/NTRUPlus768GenKeyProjection.ec)
connect the actual decoded public polynomial and secret f to that independent
relation.

## Exact Figure 18 execution and returned-key laws

[`NTRUPlus768GenDistribution.ec`](../ntruplus/proof/768/ref/keygen_gen_law/NTRUPlus768GenDistribution.ec)
defines `gen_key_law` from independent whole-polynomial conditionals:

```text
f0 ~ dcond pke_field_psi1 (fun p => unit(1+3*p))
g0 ~ dcond pke_field_psi1 unit
f  = 1+3*f0
return (h,f), where h*f = 3*g0 in Rq and degree(h) < 768.
```

The existing positive acceptance masses normalize both conditionals. The
accepted f0 and g0 are independent of each other; acceptance can introduce
dependence between coefficients within either polynomial.

[`NTRUPlus768GenProcedures.ec`](../ntruplus/proof/768/ref/keygen_gen_law/NTRUPlus768GenProcedures.ec)
defines `Figure18Gen.run()` with the two polynomial rejection loops and
`gen_key_from_fg`. `figure18_gen_probability` proves its exact `gen_key_law`
distribution, and `figure18_gen_lossless` proves termination with probability
one. The public identities below compare this procedure directly with the
projection of actual byte-returning `Keygen.run()`; they do not compare the
byte key pair to a pair of polynomials without a projection.

| Endpoint | Proved observation and law |
|---|---|
| `figure18_fresh_public_probability` | Every `gen_serialized_core` event of actual fresh Keygen has the same probability as that event of `Figure18Gen.run()`. |
| `figure18_programmed_public_probability` | The same direct probability identity for actual programmed Keygen. |
| `gen_fresh_public_key_law` | Actual `Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run()` returned bytes, projected by `gen_serialized_core`, have law `gen_key_law`. |
| `gen_programmed_public_key_law` | The same exact marginal for `ProgrammedFreshExpand`, which records fresh samples in E. |
| `gen_programmed_public_projection` | Fresh/programmed returned byte keys and final F tables agree under equal initial F state. |
| `gen_rom_public_key_law_239` | With initially empty E, every projected-key event of actual cached-ROM KeyGen differs from `gen_key_law` by less than `2^-239`. |

The final row is in
[`NTRUPlus768GenROMBridge.ec`](../ntruplus/proof/768/ref/keygen_gen_law/NTRUPlus768GenROMBridge.ec).
`gen_rom_public_key_law_256` gives the intermediate bound `130818/2^256`,
using analysis retry budgets of 256 for each phase. It compares returned-event probabilities without
conditioning on termination and without assuming actual ROM KeyGen is
lossless. Initial F may be arbitrary; the actual Finish call and its cache
updates are retained.

The exact programmed law is a marginal statement. The generated key remains
correlated with the final E table. Neither that table nor F is reset to
obtain these key laws. The earlier [CCA setup comparison](ntruplus768-cca-setup.md)
preserves the joint key/E/F observation for adaptive continuation; this
marginal identification does not erase E or replace it with an independent
oracle. Such a reduction still needs its own hit-event and query-budget
argument, including rejected proposal inputs. The subsequent
[E-erasure continuation](ntruplus768-e-erasure.md) supplies that analysis
under explicit robust adversary losslessness and an effective-query budget.
A universal initial-state count contract removes both caps in the final
original-game comparison.
It uses all attempted seeds, including duplicates, and preserves F-cache
behavior. This Gen marginal theorem itself is unchanged.

## Reproduction and remaining scope

The runner interface is available from the repository root:

```sh
./scripts/verify-ntruplus768-keygen-gen-law.sh \
  --prior-evidence-root /path/to/thesis \
  --output /path/to/new-evidence-directory
```

Use a new or empty output directory outside the checkout. Sources are in
[`ntruplus/proof/768/ref/keygen_gen_law/`](../ntruplus/proof/768/ref/keygen_gen_law/)
and controls in
[`tests/ntruplus768/keygen_gen_law/`](../tests/ntruplus768/keygen_gen_law/).
The completed `summary.json`, logs and matching source hashes determine
the full replay result recorded at the top of this page. `--check-only` checks sources and controls
and is not a proof replay. The declared proof configuration uses September
2026 EasyCrypt/Why3, Z3, `-no-eco`, `Proofs:check`, one prover and GC `o=20`.

This continuation discharges the acceptance/Gen identification left open by
[the PKE average development](ntruplus768-pke-average.md). It does not change
that experiment's `2^-354` failure bound, the separate honest-KEM `2^-238`
bound, or the fresh-key finite-G ACWC2 `2^-353` bound. Public-key-dependent
FO correctness loss, hardness reductions, complete IND-CCA security and
QROM remain separate. No C/Jasmin source, extraction, native API, Safety,
CT or SCT result is changed or newly replayed here.
