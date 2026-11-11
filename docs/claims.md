# Research claims and proof entry points

This index connects representative research claims to exact source declarations
and their verification entry points. It is not a record of a fresh proof run,
an exhaustive theorem inventory, or a substitute for the premises in each
declaration. A thesis citation should identify the release commit, the relevant
declaration, and the corresponding replay evidence. Thesis chapter and theorem
numbers are deliberately not assigned here.

## Source targets

- **Baseline:** NTRU+ commit `38201624477a7dbb2f46d1ae7686ae5ceee4eb80`,
  represented by `NTRU+/NTRU+768` and its KAT. The retained patch is comment-only.
  The original arithmetic implementation and its old-array semantics belong to
  this line of work.
- **Official target:** NTRU+ commit `3991b2ae08d6f0008d37e41b8aceaaab27b4ec89`.
  Checked decoding and complete caller developments target this revision while
  reusing arithmetic results with separately stated correspondence checks.
  Equal KATs alone do not establish equal malformed-input behavior or a formal
  C-to-Jasmin refinement.
- **Classical-ROM model:** the explicit EasyCrypt games built over the
  official-target array callers, with their stated sampling and oracle
  idealizations. A theorem about this model is not a theorem that native SHAKE
  implements a random oracle.

See the [migration record](ntruplus768-upstream-migration.md) and
[third-party provenance](../THIRD_PARTY.md) for the imported sources and reuse
boundaries.

## Claim-to-proof map

Run the commands below from the repository root in the configured toolchain.
Commands are verification entry points, not promises that a source checkout
alone contains all required tools and prior evidence.

| Claim and target | Exact declaration and source | Verification command | Essential conditions and limits |
| --- | --- | --- | --- |
| NTT/InvNTT cancellation, baseline arithmetic | `ntt_invntt_spec_roundtrip` in [NTRUPlus768NTTRoundtripSemantics.ec](../ntruplus/proof/768/ref/ring_semantics/NTRUPlus768NTTRoundtripSemantics.ec) | `./scripts/verify-ntruplus768-ntt-invntt-roundtrip-semantics.sh` | Input coefficient range; equality is polynomial congruence modulo `X^768-X^384+1` over the specified field. This is old-array semantics, without shared-memory aliasing or native C equivalence. |
| NTT/Basemul/InvNTT polynomial multiplication, baseline arithmetic | `ntt_basemul_invntt_spec_product` in [NTRUPlus768NTTBasemulInvNTTSemantics.ec](../ntruplus/proof/768/ref/ring_semantics/NTRUPlus768NTTBasemulInvNTTSemantics.ec) | `./scripts/verify-ntruplus768-ntt-basemul-invntt-semantics.sh` | Both inputs satisfy `input_qrange`; `product_ntt` satisfies the existing `is_poly_basemul` relation for 192 blocks. Spec-level composition; no newly exported combined native procedure. |
| Complete KeyGen valid-key output and termination, official target | `keygen_public_correct` in [NTRUPlus768KeygenCompleteProof.ec](../ntruplus/proof/768/ref/keygen_complete/NTRUPlus768KeygenCompleteProof.ec); explicit iid instance `keygen_iid_public_correct` in [NTRUPlus768KeygenIIDProof.ec](../ntruplus/proof/768/ref/keygen_retry/NTRUPlus768KeygenIIDProof.ec) | `./scripts/verify-ntruplus768-keygen-complete.sh` | Generic correctness retains its termination premises. The iid instance requires a lossless seed law, fixed functional expansion, positive f/g acceptance masses, and the declared hash contracts/state separation. Positivity for a chosen fixed SHAKE expansion is not inferred from RNG losslessness. |
| Complete deterministic Encaps result and designated workspace clearing, official target | `encap_derand_correct` in [NTRUPlus768EncapCompleteProof.ec](../ntruplus/proof/768/ref/encap_complete/NTRUPlus768EncapCompleteProof.ec); randomized distribution endpoint `encap_distribution_correct` in [NTRUPlus768EncapCompleteRNG.ec](../ntruplus/proof/768/ref/encap_complete/NTRUPlus768EncapCompleteRNG.ec) | `./scripts/verify-ntruplus768-encap-complete.sh` | Functional/lossless hash contracts and the exact RNG premises of the selected endpoint. Returned ciphertext, key, status and clearing are array-program contracts; they do not establish native RNG quality or register/spill erasure. |
| Complete Decaps result, status and designated workspace clearing, official target | `complete_correct` and mathematical-hash instance `complete_math_correct` in [NTRUPlus768DecapCompleteProof.ec](../ntruplus/proof/768/ref/decap_complete/NTRUPlus768DecapCompleteProof.ec) | `./scripts/verify-ntruplus768-decap-complete.sh` | Fixed-size input arrays and functional/lossless hash contracts; result equals `complete_spec`, including rejection. No native C orchestration, memory/ABI or native SHAKE refinement follows. |
| Generated-key conditional KEM agreement, official target | `keygen_iid_kem_correct` in [NTRUPlus768KeygenIIDAgreement.ec](../ntruplus/proof/768/ref/keygen_retry/NTRUPlus768KeygenIIDAgreement.ec) | `./scripts/verify-ntruplus768-keygen-complete.sh` | Key validity comes from actual KeyGen operations under the iid/positivity/hash premises. Shared-key agreement remains conditional on `keygen_coins_no_wrap`. This endpoint is neither an unconditional failure bound nor an IND-CCA theorem. |
| Uniform short-relation probability below `2^-244`, statistical ring model | `sr_uniform_bad_mass_244` in [NTRUPlus768SRBound.ec](../ntruplus/proof/768/ref/kem_short_relation_bound/NTRUPlus768SRBound.ec) | `./scripts/verify-ntruplus768-short-relation-bound.sh --prior-evidence-root "$EVIDENCE_ROOT"` | Uniform sampling over the entire `F_3457[X]/(X^768-X^384+1)` ring, including zero/nonunits; the specified nonzero short-pair event. This statistical bound needs no short-relation hardness assumption. The harness includes native Coq checks for the algebraic helpers. |
| Original classical-ROM IND-CCA reduction with numerical short-relation term | `sr_original_numerical` in [NTRUPlus768SRFinal.ec](../ntruplus/proof/768/ref/kem_short_relation_bound/NTRUPlus768SRFinal.ec) | `./scripts/verify-ntruplus768-short-relation-bound.sh --prior-evidence-root "$EVIDENCE_ROOT"` | Reduction to the specified conditioned-NTRU and computational-RLWE experiments, retaining signed gaps, the acceptance denominator, private-state exclusions, robust adversary termination, initial states and backend-specific query contracts. It does not prove those hardness problems hard. |
| Adaptive persistent-list implementation of the reduction | `ah_original_adaptive_history` in [NTRUPlus768AHFinal.ec](../ntruplus/proof/768/ref/kem_adaptive_history/NTRUPlus768AHFinal.ec) | `./scripts/verify-ntruplus768-adaptive-history.sh --prior-evidence-root "$EVIDENCE_ROOT"` | Concrete witnesses are fixed before memories and budgets; the actual G transcript is used. Retains the security contracts and adds `2*qC/2^353` outside the acceptance denominator. See [adaptive history](ntruplus768-adaptive-history.md). |
| Same word-array reduction witnesses satisfy security and closed fixed-768 cost bounds | `rt_original_runtime_bound` in [NTRUPlus768RTFinal.ec](../ntruplus/proof/768/ref/kem_runtime_bound/NTRUPlus768RTFinal.ec); exact coefficients in `rt_complete_bound_values` in [NTRUPlus768RTCompleteCost.ec](../ntruplus/proof/768/ref/kem_runtime_bound/NTRUPlus768RTCompleteCost.ec) | `./scripts/verify-ntruplus768-runtime-bound.sh --prior-evidence-root "$EVIDENCE_ROOT"` | Ideal ROM and unit-cost integer/word model; source calibration and pricing frontend are part of the cost interpretation's trust boundary. `t_A` separately bounds adversary self-work. This is not CPU time, bit complexity or a general parameter-family PPT theorem. |

The semantic arithmetic commands do not replace the independent implementation
checks: `./scripts/verify-ntruplus768-ntt.sh`,
`./scripts/verify-ntruplus768-poly-basemul.sh`, and
`./scripts/verify-ntruplus768-invntt.sh`. Likewise, runtime differential tests,
KAT equality, compilation, safety, CT/SCT and functional proofs are distinct
evidence categories. Do not promote a result in one category into another.

## Reading the final security and cost statements

The adaptive and runtime endpoints retain the following form, with the same
three concrete witnesses in the runtime security and cost clauses:

```text
Adv_CCA(A) <=
  2*(DeltaNTRU(DI) + DeltaNTRU(DO) + epsRLWE(CO) + 2^-244)/alpha_g
  + (130820 + 512*qE)/2^256
  + (q0 + qH + d + 2*qC)/2^353 + (qC + d)/2^768,
d = max(0, budget).

Cost_R(t_A) <= t_A + 10909917*Q^2 + 32450882*Q + 64*B + C_R,
C_DI = 17679874, C_DO = 10492283, C_CO = 18463740.
```

`DeltaNTRU` denotes the signed real-minus-uniform probability gap in the
specified conditioned experiment. `alpha_g` is the accepted-key factor.
The security budgets have backend-specific contracts in the declarations;
in particular, `qC` counts distinct H entries. The resource variable `Q`
counts all public callbacks, including repeats and rejected/zero-output raw
requests, and `B` counts their total raw-input bytes. These budgets cannot be
substituted for one another. The source-calibrated cost includes fixed setup
and the run dispatcher, with the adversary's own instructions reserved by
`t_A`; it does not derive that reserve for an arbitrary adversary.

## Trust, evidence and publication status

The logical statements rely on the selected EasyCrypt/Jasmin models, their
imported libraries and proof toolchain. The short-relation family additionally
uses its native Coq/Why3 connection and kernel-check controls. The cost result
also requires the documented source-to-charge calibration; a proof of an
arithmetic inequality alone does not validate a cost assigned to source code.

The cited source files and declaration names were inspected when this index
was prepared. That inspection did not rerun the full proof dependency graph.
Historical PASS descriptions in family documents must be linked to their
original manifests and evidence, not relabelled as current executions.

For a publishable claim record, retain:

1. Release commit and recursive submodule commits, source manifest and tool
   versions/configuration.
2. Exact command and environment, exit status, raw logs and the generated
   `summary.json` where provided by the family runner.
3. Freshly checked main files, imported/prior-evidence dependencies and the
   source hashes tying them together.
4. Negative controls, semantic EOF/export checks and native/kernel checks
   required by that runner; source-check-only results stay labelled as such.

Set `EVIDENCE_ROOT` explicitly to the root containing the paths listed in each
family's `prior-evidence-pins.json`. Preserve the pinned bytes and relative
layout. A missing prior artifact is a reproducibility gap, not permission to
rewrite its hash or turn a source-only check into full PASS.

Native C/Jasmin or binary equivalence, full shared-memory/ABI correctness,
native SHAKE/RNG correspondence, full-API CT/SCT, complete machine-state
erasure, HAETAE UF-CMA and QROM are not established by the endpoints in this
index. The fixed-function correctness statements and classical-ROM security
statements have different premises; their distinction must survive the
thesis narrative and release description.
