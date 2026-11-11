# NTRU+768 Decaps ternary-polynomial computation

`ntruplus/jasmin/768/ref/decap_candidate.jazz` implements the first three
normal-path calls in official `3991b2ae08d6f0008d37e41b8aceaaab27b4ec89`
Decaps: polynomial multiplication, inverse NTT, and centered reduction
modulo three. It produces the intermediate polynomial `m1`; SOTP decoding
and the remaining rejection checks follow later.

## Contract and source correspondence

The native entry is
`jade_ntruplus_ntruplus768_amd64_ref_decap_candidate(rp, cp, fp)`.
The three regions are disjoint, u16-aligned, and each contains 1536 bytes.
`cp` and `fp` are initialized readable inputs; `rp` is writable and requires
no initial contents. The procedure uses two internal 1536-byte stack arrays,
initialized by a fixed-index loop before their pointer views are formed.
It preserves both external inputs and fills all 768 output coefficients.

The extracted-procedure contract identifies the result with the composition
of the existing exact word specifications and proves termination, including
the scratch-initialization loop with integer variant `768-i`. The
arithmetic interpretation additionally uses canonical input coefficients
in `[0,3457)`. The product range establishes the inverse-NTT precondition;
its output range establishes the centered-reduction precondition. Each
result is the 16-bit encoding of `-1`, `0`, or `1`, congruent modulo three
to the centered representative modulo 3457 of the inverse result.

Guard acceptance supplies canonical decoded ciphertext and first-key-block
inputs. It does not imply the algebraic key relation or the no-wrap condition
needed to identify this intermediate polynomial with the encapsulated one.
The guard/candidate EasyCrypt caller is a composition of extracted procedures;
it is not an extraction of the full native Decaps API.

The unchanged arithmetic kernels remain separately pinned to the earlier
baseline. For this slice, official `basemul` changes intermediate variable
storage, the inverse transform removes the initial out-of-place copy, and
`poly_crepmod3` adopts an in-place interface. The relevant arithmetic formulas
and constants are preserved. The new composition uses separate scratch arrays,
so its memory access trace differs from official C. The upstream change to
forward-NTT reduction placement is outside these three calls.

## Execution and information flow

The candidate's input and output values are secret, with no declassification.
Safety and CT/SCT checks concern the Jasmin candidate under its native
memory contract and the checkers' observation models. They do not prove
the information flow of the remaining C caller. When used with the existing
Jasmin guard, that guard's two key-encoding disclosures and their canonical-key
interpretation still apply; the candidate adds no further disclosures.

The default safety checker initializes exported array arguments in its
analysis state, including the mutable destination. Its result alone therefore
does not establish that incoming destination contents are unnecessary.
That property follows separately from inspecting the candidate's write-only
destination path; the exact functional contract also shows independence
from arbitrary initial destination values. The internal scratch arrays are
explicitly initialized and are checked inside the analyzed body.

The scratch arrays are not explicitly erased. Existing C cleanup is retained
in integration tests, but this is not an erasure guarantee for the candidate's
internal stack storage. Whole-API cleanup remains a separate obligation.

## Reproduction and scope

Run with the selected 2026.09 Jasmin/EasyCrypt/Why3 tools:

```sh
./scripts/verify-ntruplus768-decap-candidate.sh
```

The replay checks source and reference identities, fresh extraction,
completed EasyCrypt contracts, Jasmin safety and CT/SCT, and native
normal/UBSan comparisons. It reuses the immutable official C and KAT fixtures
under `tests/ntruplus768/decap_guard/reference/`; no new upstream snapshot
is substituted for the older arithmetic baseline.

Native integration compares official C with two mixed implementations:
the C guard followed by the Jasmin candidate, and the existing Jasmin guard
followed by the Jasmin candidate. Only the corresponding pinned blocks are
replaced; the later arithmetic, hashes, rejection, shared-secret selection,
and cleanup remain C. Rejected encodings must never invoke the candidate.
C correspondence is supported by source comparison and execution tests,
not a C-AST equivalence theorem. This result does not complete message
recovery, full Decaps correctness, the KEM failure bound, or IND-CCA security.
