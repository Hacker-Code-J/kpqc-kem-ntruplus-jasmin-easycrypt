# NTRU+768 executable Decaps r2 computation

`ntruplus/jasmin/768/ref/decap_r2.jazz` computes
`BaseMul(c - NTT(m1), hinv)`, the polynomial used to derive the SOTP pad.
It composes the existing NTT, subtraction and multiplication kernels.
The guard supplies decoded inputs, and the preceding actual candidate
procedure supplies the ternary `m1`. Original encapsulation-randomness
recovery additionally requires key and message-recovery relations.

## Exact computation and caller conditions

The native export is
`jade_ntruplus_ntruplus768_amd64_ref_decap_r2(rp, cp, mp, hp)`.
The four regions are disjoint, two-byte-aligned, 1536-byte arrays. `cp` and
`hp` have canonical coefficients in `[0,3457)`; `mp` has signed coefficients
in `{-1,0,1}`. The source preserves these three inputs and writes all output
coefficients. Two internal arrays are initialized with fixed indices before
their pointer views are passed to the kernels.

The extracted-program proof identifies the exact word-array output and
proves termination. The algebraic bridge uses the centered NTT output,
signed subtraction without wraparound, and the existing asymmetric
multiplication contract. The resulting polynomial is in `[-3457,3457)`.
The subtraction need not itself be in this interval; its wider range is
handled by that multiplication contract.

An EasyCrypt caller composes the actual guard, candidate and r2 procedures.
Guard acceptance and the proved ternary candidate establish the arithmetic
premises internally. Rejection preserves unvisited arithmetic destinations
and clears the shared secret. Acceptance preserves the shared-secret buffer
at this intermediate boundary; status zero here is not the final Decaps
success decision. The caller is not an extraction of the whole native API.

## Why the existing NTT can be reused here

Official `3991b2ae08d6f0008d37e41b8aceaaab27b4ec89` moves Barrett reductions
from individual radix-2 butterflies to one final sweep. The existing kernel
retains its proved schedule. A strict source comparison identifies identical
indexed butterflies, twiddles and reducers after exactly those changes.

An executable integer interval certificate starts with every input
coefficient in `[-1,1]`. It bounds the official final unreduced coefficients
by `[-14821,14821]`; butterfly argument/store narrowings fit int16, and
intermediate integer arithmetic fits int32. The intentional Montgomery
low-word truncations are modeled separately. Exhaustive checking of the
scalar Barrett formula establishes centered output throughout
`[-22470,22470]`, including every certified final coefficient. Barrett does
not have this stronger property for every int16 input.

Barrett subtracts a multiple of q, and Montgomery multiplication preserves
the prescribed field product. The two indexed schedules therefore agree
modulo q; both final representatives lie in `[-1728,1728]`, so they are equal
as signed words for these trit inputs. This is a source-audited arithmetic
argument with an executable bound certificate. EasyCrypt verifies the actual
Jasmin composition and its own specification; no C-AST equivalence theorem
or equality of the two implementations' internal traces is claimed. This
restricted correspondence does not migrate every other NTT caller.

## Safety and native correspondence

The candidate and r2 procedures disclose no predicates. The existing guard
retains its two key-encoding disclosures and stated canonical-key policy.
The new safety and CT/SCT checks concern the r2 procedure under their models,
not the information flow of the remaining C API. In particular, the default
safety checker initializes exported array arguments. The source's absence
of incoming output reads and the functional result's independence from
initial output values are separate facts.

Native comparisons use immutable official C/KAT fixtures. They compare the
official implementation, a replacement of only the r2 block, and the combined
guard/candidate/r2 replacement. Only the selected blocks change. The source
preserves `cp` and `mp`; the original C's dead `c`/`m2` contents are irrelevant
to later computations and are still cleared by its cleanup. Internal Jasmin
scratch erasure is not proved. Later rejection and shared-secret selection
remain in C, including tested accepted encodings that subsequently fail.

## Reproduction

```sh
./scripts/verify-ntruplus768-decap-r2-comp.sh
```

The default entry checks source/reference identities, exact fresh extraction,
completed EasyCrypt proofs, the arithmetic certificate, native ordinary/UBSan
comparisons, safety and CT/SCT. `--defer-safety` explicitly reports a partial
result; any separately run safety result must be bound to the identical
source dependencies, checker and command before combining the evidence.
This unit does not complete Decaps, unconditional message/randomness recovery,
whole-API cleanup, KEM correctness or classical-ROM IND-CCA.
