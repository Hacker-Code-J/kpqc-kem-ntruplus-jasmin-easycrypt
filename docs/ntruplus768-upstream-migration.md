# NTRU+768 upstream compatibility and paper-target decision

Audit date: 2026-08-26

## Decision

The functional-correctness paper remains pinned to the already verified
NTRU+768 reference baseline:

```text
38201624477a7dbb2f46d1ae7686ae5ceee4eb80
```

The local tree differs from that upstream commit by one tracked,
documentation-only patch:

```text
patches/ntruplus768-3820162-comment-fix.patch
```

It corrects the `baseinv` `fqinv(t3)` Montgomery annotation from `R^5` to
`R^3`; it does not change executable C.  The current official migration target
is pinned separately as:

```text
3991b2ae08d6f0008d37e41b8aceaaab27b4ec89
```

That commit was both `HEAD` and `refs/heads/main` of the official NTRU+
repository at audit time.  It is not imported into this repository and is not
covered by the current Jasmin/EasyCrypt claims.  The paper and artifact must
name the verified baseline commit explicitly and must not describe it as the
current upstream implementation.

This freeze keeps the high-level ring-semantics and valid-ciphertext recovery
work on the critical paper path.  Migration to the hardened target proceeds on
a separate track and must complete the exit criteria below before the source
pin changes.

## Reproduction

Run the immutable source/KAT audit:

```sh
./scripts/audit-ntruplus768-upstream.sh
```

It verifies all of the following:

- the local reference tree equals upstream `3820162` plus the tracked
  comment-only patch;
- the local KAT tree byte-matches upstream `3820162`;
- exactly 15 NTRU+768 reference files changed between the two commits;
- the NTRU+768 KAT tree did not change;
- candidate `3991b2a` builds, reports zero functional-test failures, and
  regenerates the committed response file byte-for-byte;
- the candidate contains the expected canonical-decoding, invalid-input,
  in-place-ABI, reduction-placement, `fqinv`, declassification, and clearing
  changes.

Run the bounded fail-closed checker impact audit:

```sh
./scripts/audit-ntruplus768-checker-impact.sh
```

This checks only the `check` and `selfcheck` targets.  It deliberately avoids
EasyCrypt compilation, Jasmin safety/CT analysis, differential execution, and
UBSan.

## Measured results

The candidate preserves the KAT response SHA-256:

```text
22c72039845361ff142273150a59785bada5146c04018ce0a8b67b99a647eaa8
```

The source delta is 15 files, 319 insertions, and 611 deletions under
`Reference_Implementation/NTRU+768`.  No file under `KAT/NTRU+768` changes.

The bounded checker matrix counts individual targets, not directories:

The repository-side checker tree is frozen at verified commit
`d2cb239d262fb4f656992d6bd7e6220dc82748b4` so the audit remains reproducible
after later migration work changes the main branch.

| Source tree | PASS | FAIL | SKIP |
| --- | ---: | ---: | ---: |
| Verified baseline | 88 | 0 | 4 |
| Candidate `3991b2a` | 6 | 82 | 4 |

The four skipped targets are `check` and `selfcheck` in `basemul` and
`poly_basemul`, whose Makefiles expose neither target.  Only these candidate
directories pass both targets:

- `tests/ntruplus768/decap_verify`
- `tests/ntruplus768/invntt_final`
- `tests/ntruplus768/ntt_schedule`

The 82 failures are expected fail-closed detections.  They demonstrate that a
pin-only update would be unsound; they do not imply that the candidate C code
is functionally incorrect.

## Compatibility classification

| Candidate change | Class | Current impact | Reuse assessment |
| --- | --- | --- | --- |
| `poly_frombytes` returns failure for coefficients `>= q` | Semantic + ABI | Decoder signature/body and every unconditional caller seam fail | Pure decode arithmetic and canonical round-trip lemmas remain useful; return-value and reject-path proofs are new |
| Encapsulation rejects invalid `pk` and zeros `ct`/`ss` | Semantic control flow | Existing encap proofs cover only the valid branch | Valid-branch ring algebra is reusable; invalid-key return/zeroization needs a new theorem and tests |
| Decapsulation rejects invalid `ct`, `f`, or `hinv` before arithmetic | Semantic control flow | Existing decap chain assumes all three decoders continue | Established valid-branch seams are reusable behind a validity premise; early failure/cleanup must be composed separately |
| NTT, InvNTT, triple, and `crepmod3` become in-place APIs | ABI + trace | Exact signatures, wrapper forwarding, and caller-order checks fail | Alias-value algebra is largely reusable; extracted procedures and caller checkers need rebinding |
| Forward NTT defers Barrett reduction to one final sweep | Word trace/range | Current staged word proofs and source checker pin per-layer reduction | Root schedule and abstract transform goal remain reusable; word bounds and stage composition require new proofs |
| Inverse NTT removes the initial two-buffer copy | ABI + wrapper trace | Whole-wrapper checker/proof no longer matches | In-place stage algebra and final layer remain useful; wrapper theorem must be replaced |
| `fqinv` uses a different 15-step addition chain | Exact arithmetic trace | C/Jasmin exact-chain checkers fail | Prime-field inverse theorem is reusable; exact word trace and C/Jasmin coupling require refresh or chain equivalence |
| `basemul` and `basemul_add` use local temporaries | Source shape | Exact-body checkers fail | Four-lane quotient-ring formulas are unchanged and should be reused |
| `secure_clear`, declassification, visibility macros, SHAKE workspace changes | Hardening + source shape | KEM/hash source checkers and cleanup order fail | Hash value specifications remain reusable; cleanup/declassification are separate implementation properties |

## Missing candidate coverage

The current suite has no dedicated regression for the newly introduced
malformed-input behavior.  Migration must add at least these behaviors before
repairing downstream success paths:

1. A public key containing a decoded coefficient `>= q` makes encapsulation
   return `1` and zero both ciphertext and shared secret.
2. A non-canonical ciphertext, serialized `f`, or serialized `hinv` makes
   decapsulation return failure and zero the shared secret.
3. Canonical encodings retain the existing valid-input values and KAT.
4. Cleanup does not alter returned public outputs, and retry-status
   declassification remains explicit.

## Proof reuse map

Likely reusable with small adapters:

- NTRU+ root order, factor schedule, and terminal-root lemmas;
- four-coefficient quotient-ring multiplication and inverse identities;
- canonical serialization/round-trip mathematics for valid inputs;
- SOTP encode/decode value algebra;
- `hash_f`, `hash_g`, and `hash_h` domain-separated value specifications;
- valid-branch terminal failure/mask Boolean algebra.

Requires procedure- or trace-level repair:

- `fqinv`, `baseinv`, and `poly_baseinv` exact C/Jasmin trace coupling;
- forward NTT stages and whole-wrapper bounds after reduction relocation;
- inverse NTT whole-wrapper composition after copy removal;
- every caller checker that pins two-buffer transform/triple/`crepmod3` APIs;
- `poly_frombytes` status and all new malformed-input branches;
- KEM cleanup/declassification/source-order checks.

## Migration order

1. Prove and test the fallible canonical decoder, including malformed public
   key and ciphertext behavior.
2. Rebind one-buffer APIs and prove equivalence to the existing valid-input
   array specifications.
3. Refresh the forward/inverse NTT word-level traces while reusing the root
   schedule and high-level ring target.
4. Refresh `fqinv` and helper-body C/Jasmin coupling; reuse the field and
   quotient-ring algebra.
5. Add hardening/cleanup/declassification source and runtime checks.
6. Run the complete EasyCrypt, Jasmin safety/CT, differential, UBSan, and KAT
   chains before changing `THIRD_PARTY.md`'s imported source commit.

## Pin-change exit criteria

Do not replace the verified baseline until all conditions hold:

- candidate reference and KAT trees are imported with exact provenance;
- all 88 bounded checker targets pass against the candidate;
- new malformed-input and zeroization tests pass under normal and UBSan builds;
- every affected tracked Jasmin extraction is refreshed and reviewed;
- strict EasyCrypt proof chains pass without holes or stale assumptions;
- the paper's theorem statements distinguish valid-input correctness from
  malformed-input rejection and name the exact target commit.
