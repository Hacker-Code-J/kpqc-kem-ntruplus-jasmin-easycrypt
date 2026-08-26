# Third-party materials

## NTRU+ reference implementation

- Paths: `NTRU+/LICENSE`, `NTRU+/NTRU+768`, and `NTRU+/KAT/NTRU+768`
- Source: <https://github.com/ntruplus/ntruplus.git>
- Source commit: `38201624477a7dbb2f46d1ae7686ae5ceee4eb80`
- Retrieved/verified: 2026-08-11
- Purpose: C behavior oracle and deterministic KAT baseline for the NTRU+768
  Jasmin and EasyCrypt work
- License: MIT; preserved in `NTRU+/LICENSE`

The imported NTRU+768 KAT directory and license byte-match the corresponding
upstream files at the source commit. The local `NTRU+/NTRU+768` path
corresponds to upstream `Reference_Implementation/NTRU+768` plus the tracked
`patches/ntruplus768-3820162-comment-fix.patch`. That patch changes only the
Montgomery-domain comment on `baseinv`'s `fqinv(t3)` result from `R^5` to
`R^3`; it does not alter executable C.

The NTT root-schedule proof also follows Section 6.2, Table 5, and Figure 22 of
the upstream
[`Supporting_Documentation/NTRU+.pdf`](https://github.com/ntruplus/ntruplus/blob/38201624477a7dbb2f46d1ae7686ae5ceee4eb80/Supporting_Documentation/NTRU%2B.pdf)
at the same pinned commit.
That document specifies `q = 3457`, the primitive 576th root `22`, the
radix-2/radix-3 factorization rules, and the 192 terminal exponents for
NTRU+768. The PDF is referenced as specification provenance and is not copied
into this repository; the concrete constants and closed EasyCrypt lemmas are
maintained locally.

### Audited migration target

The official upstream commit
`3991b2ae08d6f0008d37e41b8aceaaab27b4ec89` was audited on 2026-08-26 and was
the upstream `HEAD`/`main` at that time. It is an immutable migration target,
not the source currently imported or verified here. It preserves the
NTRU+768 KAT but changes 15 reference files, including canonical decoding and
malformed-input behavior, one-buffer transform APIs, reduction placement, the
`fqinv` trace, and secret-state cleanup.

The paper remains explicitly scoped to the verified source commit above while
the migration is pursued separately. Run
`scripts/audit-ntruplus768-upstream.sh` and
`scripts/audit-ntruplus768-checker-impact.sh` to reproduce the compatibility
evidence. See `docs/ntruplus768-upstream-migration.md` for the measured impact,
proof reuse map, and required conditions before changing the imported pin.

## Formosa ML-KEM

- Path: `external/formosa-mlkem`
- Source: <https://github.com/formosa-crypto/formosa-mlkem.git>
- Pinned commit: `475b87434506280fdfa1a1ba5da0af3787e00579`
- Retrieved: 2026-08-11
- Purpose: external reference for Jasmin implementation and EasyCrypt proof
  structure, plus imported generic signed-Montgomery and word-shift lemmas; not
  an NTRU+ verification result

This dependency is represented by a Git submodule, so its source and commit
history remain attributable to the Formosa Crypto project. It in turn pins
third-party repositories including `crypto-specs`, `formosa-keccak`, Jasmin,
Kyber, and benchmark implementations.

`ntruplus/proof/768/ref/basemul/NTRUPlus768BasemulAlgebra.ec` and
`ntruplus/proof/768/ref/poly_basemul/NTRUPlus768PolyBasemulAlgebra.ec` import
generic signed-word lemmas from `proof/eclib`, including `W16extra.ec`, and
`common/JWord_extra.ec` from the pinned `crypto-specs` submodule. The NTRU+
modulus, Montgomery constants, recursive twiddle schedule, input bounds, and
quotient-ring coefficient formulas are defined and proved in this repository
rather than inherited from the ML-KEM development.

The root MIT license of this repository does not relicense the Formosa ML-KEM
submodule or any of its nested dependencies. At the pinned commit, the upstream
repository does not contain a top-level `LICENSE` file. Preserve upstream
provenance and review the applicable upstream and file-specific terms before
copying, modifying, or redistributing any of its contents outside the
submodule.
