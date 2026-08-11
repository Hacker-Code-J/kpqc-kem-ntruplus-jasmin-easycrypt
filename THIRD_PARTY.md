# Third-party materials

## NTRU+ reference implementation

- Paths: `NTRU+/LICENSE`, `NTRU+/NTRU+768`, and `NTRU+/KAT/NTRU+768`
- Source: <https://github.com/ntruplus/ntruplus.git>
- Source commit: `38201624477a7dbb2f46d1ae7686ae5ceee4eb80`
- Retrieved/verified: 2026-08-11
- Purpose: C behavior oracle and deterministic KAT baseline for the NTRU+768
  Jasmin and EasyCrypt work
- License: MIT; preserved in `NTRU+/LICENSE`

The imported NTRU+768 implementation, KAT directory, and license byte-match
the corresponding upstream files at the source commit. The local
`NTRU+/NTRU+768` path corresponds to upstream
`Reference_Implementation/NTRU+768`.

## Formosa ML-KEM

- Path: `external/formosa-mlkem`
- Source: <https://github.com/formosa-crypto/formosa-mlkem.git>
- Pinned commit: `475b87434506280fdfa1a1ba5da0af3787e00579`
- Retrieved: 2026-08-11
- Purpose: external reference for Jasmin implementation and EasyCrypt proof
  structure; not an NTRU+ verification result

This dependency is represented by a Git submodule, so its source and commit
history remain attributable to the Formosa Crypto project. It in turn pins
third-party repositories including `crypto-specs`, `formosa-keccak`, Jasmin,
Kyber, and benchmark implementations.

The root MIT license of this repository does not relicense the Formosa ML-KEM
submodule or any of its nested dependencies. At the pinned commit, the upstream
repository does not contain a top-level `LICENSE` file. Preserve upstream
provenance and review the applicable upstream and file-specific terms before
copying, modifying, or redistributing any of its contents outside the
submodule.
