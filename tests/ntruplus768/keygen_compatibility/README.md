# Official KeyGen arithmetic compatibility

Run `python3 -B tests/ntruplus768/keygen_compatibility/audit_keygen_compatibility.py --root . --self-test --output certificate.json`.

The existing Decaps/Encaps forward-NTT certificate covers trit inputs only.
KeyGen instead transforms `3 CBD1(buf) + 1` for `f` and `3 CBD1(buf)` for `g`.
This separate certificate covers every integer vector with `f[0]` in `[-2,4]`,
the other `f` coefficients in `[-3,3]`, and every `g` coefficient in `[-3,3]`.
These interval domains contain all actual sampler outputs, including `f[0]=4`.

Both the frozen per-layer Barrett schedule and the official final-sweep schedule
keep all nonintentional 16-bit narrowings and 32-bit expressions in range.
The official pre-sweep bounds are `[-14825,14828]` for `f` and
`[-14825,14827]` for `g`. They lie inside the exhaustively checked unique
Barrett representative interval `[-22470,22470]`. Source-bound identical
butterfly/twiddle expressions have equal residues, so their final centered
signed output words are equal. This does not assert equality of intermediate
words, storage or traces.

The official `baseinv` determinant and success body, polynomial block schedule,
failure clearing and status are unchanged. Its scalar `fqinv` chain changed.
For all centered four-coefficient inputs and all 192 signed block twiddles,
outward interval arithmetic bounds the actual determinant by `[-1780,1831]`.
Thus its raw zero test is equivalent to residue zero; neither `-q` nor `q`
can reach that test. Exact evaluation of both scalar chains on all 6,913
integers in `[-3456,3456]` gives equal raw outputs, in `[-1741,1741]`.
This contains every reachable determinant. The successful inverse outputs are
therefore equal raw words, bounded by `[-1777,1777]`. On failure both wrappers
return 1 and overwrite the complete polynomial with zero.

The audit also binds the unchanged base-multiplication value expressions,
block schedule and serializer (apart from the old unroll pragma). Identical
inverse and NTT words therefore preserve the subsequent accepted key bytes.
Canonical scalar serialization is checked for the full `[-3456,3456]` domain.
Independent native KeyGen/API comparisons belong to `keygen_complete/`.

`pinned_sources.json` freezes 31 concrete arithmetic and source-checker inputs.
The audit additionally calls the existing token/source checks and records each
input hash. `--self-test` confirms rejection after changing each pinned input;
these are identity-gate checks, not semantic mutation proofs. The production
arithmetic and earlier trit-only certificate are unchanged.

This is an executable integer certificate and source comparison under the
x86-64 two's-complement signed-cast/right-shift conventions. Montgomery
low-word truncations are modeled modulo `2^16`, not asserted to fit before
truncation. It is not an EasyCrypt C-AST or binary equivalence theorem. The
existing extracted-Jasmin proofs, native compilation/execution, caller memory
contracts, retry/RNG assumptions, and API composition are separate evidence.
