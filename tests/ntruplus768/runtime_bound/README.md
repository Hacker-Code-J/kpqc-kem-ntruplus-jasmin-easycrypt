# Runtime resource proof replay

This family checks actual reduction bodies under a **unit-cost integer/word model with ideal-ROM primitives**. It does not establish native CPU cycles, wall-clock time, arbitrary-precision bit complexity, Safety/CT/SCT, or a general PPT theorem.

The runner reuses the preceding adaptive-history harness: every frozen new EasyCrypt main is compiled with `-no-eco -pragmas Proofs:check`, followed by its own missing-proof negative control and semantic EOF theorem. The pinned fresh-local scope fixtures are unchanged. Imported proof evidence is linked to the preceding adaptive-history full PASS; imported Coq/native proofs are not claimed as freshly replayed.

Source calibration is required in addition to successful proofs. Generated instruction counters are regenerated from pinned original bodies in a new directory and compared by body and AST/charge records. Manual word scans have separate source-to-charge templates. Reducing both a counter and its proved bound must fail the calibration checks even if the changed file has a new hash. Unsupported instructions, missing loops, omitted charges and polynomial reification in word execution paths are rejected.

At a procedure boundary, simultaneous tuple-return binding is one abstract transfer. Tuple construction, source-expression evaluation and each owned array payload copy (three operations per cell) are charged separately. This convention does not count native register moves. Full coverage requires the fixed, primitive, word-check, sampling, kernel, simulation, adaptive-phase and outer-reducer source checks, together with the reviewed final theorem declarations.

`--check-only --draft` is a draft/source inspection and cannot emit full PASS.
The current proof manifest is `FROZEN` with review state
`ROOT_REVIEWED_ALPHA_RENAME_NOT_REPLAYED`; that label alone is not evidence of a
successful replay of this checkout. Full replay validates the reviewed inventory,
final export, complete source calibration, source pins and prior evidence. No
manifest is automatically approved or frozen. See the repository
[release status](../../../docs/release.md) for the publication boundary.

```
./scripts/verify-ntruplus768-runtime-bound.sh --check-only --draft \
  --prior-evidence-root '/path/to/evidence-bundle' --output '/tmp/new-empty-evidence'
```

`generate_fixed.py` and `calibration/manifest.json` are produced by the leaf-calibration owner. Final source hashes, theorem bindings and proof inventory are reviewed before `freeze_manifest.py` is used.
