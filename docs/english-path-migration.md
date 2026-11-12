# English evidence paths and preserved metadata

The publication interface uses English evidence-directory names and
evidence-relative identifiers. Historical proof records and the original
preserved-environment archive retain their exact bytes.

## Verifier defaults

The 24 direct verifier drivers that previously selected a machine-specific
thesis directory now default to the sibling directory `research-evidence`.
Their `--prior-evidence-root` argument still selects an explicit directory.
The public `scripts/reproduce.py` wrapper and `env/replay_runtime.py` launcher
continue to require and pass that argument explicitly; their selected evidence
does not depend on the direct-driver default.

The native Coq integration test uses English `café` path labels containing spaces.
These remain genuinely non-ASCII paths, preserving the Unicode-path regression
case without retaining language-specific folder labels.

[english-path-migration.json](english-path-migration.json) records the baseline
commit, old/new hashes of all 25 Python files, literal identities, and normalized
AST fingerprints. After replacing only the reviewed literal nodes with fixed
markers, each old and new AST is identical. The nine affected source-pin
inventories change only 19 entries referring to those Python files. Their
`.ec`/`.v` entries are unchanged. No proof manifest, prior-evidence pin, imported
proof source, or historical summary is refreshed.

## English representation of the environment manifest

The original environment archive's `manifest.json` remains authenticated by
SHA-256:

```text
fb2cb4f9be729ef3706d9ec7a98e44ad6b35230e743762ba29899301b732d4d5
```

The repository's [preserved-inputs.json](../env/preserved-inputs.json) is an
explicitly identified representation of that original document. Only the
informational `separate_evidence_inputs` keys are projected from historical
absolute identifiers to `handoff/verification/...` paths. Each record additionally
retains the SHA-256 of its original UTF-8 absolute identifier. The exact original
identifiers remain available in the immutable archive; they are not escaped or
silently rewritten to look like different historical paths. All 3,145 payload
records, file hashes, modes and original mount paths remain unchanged.

Authentication has three ordered stages:

1. Require the archive manifest's exact original byte hash, before projecting it.
2. Compute the deterministic `evidence-relative-paths-v1` representation and
   require equality with the entire checked-in representation. Reject duplicate
   JSON keys, ambiguous projected paths, record omissions and metadata drift.
3. Apply the existing payload hash, mode, inventory, path and symlink checks.

This is implemented in [preserved_environment.py](../scripts/preserved_environment.py)
and used by both the preserved-layout launcher and the distribution inventory
generator. Unprojected inventories retain the original byte-for-byte comparison.
The recorded full replay and existing distribution companions continue to refer
to the unchanged archive-manifest hash, not to the new representation file's hash.

## Verification scope

The migration tests check exact reviewed source changes, unchanged proof-pin
inventories, continued non-ASCII path coverage, and rejection of an attempted
`Proofs:check` to `Proofs:weak` change. Manifest tests reject mutations to original
bytes, projected metadata and historical identifier hashes. The existing
launcher tests continue to reject altered payloads, modes, extra files, symlinks
and unsafe mount/output paths.

Source-only verifier runs authenticate their historical dependencies according
to each existing runner's scope. A runner that does not consume prior evidence
in `--check-only` mode remains distinguished from one that does. Neither these
checks nor the path migration itself establish a fresh formal proof replay.
Historical PASS records remain tied to their original source/tool snapshots.
