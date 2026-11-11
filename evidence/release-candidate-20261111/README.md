# Local release-candidate validation

Status: **local candidate, not a published or whole-suite validated release**.
The machine-readable result is [summary.json](summary.json).

## Fresh execution

The default runtime-bound verifier completed with **PASS**: 37 main proofs,
37 corresponding unfinished-proof rejections, scope and calibration controls,
and the actual exported theorem type check. All 105 commands completed with
their expected outcomes. See [the original report](runtime-bound-summary.json).
The recorded source and external-input audits were unchanged.

This run used the existing authenticated prover environment and the exact
historical Python binary, mounted read-only at its original path. The host
installation and verifier acceptance conditions were not changed. The initial
attempt correctly rejected the upgraded host interpreter; its
[failed report](initial-runtime-bound-failure.json) is preserved separately.
The [launch command](runtime-bound-launch.json) identifies the successful run.

Wall time was **23 minutes 32.23 seconds**; maximum RSS was **2,696,728 KiB**.
These measurements apply to this target on this host, not the whole suite.
See [the resource record](runtime-bound-resources.txt) and the host information
in `summary.json`.

Imported theorem prerequisites were authenticated through pinned historical
evidence. They were not all freshly replayed. The historical manifest marker
`ROOT_REVIEWED_ALPHA_RENAME_NOT_REPLAYED` remains an immutable description of
that manifest's preparation; this new execution has its own report.

## Packaging checks

- [57 public-tool tests](public-tool-checks.json), Ruff and Python syntax passed.
- [Source compatibility smoke controls](smoke.log) and the
  [C functional/deterministic KAT check](baseline.log) passed.
- The [isolated-home source check](isolated-source-summary.json) and
  [public launcher source check](launcher-source-summary.json) completed as
  `SOURCE_CHECK_ONLY`. They exposed the selected repository, evidence bundle
  and preserved home inputs without the private thesis tree.
- The final [captured-tool probe](captured-tool-probe.json) compiled a small
  completed theorem and rejected its unfinished counterpart using a trailing
  declaration sentinel. The probe sources and logs are retained here. A bare
  unfinished proof at EOF is not a sufficient rejection test for this compiler;
  the real runtime verifier already uses its own sentinel controls.

The environment inventory preserves 3,109 historically pinned/calibrated files
and separately identifies 36 observed `.eca` library sources. These `.eca`
sources are required at runtime but were omitted by the historical `*.ec`
external audits. They must not be described as historically hash-authenticated.
See [the preserved environment guide](../../env/README.md).

The full runtime-bound run above used the existing host prover layout. The
public preserved-home launcher has been tested with source controls and the
small actual compiler probe, not a second full runtime-bound replay. The
capture still requires compatible host OS libraries and Python standard
library; it is not a standalone OS image.

## Complete logs and integrity

The complete runtime output, checked proof copies, negative fixtures, logs,
launch command and resources are packaged as
`ntru-runtime-bound-replay-20261111.tar.gz` (569,715 bytes), SHA-256:

```text
2850b17b8fb8fc995afea8b7b66a6ccd8abba46e1415091e21c915fc15712348
```

The local preparation directory holds this candidate attachment. No public
download URL, release tag or DOI has been assigned. Original absolute paths in
the raw reports identify their execution context; archive members retain the
same original bytes. Summary records in Git do not replace the complete logs.

Verify the files in this directory with:

```sh
sha256sum --check --quiet SHA256SUMS
```

Hosted CI, a complete clean-machine installation, and the whole NTRU+ proof
suite were not executed by this preparation. Release-wide claims still follow
the [release gates](../../docs/release.md).
