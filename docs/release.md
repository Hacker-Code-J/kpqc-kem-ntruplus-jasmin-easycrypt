# Research artifact publication

The initial source, proof, and evidence artifact is published as
[NTRU+768 Correctness & ROM Reduction Proofs](https://github.com/Hacker-Code-J/kpqc-kem-ntruplus-jasmin-easycrypt/releases/tag/ntruplus768-correctness-rom-proofs-v1.0.0).
That release fixes publication commit `9f4eef4`; later commits on `main` do not
replace its tag or attachments. A release is not a claim of fresh whole-suite
proof replay, and no DOI has been assigned.

## Release contents

The initial distribution contains implementation/proof sources, reproducibility
scripts, pinned dependency recovery sources, license notices, and verification
reports/logs. It does not distribute compiler/prover executables, installed opam
switches, a VM/container image, or the preserved binary environment attachment.
The environment inventory describes those separately captured inputs.

Source-package acquisition for Bash, coreutils and Python concerns the optional
binary distribution. The source-and-evidence release uses the documented tool
installation requirements. The prior-evidence attachment contains the summaries
and KeyGen contract; obtain the specification text with the documented
hash-checked acquisition procedure.

For the 31-file EasyCrypt 2026.10 replay, use the compiler and prover versions
in the [current toolchain record](toolchain-current.json). The historical
`runtime-bound` execution uses the source revision and environment inventory
named in its [replay record](../evidence/preserved-full-replay-20261111/README.md).
Each verification summary identifies the source hashes it checked.

## Changes after the initial release

The [EasyCrypt 2026.10 migration](../evidence/easycrypt-2026.10-20261116/README.md)
checked 9 CCA setup, 14 stopped-ROM and 8 spreadness proof files, with one
unfinished-proof rejection test per file. Twelve proof bodies changed; their
declarations, assumptions and exported bounds stayed identical. Imported proofs
outside these 31 files retain their earlier verification records. The initial
release tag and attachments remain unchanged.

## What is available

- A [README](../README.md) and [development history](development-record.md).
- A [claim-to-proof map](claims.md), [reproduction guide](reproduction.md),
  and [historical evidence guide](evidence.md).
- Citation metadata in [CITATION.cff](../CITATION.cff).
- Separate source smoke, C/KAT and proof commands; bounded GitHub Actions CI
  does not represent full formal verification.
- An [observed toolchain inventory](toolchain-observed.json), including the
  EasyCrypt source commit. This is not a validated installation lockfile.

## Verification records

The [2026-11-11 preparation record](publication-checks.json) contains source
hashes and results for 24 public-tool tests, source smoke controls, the C
functional/KAT test, historical-summary authentication, document links and Ruff.
It predates hosted CI and excludes complete proof replay, Python typechecking
and clean-environment installation.

Subsequently, [hosted source and C baseline CI](https://github.com/Hacker-Code-J/kpqc-kem-ntruplus-jasmin-easycrypt/actions/runs/43164613909)
passed on English-edition commit `986cacc`. It checks public tooling, source smoke
controls, the historical-evidence inventory, and the C reference/KAT baseline;
it is not formal proof replay. The [English path migration](english-path-migration.md)
also records its local regression and source-only checks while preserving original
proof and evidence identities.

The subsequent [local candidate validation](../evidence/release-candidate-20261111/README.md)
records 57 public-tool tests, source and C/KAT checks, and a fresh default
runtime-bound replay: 37 main proofs, 37 unfinished-proof rejections and 105
commands with expected outcomes. It also records preserved-home source controls
and a small actual compiler probe. The target's imported prerequisites remain
authenticated historical results. This does not supersede the whole-suite and
clean-machine gates below.

The [full public preserved-environment replay](../evidence/preserved-full-replay-20261111/README.md)
subsequently passed on source commit `359b927`: 37 main proofs, 37 own unfinished
proof rejections and all 105 commands completed with expected outcomes through
`env/replay_runtime.py`. Source, captured environment and log hashes were checked.
The [earlier server-start failure](../evidence/preserved-replay-attempt-20261111/README.md)
remains a separate record. This successful replay used the same Linux host's
OS/runtime dependencies; it does not establish a standalone image or new-host replay.

## Release gates

| Gate | Current boundary | Required release evidence |
| --- | --- | --- |
| Research snapshot | The local candidate preserves the existing research changes and public tooling in an identifiable commit; source archives carry a file manifest | Check the selected commit, archive contents and recursive submodule pins before publishing |
| Historical artifacts | 26 summaries and two specification inputs have been exported with original bytes and checksums | Review redistribution/provenance and supply an immutable download URL; include final replay logs |
| Host/runtime support | Exact tool inputs are captured and the full target passed; OS libraries and Python stdlib remain host dependencies | Document compatible host requirements; validate additional platforms before claiming their support |
| Evidence portability | The full runtime-bound target passed through the public preserved-layout launcher | Retain the verified source/environment/evidence bytes and full logs; never rewrite historical pins |
| Full proof replay | The default runtime-bound target passed freshly; its prerequisite proofs are authenticated historical imports | Replay other release claims as needed, including negative controls, EOF/kernel checks; retain all results |
| Resources | The public preserved-environment runtime-bound run took 23:57.69 and maximum RSS 2,694,052 KiB | Retain the measured environment; measure other targets or platforms before quoting their costs |
| Third-party materials | Source notices and exact dependency recovery are included; the binary environment is outside this initial publication scope | Retain notices and scope boundaries for the selected source/evidence files; handle optional binary redistribution separately |
| Citation | Repository author/title and the initial release are available; DOI and thesis metadata remain separate | Cite the exact release or commit used; archive it and record a version DOI only after one is assigned |

The [runtime proof manifest](../tests/ntruplus768/runtime_bound/proof-manifest.json)
records the root-theory renaming separately from proof execution. Later replays
have their own results tied to source and tool versions.

See [Formosa's location and exact-file evidence](provenance/formosa.md) and the
[preserved environment distribution inventory](../env/distribution/README.md).
The original tested source/runtime archives are immutable evidence; they predate
the newly assembled notices. A public distribution using those archives must
include the notice/provenance companion and current acquisition instructions
alongside them. Adding these materials does not claim a new proof replay.

## Freeze and cite

1. Select and commit the source snapshot. Include the proof sources, required
   extraction sources, deterministic KAT fixtures, manifests and negative
   controls. Check the contents and history for private files or credentials;
   ignore rules do not remove previously committed data. KAT key bytes are
   public deterministic fixtures.
2. In a fresh checkout of that commit, run the reproduction commands linked from
   [claims.md](claims.md) for each result included in the release. Use the stated
   tool versions and evidence bundle, and retain the new execution reports.
3. Create a versioned release after those commands pass. Preserve existing
   tags and attachments. Include the source commit, submodule pins, checksums,
   environment, commands and verification report. Parent-repository source
   archives omit submodule contents, so include acquisition instructions.
4. Archive the release and update `CITATION.cff` with its version, date and DOI
   when assigned. Cite the version used in the research.

GitHub explains [CITATION.cff support](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/about-citation-files)
and [versioned archiving with Zenodo](https://docs.github.com/en/repositories/archiving-a-github-repository/referencing-and-citing-content).
