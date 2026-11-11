# Thesis artifact release preparation

Status: **publication preparation, not a validated thesis release**.
The repository interface and lightweight CI are prepared. No public release,
tag, DOI, push, or fresh whole-suite proof replay is implied by this document.

## What is available

- A concise [README](../README.md) and preserved [development record](development-record.md).
- A [claim-to-proof map](claims.md), [reproduction guide](reproduction.md),
  and [historical evidence guide](evidence.md).
- Repository citation metadata in [CITATION.cff](../CITATION.cff), using the
  author from the existing license and the configured GitHub remote.
- Separate source smoke, C/KAT and proof commands; bounded GitHub Actions CI
  does not represent full formal verification.
- An [observed toolchain inventory](toolchain-observed.json), including the
  EasyCrypt source commit. This is not a validated installation lockfile.

## Preparation validation

The bounded checks performed during this preparation are recorded in
[publication-checks.json](publication-checks.json), with source hashes for the
reviewed files. They include 24 public-tool tests, source smoke controls, the C
functional/KAT test, historical-summary authentication, document-link checks and
Ruff. GitHub Actions itself has not been run on the hosted service. No complete
proof replay, Python typechecker run or clean-environment installation is claimed.

The subsequent [local candidate validation](../evidence/release-candidate-20261111/README.md)
records 57 public-tool tests, source and C/KAT checks, and a fresh default
runtime-bound replay: 37 main proofs, 37 unfinished-proof rejections and 105
commands with expected outcomes. It also records preserved-home source controls
and a small actual compiler probe. The target's imported prerequisites remain
authenticated historical results. This does not supersede the whole-suite and
clean-machine gates below.

A subsequent [full preserved-environment attempt](../evidence/preserved-replay-attempt-20261111/README.md)
authenticated the public inputs but failed when EasyCrypt automatically started
its Why3 server. Separate socket/direct-server diagnostics passed, so the exact
failing operation in that full-run context remains unresolved. This attempt
does not establish a full PASS for the public preserved-home launcher.

## Release gates

| Gate | Current boundary | Required release evidence |
| --- | --- | --- |
| Research snapshot | The local candidate preserves the existing research changes and public tooling in an identifiable commit; source archives carry a file manifest | Check the selected commit, archive contents and recursive submodule pins before publishing |
| Historical artifacts | 26 summaries and two specification inputs have been exported with original bytes and checksums | Review redistribution/provenance and supply an immutable download URL; include final replay logs |
| Fresh installation | Exact audited tool inputs are captured; the package still depends on host OS libraries and Python stdlib | Provide the necessary OS/runtime closure and validate setup in a new machine/container |
| Evidence portability | A preserved-layout launcher restores captured inputs; isolated source controls and a small compiler probe passed | Replay the selected full targets under the final captured environment; never rewrite frozen hashes just to pass |
| Full proof replay | The default runtime-bound target passed freshly; its prerequisite proofs are authenticated historical imports | Replay other release claims as needed, including negative controls, EOF/kernel checks; retain all results |
| Resources | The fresh runtime-bound target took 23:32.23 and maximum RSS 2,696,728 KiB on this host | Measure the remaining selected release targets and record the final release environment |
| Third-party redistribution | Root MIT covers repository-owned material; Formosa has no top-level license at its pinned commit | Resolve applicable file/upstream terms before bundling external sources; retain provenance and notices |
| Citation | Repository author/title available; thesis metadata, DOI and release date are not finalized here | Confirm authorship/title, create the validated release, archive it and record its version DOI |

The runtime proof manifest's `ROOT_REVIEWED_ALPHA_RENAME_NOT_REPLAYED` state
must not be silently converted into a new PASS. Family documentation may retain
historical proof descriptions; only a fresh run against the release sources
establishes release verification status.

## Public contents and credentials

`.aws/`, `.env`, `.env.*`, agent state and Python caches are ignored. Ignore
rules do not remove anything already committed or purge history. Keep proof
sources, generated extraction sources required by the checkers, deterministic
KAT fixtures, manifests and negative controls: generated does not mean disposable.
KAT secret-key bytes are public deterministic test fixtures, not deployment keys.

Before publication, inspect the exact staged snapshot and reachable history for
credentials and private material. Do not upload the entire working directory,
agent state, thesis directory, or unreviewed logs. A source archive of the parent
repository does not automatically package its submodule contents; document how
they are obtained and verify any separately distributed bundle.

## Freeze and cite

1. Review and commit the intended research and preparation files using the
   repository's Lore commit-message protocol. Avoid `git add .` on this working
   tree; inspect staged changes and required untracked proof families.
2. Validate a fresh checkout of that exact commit with the documented environment
   and public evidence bundle. Record new results separately from inherited ones.
3. Create a versioned release (for example `thesis-v1.0`) only after the gates
   above pass. Include the source commit, submodule pins, checksums, environment,
   commands and verification report in the release description.
4. Archive that release, obtain its DOI, and then update `CITATION.cff` with real
   version/date/DOI and confirmed thesis metadata. Cite the version used in the
   thesis rather than a moving branch.

GitHub explains [CITATION.cff support](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/about-citation-files)
and [versioned archiving with Zenodo](https://docs.github.com/en/repositories/archiving-a-github-repository/referencing-and-citing-content).
No DOI or release identity has been fabricated for this preparation.
