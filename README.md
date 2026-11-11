# NTRU+768 in Jasmin and EasyCrypt

Research artifacts for the implementation and formal analysis of NTRU+768:
Jasmin arithmetic, EasyCrypt correctness proofs, classical random-oracle-model
security reductions, and a source-calibrated reduction cost model.

**Publication preparation is in progress.** This checkout is not yet a frozen
thesis release. Historical verification records are not a fresh full replay of
the current sources. See [release status](docs/release.md) before citing a result
as reproduced.

## Research scope

- Arithmetic and serialization artifacts connect word operations to polynomial
  semantics for NTRU+768.
- KeyGen, Encaps and Decaps formal callers have explicitly scoped contracts.
- The security development includes classical-ROM reductions and a concrete
  short-relation bound.
- Reduction costs use a fixed-768 primitive model with ideal-ROM operations
  and unit-cost integer/word arithmetic.

The [claim-to-proof map](docs/claims.md) identifies theorem names, commands,
assumptions and exclusions. These results do not collectively establish native
C/binary equivalence, a complete shared-memory/ABI theorem, full-API CT/SCT,
QROM security, or a parameter-family PPT theorem. Scope is target-specific.

## Start here

The lightweight checks require Python 3.10+; the C reference check additionally
requires Bash, GCC and standard Unix build utilities. Run commands at the
repository root:

```sh
git clone https://github.com/Hacker-Code-J/kpqc-kem-ntruplus-jasmin-easycrypt.git
cd kpqc-kem-ntruplus-jasmin-easycrypt
python3 scripts/reproduce.py list
python3 scripts/reproduce.py smoke
python3 scripts/reproduce.py baseline
```

The smoke check is a source check. The baseline command compiles and tests the
C reference, regenerates its deterministic KAT, and compares bytes. Neither is
a formal proof replay. The [reproduction guide](docs/reproduction.md) describes
proof targets, toolchain selection, submodules and explicit prior-evidence input.
The [evidence guide](docs/evidence.md) distinguishes historical evidence checks
from fresh proof execution.
The [preserved environment inventory](env/README.md) identifies the exact
toolchain inputs required by historical checks and its remaining OS dependencies.

## Source versions

| Material | Immutable reference | Role |
| --- | --- | --- |
| Imported NTRU+768 C and KAT | `38201624477a7dbb2f46d1ae7686ae5ceee4eb80` | Baseline, with a documented comment-only patch |
| Official NTRU+ migration target | `3991b2ae08d6f0008d37e41b8aceaaab27b4ec89` | Separately identified checked decoder and caller work |
| Formosa ML-KEM submodule | `475b87434506280fdfa1a1ba5da0af3787e00579` | External proof helpers and reference structure |

A preserved KAT does not establish equivalence for malformed inputs or native
execution. See the [migration analysis](docs/ntruplus768-upstream-migration.md)
and [third-party provenance](THIRD_PARTY.md).

## Repository guide

| Path | Contents |
| --- | --- |
| `ntruplus/jasmin/768/ref/` | Jasmin implementations and extraction targets |
| `ntruplus/proof/768/ref/` | EasyCrypt theories and proof projects |
| `tests/ntruplus768/` | Runtime tests, policy checks, frozen manifests and proof runners |
| `scripts/` | Verification wrappers and public reproduction entrypoints |
| `NTRU+/` | Imported C references and deterministic KAT fixtures; formal scope here is 768 |
| `external/formosa-mlkem/` | Pinned external submodule |
| `docs/` | Claim map, reproduction instructions, scope and detailed research records |

The former long README is preserved as the
[development record](docs/development-record.md). It records historical
milestones; use the guides above for the current public interface.

## Citation and reuse

[CITATION.cff](CITATION.cff) provides repository citation metadata. Until a
validated thesis release and DOI exist, include the exact Git commit in any
citation. A DOI, thesis title and release version are deliberately not invented.

Repository-owned code is provided under [MIT](LICENSE). External materials
retain their own terms; see [THIRD_PARTY.md](THIRD_PARTY.md), especially the
Formosa dependency. The artifact is research software, with verification claims
limited to the explicitly documented models and targets.
