# Reproducing the NTRU+768 artifacts

The initial public package contains sources and verification evidence, with tool
versions and installation/provenance information. It does not include the
preserved compiler/prover binaries. Source inspection and C/KAT checks can run
with their listed prerequisites. Full formal replay additionally needs the
matching documented environment; equally numbered rebuilt tools do not
automatically satisfy historical binary-identity checks.

This guide separates source inspection, C/KAT execution, and formal verification.
The [claim map](claims.md) defines the scope of individual results. A successful
source check or C test does not establish a formal theorem. Some formal harnesses
check new proof mains while validating imported results through historical,
hash-pinned evidence; that is not a fresh replay of every imported theorem.

## Current EasyCrypt 2026.10 scope

Current development uses EasyCrypt **r2026.10** (commit
`859766e50e936fb9e420fb6fb1ad8824ffb8d83e`) for `cca-setup`, `stopped-rom` and
`spreadness`, with Why3 1.8.2, Z3 4.12.6 and Jasmin 2026.09.0. The
[current toolchain record](toolchain-current.json) and
[31-target replay evidence](../evidence/easycrypt-2026.10-20261116/README.md)
describe the checked scope. `toolchain-observed.json` records the earlier
2026.09 environment.

The three verifiers run source-mutation tests and semantic EOF checks with the
recorded prover limits. Current source pins identify the updated proof files.
For historical imported sources, only the twelve exact before/after pairs in
`tests/ntruplus768/easycrypt-2026.10-proof-transitions.json` are recognized. Their
preserved original bytes and unchanged non-proof declarations are checked and
each use is recorded as `reviewed_import_transitions`. This establishes a reviewed
source transition, not a fresh replay of the imported proof bodies.

After preparing the pinned external libraries and selecting the current tools,
the public commands remain:

```sh
export EASYCRYPT="$(command -v easycrypt)"
export WHY3="$(command -v why3)"
python3 scripts/reproduce.py proof cca-setup stopped-rom spreadness \
  --prior-evidence-root /absolute/path/to/evidence
```

Other targets retain the source and tool requirements of their historical
records. Reproduce those results with the corresponding commit and environment;
the current development tree may not satisfy their frozen pins.

The repository-local evidence integrity check is separate from proof execution:

```sh
python3 evidence/easycrypt-2026.10-20261116/check.py
```

## Checkout and prerequisites

Clone this repository at the commit or release cited by the paper, then run:

```sh
git submodule update --init external/formosa-mlkem
git clone --no-checkout dependencies/crypto-specs-fb050598ed35.bundle external/formosa-mlkem/crypto-specs
git -C external/formosa-mlkem/crypto-specs checkout --detach fb050598ed356c5c6604d92a1e198b2dd4543777
python3 --version
python3 scripts/reproduce.py list
```

For a source archive without the parent repository's Git metadata, obtain the
external dependency explicitly instead of running `git submodule` at its root:

```sh
git clone --no-checkout https://github.com/formosa-crypto/formosa-libjade.git external/formosa-mlkem
git -C external/formosa-mlkem checkout --detach 475b87434506280fdfa1a1ba5da0af3787e00579
git clone --no-checkout /path/to/crypto-specs-fb050598ed35.bundle external/formosa-mlkem/crypto-specs
git -C external/formosa-mlkem/crypto-specs checkout --detach fb050598ed356c5c6604d92a1e198b2dd4543777
```

The tested source archive does not embed the external repositories. Retain the
Formosa commit and exact `crypto-specs` dependency; their upstream terms are described in
[THIRD_PARTY.md](../THIRD_PARTY.md). Source smoke and the C baseline do not need
these external proof libraries.

The old `crypto-specs` URL also became a move notice and did not serve the
required historical commit in the inspected endpoints. The
[CC0 recovery bundle](../dependencies/README.md) restores that exact commit
offline and was checked against all 136 source files. It is included in current
checkouts and the separate publication companion, not retroactively inserted
into the immutable tested source archive. Verify its documented checksum and
use a fresh dependency path; keep an existing checkout already at the exact pin.

The public NTRU+ verification entry points use Formosa's `proof/eclib` and
`crypto-specs` subtrees. The upstream repository's other benchmark, implementation
and compiler submodules are not required by these entry points. The documented
Jasmin compiler and installed model library are configured separately below.

The upstream repository moved to `formosa-crypto/formosa-libjade`. The local
directory remains `external/formosa-mlkem`, and the required commit remains
`475b87434506280fdfa1a1ba5da0af3787e00579`. On 2026-11-12, a fresh fetch from
the successor verified the exact original commit and tree. The old remote now
contains a move notice rather than the original history. For a checkout made
before this URL update, use `git submodule sync -- external/formosa-mlkem`
before updating its dependencies. A pre-update source archive can use the
explicit successor-clone commands above without changing proof source pins.

The wrapper requires Python 3.10 or later. C baseline tests additionally require
Bash, GCC (or a compatible compiler selected by `CC`), and standard Unix tools.
Proof and Jasmin targets need the matching compiler/proof environment and the
pinned Formosa/crypto-specs proof libraries. The documented extraction baseline is Jasmin 2026.09.0 and
Why3 1.8.2. Some algebraic targets also use Coq 8.20.1 and MathComp 2.2.

The [historical tool inventory](toolchain-observed.json) records observed
versions and binary hashes; it is not an installation lock. A replay with
different tools needs its own results and environment record.

Use one consistent toolchain on `PATH`. Select absolute executable paths through
`EASYCRYPT` and `WHY3` to override historical harness defaults. After activating
the intended switch, run:

```sh
export EASYCRYPT="$(command -v easycrypt)"
export WHY3="$(command -v why3)"
export OCAMLRUNPARAM=o=20
```

Inspect the selected harness and its target documentation for additional
requirements. SMT prover selection is also controlled by the effective Why3
configuration. The wrapper neither installs tools nor changes prover settings.
Historical evidence can require matching executable/library hashes and absolute
paths; merely selecting equally numbered tool versions may not be sufficient.
See [evidence.md](evidence.md) for the remaining portability boundary.
The [preserved-input guide](../env/README.md) describes the local environment
capture, including recovery of historical system executables. Its manifest
identifies preserved bytes; it is not an independently validated OS image.

## Three execution levels

### 1. Source smoke check

```sh
python3 scripts/reproduce.py smoke
```

This runs the compatibility shim's exact-source gate and its eight negative
controls. It requires no EasyCrypt or Jasmin installation. Expected output includes
`PASS: compatibility source gate rejects eight model/assumption mutations`.
It does not compile proofs, build native code, or establish whole-repository
source integrity.

### 2. C reference and KAT

```sh
python3 scripts/reproduce.py baseline
```

This invokes `scripts/verify-ntruplus768-baseline.sh`: build and run the imported
C reference's functional test, regenerate the deterministic KAT, and compare its
response file byte for byte. Expected output includes `count: 0`, a matching-KAT
message, and the generated response SHA-256. This checks the frozen baseline C
reference, not the official-target migration or any EasyCrypt theorem.

The existing script accepts `CC`, `TMPDIR`, `NTRUPLUS768_SRC_DIR`, and
`NTRUPLUS768_EXPECTED_RSP` environment overrides. Leave the source and response
overrides unset when reproducing the repository's baseline.

### 3. Existing formal verification targets

```sh
python3 scripts/reproduce.py list
python3 scripts/reproduce.py proof basemul --dry-run
python3 scripts/reproduce.py proof basemul
```

Names are the suffixes of `scripts/verify-ntruplus768-*.sh`. The inventory includes
all such shell entry points; it is not an inventory of every direct Make target.
Each verifier keeps its existing default checks, negative controls, extraction
comparisons, proof scope, and success criteria. The wrapper does not pass
`--check-only`, `--draft`, `--native-only`, or `--defer-safety`.

Targets marked `requires --prior-evidence-root` need an explicitly supplied
directory containing the paths specified in their `prior-evidence-pins.json`:

```sh
python3 scripts/check_public_evidence.py --evidence-root /absolute/path/to/evidence
python3 scripts/reproduce.py proof runtime-bound \
  --prior-evidence-root /absolute/path/to/evidence --dry-run
python3 scripts/reproduce.py proof runtime-bound \
  --prior-evidence-root /absolute/path/to/evidence
```

Replace the example path with an actual evidence bundle; it is not a download
location. The wrapper rejects a missing/non-directory evidence root before
launching targets. Each selected verifier remains responsible for validating
the precise historical hashes, statuses, source coverage, and toolchain inputs.
For targets that use prior evidence, the public entry point requires an explicit
evidence root. Direct driver invocations default to the sibling
`research-evidence` directory; override it with `--prior-evidence-root`. The
[path migration record](english-path-migration.md) describes that default.

For all listed verification scripts except the separate C baseline:

```sh
python3 scripts/reproduce.py proof --all \
  --prior-evidence-root /absolute/path/to/evidence --dry-run
python3 scripts/reproduce.py proof --all \
  --prior-evidence-root /absolute/path/to/evidence
```

This runs targets sequentially in name order and stops at the first nonzero exit.
Dependency evidence must already exist at the expected hashes. Re-running a
predecessor creates a separate result; successor pins still identify their
recorded inputs. Check each target's report for the scope of a successful run.

## Recording a replay

Record the exact commit, working-tree status, recursive submodule commits,
environment overrides, tool versions/configurations, selected targets, return
codes, elapsed time, and peak memory. Retain the harness-generated evidence
directories and hashes, including negative controls. Many legacy shell targets
clean temporary build directories; save their console output separately if it
is needed for review. For example, in Bash:

```sh
set -o pipefail
python3 scripts/reproduce.py baseline 2>&1 | tee /tmp/ntruplus-baseline.log
```

`pipefail` ensures a successful `tee` cannot hide a failed verifier. The example
log path is temporary storage; move a reviewed copy into the release's evidence
archive. Avoid putting private paths or credentials in a public transcript.

Measure runtime and peak memory for the selected targets and environment.
Run large proofs one at a time. Report complete dependency replay separately
from runs that authenticate historical imports.

## Checking the wrapper itself

```sh
python3 -B -m unittest discover -s tests -p test_reproduce.py -v
```

These tests check explicit evidence requirements, selective argument forwarding,
inventory coverage, and stopping on errors. They do not execute expensive proofs.
