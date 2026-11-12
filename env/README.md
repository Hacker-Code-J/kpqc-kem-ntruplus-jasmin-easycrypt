# Preserved verification inputs

The historical NTRU+ runners authenticate source files, prover binaries,
configuration, and library files by SHA-256. Some also compare their absolute
paths. [preserved-inputs.json](preserved-inputs.json) inventories the corresponding
local environment capture. This inventory does not install an environment or
establish a fresh proof result.

## Capture status

The local capture covers the environment inputs named by all 26 authenticated
historical summaries listed in `tests/ntruplus768/*/prior-evidence-pins.json`,
plus the runtime-bound calibration's two semantic-support files. Each record
identifies its referring summary or calibration input. The separate historical
evidence bundle supplies the 27 summary/specification paths encountered in those
external-input audits; this environment capture does not copy the thesis tree.

- 3,109 pinned historical/calibration inputs, totaling 814,368,311 bytes, were
  captured with matching hashes and file modes. This includes the native Coq
  library/plugin audit set; `audited_input_count` reports this category separately.
- Another 36 installed EasyCrypt `.eca` library sources (746,529 bytes) are
  captured as `SUPPLEMENTAL_OBSERVED_RUNTIME_INPUTS`. These are abstract or
  cloneable theory sources, including `Monoid.eca`; they are not compiled caches.
  Historical audits enumerate `*.ec` and did not authenticate these `.eca` files.
  Their recorded hashes establish this capture's observed bytes only.
- The combined payload contains 3,145 files and 815,114,840 bytes. Every installed
  `theories/**/*.eca` source is included to cover recursive imports and clones;
  all 92 installed `theories/**/*.ec` sources are already in the pinned set.
- The installed `/usr/bin/env` and Python interpreter had changed. Exact
  historical binaries were recovered from Ubuntu packages and authenticated
  against the historical hashes before capture. The host installations were
  not modified. `python_restoration` and `coreutils_restoration` record package
  and binary hashes, download URLs, and observed host hashes.
- The coreutils package was also authenticated through Ubuntu's signed
  InRelease, package index and package digest. The package, index, signature,
  keyring and verification record are retained with the local package.
- `missing_or_mismatched_inputs` is empty; the status is
  `LOCAL_PRESERVED_INPUT_CAPTURE_NOT_REPLAYED`.

The initial incomplete inventory and the capture before supplemental `.eca`
sources were added are retained under the package's `history/` directory.
The missing `.eca` sources were discovered by an isolated EasyCrypt import
probe. Target-specific preflight and fresh execution must still determine
whether a target can run with the provided inputs.

## Package layout and integrity

The binary payload is kept outside the Git source checkout during preparation:

```text
preserved-environment/
  manifest.json                  Immutable original; repository has an English view
  SHA256SUMS                     Payload and metadata hashes
  runtime-dependencies.json      Host OS and dynamic dependency observations
  capture.py                     Explicit-root local capture procedure
  sources/                       Python/coreutils packages and recovery provenance
  history/                       Earlier capture inventories and integrity checks
  rootfs/
    home/hacker-code-j/...       Pinned inputs and separately observed .eca sources
    usr/bin/...                  Matching historical system executables
```

From an obtained package directory, verify its contents before using it:

```sh
sha256sum --check --quiet SHA256SUMS
```

No immutable public download is assigned to this local preparation package.
The file inventory is included in Git; the approximately 815 MB payload
is a candidate release attachment requiring its own provenance/license review.
Repository MIT terms do not replace the terms of the captured third-party
tools, libraries or system package.

The [distribution companion](distribution/README.md) now attributes all 3,145
captured files across 150 components and preserves 169 original notice texts.
Its separate source-material companion contains 124 digest-identified blobs,
including upstream archives, pinned Git snapshots and registered build patches.
These materials are additional attachments; the tested runtime archive and its
manifest are unchanged. Three exact Ubuntu source-package payloads still need
acquisition through the prepared signed-index recipe, and component/build-option
limits remain explicit in the inventory. The companion is not a blanket
redistribution clearance for the binary package.

## Reconstructing the expected layout

Use a supported, isolated Linux x86-64 environment that exposes each captured
file at the original absolute path recorded as its manifest key. Keep the
captured configuration bytes and prover selection intact. Supply the source
checkout and authenticated historical evidence through separate explicit
directories, and preserve fresh outputs in a new directory. Changes to frozen
source pins or historical evidence are not part of this procedure.

The target command remains the documented public entry point, for example:

```sh
python3 scripts/reproduce.py proof runtime-bound \
  --prior-evidence-root /absolute/path/to/evidence-bundle
```

Its Python process must resolve to the authenticated interpreter at
`/usr/bin/python3.10` inside that environment. The runtime-bound verifier also
requires its locally managed Why3 server; an externally supplied
`WHY3_SERVER_SOCKET` is rejected. A host policy that disallows the required
local Unix sockets remains a replay blocker.

## Remaining environment work

This capture is **not a standalone OS image**. `runtime-dependencies.json`
records 381 ELF inspections and 53 distinct observed dynamic-dependency paths.
Most OS libraries and the dynamic loader are inventoried rather than bundled.
The Python standard library, transitive OS resources, and complete Jasmin/C
build dependencies are also outside this capture's completeness claim.

The audited Coq installation contains a broad plugin superset. Some unrelated
Apron plugins already have unresolved `ldd` dependencies in the original host;
those observations are retained rather than silently classified as resolved.
The inventory does not assert that every recorded plugin is loaded by a proof.

Before claiming independent environment reproduction, provide the necessary
OS/runtime closure, review redistribution terms, and replay the selected full verifiers
in that environment. Same version numbers alone do not imply matching bytes.
Successful checksum verification establishes preservation of the captured
files, not a theorem or whole-suite PASS. See the [evidence guide](../docs/evidence.md)
and [release gates](../docs/release.md).

## Running the preserved runtime-bound target

On a compatible Linux x86-64 host with Bubblewrap (`bwrap`), use the explicit
launcher to expose the captured inputs at their original paths inside a mount
namespace:

```sh
mkdir -p /tmp/ntruplus-replay-results
python3 env/replay_runtime.py \
  --environment /path/to/preserved-environment \
  --evidence-root /path/to/historical-evidence-bundle \
  --output /tmp/ntruplus-replay-results/runtime-bound-full
```

The output must not exist. Its parent must already exist and be separate from
the source, environment and evidence trees: the parent is the writable result
mount. Source and input mounts are read-only. The launcher first authenticates
the original package manifest by its pinned byte hash, then requires its
deterministic English representation to equal `env/preserved-inputs.json`.
It authenticates all payload hashes and modes, rejects extra files and symlinks, and
checks the historical summaries. Mount destinations are fixed by the launcher,
not selected by a caller-provided manifest.

The [English-path migration](../docs/english-path-migration.md) explains the
27 informational evidence-key projections and their historical identifier hashes.
The archive manifest, payloads and original mount paths are unchanged.

The original tool/configuration paths exist only inside this namespace.
Explicit `EASYCRYPT`, `WHY3` and `XDG_CONFIG_HOME` selections point to the
authenticated capture, without changing the host user's home or shell setup.
An external `WHY3_SERVER_SOCKET` is rejected. Inherited host restrictions still
apply; Bubblewrap is used to restore the recorded layout, not to bypass those
restrictions. OS libraries, the Python standard library and other host runtime
dependencies remain required; this does not turn the capture into a standalone
image or prove clean-machine reproducibility.

The default command runs the full runtime-bound verifier with its existing
gates and returns its exit status. Add `--check-only` only for source controls;
such a result is not a full proof PASS. Preserve the output `summary.json` and
logs, and distinguish this target's fresh checks from its authenticated
historical dependencies.

## Recorded full replay

The public launcher completed a full runtime-bound replay on source commit
`359b9279b7718912951a2ce9141d4014f92bbddf`: 37 main proofs, 37 own unfinished-proof
rejections and 105 commands with expected outcomes. The complete command took
23:57.69 with maximum RSS 2,694,052 KiB. See the
[source-bound full record](../evidence/preserved-full-replay-20261111/README.md).

The capture manifest retains its creation-time `NOT_REPLAYED` status and exact
bytes; the later proof result is a separate record bound to that manifest's
SHA-256. This avoids changing a verified package merely to update its status.
The successful replay used the same host OS/runtime dependencies and does not
establish independent-machine reproduction or a standalone OS image.
