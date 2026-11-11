# Preserved environment: attribution, notices and source materials

This companion attributes the 3,145 files in `../preserved-inputs.json` and
preserves the available original notices. It does not modify the preserved
environment, authorize redistribution, or establish a reproducible binary build.

## Read the inventory

- [generated/COMPONENTS.md](generated/COMPONENTS.md) is the readable component,
  version, recorded-license and file-count table.
- [generated/files.json](generated/files.json) maps every captured path and hash
  to a component and the evidence used for that assignment. It retains the
  distinction between historically pinned inputs and separately observed `.eca`
  library sources from the preserved environment manifest.
- [generated/inventory.json](generated/inventory.json) records component versions,
  metadata-declared licenses, source URLs and checksums, notices, retained source
  identities, available source materials and remaining gaps.
- [generated/embedded-components.json](generated/embedded-components.json) records
  defined OCaml/native symbols found in the main EasyCrypt, Why3 and Coq binaries.
  Module names are matched to installation records, with confidence and limits.
- `generated/notices/` contains original notice bytes, deduplicated by SHA-256.
  Some packages carry their notice in source headers; the entire original
  source file is retained when no standalone notice is available.
- `generated/evidence/` contains the original installed opam metadata, installation
  records, switch state, Debian control/copyright evidence and source comparison
  records. Each inventory reference gives the original location and digest.

The opam file assignments use exact `.opam-switch/install/*.changes` entries
and registered installed versions. Matching `.install` files and package `opam`
metadata are preserved. File association records contain size/time information;
they are not falsely treated as content hashes. The captured opam-owned bytes
are also compared to the actual installed files before attribution.

The historical Python and `env` binaries are matched to the payloads of their
exact preserved Debian packages. Their newer host installations are not used
as the historical owners. Bash is matched to its installed dpkg ownership and
payload checksum, with that evidence distinguished from signed package
authentication. Local configuration and retained source files receive explicit
separate classifications.

## Source-material companion

The separate local source-material package is prepared under
`artifact-release-preparation/provenance-20261112/environment/source-companion/`.
Its `source-materials.json` maps source blobs to components and original
registered build/install metadata. Source blobs are deduplicated by SHA-256.

The materials include exact cached upstream archives; labelled source snapshots
from clean pinned Git revisions; the authenticated Jasmin release archive; all
registered cached opam patch/extra-source files found for these components; and
the exact historical calibration file with its upstream notices. Original
archives are preserved without repacking. Generated Git snapshots are identified
separately, and submodule entries are checked and recorded.

The Bitwuzla OCaml binding archive contains five top-level solver source trees:
Bitwuzla, CaDiCaL, Kissat, CryptoMiniSat and SymFPU. The nested PicoSAT sources
inside CryptoMiniSat have their own component, notice and source record. Source
presence, explicit recipe linkage and actual defined-symbol observations are
separate fields; none is silently substituted for another. Every archived
file in those trees is compared to the retained package source. Their source
versions and byte coverage are recorded separately from binary symbol evidence.
The comparison does not prove that the preserved executable was built from those
exact source bytes or options.

The original opam `patches` expressions and `extra-source` records are retained.
Conditional version strings are not interpreted as patch filenames. A component
with missing source materials or unresolved patch inputs is reported explicitly.
The system Debian source-package companion is separate; this inventory does not
assert those source downloads or their signature checks have completed.

The exact pending system source packages are Bash `5.1-6ubuntu1.1`, coreutils
`8.32-4.1ubuntu1.3`, and Python `3.10.12-1~22.04.15`. Their source payloads have
not been downloaded because both Ubuntu endpoints failed DNS resolution in
this execution environment. The separate `system-sources/` companion contains
the signed-index acquisition recipe and its offline checks. The recorded
[acquisition status](generated/system-source-status.json) is included here;
the cached signed index is not represented as downloaded source packages.

## Findings that must remain visible

- The EasyCrypt source license is MIT at the recorded upstream revisions. Its
  opam metadata still says CeCILL-C. Both original statements are preserved as
  an upstream metadata discrepancy; this is not asserted to be dual licensing.
- The calibration `List.ec` is the exact upstream file at
  `b682e63f4ba9eed9220eb763fa73baa8f663046b`. It differs from the installed library
  at `2aaa14acf7b2ce234b475f24f9e85ba0bdaeb024`. File-level identification does not
  identify the whole unpacked local tree.
- Defined solver/module symbols establish embedded code observations, not a
  complete dependency or license closure. Native plugins and system executable
  embedded components are not exhaustively analyzed. CryptoMiniSat's original
  notice contains conditional GPL provisions whose build applicability is not
  resolved by symbol presence. The retained wrapper recipe explicitly selects
  CryptoMiniSat and PicoSAT through Dune; CMake's `MIT` option is not taken as
  evidence of the preserved binary's options. Original build logs are unavailable.
- Source archives, build recipes and notices alone do not establish exact
  corresponding-source completeness for every binary. Conditional dependencies,
  local patches, build options and system runtime dependencies remain separately
  reviewable requirements. No new compiler/proof replay is claimed here.

## Verify and regenerate

From `generated/`, run `sha256sum --check --quiet SHA256SUMS`. The source-material
companion has its own checksum file. Detailed validation is recorded separately
under `artifact-release-preparation/provenance-20261112/environment/`.

To regenerate from the same local installations and authenticated capture,
choose new output directories and run from the repository root:

```sh
python3 -B -m unittest discover -s env/distribution -p test_inventory.py -v
python3 -B env/distribution/inventory.py \
  --manifest env/preserved-inputs.json \
  --capture /path/to/preserved-environment \
  --calibration-evidence /path/to/calibration-list \
  --system-source-status /path/to/system-sources/ACQUISITION-STATUS.json \
  --output /path/to/new-notice-companion \
  --source-output /path/to/new-source-material-companion
```

The generator uses Python's standard library and the already installed `git`,
`dpkg-query`, `dpkg-deb` and `nm` tools. It performs no downloads or package
installation. It rejects existing output directories, verifies capture and
source-archive hashes, and reads archive members without extracting them into
the working tree. The local opam installation records are inputs to provenance
inspection; ordinary artifact users can read the generated companion without
having those private installation paths.
