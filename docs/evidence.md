# Historical verification evidence

Some proof runners authenticate earlier verification summaries instead of
replaying every imported theory. A successful historical-evidence check is
**not a fresh proof replay**, and does not certify the current working tree.
See [reproduction](reproduction.md) for the public execution entry point and
[claims](claims.md) for the scope of the research claims.

## Inventory and check

The authoritative records are the existing
`tests/ntruplus768/*/prior-evidence-pins.json` files. Generate a portable
inventory directly from those pins; this command needs only Python 3.10+ and
does not open any external evidence files:

```sh
python3 scripts/check_public_evidence.py > /tmp/ntruplus-evidence-inventory.json
```

The inventory contains evidence-relative paths, expected SHA-256 digests and
the pin manifests requiring each file. It deliberately contains no local
absolute paths, download URLs or invented release identifiers. At the time of
this preparation, 24 pin manifests reference 26 distinct summaries.

After obtaining an evidence bundle, extract it to a directory outside the
checkout. That directory must contain `handoff/verification/`, with the exact
relative paths in the inventory. Authenticate it explicitly:

```sh
python3 scripts/check_public_evidence.py --evidence-root /path/to/evidence-bundle
```

The command rejects missing files, changed bytes, non-PASS summaries, unstable
recorded source/external audits, noncanonical paths, conflicting pins and
symlinked evidence paths. Legacy records without an external audit remain
legacy records. Exit code 0 means the historical summaries match the declared
pins and their recorded audit status; exit code 1 means verification failed.
It does not execute the commands in a summary or trust a path named inside it.

## Preparing a bounded local bundle

The exporter selects files from the repository's pin manifests, rather than
copying a surrounding thesis or work directory. Supply the existing evidence
root explicitly and choose a new output directory outside both input trees:

```sh
python3 scripts/export_public_evidence.py \
  --evidence-root /path/to/original-evidence /path/to/new-evidence-bundle
python3 scripts/check_public_evidence.py \
  --evidence-root /path/to/new-evidence-bundle
(cd /path/to/new-evidence-bundle && sha256sum --check SHA256SUMS)
```

The exporter authenticates all 26 historical summaries and the two separately
pinned KeyGen specification inputs before writing. It refuses existing output
directories, overlapping input/output trees, symlinks, missing files and changed
bytes. The resulting 28 inputs retain their exact bytes and relative paths.
`BUNDLE-MANIFEST.json` records each input's hash, size, kind and consumers, plus
the pin-manifest hashes. `SHA256SUMS` also covers that manifest and the bundle
notice. Extra files referenced inside a summary are not automatically copied or
executed. Repeated exports of the same inputs produce identical bundle files.

This output is a **local release candidate**, not a public upload or a complete
proof archive. Historical records preserve host paths, and the specification
text retains its original rights. Review those before redistribution. Neither
the exporter nor a matching checksum certifies current proofs or licenses the
bundle as a whole. Export regression tests are available with:

```sh
python3 -B -m unittest discover -s tests -p 'test_*public_evidence.py'
```

## What must be preserved

During local preparation on 2026-11-11, all 26 summaries were found and matched
their current pins and recorded PASS audits. Together they occupy 28,267,708
bytes. Their structured `prior_evidence` references point to summaries already
covered by this set. The subsequent bounded exporter copied these summaries
and the two specification inputs into a separately checked local candidate.
It did not copy the private thesis directory, publish a bundle, inspect every
referenced log or rerun the proofs.

The summary dependency chain culminates in:

```text
short-relation-bound -> reduction-cost -> history-refinement -> adaptive-history
                                                                  |
                                                         runtime-bound runner
```

The final runtime-bound runner consumes the historical adaptive-history
summary. A bundle of its prerequisites does not by itself provide a final
runtime-bound replay result.

The 26 summaries are the minimum historical-summary input set, not a complete
research archive. A release should also preserve relevant command logs,
negative-control results, generated statements, toolchain provenance and the
final results being cited. Publish an archive checksum and immutable download
location with the release. No public evidence archive or DOI is declared here.

## Additional specification inputs

The KeyGen generation-law runner separately requires the two records in
[`specification-pins.json`](../tests/ntruplus768/keygen_gen_law/specification-pins.json):

| Kind | Evidence-relative path |
| --- | --- |
| Reviewed contract | `handoff/verification/ntruplus-keygen-gen-law-20261014/specification-contract.json` |
| Extracted source text | `handoff/verification/ntruplus-classical-rom-20261013/research/ntruplus-specification.txt` |

These inputs are outside `check_public_evidence.py`'s historical-summary scope;
the original KeyGen runner authenticates them. Preserve their hashes and
relative paths when making them available. Review the source document's
redistribution terms before bundling extracted text; source availability alone
does not establish permission to redistribute it. If it cannot be bundled,
provide a documented acquisition/extraction procedure that produces the pinned
bytes and verify that procedure independently.

The [official specification page](https://www.ntruplus.org/specification) links
the [July 10, 2026 PDF](https://data.ntruplus.org/NTRU%2B_20260710.pdf).
On 2026-11-11, the downloaded 559,101-byte PDF matched the existing provenance
record's SHA-256, and extraction with Poppler `pdftotext` 22.02.0 produced the
exact pinned 164,278-byte specification text:

```sh
wget -O NTRU+_20260710.pdf 'https://data.ntruplus.org/NTRU%2B_20260710.pdf'
printf '%s  %s\n' '5899bf061d3814c1c003f69df79b13dbea203b2ac7e6ec52f7c35699f020b2bc' 'NTRU+_20260710.pdf' | sha256sum --check -
pdftotext -layout NTRU+_20260710.pdf ntruplus-specification.txt
printf '%s  %s\n' '2e19833445d3c2fcb0abb226234c86b960058b10441e1093657ecf550fc0be27' 'ntruplus-specification.txt' | sha256sum --check -
```

Use new output paths when acquiring these files, then place the verified text
at the evidence-relative path in the table above. This gives recipients an
exact-byte acquisition/extraction procedure without requiring the text to be
redistributed in the artifact. The dated URL is not a promise of immutable
hosting: the hashes reject changed bytes. Public availability does not establish
redistribution permission if the PDF or extracted text is bundled.

## Portability and release gates

Historical summaries contain original absolute paths, command lines and
compiler/prover hashes. Review them and their logs before public distribution.
Do not silently redact or rewrite them: even a whitespace edit changes a pinned
digest. A sanitized replacement needs a separately reviewed provenance record
and an explicit update of every affected pin, not an automatic hash refresh.

Several current full-replay runners compare installed prover binaries with the
hashes in previous summaries. They also require overlap between historical and
current absolute external-input paths. Consequently, supplying the 26 summaries
alone is insufficient to establish portability to a newly installed toolchain
or a different filesystem layout. That compatibility must be demonstrated with
the preserved environment or addressed by a reviewed verifier/provenance
migration. Neither the inventory tool nor the public runner weakens those checks.

Before declaring the release independently reproducible:

1. Supply the reviewed evidence bundle and any additional specification inputs
   with immutable locations and checksums.
2. Preserve or reconstruct the required exact toolchain, and resolve the
   historical absolute-path compatibility requirement without bypassing checks.
3. Run the documented procedure on a separate checkout/environment and retain
   the actual commands, resource measurements and outputs.
4. State which results were freshly checked and which were inherited through
   authenticated historical evidence. Keep partial/source-only runs distinct
   from full runner PASS results.

The historical evidence checker is intentionally a small, dependency-free
preflight. It does not replace the existing source inventories, proof checks,
semantic EOF checks, negative controls or toolchain audits.
