# Formosa location and exact-file licensing evidence

The original repository moved to
[`formosa-crypto/formosa-libjade`](https://github.com/formosa-crypto/formosa-libjade).
The old URL now serves an archived move notice. A fresh fetch from the successor
returned the original pin `475b87434506280fdfa1a1ba5da0af3787e00579` and tree
`609f884ab7abcf7baf6f57f53687c2087c8fbfe9`, identical to the existing dependency
([acquisition record](formosa-acquisition.json)). The Gitlink and local path
`external/formosa-mlkem` are unchanged.

The later successor revision
[`589038b`](https://github.com/formosa-crypto/formosa-libjade/tree/589038bbae572525ff6a8281f6bc07fa5a31ff7b)
has an explicit `CC0-1.0 OR Apache-2.0` declaration. We compared every `.ec`
file under the old `proof/eclib/` subtree with all non-`bench/` blobs in that
licensed revision. The [file-by-file record](formosa-helper-matches.json)
contains old and new paths, Git blob IDs, SHA-256 values and source links.

Five of the 21 files have exact-byte copies in that later licensed revision:

- `Fastexp.ec`
- `For.ec`
- `IntDiv_extra.ec`
- `Jcheck.ec`
- `barrett_mlkem_general.ec`

The other 16 do not have identical blobs there, including directly used
`Montgomery.ec` and `W16extra.ec`. The later declaration is therefore recorded
only for the five exact matches, without assigning it retroactively to the old
revision or treating the entire old helper set as resolved. The nested
`crypto-specs` repository has its own CC0 notice; that does not license the
parent repository's helpers.

The exact later [upstream declaration](../../LICENSES/formosa-libjade/UPSTREAM-LICENSE.txt),
[CC0 text](../../LICENSES/formosa-libjade/CC0-1.0.txt),
[Apache 2.0 text](../../LICENSES/formosa-libjade/Apache-2.0.txt) and
[contributors list](../../LICENSES/formosa-libjade/CONTRIBUTORS.md) are preserved.
Their Git blob identities and digests are in the comparison record. The
contributors list is project-wide, not an authorship claim for every file.

No helper, proof pin or historical evidence was edited. The source distribution
continues to obtain this dependency separately at its exact pin. Packaging its
old helper sources into an additional distribution would require establishing
the applicable terms for the unmatched files rather than extrapolating from
the five matches.
