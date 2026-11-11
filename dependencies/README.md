# Pinned crypto-specs recovery

The former `formosa-crypto/crypto-specs` URL now contains an official move notice.
On 2026-11-12, neither its old endpoint nor the successor exposed the required
commit `fb050598ed356c5c6604d92a1e198b2dd4543777` through the inspected commit API.
This bundle preserves that exact locally retained upstream commit rather than
substituting a different specification revision.

- File: `crypto-specs-fb050598ed35.bundle`
- SHA-256: `3ace5d093cfb85db338d5b4ff24d09fa84e3bd704ad01a3e7cf2aa92a69671e5`
- Size: 336,063 bytes
- Commit: `fb050598ed356c5c6604d92a1e198b2dd4543777`
- Tree: `1c21500d8893456787cdc52fdfde8a50f429fcff`

The [origin manifest](crypto-specs-origin.json) contains the 136 file hashes and
verification results. A fresh offline clone and detached checkout reproduced
all files exactly. The bundle includes only history reachable from this pin;
it contains no local Git configuration, credentials or unrelated branch refs.

The original [CC0 1.0 notice](../LICENSES/crypto-specs/CC0-1.0.txt) is retained.
Its Git blob is unchanged in all 126 preserved reachable commits, including the
initial commit. Original file-level notices remain in the bundle. These notices
apply to this separate repository, not to Formosa's parent `proof/eclib` helpers.

From the NTRU+ repository root, restore into a fresh, empty dependency path:

```sh
printf '%s  %s\n' '3ace5d093cfb85db338d5b4ff24d09fa84e3bd704ad01a3e7cf2aa92a69671e5' 'dependencies/crypto-specs-fb050598ed35.bundle' | sha256sum --check -
git clone --no-checkout dependencies/crypto-specs-fb050598ed35.bundle external/formosa-mlkem/crypto-specs
git -C external/formosa-mlkem/crypto-specs checkout --detach fb050598ed356c5c6604d92a1e198b2dd4543777
```

Keep an existing verified checkout at this exact pin instead of overwriting it.
The immutable tested source archive predates this recovery bundle; it can use
the bundle supplied in the publication companion by passing its absolute path
to `git clone`. See the [current reproduction guide](../docs/reproduction.md).
