# NTRU+768 complete KeyGen replay

Run `./scripts/verify-ntruplus768-keygen-complete.sh` from the repository root.
The report distinguishes generated extraction mains, new authored proof mains,
and selected reused proof mains. Other imported theories are bound by content
hashes and retain their prior proof evidence. No claim is made that all imported
files were freshly replayed. The full result requires all listed proof mains,
semantic end-of-file witnesses, unfinished-proof negative controls, source and
extraction gates, four helper Safety/CT/SCT checks, and both native variants.

`--native-only` reports `NATIVE_PASS`, never full proof `PASS`.
`--defer-safety` adds `_EXCEPT_SAFETY`; the omission remains explicit.
Evidence must be written outside the checkout to a new or empty directory.

The native test uses the pinned official `kem.c` unchanged after a tracing and
API namespace preamble. Its actual CBD, NTT, inversion, serialization, SHAKE and
HashF functions execute. The independent production KeyGen C file calls freshly
compiled Jasmin procedures through transparent trace hooks. The existing inverse
uses its established `-auto-spill-all` build option. Failure output bytes of the
official inverse are unspecified and are not compared; successful inverse
raw words, residues and canonical bytes and all returned statuses are compared.

Each of normal and C-UBSan variants covers 100 official KATs, 64 fresh seeds,
16 independent f/g retry schedules and four output initialization patterns:
1,440 KeyGen calls, 720 actual workspace clears, and 1,440 executions of the
existing Encaps/Decaps with generated keys. It compares exact public/secret key
bytes, all 32-byte RNG requests and seed-expansion results, inverse statuses,
complete DRBG Key/V/reseed-counter state immediately after KeyGen, subsequent
RNG output, output canaries and preserved key inputs. KAT cases
also verify that the RNG state after KeyGen produces the original KAT ciphertext
and shared secret through the actual randomized Encaps API.

The 16 retry schedules intentionally substitute deterministic SHAKE output
buffers. Each fixture is generated and rechecked using actual CBD/shape/NTT/
inverse operations; no inverse status is forced. Fixture hashes are reported.
These tests exercise retry control flow. They are separate from the real-SHAKE
runs and do not estimate sampling or decryption-failure probabilities.

The Python oracle checks actual shape operations, f/g-domain NTT boundaries,
raw NTT words, inverse statuses and successful raw/canonical output, full secret-key concatenation,
and all workspace bytes after the actual clear. It independently checks actual
seed-SHAKE and public-key HashF inputs/outputs against `hashlib.shake_256`.
The separate source-bound compatibility certificate covers f coefficients
`[-2,4]` at index zero and `[-3,3]` elsewhere, g coefficients `[-3,3]`, and the
inverse arithmetic; the earlier trit-only NTT certificate is insufficient here.

Only four new helper slices are checked for Safety/CT/SCT. Existing base inversion
and secret-dependent rejection counts are not claimed CT/SCT. C orchestration,
C memory/ABI correspondence, concrete SHAKE/RNG implementations, whole-machine
erasure, quantitative decryption-failure bounds and IND-CCA security remain
outside these checks. Default checker array initialization assumptions are not
silently removed by functional output-independence proofs. UBSan covers C, not
Jasmin-generated assembly.
