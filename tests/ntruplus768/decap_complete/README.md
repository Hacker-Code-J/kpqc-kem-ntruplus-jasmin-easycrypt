# NTRU+768 complete Decaps replay

The production entry point is `ntruplus768_decaps(ss, ct, sk)` in
`ntruplus/c/768/ref/decap_complete.c`. It uses existing Jasmin entry validation,
candidate-message/r2 calculation and message decoding, new HashH preparation,
CBD1 sampling, final comparison/key selection, and workspace clearing. SHAKE256
uses the immutable official C implementation. This is a mixed C/Jasmin API.

```sh
EASYCRYPT=/path/to/easycrypt WHY3=/path/to/why3 \
  ./scripts/verify-ntruplus768-decap-complete.sh --output /tmp/new-complete-evidence
```

`--native-only` skips proofs and reports `NATIVE_PASS`, never full `PASS`.
`--defer-safety` skips all four new safety analyses and appends
`_EXCEPT_SAFETY`. Evidence must be written into a new/empty directory outside
the checkout. Full replay runs `Proofs:check`, semantic EOF witnesses and
open-proof negative controls without proof caches. Each proof process receives
`OCAMLRUNPARAM=o=20` from process start by default; the value, Z3 choice,
single-prover setting and timeout are recorded. `EC_TIMEOUT` defaults to 60.
No network access or additional Python dependencies are required.

## Scope and memory boundary

The caller provides disjoint regions of 32 writable shared-secret bytes,
1152 readable ciphertext bytes and 2336 readable secret-key bytes. Only the
first 2304 key bytes are checked as canonical polynomials; the final 32 bytes
are consumed as the stored public-key hash. Canonical encoding is not algebraic
key validity.

The wrapper's 13506-byte workspace has static offset, size and alignment
assertions and is aggregate-initialized. It has one cleanup path after either
early rejection or the full normal calculation. A test hook calls the actual
Jasmin clear procedure first, then reads every workspace byte, including final
padding. It never reads workspace bytes before clearing. This checks this
caller-owned region; registers, spills, nested callees' storage and physical
erasure are outside the result. The reused message wrapper separately calls
its existing C `secure_clear` on its own SHAKE input and pad.

New kernel source contracts require readable inputs and promise initialized
outputs. Source contracts and pure value proofs are distinct from the default
safety checker's exported-array initialization assumptions. CT/SCT is checked
for the four new kernels with secret values and no new declassification.
The reused guard has its separately documented canonicality disclosures.
These checks do not prove CT/SCT of the complete C/Jasmin API or SHAKE256.
C orchestration, memory/ABI behavior, and native SHAKE256 remain explicit
boundaries of the modeled composition proof. This is not an IND-CCA proof,
full KEM correctness theorem or C-AST equivalence proof.

## Native evidence

Both ordinary and UBSan builds run the following. UBSan instruments C only,
not assembled Jasmin. Source, extraction, fixture, compiled input and binary
hashes are retained, and replay rejects changes to inputs during execution.

- The official `3991b2ae08d6f0008d37e41b8aceaaab27b4ec89` C/KAT fixture is shared
  with `decap_guard`. Its complete API body remains unchanged; only a common
  test preamble namespaces APIs and traces external dependency calls. The new
  production API is compiled separately, with macros redirecting calls through
  hooks that invoke the actual primitives.
- 100 official KATs regenerate exact keys, ciphertexts and shared secrets.
  Official and new Decaps run on 4622 malformed and 356 canonical-encoding
  inputs, including 32 fresh keypairs, 192 SOTP failures and 32 later comparison
  failures caused by changing the key suffix. Eight initial shared-secret byte
  patterns give 79648 Decaps calls, including 39824 new-API cleanup checks.
- All ciphertext and complete secret-key bytes are preserved. Canaries protect
  all external outputs and inputs. Exact normal/early-rejection call order,
  zero randomness consumption, binary status, failure output zeroing, and
  successful shared-key bytes are checked.
- Independent Python tests compare CBD signed bit differences, official C CBD,
  existing Jasmin/official NTT on generated trits, and canonical serialization
  in 4267 cases. All 65536 two-byte CBD inputs occur across 683 batches; this
  does not enumerate every polynomial vector or every pair at every position.
- HashH preparation has 1280 cases checking `02 || message96 || key_suffix32`
  and Python `hashlib.shake_256` output224 against official C. In 263 full-API
  cases, 260 accepted entry guards exercise the actual HashG1153/output192 and
  HashH129/output224 calls against `hashlib` using captured actual input bytes.
- Final comparison/masking has 18690 cases, including every one of 1152 byte
  positions and all eight mismatch bits with both decoder status values 0/1.
  Direct workspace clearing has 22 fully checked patterns.
- Four new kernels have 22 freshly generated extraction files compared by raw
  bytes and complete file inventory. Thirteen negative controls reject changed
  C wiring, unchecked proofs and extraction drift. Full replay checks new and
  selected directly reused proof mains; it does not rerun every legacy suite.
  Only the exact `proof_mains` list in the result is fresh main-level evidence.
  Other imported theories are bound by source hashes and retain their prior
  evidence; importing them does not establish a fresh main replay for every
  imported theorem.
