# NTRU+768 Encaps and conditional agreement replay

Production entry points in `ntruplus/c/768/ref/encap_complete.c`:

- `ntruplus768_encaps_derand(ct, ss, pk, coins)` consumes explicit 96-byte coins.
- `ntruplus768_encaps(ct, ss, pk)` obtains 96 bytes from its external RNG before
  checking the public key, including when the public-key encoding is rejected.

Both use Jasmin kernels with explicit C orchestration, SHAKE256 and memory/ABI
boundaries. The deterministic core clears its 13634-byte workspace on every
return path. The randomized wrapper subsequently clears all 96 sampled coin
bytes. These regions exclude registers, spills and nested callees' workspaces.

```sh
EASYCRYPT=/path/to/easycrypt WHY3=/path/to/why3 \
  ./scripts/verify-ntruplus768-encap-complete.sh --output /tmp/new-encap-evidence
```

`--native-only` skips proofs and reports `NATIVE_PASS`, never full `PASS`.
`--defer-safety` skips the six new safety checks and appends `_EXCEPT_SAFETY`.
The evidence directory must be new/empty and outside the checkout. Full replay
checks exact new/selected-reused main inventories, semantic EOF witnesses,
open-proof negative controls, source snapshots and raw fresh extraction files.
Each proof process starts with `OCAMLRUNPARAM=o=20` unless overridden; this value
and the Z3/single-prover/timeout settings are recorded. `EC_TIMEOUT` defaults
to 60. Only `proof_mains` entries constitute fresh main-level proof execution.
Other imported theories remain bound by source hashes and their prior evidence;
imports do not establish a fresh replay of every imported theorem.

## Native checks

Normal and UBSan builds each verify:

- 100 official KATs against official and new randomized Encaps, with the exact
  official AES DRBG state after key generation. The actual sampled coins also
  drive both deterministic cores. Generated ciphertext/shared-secret bytes
  match exactly, and the existing full native Decaps is used for agreement.
- 1800 deterministic and 1700 randomized input cases across four initial
  ciphertext/shared-secret patterns and both implementations, plus 200 direct
  randomized KAT calls: 28200 API calls total. These include all 768 public-key
  coefficient positions set to each noncanonical boundary 3457/4095, four
  multiple-error inputs, 128 canonical-key mutations and 32 fresh keypairs.
- RNG size/order/count and identical sampled coins; deterministic cores request
  no randomness, while randomized rejection still requests 96 bytes. Rejected
  keys cause no hash calls and return zero ciphertext and shared-secret bytes.
- 14100 real workspace-clear and 6900 real coin-clear calls, with every byte
  examined only after the actual Jasmin clear. Input bytes and buffer canaries
  are preserved. There are 1512 native Encaps/Decaps roundtrip checks.
- 3243 independent SOTP encoding cases compare signed trits with bit-level
  arithmetic and official C, then run the actual SOTP decoder and compare
  Jasmin/official NTT words. All 65536 effective head/tail byte pairs occur
  across 683 batches; this does not enumerate every input vector.
- 5197 centered-add boundary/random cases check modular sums, admitted signed
  ranges and canonical bytes. Another 256 fused-product cases compare the
  official fused operation with Jasmin product plus range correction using
  congruence and canonical serialization. Raw representatives can differ.
- 2560 HashF preparation cases compare `00 || pk` and Python
  `hashlib.shake_256` against official C. Key-copy and both clear kernels have
  separate input/output/canary tests. In 264 complete-API Python cases, 200
  accepted guards compare all three actual SHAKE calls with independent hash
  results and reconstruct the HashG polynomial input through the reference NTT.
- 26 new extraction files are compared by complete inventory and raw bytes.
  Fourteen source/proof/extraction negative controls reject changed RNG size,
  offsets, failure handling, cleanup, unchecked proof text and extraction drift.

The official `3991b2ae08d6f0008d37e41b8aceaaab27b4ec89` fixture is reused from
`decap_guard`. Its `kem.c` body is unchanged. A common preamble namespaces APIs
and traces calls; a fixed wrapper appended in the same translation unit exposes
its actual static deterministic core. Native test hooks invoke the real kernels
and hash/RNG implementations. UBSan instruments C, not assembled Jasmin.

`audit_fused_basemul_add.py` binds the exact official/legacy source and twiddles
and records the arithmetic range/congruence certificate. The comparison is
canonical byte equality; it does not assert equality of every intermediate
word or trace, or a machine proof of C-AST equivalence.

## Claim boundaries

The conditional agreement theorem states explicit key/sampling/serialization
relations and the arithmetic no-wrap condition. KAT roundtrips do not establish
a decryption-failure probability bound. This replay does not complete IND-CCA,
prove the native RNG or SHAKE implementation, or establish whole-API CT/SCT.
Six new kernels are checked for CT/SCT with their stated policies; C orchestration
and the external primitive contracts remain separate. Source initialization
contracts, pure value proofs and the default safety checker's assumptions about
exported arrays must also remain distinct.
