# NTRU+768 complete Encaps and conditional key agreement

`ntruplus/c/768/ref/encap_complete.c` supplies a deterministic Encaps entry
point and its randomized wrapper. They use actual Jasmin procedures with
official C SHAKE256 and an external RNG. The completed Decaps entry point is
documented separately in [the Decaps contract](ntruplus768-decap-complete.md).

## Interfaces and computation

`ntruplus768_encaps_derand(ct, ss, pk, coins)` accepts 1152-byte ciphertext
and 32-byte shared-secret destinations, a 1152-byte public key and 96 input
coin bytes. All four regions must be disjoint and accessible for their full
lengths; `pk` and `coins` are initialized and read-only. Noncanonical public
keys return one and zero both outputs. Accepted keys return zero.

`ntruplus768_encaps(ct, ss, pk)` uses the same three external-region conditions.
It invokes `randombytes` exactly once for 96 bytes before public-key
validation, even when validation rejects. This preserves the official API's
randomness-consumption order. The deterministic entry never requests randomness.

For an accepted key, the native caller performs:

1. HashF: `SHAKE256(0x00 || pk, 32)`.
2. HashH: `SHAKE256(0x02 || coins || HashF(pk), 224)`; its first 32 bytes are
   the candidate shared key, and CBD1 consumes its final 192 bytes.
3. NTT and serialization of the sampled polynomial, followed by
   HashG: `SHAKE256(0x01 || serialized_r, 192)`.
4. SOTP encoding of the coin bytes using that pad, then NTT, the reused
   polynomial multiplication, the new addition procedure, and ciphertext
   serialization. Jasmin copies the first 32 HashH bytes to the shared secret.

The four new support procedures prepare HashF input, copy the shared key,
clear the 13634-byte workspace and clear 96 local coin bytes. Separate
actual-procedure proofs cover the new SOTP encoder and `poly_centered_add`.
The addition output lies in `[-3457,3457)`; serialization selects
the canonical residues. Both CBD1 and SOTP produce trits, discharging the
reused NTT input conditions.

## Deterministic and randomized formal contracts

`ntruplus/proof/768/ref/encap_complete/` connects the actual extracted calls
to `encap_derand_spec` for arbitrary public-key and coin arrays. The checked
deterministic theorem gives exact ciphertext, shared key, status and a zero
workspace array, together with termination under functional and lossless
HashF, HashG and HashH module contracts. Invalid public keys skip all hashes
and preserve their module states.

The randomized model samples coins before calling that deterministic model.
Its relational theorem preserves the output distribution and RNG state
against a specification that calls the same RNG once. The hash modules must
not modify RNG state. This equivalence assumes neither a uniform coin law nor
RNG termination; losslessness is a separate result requiring a lossless RNG.
A further theorem expresses output-event probabilities as the image of any
supplied coin distribution under `encap_derand_spec`. Uniform independent
coins are a possible additional RNG contract, not a proved property of the
native RNG.

Native use requires SHAKE to terminate with the FIPS202 output, and requires
the RNG to initialize exactly the requested coin region, terminate, respect
memory/ABI conditions and implement the specified probabilistic behavior.
Mathematical SHAKE instances establish these contracts for their models only.
The C orchestration, pointer offsets and correspondence with the array caller
remain separate from these extracted-procedure theorems.

## Conditional agreement with Decaps

The theories in `ntruplus/proof/768/ref/kem_agreement/` connect the deterministic
Encaps caller to the complete Decaps caller. Their independently defined
premises require:

- sampled-key polynomial relations with successful inverses;
- the public key and secret-key polynomial blocks to be the corresponding
  serialized values, and the final key suffix to equal `HashF(pk)`;
- the integer decryption lift, for the actual sampled randomness and encoded
  message, to have every coefficient in `[-1728,1728]` (the no-wrap condition).

From these premises, the proof derives canonical key/ciphertext encodings,
guard acceptance, message recovery, equal serialized randomness and HashG
pads, equal HashH inputs, final comparison success and identical shared keys.
It does not assume successful Decaps or matching pads as separate premises.
The proved probability-one caller theorem gives both statuses zero and
equal keys, conditional on the hash contracts and termination.

The no-wrap premise is pointwise. No probability that it holds, numerical
failure bound, unconditional correctness of actual KeyGen, or IND-CCA
security follows from this conditional agreement result.

## Official implementation and cleanup correspondence

The official `3991b2ae08d6f0008d37e41b8aceaaab27b4ec89` implementation fuses
multiplication and addition inside the Montgomery reduction. The new caller
uses the proved multiplication and a separate addition procedure. Their raw
coefficient words need not match. The source-bound arithmetic certificate
checks the official formula, constants and block schedule; interval bounds
justify signed arithmetic and coefficient ranges, and modular congruence
followed by canonical serialization establishes the required byte equality.
The certificate explicitly models intentional Montgomery low-word
truncations. Native tests check final bytes separately. Neither is a C-AST
or binary-equivalence theorem. The earlier trit-input NTT certificate is
reused for both transforms.

The C struct has seven polynomial arrays and all hash buffers, with static
size, alignment and field-offset assertions. Its fields are initialized, and
the actual Jasmin clear runs over all 13634 workspace bytes on both accepted
and rejected paths. The randomized wrapper subsequently clears its own 96
coin bytes; the deterministic caller preserves externally supplied coins.

The clear proofs establish zero arrays for these designated regions. The
array caller's workspace is not a formal representation of every C struct
field, so the composition does not prove complete erasure of native
intermediate secrets. Registers, spills and nested-call workspaces remain
outside the result. C memory/ABI correctness remains an external condition.

## Verification status and remaining scope

The full default replay passed 54 EasyCrypt main files: 26 generated files,
16 new proof files and 12 reused proof files. The new proofs contain 84
lemmas, including the conditional agreement theorem. Checking used
`Proofs:check`, no proof cache and semantic end-of-file guards; three
unfinished-proof controls were rejected. Only the recorded `proof_mains`
inventory is fresh main-level evidence; other imports retain their prior
evidence and are bound by source hashes. The same run passed exact fresh
extraction of all 26 generated files, 14 negative gate controls and six slice
safety/CT/SCT checks. Inputs were unchanged throughout replay.

Each normal and UBSan native run passed:

- 100 official KATs, 1800 deterministic cases and 1700 randomized cases,
  totaling 28200 API calls across both implementations and four initial
  output patterns, plus 1512 Encaps/Decaps roundtrip checks;
- 14100 workspace-clear and 6900 coin-clear calls, checking every designated
  byte after the actual Jasmin procedure returns;
- 3243 independent SOTP encoding cases, 5197 addition cases, 256 fused-product
  cases, 2560 HashF cases, 256 key-copy cases and 14 cases for each clear;
- 264 independent full-API cases, including 200 accepted guards with all
  three actual SHAKE calls checked against Python `hashlib.shake_256`.

The independent oracle checked 79904 assertions per build. Its 256 fused
cases observed 49201 differing raw coefficient words while the prescribed
congruence, ranges and canonical bytes agreed. These differences are expected
and demonstrate why raw-word equality is not the comparison criterion.
SOTP cases cover all 65536 effective head/tail byte pairs across 683 batches,
not every polynomial vector. UBSan instruments C, not assembled Jasmin.
The roundtrip tests do not prove the no-wrap condition or bound its failure
probability.

Replay from the repository root:

```sh
./scripts/verify-ntruplus768-encap-complete.sh
```

Options and evidence details are in
[`tests/ntruplus768/encap_complete/README.md`](../tests/ntruplus768/encap_complete/README.md).
Partial runs retain explicit partial statuses.

Default safety checking assumes initialized exported arrays, including
outputs. This is separate from source absence of incoming-output reads and
functional independence from initial output contents. Slice CT/SCT results
do not establish CT/SCT of the complete mixed API, the external SHAKE or RNG.
The completed Decaps results retain their existing scope; full KEM
correctness and classical-ROM IND-CCA remain separate goals.
