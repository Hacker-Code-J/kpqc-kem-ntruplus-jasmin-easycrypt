# NTRU+768 executable Decaps message continuation

`ntruplus768_decap_message` connects the three operations following the `r2`
calculation: serialization, HashG and SOTP decoding. It retains the serialized
`r2` for the later ciphertext comparison and returns a 96-byte candidate
message with a 0/1 SOTP failure flag. A zero flag does not establish final
Decaps success: ciphertext regeneration and comparison can still reject.

## Computation and native interface

The source is `ntruplus/c/768/ref/decap_message.c`, with its public contract in
the adjacent header. Its four arguments are `msg`, `serialized`, `m1` and `r2`:

| Region | Size | Condition |
| --- | --- | --- |
| `msg` | 96 bytes | Writable output |
| `serialized` | 1152 bytes | Writable output, retained for later comparison |
| `m1` | 768 `uint16_t` words | Initialized, aligned, signed coefficients in `{-1,0,1}` |
| `r2` | 768 `uint16_t` words | Initialized, aligned, signed coefficients in `[-3457,3457)` |

All four regions are mutually disjoint and accessible for their full lengths.
The source reads neither output's incoming contents. This native memory
contract is separate from the pure-array statements in EasyCrypt.

The wrapper calls:

1. `decap_message_prepare.jazz`, which calls the existing serializer, writes
   the domain byte `0x01`, and copies the 1152 serialized bytes after it;
2. the official C `shake256`, with exactly 1153 input and 192 output bytes;
3. the existing `poly_sotp_decode.jazz`, with `m1` and the 192-byte pad.

The C hash and headers are pinned to official commit
`3991b2ae08d6f0008d37e41b8aceaaab27b4ec89` in the existing immutable
`tests/ntruplus768/decap_guard/reference/` fixture. The wrapper uses that
fixture's `secure_clear` on its private input and pad arrays before returning.
This checked source order is not a machine-level erasure theorem.

## Formal contract and external SHAKE boundary

The preparation proof under `ntruplus/proof/768/ref/decap_message/` relates
the actual extracted serializer call and prefix-copy loop to their exact
array result, independently of the initial output values, and proves
termination. It returns the canonical 12-bit serialization of `r2` together
with the exact domain-separated SHAKE input.

The SOTP proof under `ntruplus/proof/768/ref/poly_sotp_decode_checked/` verifies
the actual extracted 96-by-8 decoding loop, failure normalization and final
message mask, and proves termination. Its contract equates the result to the existing
independent integer specification: failure occurs exactly when a trit plus
its corresponding upper-pad bit is outside `{0,1}`; failure returns a zero
message, and success returns the packed decoded bits. This proof is separate
from the earlier value-level SOTP results and extraction shape checks.

`DecapMessage(H)` composes the two actual extracted procedures with a hash
module `H`. Its probability-one contract gives:

```text
serialized = poly_tobytes_spec(r2)
pad        = SHAKE256(0x01 || serialized, 192)
msg        = poly_sotp_decode_msg_spec(m1,pad)
flag       = W32.of_int(b2i(poly_sotp_decode_fail_spec(m1,pad)))
```

The premises require exact functional agreement of `H` with SHAKE256 and
losslessness. `MathematicalSHAKE` discharges those premises using the existing
FIPS202 model. It does not identify the native C SHAKE implementation with
that model. Using the theorem for the native continuation additionally
requires the C SHAKE implementation to terminate with those output bytes,
respect its input/output memory extents and preservation conditions, and
respect the native calling convention. The C glue's call/clear order is
source-checked and tested; it is not covered by a C-AST refinement theorem.

The caller model connects guard acceptance, the actual ternary candidate and
the actual `r2` calculation to the decoder's trit and serializer range
premises. Its rejection branch skips SHAKE and preserves the unvisited
message/serialization outputs while retaining the guard's zero shared
secret. On the accepted branch the shared-secret buffer is still unchanged
at this intermediate point, even when SOTP rejects. Later C code performs
the final shared-secret handling.

## Verification status and limits

The full default replay passed 32 EasyCrypt main files: 14 generated files,
10 new proof files containing 50 lemmas, and 8 reused proof files. It used
`Proofs:check`, no proof cache, one prover and semantic end-of-file guards;
two unfinished-proof negative controls were rejected. This is the replayed
main-file inventory, not the number of all transitively imported theories.

The same replay passed compilation, default safety and CT/SCT for the two
Jasmin slices, 14 exact fresh extracted files and 15 negative gate mutations.
Source, checker and command bindings are recorded; inputs were unchanged.
The default safety checker initializes exported array arguments, including outputs.
That checker premise is distinct from the absence of incoming-output reads
and from functional independence of initial output values. CT/SCT results
apply to the declared Jasmin slices and their models, not the C hash, C glue
or complete mixed API.

Normal and UBSan native runs each passed 2582 independent message cases and
8278 raw SOTP cases, including successful and rejected inputs. Python's
`hashlib.shake_256` supplies the independent hash oracle. All 65536 coefficient
word values occur across 86 batches; this is not exhaustive coverage of
vectors or of every value at every coefficient position. UBSan checks C
execution, not the emitted assembly.

Each native run also compares official C, a message-only replacement and the
combined guard/candidate/r2/message replacement on 100 official KATs (300 API
runs), 4622 malformed-encoding triples and 356 canonical-encoding triples.
The latter include 192 SOTP failures and 32 later comparison failures after
SOTP success. Traces bind the actual SHAKE input/output and call order.
HashH, regeneration, comparison, final masking and cleanup outside the
replaced blocks remain official C.

The replay entry is `scripts/verify-ntruplus768-decap-message.sh`; options
and recorded evidence are described in
[`tests/ntruplus768/decap_message/README.md`](../tests/ntruplus768/decap_message/README.md).
Partial runs retain explicit partial statuses. This boundary does not prove
whole Decaps, unconditional recovery of the encapsulated message or
randomness, complete cleanup, full-API CT/SCT, KEM correctness or classical-ROM
IND-CCA security.
