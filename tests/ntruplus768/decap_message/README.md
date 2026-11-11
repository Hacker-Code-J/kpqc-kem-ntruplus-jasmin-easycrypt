# NTRU+768 Decaps message pipeline replay

Run from the repository root:

```sh
EASYCRYPT=/path/to/easycrypt WHY3=/path/to/why3 \
  ./scripts/verify-ntruplus768-decap-message.sh --output /tmp/new-message-evidence
```

`--native-only` skips proofs and reports `NATIVE_PASS`, never full `PASS`.
`--defer-safety` skips both safety analyses and appends `_EXCEPT_SAFETY`.
Full replay checks semantic EOF sentinels with `Proofs:check`, no proof cache,
Z3 and one prover. Every proof process receives `OCAMLRUNPARAM=o=20` by default
from process start; the selected value is recorded. `EC_TIMEOUT` defaults to 60.
The output directory must be empty and outside the checkout. Source snapshots,
binary hashes, commands, logs, both successful and failed statuses are retained.

## What is checked

- Exact source/dependency pins and static native C ABI/call/clear order.
- The immutable official `3991b2ae08d6f0008d37e41b8aceaaab27b4ec89` C/KAT
  fixture shared with `decap_guard`; no network or new runtime dependency.
- Raw fresh extraction and exact seven-file inventory for each of message
  preparation and the existing SOTP source (14 generated files total).
- New and selected reused EasyCrypt mains, semantic final-lemma sentinels,
  open-proof negative controls, and 15 source/extraction/proof gate mutations.
- Compilation, safety, CT and SCT for the two Jasmin procedures. Inputs/outputs
  are secret; there is no new declassification. The source annotations require
  only initialized inputs and promise initialized outputs. The default checker
  may assume initialized exported arrays: a checker pass alone does not remove
  that model premise. The pure value proofs' output independence is separate.
- Native tests under normal compilation and UBSan. UBSan covers C, not assembly.

The native message function calls Jasmin preparation, the pinned official C
SHAKE256, then Jasmin SOTP. Its four external buffers are mutually disjoint:
96 message bytes, 1152 serialized bytes, 768 `u16` message coefficients, and
768 `u16` `r2` coefficients. Word arrays are aligned and initialized. The
preceding pipeline produces signed-trit `m1` and signed `r2` in `[-3457,3457)`.
The wrapper preserves the serialized output for the later verify comparison
and clears its 1153-byte SHAKE input and 192-byte pad using official
`secure_clear`. Static source checking is not a formal erasure proof.

The formal hash composition requires an explicit external SHAKE256 contract.
The C glue and SHAKE implementation are not machine-proved by these Jasmin
checks; whole mixed-API CT/SCT, C-AST equivalence, complete Decaps and IND-CCA
are outside this result.

## Native coverage

Each normal/UBSan run includes:

- 100 official KATs for official C, message-only replacement and the combined
  guard/candidate/r2/message replacement (300 API runs).
- 4622 malformed-encoding API triples; the message stage must be skipped.
- 356 canonical-encoding API triples, including 32 fresh keypairs, 192 SOTP
  failures and 32 failures occurring after successful SOTP at final comparison.
- Exact exported call order, actual SHAKE prefix byte `01`, input length 1153
  and output length 192; all input bytes and surrounding canaries preserved.
- 2582 independent message cases. Python builds the coefficient bit stream,
  obtains the pad with `hashlib.shake_256`, and decodes bits independently.
  It compares both actual native message calls and the three official C calls,
  including captured actual SHAKE input/output bytes.
- 8278 raw SOTP cases: every coefficient position with boundary values and
  both pad-bit settings, randomized inputs, and every one of the 65536 word
  values across 86 batches. This is not an exhaustive test of all vectors or
  every word at every position. Successful and rejected cases are both required.

The full-API generated bodies replace only fixed exact blocks. HashH,
regeneration, final comparison, output masking, cleanup and return remain
byte-for-byte official C after the replacement boundaries. The trace observes
exported Jasmin calls, not internal Jasmin loads or individual instruction
counts. The independent test suite uses only Python standard-library modules.
