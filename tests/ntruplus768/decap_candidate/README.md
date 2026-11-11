# NTRU+768 Decaps candidate calculation

Run from the repository root:

```sh
EASYCRYPT=/home/hacker-code-j/.opam/cryptotools-2026.09/bin/easycrypt \
WHY3=/home/hacker-code-j/.opam/cryptotools-2026.09/bin/why3 \
./scripts/verify-ntruplus768-decap-candidate.sh
```

Override the tool paths for another installation. The replay keeps commands,
versions, input hashes, source copies with EOF guards, extraction, assembly,
native executables and logs in a new directory outside the checkout. `--output`
selects a new or empty directory. `--native-only` omits EasyCrypt and reports
`NATIVE_PASS`, never a full proof pass. Safety analysis of the whole inlined
calculation can take tens of minutes. `--defer-safety` deliberately omits only
that analysis and reports `PASS_EXCEPT_SAFETY` (or
`NATIVE_PASS_EXCEPT_SAFETY` with `--native-only`), with `safety_replayed=false`.
It never accepts a cached safety result or reports a full pass. A separate
fresh safety run must still be checked against exactly the same source,
transitive dependencies, checker binary and command, retaining its complete
log, before claiming that the combined verification is complete.

The native interface is
`void jade_ntruplus_ntruplus768_amd64_ref_decap_candidate(uint16_t *rp,
const uint16_t *cp, const uint16_t *fp)`. It uses three disjoint, two-byte-aligned
1536-byte regions. Inputs are initialized with canonical coefficients
`0 <= x < 3457`; output need not be initialized. The result has signed
coefficients in `{-1,0,1}`. Output values are compared with the official C
sequence `poly_basemul; poly_invntt; poly_crepmod3`. This is the candidate
polynomial, not a proof that every ciphertext yields the original message.

The immutable official source and KAT are reused from
`../decap_guard/reference`, pinned to commit
`3991b2ae08d6f0008d37e41b8aceaaab27b4ec89`; no second fixture copy is maintained.
The bounded compatibility audit records that the selected baseline inverse
body differs by its initial copy, that the scalar mod3 body is identical,
that disjoint-input multiplication formulas agree after temporary substitution,
and that multiplication twiddles agree. It does not establish C-AST or trace
equivalence; the Jasmin inverse retains its out-of-place copy and scratch.
Source hashes, native differential execution and extracted-procedure proofs
are separate evidence.

Each normal and UBSan native run checks:

- 69,428 canonical input pairs: constant boundaries, six boundaries at every
  coefficient in each input, all 3,457 canonical values at eight terminal-block
  lanes of both inputs, 768 sparse pairs, and 4,096 random pairs;
- exact 768-word output equality and ternary range, complete input preservation,
  disjointness, alignment and adjacent canaries;
- all 100 official KATs across three implementations (300 API transcripts),
  4,622 malformed-input triples, and 356 canonical-encoding triples, including
  32 fresh key generation/encapsulation pairs.

The three API variants are original C, C with only the exact three-call
candidate block replaced, and C with both the prior Jasmin entry guard and the
candidate block substituted. All remaining official bytes, including later
failure selection and cleanup, are preserved. Instrumentation checks that the
candidate is called exactly once after encoding acceptance and never after
rejection, preserves the remaining dependency-call order, and consumes no
randomness in Decaps. One Jasmin export is one native trace event; this is not
an observation of its internal branch or load trace. The unchanged official
KAT RNG/AES retain their upstream compiler warnings; authored C builds with
`-Werror`. UBSan instruments C, not Jasmin assembly.

Candidate CT/SCT treats all coefficient values as secret and uses no
declassification. The optional guard+candidate API regression inherits the
previous guard's two key-canonicality-bit disclosures; it does not prove
constant time for the remaining C implementation. The default safety checker models all exported array arguments as
initialized, including the mutable destination. Its result alone does not
show that incoming output contents are unnecessary. The candidate source's
write-only destination path establishes that property separately, and the
functional theorem is independent of arbitrary initial output values.
Native tests initialize outputs to observe that every returned word is written.

Proof replay uses `Proofs:check`, `-no-eco`, reviewed source hashes and semantic
EOF guards on hand-authored mains. Generated extraction files use a structural
EOF guard and must match a fresh extraction byte-for-byte. Mutated source,
reference splice, extraction and proof escapes are rejected by the gate tests;
a copy of the final proof with its last `qed` removed must also be rejected.
Imported dependencies are hashed; only the proof mains listed in the summary
are separately replayed. The complete Decaps procedure, probabilistic message
recovery, retry behavior, erasure and classical-ROM IND-CCA reduction remain
outside this test's claim.
