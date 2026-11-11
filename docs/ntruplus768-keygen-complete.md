# NTRU+768 complete KeyGen and accepted-seed distribution

`ntruplus/c/768/ref/keygen_complete.c` provides `ntruplus768_keypair(pk, sk)`
for disjoint writable 1152-byte public-key and 2336-byte secret-key regions.
The API returns zero after both independent inverse-rejection loops finish.
SHAKE256, native RNG behavior, C orchestration and memory/ABI correspondence
remain external proof conditions.

## Actual computation and key provenance

Each f attempt obtains one32-byte seed, expands it to192bytes with
`SHAKE256(seed,192)`, then calls actual CBD1, inplace triple-plus-one shaping,
NTT and polynomial inversion. Each g attempt uses the same seed expansion
and CBD1, with triple shaping only. The entire f loop finishes before the g
loop starts; rejecting g does not resample f. No uniform192-byte source is
substituted for the seed/expansion computation.

After both inverses succeed, actual polynomial products compute h=g*finv and
hinv=f*ginv. Actual serialization produces the public key and two secret-key
polynomial blocks. The reused HashF preparation constructs0x00||pk and native
SHAKE256 supplies32bytes. The new pack procedure concatenates the two1152-byte
blocks and this hash suffix. The new clear overwrites the full14466-byte
workspace before return, including its seed and explicit reserved byte.
Fourteen field offsets, size and two-byte alignment are statically asserted.

The array-call proofs derive the existing `agreement_key_relation` from these
actual operations. They do not assume validity of the entire keypair. The
private instrumented procedure retains proof witnesses; the public procedure
projects only pk/sk and does not publish seeds or intermediate polynomials.
A finite termination proof for the actual inversion core is included.

## Rejection sampling and termination

Let d be the fixed lossless32-byte seed proposal law, with independent draws.
Let expand be the fixed expansion function and A_f/A_g the actual inverse
success predicates applied after expansion and coefficient shaping. The
accepted-buffer law for either loop is exactly

`dmap (dcond d (A_v composed with expand)) expand`.

This includes the seed-conditioned distribution and the deterministic
expansion pushforward. The models prove equality for every output event.
Each loop terminates with probability one when its acceptance mass under d
is positive. Zero acceptance instead gives termination probability zero.
The full iid KeyGen theorem establishes termination and valid-key output
under these explicit positivity, lossless-seed, hash-functionality and
hash-termination conditions. Hash modules are separated from RNG state.
Generic stateful RNG correctness does not alone imply loop termination.

A concrete mathematical instance uses `SHAKE256(seed32,192)`. Positivity for
this fixed function and the chosen seed law remains a premise, not a proved
numerical acceptance bound. Neither native RNG uniformity nor independent
uniform192-byte expansion is inferred. Future ROM/failure analysis must retain
this law or justify a separate idealization, including seed/query collisions.

## Connection to complete Encaps and Decaps

The generated-key witness discharges all key-related premises of the previous
conditional key-agreement theorem. The actual KeyGen--Encaps--Decaps array
composition terminates under the stated iid/positivity/hash assumptions and
satisfies shared-key agreement whenever the existing sufficient integer
no-wrap condition holds for its generated witness and encapsulation coins.
The theorem does not bound the probability that no-wrap fails and is not an
IND-CCA reduction.

## Official arithmetic and implementation boundaries

The new source-bound certificate covers all f pre-NTT coefficients in
[-2,4] at index0 and [-3,3] elsewhere, and all g coefficients in[-3,3].
Official final-sweep pre-Barrett bounds are[-14825,14828] and[-14825,14827],
inside the unique-representative interval[-22470,22470]. Thus the official
and reused Jasmin NTT return the same word representatives on this domain.
For all centered input blocks and192 signed twiddles, the determinant lies
in[-1780,1831], so raw zero and zero residue coincide. Exhaustive comparison
of the two fqinv chains on6913 inputs[-3456,3456] gives equal raw results;
successful inverse outputs lie in[-1777,1777]. These are source-bound integer
certificates and native comparisons, not C-AST equivalence proofs.

The workspace array in the logical caller is a designated clearing target,
not a proved C struct-field representation. Clearing does not establish
register/spill/nested-stack erasure. Native SHAKE/RNG and C memory/ABI remain
external. Inverse-dependent branches retain their prior disclosure boundary;
there is no full KeyGen CT/SCT claim. Default helper safety checks retain
initialized exported-array assumptions, distinct from functional output
independence and the source's absence of incoming-output reads.

## Reproduction and verified scope

Run `scripts/verify-ntruplus768-keygen-complete.sh` with the2026.09 toolchain
selected explicitly through EASYCRYPT/WHY3 when absent from PATH; EC subprocesses
use `OCAMLRUNPARAM=o=20`.

The coherent replay passed31mains:14generated,14new authored and3reused.
New authored theories contain87lemmas. Three unfinished-proof negative
controls,16source/proof gates and31arithmetic source-identity controls passed.
All four new slices passed compilation, extraction and defaultSafety/CT/SCT.
Only these listed proof mains were freshly checked; other imports retain
prior evidence and source hashes.

Normal and UBSan runs each checked100official KATs,64fresh seeds and16controlled
retry schedules at4initial-output patterns. Official and new implementations
combined performed1440KeyGen calls and1440complete Encaps--Decaps roundtrips;
the new implementation cleared its actual workspace720times. The tests compare
the immediate post-KeyGen DRBG state and subsequent bytes, call order, outputs
and canaries. Controlled SHAKE-output retries are explicitly separate from
real-hash tests and exercise actual inversions without replacing their status.
Independent Python tests give4504assertions per build, including real SHAKE
comparison with hashlib. UBSan instruments C, not generated assembly.

The final record contains169commands,619source hashes,31checked main copies
and37native compilation inputs. Exact sources and configurations are recorded
with each replay. No decryption-failure bound, IND-CCA, whole-API CT/SCT or
native C memory-refinement theorem is claimed.
