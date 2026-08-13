# kpqc-sig-ntruplus-jasmin-easycrypt

This repository is a workspace for developing and checking Jasmin and
EasyCrypt artifacts for NTRU+.

## NTRU+768 baseline

The imported NTRU+768 C reference implementation and KAT are rooted at
`NTRU+/NTRU+768` and `NTRU+/KAT/NTRU+768`. They byte-match the corresponding
trees at upstream NTRU+ commit
[`38201624477a7dbb2f46d1ae7686ae5ceee4eb80`](https://github.com/ntruplus/ntruplus/commit/38201624477a7dbb2f46d1ae7686ae5ceee4eb80).

Build the reference KEM, run its functional test, regenerate the deterministic
KAT, and compare it byte-for-byte with the imported response file:

```sh
./scripts/verify-ntruplus768-baseline.sh
```

## First verified slice: NTRU+768 `basemul`

The scalar Jasmin implementation at `ntruplus/jasmin/768/ref/basemul.jazz`
matches the defined signed-32-bit domain of
`NTRU+/NTRU+768/ntt.c::basemul`. The verification surface includes:

- Jasmin compilation and automatic memory-safety checking;
- cryptographic constant-time and speculative constant-time checking;
- deterministic C/Jasmin differential testing, including UBSan;
- reproducible `jasmin2ec` extraction; and
- an EasyCrypt total functional-correctness proof against an explicit
  word-level specification, followed by a mathematical quotient-ring bridge.

Run the complete slice check with:

```sh
./scripts/verify-ntruplus768-basemul.sh
```

The EasyCrypt proof is split into two layers. The first covers exact word-level
behavior of the isolated four-coefficient kernel. The second interprets signed
words as integers and proves the four coefficient congruences for multiplication
in `Z_q[X]/(X^4-zeta)`, with `q = 3457`. The bridge assumes every input
coefficient and the supplied twiddle lie in `[-q, q)`, and that the supplied
twiddle represents the mathematical `zeta` in Montgomery form. It also proves
that each result lies in `[-q, q)`.

This does not yet prove that every caller establishes those range and twiddle
preconditions or the KEM. The C/Jasmin correspondence also assumes distinct
output and input buffers, which is how the current `poly_basemul` call sites
use the kernel.

## Full verified slice: NTRU+768 `poly_basemul`

The scalar Jasmin implementation at `ntruplus/jasmin/768/ref/poly_basemul.jazz`
matches the full 96-iteration `NTRU+/NTRU+768/poly.c::poly_basemul` loop at the
word level. Each iteration consumes one twiddle from `zetas[96..191]` and
applies two four-coefficient `basemul` blocks, first with `zeta` and then with
`-zeta`, covering all 192 four-coefficient blocks in the 768-coefficient
polynomial.

Run the complete loop check with:

```sh
./scripts/verify-ntruplus768-poly-basemul.sh
```

The EasyCrypt development for this slice is again split into two layers. The
word-level proof shows exact agreement with the extracted Jasmin procedure for
all 96 iterations. The algebra layer lifts each of the 192 output blocks into
`Z_q[X]/(X^4-zeta_k)` using the shared NTRU+768 NTT schedule theorem described
below. Its only remaining data precondition is that every input coefficient
lies in `[-q, q)`.

Under that assumption, every output coefficient is again in `[-q, q)`, and
each block satisfies the expected four coefficient congruences modulo `q = 3457`.

## First executable forward-NTT slice: initial split

The scalar Jasmin procedure at `ntruplus/jasmin/768/ref/ntt_stage1.jazz`
implements the first loop of `NTRU+/NTRU+768/ntt.c::ntt`. It consumes
`zetas[1] = -1033` and transforms all 384 pairs `(a[i], a[i+384])`. A
fail-closed source checker pins the C twiddle index and butterfly data flow to
the standalone Jasmin slice, and its self-check rejects representative twiddle,
index, and sign mutations.

Run the complete initial-split check with:

```sh
./scripts/verify-ntruplus768-ntt-stage1.sh
```

The check covers reproducible `jasmin2ec` extraction, exact word-level
functional correctness, losslessness, Jasmin safety, CT and SCT analysis, and
C-oracle differential tests over 8 boundary and 4096 deterministic random
vectors. The differential suite exercises both distinct buffers and the
in-place call shape used by the reference transform.

The algebra layer connects `-1033` to schedule entry 1 and therefore to the
mathematical root `zeta_root^96`. Assuming every input coefficient is in
`[-q, q)`, it proves the two butterfly congruences modulo `q = 3457`. It also
proves the explicit bounds `[-2q, 2q)` for the low half and `[-3q, 3q)` for
the high half, providing the range contract needed by the next transform
layer.

This slice is deliberately only the initial cyclotomic split. It does not yet
include the following radix-3 layer, the five radix-2 layers, their composition
into the complete forward transform, or `invntt`. The EasyCrypt model proves
array-value behavior; in-place pointer aliasing is covered by Jasmin's safety
check and the machine-level differential suite rather than a separate formal
aliasing theorem.

## Executable forward-NTT radix-3 layer

The in-place scalar procedure at `ntruplus/jasmin/768/ref/ntt_radix3.jazz`
implements the second loop of `NTRU+/NTRU+768/ntt.c::ntt`. Its two 128-lane
blocks consume `zetas[2..5] = {-682, -248, -708, 682}` and use
`NTRUPLUS_OMEGA = -886`. The standalone boundary accepts the widened output of
the initial split instead of duplicating the already verified stage-1 code.

Run the complete radix-3 check with:

```sh
./scripts/verify-ntruplus768-ntt-radix3.sh
```

The check covers reproducible extraction, exact word-level correctness and
losslessness, Jasmin safety, CT and SCT analysis, and fail-closed coupling to
the C twiddle order and butterfly data flow. Differential and UBSan tests cover
10 boundary vectors, 4096 direct radix-3 vectors, and 2048 vectors chained
through the Jasmin stage-1 slice; the chained suite exercises both the original
disjoint stage-1 call and its in-place caller shape.

The algebra layer ties the four twiddles to root exponents `32`, `64`, `160`,
and `320`, and ties `OMEGA` to exponent `192`. Assuming the stage-1 contract
(`[-2q,2q)` on indices below 384 and `[-3q,3q)` on the upper half), it proves
the Montgomery input bounds, the three radix-3 butterfly congruences for every
triple, and exact signed output bounds `[-4q,4q)` for the first block and
`[-5q,5q)` for the second.

This layer remains a standalone in-place array-value theorem. A later
composition theorem will connect it with stage 1 and all five standard
radix-2 layers into a complete forward transform.

## Executable forward-NTT radix-2 `step=64` layer

The in-place scalar procedure at
`ntruplus/jasmin/768/ref/ntt_radix2_64.jazz` implements the first iteration of
the final loop in `NTRU+/NTRU+768/ntt.c::ntt`. Its six 64-pair blocks consume
`zetas[6..11] = {1, -722, -723, -257, -1124, -867}` at bases `0`, `128`,
`256`, `384`, `512`, and `640`. The standalone boundary accepts the widened
output contract of the verified radix-3 layer.

Run the complete `step=64` check with:

```sh
./scripts/verify-ntruplus768-ntt-radix2-64.sh
```

The check covers reproducible extraction, exact word-level correctness and
losslessness, Jasmin safety, CT and SCT analysis, and fail-closed coupling to
the C prefix, twiddle order, Montgomery reduction, Barrett reduction, pair
offsets, and butterfly stores. Differential and UBSan tests cover 15 boundary
vectors, 4096 direct `step=64` vectors, and 2048 vectors chained through the
Jasmin stage-1 and radix-3 slices; both disjoint and in-place stage-1 caller
shapes are exercised.

The algebra layer ties the six twiddles to root exponents `16`, `112`, `208`,
`80`, `176`, and `272`. Assuming the radix-3 contract (`[-4q,4q)` below index
384 and `[-5q,5q)` at and above index 384), it proves the Montgomery product
bounds, absence of signed-word wrap in every butterfly input, the two output
congruences modulo `q = 3457`, and the centered Barrett output range
`[-1728,1728]` for every coefficient.

This layer is also a standalone in-place array-value theorem. The `step=32`
layer below consumes its centered output contract; a full composition theorem
and the remaining `step=16`, `8`, and `4` layers remain separate milestones.

## Executable forward-NTT radix-2 `step=32` layer

The in-place scalar procedure at
`ntruplus/jasmin/768/ref/ntt_radix2_32.jazz` implements the second iteration of
the final loop in `NTRU+/NTRU+768/ntt.c::ntt`. Its twelve 32-pair blocks
consume `zetas[12..23]` at bases `0`, `64`, ..., `704`, preserving the same
signed multiply, Montgomery reduction, promoted butterfly, and centered
Barrett data flow as the C implementation.

Run the complete `step=32` check with:

```sh
./scripts/verify-ntruplus768-ntt-radix2-32.sh
```

The check covers reproducible extraction, exact word-level correctness and
losslessness, Jasmin safety, CT and SCT analysis, and fail-closed coupling to
the C prefix, twiddle order, pair offsets, helper bodies, and twelve-block call
schedule. Differential and UBSan tests cover 16 boundary vectors, 4096 direct
`step=32` vectors, and 2048 vectors chained through the Jasmin stage-1,
radix-3, and `step=64` slices; both disjoint and in-place stage-1 caller shapes
are exercised.

The algebra layer ties the twelve twiddles to root exponents `8`, `152`, `56`,
`200`, `104`, `248`, `40`, `184`, `88`, `232`, `136`, and `280`. Assuming
exactly the centered output contract established for `step=64`, an explicit
bridge derives this precondition from the `step=64` algebra relation. The
layer then proves the Montgomery product bounds, absence of signed-word wrap,
both butterfly congruences modulo `q = 3457`, and the centered Barrett output
range `[-1728,1728]` for every coefficient.

This layer remains a standalone in-place array-value theorem. The downstream
`step=16`, `8`, and `4` layers, a composition theorem for the complete forward
transform, and executable `invntt` correctness are separate milestones.

## Executable forward-NTT radix-2 `step=16` layer

The in-place scalar procedure at
`ntruplus/jasmin/768/ref/ntt_radix2_16.jazz` implements the third iteration of
the final `for (step = 64; step >= 4; step >>= 1)` loop in
`NTRU+/NTRU+768/ntt.c::ntt`. Its 24 16-pair blocks use bases `0`, `32`, ...,
`736` and consume exactly
`zetas[24..47] = {-455, 639, 502, 655, -699, 541, 95, -1577, -1241, 550, -44, 39, -820, -216, -121, -757, -348, 937, 893, 387, -603, 1713, -1105, 1058}`.
The standalone slice preserves the same signed multiply, Montgomery reduction,
promoted butterfly, and centered Barrett data flow as the C implementation.

Run the complete `step=16` check with:

```sh
./scripts/verify-ntruplus768-ntt-radix2-16.sh
```

The check covers reproducible extraction, exact word-level correctness and
losslessness, the indexed algebra bridge, Jasmin safety, CT and SCT analysis,
and fail-closed coupling to the C prefix, twiddle order, pair offsets, helper
bodies, and 24-block call schedule. Differential and UBSan tests cover 24
boundary vectors, 4096 direct `step=16` vectors, and 2048 vectors chained
through the Jasmin stage-1, radix-3, `step=64`, and `step=32` slices; both
disjoint and in-place stage-1 caller shapes are exercised.

The algebra layer ties the 24 twiddles to root exponents
`4`, `148`, `76`, `220`, `28`, `172`, `100`, `244`, `52`, `196`, `124`, `268`,
`20`, `164`, `92`, `236`, `44`, `188`, `116`, `260`, `68`, `212`, `140`, and
`284`. Assuming exactly the centered output contract established for
`step=32`, an explicit bridge derives the precondition from the `step=32`
algebra relation. The layer proves the Montgomery product bounds, absence of
signed-word wrap in every butterfly input, both output congruences modulo
`q = 3457`, and the centered Barrett output range `[-1728,1728]` for every
coefficient.

This layer remains a standalone in-place array-value theorem. The downstream
`step=8` and `step=4` layers, full forward-NTT composition, and executable
`invntt` correctness remain separate milestones.

## Executable forward-NTT radix-2 `step=8` layer

The in-place scalar procedure at
`ntruplus/jasmin/768/ref/ntt_radix2_8.jazz` implements the fourth iteration of
the final `for (step = 64; step >= 4; step >>= 1)` loop in
`NTRU+/NTRU+768/ntt.c::ntt`. Its 48 8-pair blocks use bases `0`, `16`, ...,
`752` and consume exactly
`zetas[48..95] = {1449, 837, 901, 1637, -569, -1617, -1530, 1199, 50, -830, -625, 4, 176, -156, 1257, -1507, -380, -606, 1293, 661, 1428, -1580, -565, -992, 548, -800, 64, -371, 961, 641, 87, 630, 675, -834, 205, 54, -1081, 1351, 1413, -1331, -1673, -1267, -1558, 281, -1464, -588, 1015, 436}`.
The standalone slice preserves the same signed multiply, Montgomery reduction,
promoted butterfly, and centered Barrett data flow as the C implementation.

Run the complete `step=8` check with:

```sh
./scripts/verify-ntruplus768-ntt-radix2-8.sh
```

The check covers reproducible extraction, exact word-level correctness and
losslessness, the indexed algebra bridge, Jasmin safety, CT and SCT analysis,
and fail-closed coupling to the C prefix, twiddle order, pair offsets, helper
bodies, and 48-block call schedule. Differential and UBSan tests cover 32
boundary vectors, 4096 direct `step=8` vectors, and 2048 vectors chained
through the Jasmin stage-1, radix-3, `step=64`, `step=32`, and `step=16`
slices; both disjoint and in-place stage-1 caller shapes are exercised.

The algebra layer ties the 48 twiddles to root exponents
`2`, `146`, `74`, `218`, `38`, `182`, `110`, `254`, `14`, `158`, `86`, `230`,
`50`, `194`, `122`, `266`, `26`, `170`, `98`, `242`, `62`, `206`, `134`,
`278`, `10`, `154`, `82`, `226`, `46`, `190`, `118`, `262`, `22`, `166`,
`94`, `238`, `58`, `202`, `130`, `274`, `34`, `178`, `106`, `250`, `70`,
`214`, `142`, and `286`. Assuming exactly the centered output contract
established for `step=16`, an explicit bridge derives this precondition from
the `step=16` algebra relation. The layer proves the Montgomery product
bounds, absence of signed-word wrap in every butterfly input, both output
congruences modulo `q = 3457`, and the centered Barrett output range
`[-1728,1728]` for every coefficient.

This layer remains a standalone in-place array-value theorem. The final
`step=4` layer below consumes its centered output contract, and the composed
wrapper section immediately after it closes the full forward executable.

## Executable forward-NTT radix-2 `step=4` layer

The in-place scalar procedure at
`ntruplus/jasmin/768/ref/ntt_radix2_4.jazz` implements the final iteration of
the `for (step = 64; step >= 4; step >>= 1)` loop in
`NTRU+/NTRU+768/ntt.c::ntt`. Its 96 4-pair blocks cover bases `0`, `8`, ...,
`760`, for 384 butterflies total, and consume exactly
`zetas[96..191] = {223, 1138, -1059, -397, -183, 1655, 559, -1674, 277, 933, 1723, 437, -1514, 242, 1640, 432, -1583, 696, 774, 1671, 927, 514, 512, 489, 297, 601, 1473, 1130, 1322, 871, 760, 1212, -312, -352, 443, 943, 8, 1250, -100, 1660, -31, 1206, -1341, -1247, 444, 235, 1364, -1209, 361, 230, 673, 582, 1409, 1501, 1401, 251, 1022, -1063, 1053, 1188, 417, -1391, -27, -1626, 1685, -315, 1408, -1248, 400, 274, -1543, 32, -1550, 1531, -1367, -124, 1458, 1379, -940, -1681, 22, 1709, -275, 1108, 354, -1728, -968, 858, 1221, -218, 294, -732, -1095, 892, 1588, -779}`.
The standalone slice preserves the same signed multiply, Montgomery reduction,
promoted butterfly, and centered Barrett data flow as the C implementation.

Run the complete `step=4` check with:

```sh
./scripts/verify-ntruplus768-ntt-radix2-4.sh
```

The check is fail-closed on tools, dependency trees, fresh old-array-model
`jasmin2ec` extraction, checker self-check, Jasmin build, safety, CT, and SCT
analysis, differential and chained-prefix tests, UBSan coverage, exact
word-level correctness and losslessness, and the schedule/range/algebra bridge.
Differential and UBSan tests cover 44 boundary vectors, 4096 direct `step=4`
vectors, and 2048 vectors chained through the Jasmin stage-1, radix-3,
`step=64`, `step=32`, `step=16`, and `step=8` slices; both disjoint and
in-place stage-1 caller shapes are exercised.

The algebra layer ties the 96 twiddles to the final 96 schedule exponents
`1`, `145`, `73`, `217`, `37`, `181`, `109`, `253`, `19`, `163`, `91`, `235`,
`55`, `199`, `127`, `271`, `7`, `151`, `79`, `223`, `43`, `187`, `115`, `259`,
`25`, `169`, `97`, `241`, `61`, `205`, `133`, `277`, `13`, `157`, `85`, `229`,
`49`, `193`, `121`, `265`, `31`, `175`, `103`, `247`, `67`, `211`, `139`,
`283`, `5`, `149`, `77`, `221`, `41`, `185`, `113`, `257`, `23`, `167`, `95`,
`239`, `59`, `203`, `131`, `275`, `11`, `155`, `83`, `227`, `47`, `191`,
`119`, `263`, `29`, `173`, `101`, `245`, `65`, `209`, `137`, `281`, `17`,
`161`, `89`, `233`, `53`, `197`, `125`, `269`, `35`, `179`, `107`, `251`,
`71`, `215`, `143`, and `287`. Assuming exactly the centered output contract
established for `step=8`, an explicit bridge derives this precondition from
the `step=8` algebra relation. The layer then proves the Montgomery product
bounds, absence of signed-word wrap in every butterfly input, both output
congruences modulo `q = 3457`, and the centered Barrett output range
`[-1728,1728]` for every coefficient.

This layer remains a standalone in-place array-value theorem. The composed
wrapper section below discharges the full forward composition. The remaining
boundaries are formal caller-range establishment where it is still needed,
executable `invntt`, and the full NTRU+768 KEM proof chain.

## Composed executable forward NTT

The wrapper at `ntruplus/jasmin/768/ref/ntt.jazz` now exports the single
symbol `jade_ntruplus_ntruplus768_amd64_ref_ntt`. It reuses the verified
stage namespaces and `require` edges for `ntt_stage1.jazz`, `ntt_radix3.jazz`,
`ntt_radix2_64.jazz`, `ntt_radix2_32.jazz`, `ntt_radix2_16.jazz`,
`ntt_radix2_8.jazz`, and `ntt_radix2_4.jazz`, and calls them in exactly that
seven-stage order.

Collectively, the wrapper consumes exactly `zetas[1..191]`: stage 1 reads
index `1`, radix-3 reads `2..5`, the radix-2 `step=64` layer reads `6..11`,
`step=32` reads `12..23`, `step=16` reads `24..47`, `step=8` reads `48..95`,
and `step=4` reads `96..191`. The checker is fail-closed on the C schedule,
the Jasmin namespace/require reuse, the two-buffer wrapper signature, and the
seven-call body order.

Run the complete composed forward-NTT check with:

```sh
./scripts/verify-ntruplus768-ntt.sh
```

The verifier is fail-closed on tools, dependency trees, bash syntax, proof
holes, fresh old-array-model `jasmin2ec` extraction, checker self-check,
Jasmin build, safety, CT, and SCT analysis, differential and UBSan coverage,
and both the word-level and algebra EasyCrypt proofs through the Why3-server
wrapper flow. Differential and UBSan tests cover 8 boundary vectors and 4096
deterministic random vectors for both the disjoint two-buffer call and the
in-place caller shape used by the reference transform.

The EasyCrypt word proof imports the extracted `NTRUPlus768NTT.ec` wrapper
together with the seven previously verified stage proofs, proves exact
functional correctness against their composed specification, and proves
losslessness for the exported symbol. The algebra layer threads the exact
top-level input contract `[-q, q)` coefficientwise through stage 1, radix-3,
and the five centered radix-2 layers, yielding the forward-NTT congruence
chain modulo `q = 3457`.

This milestone does not overclaim a formal C equivalence theorem. The
parser-based differential checker provides executable C/Jasmin evidence for
the full wrapper, while EasyCrypt proves the Jasmin wrapper against the
composed stage specifications and algebra bridges. The remaining boundaries
are formal caller-range establishment where it is still needed, the complete
executable `invntt`, and the full NTRU+768 KEM proof chain.

## Executable inverse-NTT radix-2 `step=4` layer

The in-place scalar procedure at
`ntruplus/jasmin/768/ref/invntt_radix2_4.jazz` implements the first iteration
of the `for (step = 4; step <= 64; step <<= 1)` loop in
`NTRU+/NTRU+768/ntt.c::invntt`. Its 96 four-pair blocks cover bases `0`, `8`,
..., `760`, for 384 butterflies total. They consume the terminal forward
twiddles in exact reverse order, from `zetas[191]` through `zetas[96]`.

Run the complete inverse `step=4` check with:

```sh
./scripts/verify-ntruplus768-invntt-radix2-4.sh
```

The verifier fails closed on missing tools or dependencies, proof holes,
source/schedule drift, stale old-array-model extraction, Jasmin build and
safety, CT and SCT analysis, differential execution, UBSan, and the EasyCrypt
word and algebra proofs. The word proof establishes exact array semantics and
losslessness. Under the coefficientwise input range `[-q,q)`, the algebra
proof shows that each low lane is the centered representative of `lo+hi`,
each high lane is congruent to `zeta*(hi-lo)`, low outputs lie in
`[-1728,1728]`, and high outputs remain in `[-q,q)`.

This is deliberately an in-place layer over an already materialized result
buffer. The initial `a -> r` copy in the C function belongs to the final
two-buffer `invntt(r,a)` wrapper, where its alias behavior can be checked once.
The inverse `step=16`, `step=32`, and `step=64` layers, inverse radix-3 layer,
final cyclotomic recombination and scaling, complete wrapper, and full KEM
proof remain separate milestones.

## Executable inverse-NTT radix-2 `step=8` layer

The in-place scalar procedure at
`ntruplus/jasmin/768/ref/invntt_radix2_8.jazz` implements the second iteration
of the inverse radix-2 loop. Its 48 eight-pair blocks cover bases `0`, `16`,
..., `752`, for another 384 butterflies. After `step=4` has consumed
`zetas[191..96]`, this layer consumes `zetas[95]` through `zetas[48]` in exact
descending order.

Run the complete inverse `step=8` check with:

```sh
./scripts/verify-ntruplus768-invntt-radix2-8.sh
```

As for `step=4`, the verifier fails closed on source or schedule drift, proof
holes, stale extraction, missing dependencies, Jasmin build and safety, CT and
SCT analysis, differential execution, UBSan, and both EasyCrypt proof layers.
The word proof establishes exact in-place array semantics and losslessness.
The algebra proof links the descending twiddles to the shared 192-entry root
schedule and shows, for coefficientwise inputs in `[-q,q)`, that low lanes are
centered representatives of `lo+hi`, high lanes are congruent to
`zeta*(hi-lo)`, low outputs lie in `[-1728,1728]`, and high outputs remain in
`[-q,q)`. The preceding `step=4` algebra bounds imply this input domain for
every coefficient, so the two inverse-layer contracts compose at their range
boundary.

This milestone still isolates one arithmetic layer. It does not include the C
copy prelude, the later radix-2 and radix-3 layers, final recombination and
scaling, the two-buffer wrapper, caller-range establishment, or the full KEM
proof.

## Verified NTRU+768 NTT root schedule

The shared EasyCrypt theory at
`ntruplus/proof/768/ref/ntt_schedule/NTRUPlus768NTTSchedule.ec` proves that the
explicit complete signed `zetas[192]` table and transform constants encode the
NTRU+ specification's recursive factorization schedule. For `q = 3457`, it
proves that `22` has exact order `576`, generates the terminal exponents from
the initial radix-2 layer, one radix-3 layer, and five standard radix-2 layers,
and matches all 192 Figure 22 indices. It also proves that:

- every concrete table entry is the centered Montgomery encoding of the
  corresponding power of the root;
- the exponents represented by `zetas[96..191]`, interleaved with their
  order-2 shifts, match the 192 terminal roots used by the `X^4-zeta_i`
  blocks;
- every terminal root satisfies `Y^192-Y^96+1 = 0` modulo `q`;
- the `OMEGA`, `ZMINUSZ5INV`, `NINV`, and `2NINV` constants have their stated
  Montgomery meanings.

The parser-based verification layer ties those explicit values to
`NTRU+/NTRU+768/ntt.c` and separately checks that the forward and reverse C
loops consume exactly the intended table ranges.

Run the schedule proof and the independent parser-based check of the C table,
constants, and loop bounds with:

```sh
./scripts/verify-ntruplus768-ntt-schedule.sh
```

This milestone still does not prove:

- that upstream callers establish the signed-range preconditions for every
  call, where that argument is not already discharged elsewhere;
- a complete executable `invntt` implementing the proved inverse schedule; or
- key generation, encryption, or the full KEM.

## Formosa ML-KEM reference

The official
[`formosa-crypto/formosa-mlkem`](https://github.com/formosa-crypto/formosa-mlkem)
repository is pinned at `external/formosa-mlkem` as a Git submodule. It provides
reference Jasmin implementations and EasyCrypt proofs for ML-KEM, including
security, specification, correctness, safety, and constant-time artifacts.

The Formosa material is included as an external reference corpus. The NTRU+768
arithmetic and transform algebra bridges reuse its generic signed-Montgomery
theory and word arithmetic lemmas, then instantiate and prove the
NTRU+-specific constants, bounds, schedule, and quotient-ring semantics
locally. Formosa's ML-KEM verification results do not establish any property
of NTRU+.

Clone this repository with all nested dependencies:

```sh
git clone --recurse-submodules \
  https://github.com/Hacker-Code-J/kpqc-sig-ntruplus-jasmin-easycrypt.git
```

For an existing clone, initialize the pinned submodules with:

```sh
git submodule update --init --recursive
```

The upstream build and proof-checking requirements are documented in
`external/formosa-mlkem/README.md`. In particular, the upstream project pins a
development Jasmin compiler and requires a compatible EasyCrypt installation
with Z3 and CVC5. Once those prerequisites are available, its top-level proof
check is:

```sh
make -C external/formosa-mlkem check
```

See [THIRD_PARTY.md](THIRD_PARTY.md) for provenance and licensing boundaries.
