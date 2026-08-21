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
below. It provides both the original symmetric theorem, with both inputs in
`[-q, q)`, and an asymmetric theorem for a first input in `[-3456, 7552]` and
a second input in canonical `[0, q)`. Under either theorem's premises, every
output coefficient is again in `[-q, q)`, and each block satisfies the expected
four coefficient congruences modulo `q = 3457`.

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
The inverse `step=64` layer, inverse radix-3 layer, final
cyclotomic recombination and scaling, complete wrapper, and full KEM proof
remain separate milestones.

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
copy prelude, the inverse `step=64` or radix-3 layers, final
recombination and scaling, the two-buffer wrapper, caller-range establishment,
or the full KEM proof.

## Executable inverse-NTT radix-2 `step=16` layer

The in-place scalar procedure at
`ntruplus/jasmin/768/ref/invntt_radix2_16.jazz` implements the third iteration
of the inverse radix-2 loop. Its 24 sixteen-pair blocks cover bases `0`, `32`,
..., `736`, for another 384 butterflies. After the preceding two layers have
consumed `zetas[191..48]`, this layer consumes `zetas[47]` through `zetas[24]`
in exact descending order.

Run the complete inverse `step=16` check with:

```sh
./scripts/verify-ntruplus768-invntt-radix2-16.sh
```

The verifier fails closed on source and reverse-schedule drift, proof holes,
stale extraction, missing dependencies, Jasmin build and safety, CT and SCT
analysis, standalone and composed differential execution, UBSan, and both
EasyCrypt proof layers. The word proof establishes exact in-place semantics
and losslessness. For coefficientwise inputs in `[-q,q)`, the algebra proof
shows that low lanes are centered representatives of `lo+hi`, high lanes are
congruent to `zeta*(hi-lo)`, low outputs lie in `[-1728,1728]`, and high
outputs remain in `[-q,q)`. An explicit bridge derives this input domain from
the proved `step=8` algebra relation, extending the compositional range chain
through `step=16`.

This remains a single arithmetic-layer milestone. The C copy prelude, inverse
`step=64`, inverse radix-3, final recombination and scaling, the
complete two-buffer wrapper, caller-range establishment, and the full KEM
proof remain separate work.

## Executable inverse-NTT radix-2 `step=32` layer

The in-place scalar procedure at
`ntruplus/jasmin/768/ref/invntt_radix2_32.jazz` implements the fourth iteration
of the inverse radix-2 loop. Its 12 thirty-two-pair blocks cover bases `0`,
`64`, ..., `704`, for another 384 butterflies. After the preceding three
layers have consumed `zetas[191..24]`, this layer consumes `zetas[23]` through
`zetas[12]` in exact descending order.

Run the complete inverse `step=32` check with:

```sh
./scripts/verify-ntruplus768-invntt-radix2-32.sh
```

The verifier fails closed on source and reverse-schedule drift, proof holes,
stale extraction, missing dependencies, Jasmin build and safety, CT and SCT
analysis, standalone and `step=4 -> 8 -> 16 -> 32` differential execution,
UBSan, and both EasyCrypt proof layers. The word proof establishes exact
in-place array semantics and losslessness. For coefficientwise inputs in
`[-q,q)`, the algebra proof shows that low lanes are centered representatives
of `lo+hi`, high lanes are congruent to `zeta*(hi-lo)`, low outputs lie in
`[-1728,1728]`, and high outputs remain in `[-q,q)`. An explicit bridge derives
this input domain from the proved `step=16` algebra relation, extending the
compositional range chain through `step=32`.

This remains a single arithmetic-layer milestone. The C copy prelude, inverse
`step=64`, inverse radix-3, final recombination and scaling, the complete
two-buffer wrapper, caller-range establishment, and the full KEM proof remain
separate work.

## Executable inverse-NTT radix-2 `step=64` layer

The in-place scalar procedure at
`ntruplus/jasmin/768/ref/invntt_radix2_64.jazz` implements the fifth iteration
of the inverse radix-2 loop. Its 6 sixty-four-pair blocks cover bases `0`,
`128`, ..., `640`, for another 384 butterflies. After the preceding four
layers have consumed `zetas[191..12]`, this layer consumes `zetas[11]` through
`zetas[6]` in exact descending order.

Run the complete inverse `step=64` check with:

```sh
./scripts/verify-ntruplus768-invntt-radix2-64.sh
```

The verifier fails closed on source and reverse-schedule drift, proof holes,
stale extraction, missing dependencies, Jasmin build and safety, CT and SCT
analysis, standalone and `step=4 -> 8 -> 16 -> 32 -> 64` differential
execution, UBSan, and both EasyCrypt proof layers. The word proof establishes
exact in-place array semantics and losslessness. For coefficientwise inputs in
`[-q,q)`, the algebra proof shows that low lanes are centered representatives
of `lo+hi`, high lanes are congruent to `zeta*(hi-lo)`, low outputs lie in
`[-1728,1728]`, and high outputs remain in `[-q,q)`. An explicit bridge derives
this input domain from the proved `step=32` algebra relation, extending the
compositional range chain through `step=64`.

This remains a single arithmetic-layer milestone. The C copy prelude, inverse
radix-3 layer, final recombination and scaling, the complete two-buffer
wrapper, caller-range establishment, and the full KEM proof remain separate
work.

## Executable inverse-NTT radix-3 layer

The in-place scalar procedure at
`ntruplus/jasmin/768/ref/invntt_radix3.jazz` implements the final loop of
`NTRU+/NTRU+768/ntt.c::invntt`. It performs 256 radix-3 butterflies as two
128-lane blocks rooted at bases `0` and `384`. The C loop enters this layer
with `k = 5`: at `start = 0` it loads `zeta2 = zetas[5] = 682` and then
`zeta1 = zetas[4] = -708`, so the first Jasmin block is parameterized as
`(zeta1, zeta2) = (-708, 682)`; at `start = 384` it loads
`zeta2 = zetas[3] = -248` and then `zeta1 = zetas[2] = -682`, so the second
block is parameterized as `(-682, -248)`. Both blocks use `OMEGA = -886`, and
after the second block the C loop leaves this layer with `k = 1`.

Run the complete inverse radix-3 check with:

```sh
./scripts/verify-ntruplus768-invntt-radix3.sh
```

The verifier is intended to fail closed on exact C/Jasmin reverse-schedule
coupling and mutation self-checks, proof holes, stale extraction and helper
clones, missing dependencies, Jasmin build and safety, CT and SCT analysis,
standalone and `step=4 -> 8 -> 16 -> 32 -> 64 -> radix3` differential
execution, UBSan, fresh extraction equality, and both EasyCrypt proof layers.
The proof surface for this milestone is the same as the preceding inverse
layers: exact in-place array semantics and losslessness at the word level,
followed by the algebra bridge that consumes the proved `step=64` output range
and discharges the final inverse radix-3 schedule.

This remains a single arithmetic-layer milestone. It does not include the
initial `a -> r` copy from the two-buffer C wrapper, the final 384-pair
cyclotomic recombination and scaling, the complete `invntt(r, a)` wrapper,
caller-range establishment beyond the verified layer chain, or the full KEM
proof.

## Executable inverse-NTT final recombination and scaling layer

The in-place scalar procedure at
`ntruplus/jasmin/768/ref/invntt_final.jazz` implements lines `270..277` of
`NTRU+/NTRU+768/ntt.c::invntt`. It processes all 384 pairs `(i, i+384)` after
the verified inverse radix-3 layer, using
`NTRUPLUS_ZMINUSZ5INV = -1665`, `NTRUPLUS_NINV = -811`, and
`NTRUPLUS_2NINV = -1622`. In the shared schedule theory these decode to the
mathematical constants `1634`, `3439`, and `3421`, respectively: `1634`
inverts `z - z^5`, `3439` is `(n/d)^(-1) mod q`, and `3421` is
`2 * (n/d)^(-1) mod q`, all for `q = 3457`.

Run the complete inverse final-layer check with:

```sh
./scripts/verify-ntruplus768-invntt-final.sh
```

The verifier is fail-closed on required tools and dependency trees, bash
syntax, proof holes in the final layer and its dependent proof tree, exact
C/Jasmin coupling and checker self-checks, fresh old-array-model `jasmin2ec`
extraction equality, stale `Array768.ec` and `WArray1536.ec` helper clones,
EasyCrypt word-level and algebra compilation through the Why3 server, Jasmin
build and safety, CT and SCT analysis, and `tests/ntruplus768/invntt_final`
`selfcheck`, `run`, and `ubsan`.

The algebra layer consumes the proved `invntt_radix3` output contract. For
`0 <= i < 128`, both members of the pair `(r[i], r[i+384])` arrive in
`[-3q, 3q)`; for `128 <= i < 384`, both arrive in `[-q, q)`. Using the
decoded constants `1634`, `3439`, and `3421`, it discharges the final
recombination-and-scaling congruences and proves that every output coefficient
returns to the signed `[-q, q)` range.

This milestone still excludes the initial `a -> r` copy, the complete
two-buffer `invntt(r, a)` wrapper, caller-range establishment beyond the
proved inverse layer chain, a formal whole-wrapper C/Jasmin equivalence
theorem, and the NTRU+768 KEM proof.

## Composed executable inverse NTT

The two-buffer procedure at `ntruplus/jasmin/768/ref/invntt.jazz` implements
the complete `NTRU+/NTRU+768/ntt.c::invntt` schedule. It first copies all 768
coefficients from `a` to `r`, then calls the verified inverse layers in the
only valid order: radix-2 `step=4`, `8`, `16`, `32`, and `64`, radix-3, and
the final 384-pair recombination and scaling layer.

Run the complete wrapper check with:

```sh
./scripts/verify-ntruplus768-invntt.sh
```

The verifier is fail-closed on required tools and proof dependencies, proof
holes, exact C/Jasmin source coupling and checker mutation self-tests, fresh
old-array-model extraction equality, EasyCrypt word-level and whole-chain
algebra compilation, Jasmin build and safety, CT and SCT analysis, and the
full differential and UBSan suites. The executable tests compare the wrapper
with the authoritative C function on boundary cases and 4096 deterministic
random inputs. They cover both disjoint buffers and the exact `r == a` alias
used by the KEM, and they check that a disjoint source buffer is unchanged.

The EasyCrypt wrapper theorem is deliberately value-level: after the proved
copy loop, its result depends only on the initial `a` array and equals the
nested composition of all seven verified stage specifications. Assuming every
input coefficient is in signed `[-q, q)`, the algebra theorem reuses the
stage-to-stage range and congruence bridges and proves that every final
coefficient is again in `[-q, q)`. The old-array extraction has separate value
arguments rather than a shared memory model, so it does not prove concrete
pointer identity or overlap behavior.

Supported concrete layouts are disjoint buffers and exact alias. Partial
overlap is intentionally excluded because the forward copy can overwrite
source coefficients that have not yet been read. This milestone also does not
claim a formal C-AST/Jasmin equivalence theorem, prove that every external
caller establishes the signed input range, or prove the complete NTRU+768 KEM.

## Independent `poly_basemul -> invntt` bridge

The signed-12-bit bridge theory at
`ntruplus/proof/768/ref/poly_basemul_invntt/NTRUPlus768PolyBasemulInvNTTAlgebra.ec`
connects the strengthened `poly_basemul` contract to the composed `invntt`
input shape. For coefficientwise `poly_basemul` inputs in signed
`[-4096, 4096)`, the strengthened algebra layer still establishes the blockwise
`poly_basemul_qring` postcondition, so every `poly_basemul` output coefficient
is already in the centered `[-q, q)` range with `q = 3457`. The bridge then
discharges the exact `invntt` range precondition and reuses the composed
inverse-NTT algebra theorem to show that the resulting `invntt` output
coefficients are again in `[-q, q)`.

Run the independent bridge check with:

```sh
./scripts/verify-ntruplus768-poly-basemul-invntt.sh
```

This verifier is intentionally narrow. It syntax-checks itself, rejects proof
holes in the bridge and dependent proof trees, compiles only the new bridge
theory with fresh `easycrypt -no-eco` state through a private Why3 server, and
runs the modified `tests/ntruplus768/poly_basemul/poly_basemul_diff.c`
differential plus UBSan suite. The executable coverage exercises the
authoritative C `poly_basemul` against the Jasmin slice on the existing
q-boundary/random vectors plus the new signed-12-bit boundary/random vectors;
it does not re-run the full `invntt` wrapper or unrelated KEM checks.

That bridge milestone alone does not prove `poly_frombytes` linkage, a formal
C-AST/Jasmin equivalence theorem, shared-memory aliasing for the composed
`invntt` wrapper, or the full NTRU+768 KEM.

## Authoritative `poly_frombytes` range bridge

The proof-only decoder model at
`ntruplus/proof/768/ref/poly_frombytes/NTRUPlus768PolyFromBytesAlgebra.ec`
mirrors the authoritative C decoder's two 12-bit arithmetic expressions over
an arbitrary 1152-byte input. It proves that all 768 modeled output
coefficients are in unsigned `[0, 4096)`, hence satisfy the signed
`[-4096, 4096)` premise of the existing `poly_basemul -> invntt` bridge. Its
first caller theorem instantiates the verified Jasmin `poly_basemul` procedure
with two decoder-spec outputs and establishes `poly_basemul_invntt_ready`.

Run the complete range/linkage check with:

```sh
./scripts/verify-ntruplus768-poly-frombytes.sh
```

The executable side deliberately targets the authoritative C boundary. A
fail-closed source checker pins the `poly_frombytes` signature, `N/2` loop,
three-byte/two-coefficient indices, shifts, casts, and `0xFFF` masks. It also
pins the decapsulation order `poly_frombytes(c/f) -> poly_basemul ->
poly_invntt` and must reject representative mutated source forms. A separate
differential harness compares the C decoder with a nibble-based oracle on 8
byte-boundary patterns, 6 cross-nibble patterns, 40 isolated-triplet cases,
and 4096 deterministic random inputs, both normally and under UBSan. The
verifier then reruns the downstream `poly_basemul -> invntt` proof and tests.

This is not a formal theorem over the C AST: the universal EasyCrypt statement
is about the arithmetic decoder model, while strict source checks and
executable differential tests bind that model to the current authoritative C
implementation. It also does not prove `poly_tobytes` round-trip correctness,
shared-memory aliasing, or the full NTRU+768 decapsulation/KEM.

## Decapsulation `m1` value-flow seam

The terminal lemmas in
`ntruplus/proof/768/ref/poly_frombytes/NTRUPlus768PolyFromBytesAlgebra.ec`
now continue the two arbitrary decoded byte arrays through the verified
`poly_basemul` result and the mathematical `inverse_invntt_spec`. They prove
the complete inverse-NTT algebra contract and show that every specified final
coefficient is centered in `[-q, q)` for `q = 3457`. This is the value-level
counterpart of the `crypto_kem_dec` sequence
`poly_basemul(&m1, &c, &f); poly_invntt(&m1, &m1);`.

Run the combined seam check with:

```sh
./scripts/verify-ntruplus768-decap-m1.sh
```

The verifier requires and compiles both terminal lemmas without proof holes,
runs the fail-closed checker for the ordered decapsulation calls and the exact
`m1` alias, and reruns the complete inverse-NTT verifier. The checker also pins
the thin `poly_invntt` wrapper to `invntt(r->coeffs, a->coeffs)` and rejects
mutations of that forwarding path. The inverse-NTT executable suite covers
both disjoint buffers and exact alias on boundary and deterministic-random
inputs, normally and under UBSan.

The formal statement remains an array-value composition: old-array extraction
does not model pointer identity or shared storage. Exact alias is therefore
bound at the source and executable-test layers, not claimed as an EasyCrypt
shared-memory theorem. This milestone also does not prove partial overlap, a
formal theorem over the C AST, the following `poly_crepmod3` step, or the full
decapsulation/KEM.

## Verified NTRU+768 `poly_crepmod3` value flow

The Jasmin slice at `ntruplus/jasmin/768/ref/crepmod3.jazz` mirrors the
authoritative scalar `crepmod3` reduction and its 768-coefficient
`poly_crepmod3` loop. Its fresh old-array extraction has a functional and
lossless word-level proof. The algebra layer then separates two claims that
must not be conflated:

- for every 16-bit input, Jasmin and the authoritative C implementation
  produce the same 16-bit word under the tested GCC signed-shift behavior;
- for coefficients in the inverse-NTT output range `[-3457, 3457)`, the
  result is one of `{-1, 0, 1}` and is congruent modulo 3 to the centered
  modulo-`q` representative of the input.

The second statement is intentionally range-qualified because `q = 3457` is
not divisible by 3. The theorem `poly_crepmod3_spec_input_qrange` also proves
that every output satisfies the existing forward-NTT stage-1 input premise.
`NTRUPlus768Crepmod3DecapBridge.ec` composes that fact with the decoder,
verified `poly_basemul` result, and mathematical `inverse_invntt_spec`, ending
at `poly_frombytes_two_decoder_specs_decap_m1_crepmod3_value_flow`.

Run the complete milestone check with:

```sh
./scripts/verify-ntruplus768-crepmod3.sh
```

The verifier regenerates and compares the EasyCrypt extraction, rejects proof
holes in the new proof tree, compiles the word, algebra, and decapsulation
bridge theories, and checks Jasmin safety, CT, and SCT. Its fail-closed source
checker pins both C/Jasmin reduction sequences and the decapsulation order
`poly_basemul(&m1, &c, &f); poly_invntt(&m1, &m1);`
`poly_crepmod3(&m1, &m1); poly_ntt(&m2, &m1);`. Differential and UBSan runs
cover 8 boundary vectors, 4096 deterministic random vectors, and every 16-bit
input value, with disjoint buffers, input immutability, and exact alias.

The exhaustive 16-bit test establishes word equality only; the trit and
modulo-3 theorem remains limited to `[-q, q)`. Negative signed right shift in
the authoritative C is implementation-defined by ISO C, so the executable
claim is explicitly tied to the tested GCC behavior. The EasyCrypt result is
an array-value theorem and does not model pointer identity, shared storage, or
partial overlap. This milestone also does not claim a formal C-AST equivalence
or full decapsulation/KEM correctness.

## Verified NTRU+768 forward-NTT ciphertext subtraction seam

The Jasmin slice at `ntruplus/jasmin/768/ref/poly_sub.jazz` mirrors the
authoritative 768-coefficient `poly_sub` loop. Its old-array extraction has
functional and lossless word-level proofs for subtraction modulo `2^16`.
The range-qualified algebra layer then connects the two inputs that occur in
decapsulation:

- a `poly_frombytes` ciphertext coefficient is in `[0, 4096)`;
- the verified full forward NTT produces a centered coefficient in
  `[-3457, 3457)`;
- their exact signed difference is therefore in `[-3456, 7552]` and is
  congruent modulo `q = 3457` to ciphertext minus forward-NTT output.

`NTRUPlus768PolySubDecapBridge.ec` composes the existing decoded
`poly_basemul -> inverse_invntt_spec -> poly_crepmod3` value flow with
`forward_ntt_spec` and the subtraction specification. Its terminal theorem,
`poly_frombytes_two_decoder_specs_decap_ciphertext_sub_value_flow`, starts
from two arbitrary decoder byte arrays and follows the array values through
the subtraction that corresponds to `poly_sub(&c, &c, &m2)`.

Run the complete milestone check with:

```sh
./scripts/verify-ntruplus768-poly-sub.sh
```

The verifier regenerates and compares the EasyCrypt extraction, rejects proof
holes, compiles the word, range, congruence, and decapsulation bridge theories,
and checks Jasmin safety, CT, and SCT. Its fail-closed checker binds the scalar
C/Jasmin loops, the thin `poly_ntt` wrapper, and the ordered decapsulation
calls through the exact `c` alias. Differential and UBSan tests cover disjoint
buffers, input immutability, exact output/input alias, boundary and
deterministic-random vectors, and the complete decapsulation coefficient
envelope.

Within that decapsulation envelope, the signed subtraction fits in `int16_t`,
so the C assignment represents the exact mathematical difference. Tests over
representative unrestricted 16-bit words establish agreement with the tested
GCC wraparound behavior only; out-of-range conversion to `int16_t` is
implementation-defined by ISO C, while the EasyCrypt word theorem is modulo
`2^16`.

The result can reach `7552`, so it does not establish the older symmetric
`[-4096, 4096)` input premise for the following `poly_basemul`. This standalone
milestone stops at ciphertext subtraction. The next milestone closes the
concrete call for a range-valid serialized `hinv` with a dedicated asymmetric
theorem; it does not turn arbitrary secret-key bytes into a valid second input.

## Verified NTRU+768 range-valid `hinv` second decapsulation product

The decapsulation bridge at
`ntruplus/proof/768/ref/decap_r2/NTRUPlus768DecapR2Bridge.ec` extends the value
flow through the concrete call `poly_basemul(&r2, &c, &hinv)`. It combines
three independently checked facts:

- the subtraction result supplied as `c` lies in `[-3456, 7552]`;
- a key-generation `poly_basemul` result from q-range `f` and `ginv` inputs is
  itself q-range and is therefore a valid `poly_tobytes` input;
- `poly_frombytes(poly_tobytes(hinv))` is the canonical representative in
  `[0, q)`, coefficientwise congruent to the original `hinv` modulo `q`.

The `poly_tobytes` Jasmin slice has functional, lossless, and probability-one
procedure proofs. Its algebra theory proves exact canonical round-trip through
the existing decoder specification. The bridge explicitly equates the two
decoder specifications used by those proof trees, rather than relying on an
implicit identification of their duplicate arithmetic definitions.

The asymmetric `basemul` proof is needed for the second product. Its largest
four-product envelope for a range-valid canonical `hinv` is
`4 * 7552 * 3456 = 104398848`, below the signed Montgomery reduction limit
`32768 * 3457 = 113278976`. An arbitrary 12-bit decoder output could instead
reach `4 * 7552 * 4095 = 123701760`, which exceeds that limit. Consequently,
the terminal result is deliberately a range-qualified serialized-`hinv`
theorem, not a theorem for arbitrary secret-key bytes or a proof that `hinv`
is an inverse.

The procedure and composition results are kept as two small theorems:
`poly_frombytes_two_decoder_specs_keygen_hinv_decap_r2_poly_basemul_correct`
proves that the verified Jasmin call returns the second quotient-ring product,
and `poly_frombytes_two_decoder_specs_keygen_hinv_decap_r2_value_flow` composes
that product with the preceding decoder, inverse NTT, `crepmod3`, forward NTT,
and ciphertext subtraction facts. The key-generation theorem
`keygen_hinv_poly_basemul_roundtrip_provenance` supplies the range-valid
serialized `hinv` premise from q-range `f` and `ginv` inputs.

Run the integrated milestone check with:

```sh
./scripts/verify-ntruplus768-decap-r2.sh
```

The verifier compiles the terminal EasyCrypt bridge with a bounded single
Why3 worker, rejects proof holes, and reruns the complete `poly_tobytes`,
`poly_basemul`, and `poly_sub` verifiers. Their fail-closed source checks bind
the key-generation serialization, decapsulation deserialization, exact `c`
alias, and ordered second `poly_basemul` call. Differential and UBSan coverage
includes 5 wide boundary and 4096 deterministic wide random multiplication
cases, input immutability, output q-range, and an independent modulo-`q`
block-product oracle.

This remains an old-array value/procedure result. It assumes q-range `f` and
`ginv` rather than proving sampler or inversion provenance, and it does not
model pointer offsets, partial overlap, or shared memory. It also does not
claim formal C-AST equivalence or hash/full-KEM correctness. The successor
milestone below closes the immediate `poly_tobytes(buf1, &r2)` call.

## Verified NTRU+768 second-product serialization

The bridge at
`ntruplus/proof/768/ref/decap_r2_tobytes/NTRUPlus768DecapR2ToBytesBridge.ec`
extends the preceding result through the concrete call
`poly_tobytes(buf1, &r2)`. It reuses the blockwise quotient-ring postcondition
of the second `poly_basemul`: all 192 four-coefficient blocks place their
outputs in `[-q, q)`, which supplies the existing verified serializer's
768-coefficient input premise.

The theorem `decap_r2_poly_tobytes_correct` applies the extracted Jasmin
procedure theorem and returns the exact 1152-byte `poly_tobytes_spec` of `r2`.
The companion theorem `decap_r2_serialized_value_flow` retains the full prior
decoder, transform, subtraction, `hinv`, and second-product value flow while
adding equality with those serialized bytes. No packing arithmetic or range
argument is duplicated in the new bridge.

Run the integrated milestone with:

```sh
./scripts/verify-ntruplus768-decap-r2-tobytes.sh
```

The verifier compiles the new terminal theory with one bounded Why3 worker,
rejects proof holes, runs a fail-closed source checker, and reruns the complete
predecessor verifier. The source checker binds the ordered
`poly_sub -> poly_basemul(&r2,...) -> poly_tobytes(buf1,&r2) -> hash_g`
sequence, exact buffer extent, and call uniqueness. Its self-check rejects
wrong source or destination arrays, undersized output, duplicate or reordered
serialization, and a changed `hash_g` input.

`hash_g` is used only as the source-order successor marker: this milestone
does not prove its domain-separated SHAKE256 semantics. SOTP decoding,
reencryption, comparison, fallback selection, pointer-overlap behavior,
formal C-AST equivalence, and full decapsulation/KEM correctness also remain
out of scope.

## Verified NTRU+768 decapsulation `hash_g` specification seam

The bridge at
`ntruplus/proof/768/ref/decap_hash_g/NTRUPlus768DecapHashGBridge.ec`
extends the serialized second-product value flow to the 192-byte value

```text
SHAKE256(0x01 || poly_tobytes_spec(r2), 192).
```

It reuses the byte-level FIPS202 specification from `Keccak1600_Spec.ec`.
The input lemmas `hash_g_input_size`, `hash_g_input_domain`, and
`hash_g_input_payload` establish an exact 1153-byte input whose first byte is
`0x01` and whose remaining 1152 bytes are the preceding serializer output.
`hash_g_output_list_size` and `hash_g_spec_to_list` retain exactly the first
192 SHAKE256 output bytes in an `Array192` value.

The abstract EasyCrypt procedure `HashG.hash_g` calls the already-proved
`Keccak1600Bytes.shake256`; `hash_g_abstract_correct` proves probability-one
agreement with `hash_g_spec`. The terminal theorems
`decap_r2_hash_g_value_flow` and
`decap_hash_g_correct` connect that specification to the exact
`poly_tobytes_spec(r2)` established by the preceding milestone. This is an
FIPS202 specification/procedure theorem, not a procedure theorem for the
repository's C implementation.

Run the integrated milestone with:

```sh
./scripts/verify-ntruplus768-decap-hash-g.sh
```

The verifier compiles the new theory with one bounded Why3 worker, rejects
proof holes, and reruns the complete predecessor verifier. A fail-closed
source checker binds `HASH_G_INBYTES = 1152`, `HASH_G_OUTBYTES = 192`, the
exact C wrapper body `0x01 || msg`, and the ordered decapsulation seam
`poly_tobytes -> hash_g -> poly_sotp_decode`. Its self-check rejects changed
parameters, domain byte, copy offset or length, SHAKE lengths, call arguments,
duplicates, and reordering.

The C `hash_g` plus its bundled FIPS202 implementation is additionally tested
on 39 boundary and deterministic vectors against Python `hashlib.shake_256`,
both normally and with UBSan. These are independent differential tests, not a
formal C semantics proof. In particular, this milestone does not establish
C/Jasmin equivalence, allocation-failure behavior, pointer aliasing, or the
contents of unused `buf2[192..1151]`. SOTP decoding, reencryption, comparison,
fallback selection, and full decapsulation/KEM correctness remain out of
scope.

## Verified NTRU+768 decapsulation `poly_sotp_decode` value seam

The theories under
`ntruplus/proof/768/ref/poly_sotp_decode/` close the next array-value boundary
of decapsulation. For each of the 768 coefficients, the specification adds the
corresponding bit from the upper 96-byte half of the 192-byte `hash_g` result.
It declares failure exactly when any resulting integer is outside `{0, 1}`.
On success, the lower 96-byte half is XORed bitwise with those sums and packed
into the decoded 96-byte prefix; on failure, every output byte is zero.

`poly_sotp_trit_sum_range` proves that the preceding `crepmod3` trit input and
one hash bit restrict every sum to `[-1, 2]`. The success and failure lemmas
then expose the raw decoded bytes or the fail-closed all-zero result. The
terminal theorem `decap_terminal_poly_sotp_decode_value_flow` composes this
specification with both existing inputs:

- `m1 = inverse_invntt_crepmod3_spec(first_basemul_output)`; and
- `buf2 = hash_g_spec(poly_tobytes_spec(r2_output))`.

The Jasmin slice at `ntruplus/jasmin/768/ref/poly_sotp_decode.jazz` implements
the same 96-by-8 scalar loop, 16-bit addition, 32-bit failure accumulation,
one-bit normalization, and whole-message mask. The integrated verifier checks
that the slice still extracts to an old-array procedure with the exact
`Array96 * W32` result, builds it with safety checking, and runs both CT and
SCT analyses. A fail-closed source checker fixes the authoritative C body and
the ordered `poly_tobytes -> hash_g -> poly_sotp_decode` caller seam; its
negative mutations cover changed offsets, operators, accumulator folding,
masking, inputs, duplicates, and call reordering. Normal and UBSan C binaries
and the Jasmin binary are compared against an independent Python oracle on 56
total vectors covering success paths, boundary failures, and deterministic
random inputs.

Run the complete milestone with:

```sh
./scripts/verify-ntruplus768-decap-sotp-decode.sh
```

The new EasyCrypt result is deliberately value-level. Extraction, safety,
CT/SCT analysis, and differential tests do not constitute an EasyCrypt
functional theorem for either the Jasmin or C procedure. The milestone also
does not model C AST semantics, pointer aliasing, partial overlap, or the
encode/decode inverse. It stops before appending the 32-byte secret-key suffix
and calling `hash_h`; reencryption, ciphertext comparison, fallback selection,
and full decapsulation/KEM correctness remain out of scope.

## Verified NTRU+768 decapsulation `hash_h` value seam

The theory under `ntruplus/proof/768/ref/decap_hash_h/` extends the decoded
message-prefix boundary through the next domain-separated hash. It constructs
the exact 128-byte payload

```text
decoded message prefix (96 bytes) || secret-key suffix (32 bytes)
```

and specifies `hash_h` as the first 224 bytes of
`SHAKE256(0x02 || payload)`. Array-size, domain-byte, payload, output-size, and
array/list conversion lemmas pin that value representation. An abstract
EasyCrypt procedure invokes the existing FIPS202 byte-level `shake256`
procedure, with deterministic Hoare, losslessness, and probability-one
correctness results.

The terminal decapsulation theorem composes this specification with
`decap_terminal_poly_sotp_decode_value_flow`. Its 32-byte suffix is an explicit
arbitrary theorem parameter: the current proof tree does not yet formalize
`hash_f(pk)` during key generation or the secret-key memory layout. Separately,
the fail-closed lemma proves that when SOTP decoding fails, the hashed message
prefix is the all-zero 96-byte value while the same suffix is retained.

A fail-closed source checker anchors the value seam to the current C sources.
It fixes the key-generation write and decapsulation read at
`sk + 2 * NTRUPLUS_POLYBYTES`, the 32-byte append loop, the exact
`poly_sotp_decode -> hash_h -> poly_cbd1` order, the `0x02` wrapper domain, and
the 128-byte input and 224-byte output formulas. Negative mutations exercise
all of those offsets, lengths, arguments, call counts, and orderings. Normal
and UBSan builds of the C wrapper are compared on deterministic boundary and
random vectors with Python's independent SHAKE256 implementation.

Run the complete milestone and all predecessor regressions with:

```sh
./scripts/verify-ntruplus768-decap-hash-h.sh
```

The source checker and differential tests are not a formal C-semantics or
binary-equivalence proof. In particular, this milestone does not establish
pointer/alias behavior, allocation-failure behavior in the bundled FIPS202 C
code, the formal provenance of the suffix as `hash_f(pk)`, or the later
`poly_cbd1`, reencryption, ciphertext comparison, fail-mask/fallback behavior,
and full decapsulation/KEM correctness.

## Verified NTRU+768 decapsulation `poly_cbd1` value seam

The theories under `ntruplus/proof/768/ref/decap_poly_cbd1/` extend the
decapsulation value chain through the deterministic centered-binomial sampler.
They take the already-specified 192-byte tail of `hash_h`—that is,
`buf3[32..223]`—and define each output coefficient `k = 8*i + j` as

```text
bit(buf3[32 + i], j) - bit(buf3[32 + 96 + i], j)
```

for `0 <= i < 96` and `0 <= j < 8`. The bit operation reuses the same
byte-to-integer definition as the preceding SOTP proof. Range lemmas prove
that every resulting coefficient is in `{-1, 0, 1}` and therefore satisfies
the exact input-range condition required by the existing NTT algebra.

The terminal theorem `decap_terminal_poly_cbd1_value_flow` is parameterized by
the established predecessor predicate and preserves the same 224-byte
`buf3_prefix`. It can therefore be instantiated with the existing
`decap_hash_h` value flow without importing the monolithic Keccak procedure
theory into this downstream proof. The separate congruence lemma
`poly_cbd1_preserves_hash_output_equality` transports the predecessor's
fail-closed hash-output equality through the tail projection and deterministic
sampler.

A fail-closed source checker fixes the authoritative `poly_cbd1` prototype,
the two 96-byte halves, the 96-by-8 loop bounds, coefficient indexing,
head-minus-tail subtraction, right shifts, and the concrete
`hash_h -> poly_cbd1(buf3 + NTRUPLUS_SSBYTES) -> poly_ntt` caller order.
Negative mutations exercise those constraints. A direct C driver is compared
with an independent Python bit-sampler on 44 boundary and deterministic random
vectors, both normally and with UBSan; it also checks that the 192-byte input
is not modified.

Run the complete focused milestone, including the new proof and tests plus the
predecessor `hash_h` source and differential regressions, with:

```sh
./scripts/verify-ntruplus768-decap-poly-cbd1.sh
```

On a machine with enough memory to load the concrete Keccak theory and the
entire arithmetic chain simultaneously, replay every predecessor EasyCrypt
proof as well with:

```sh
NTRUPLUS768_FULL_PREDECESSOR=1 \
  ./scripts/verify-ntruplus768-decap-poly-cbd1.sh
```

This is an array-value proof supported by source-shape and differential tests,
not a formal theorem about C execution, pointers, aliasing, or C/Jasmin
equivalence. The new file deliberately uses a Keccak-free, parameterized
predecessor boundary; the concrete SHAKE256 theorem remains in the separately
verified `decap_hash_h` milestone. It does not strengthen the existing
assumption about the formal `hash_f` provenance of the 32-byte suffix, and it
stops before composing the concrete `poly_ntt` procedure, reencryption,
ciphertext comparison, fail-mask/fallback selection, and full
decapsulation/KEM correctness.

## Verified NTRU+768 decapsulation `r1` forward-NTT value seam

The theory under `ntruplus/proof/768/ref/decap_r1_ntt/` extends the lightweight
decapsulation chain from the sampled polynomial to the verified composed
forward NTT. Its value-flow predicate fixes

```text
r1_pre  = poly_cbd1_spec(buf3[32..223])
r1_post = ntt_spec(r1_pre)
```

while retaining the typed predecessor predicate over the same 224-byte
`buf3_prefix`. The bridge reuses `poly_cbd1_spec_input_qrange` to discharge the
NTT precondition, derives the complete staged NTT algebra, and proves every
output coefficient lies in the centered interval `[-q, q)`. Consequently,
`r1_post` satisfies the exact input-range predicate required by the existing
`poly_tobytes` proof.

The procedure results specialize the already-proved old-array Jasmin NTT with
equal input and output array values, matching the value shape of
`poly_ntt(&r1, &r1)`. This does not turn the old-array model into a formal C
pointer-alias or shared-memory theorem. Runtime coverage checks that boundary
directly: a fail-closed source checker fixes the exact `poly_ntt` forwarding
body and the concrete
`hash_h -> poly_cbd1 -> in-place poly_ntt -> poly_tobytes` order. Negative
mutations cover changed parameters, prototypes, buffers, alias shape,
destinations, duplicates, and call reordering.

The combined differential driver derives all 768 CBD coefficients independently
and checks them again with Python, runs the production C `poly_ntt` in place,
and compares every transformed coefficient against both disjoint and in-place
executions of the verified Jasmin NTT. It also checks the centered output bound,
input immutability where applicable, the following serialization, repeated-run
determinism, and UBSan on 61 boundary and deterministic random vectors.

Run the complete milestone with the full composed-NTT regression and the
focused CBD/hash predecessor regression using:

```sh
./scripts/verify-ntruplus768-decap-r1-ntt.sh
```

The new proof remains Keccak-free and parameterized by the established
predecessor value predicate. It does not prove concrete C pointer aliasing,
C/Jasmin binary equivalence, the `poly_tobytes` procedure call itself,
reencryption comparison, fail-mask/fallback selection, or full
decapsulation/KEM correctness.

## Verified NTRU+768 decapsulation `r1` NTT-to-`poly_tobytes` seam

The theory under `ntruplus/proof/768/ref/decap_r1_tobytes/` closes the next
decapsulation boundary by reusing the proved `r1_post` value from
`decap_r1_ntt` and feeding it directly into the standalone `poly_tobytes`
specification and Jasmin procedure theorem. Its value-flow predicate fixes

```text
r1_pre  = poly_cbd1_spec(buf3[32..223])
r1_post = ntt_spec(r1_pre)
buf2    = poly_tobytes_spec(r1_post)
```

while retaining the same typed 224-byte predecessor predicate. The bridge
discharges the `poly_tobytes` precondition entirely from the predecessor
`decap_r1_ntt_poly_tobytes_ready` theorem, then proves both the algebraic byte
specification and the exact old-array Jasmin procedure result with probability
1 for `poly_tobytes(buf2, &r1)`.

Runtime coverage pins the concrete decapsulation caller seam to
`hash_h -> poly_cbd1 -> in-place poly_ntt -> poly_tobytes -> verify`. The new
fail-closed checker rejects changed `buf2` extent, serialization source or
destination, reordered `poly_ntt`/`poly_tobytes`/`verify` calls, duplicate
serialization, and altered verify arguments. The milestone verifier also
reruns the predecessor `decap_r1_ntt` regression and the standalone
`poly_tobytes` proof/test suite so the composed seam stays aligned with both
upstream proofs.

The combined differential driver rebuilds all 768 CBD coefficients from the
192-byte tail with an independent Python oracle, checks them against the C
sampler, runs the production C `poly_ntt` in place, matches its output against
the verified Jasmin NTT, and then compares `poly_tobytes(buf2,&r1)` against
both independent byte packing and the verified Jasmin `poly_tobytes` slice.
The run also checks input immutability where applicable, repeated-run
determinism, and UBSan across 61 boundary and deterministic-random vectors.

Run the complete milestone with:

```sh
./scripts/verify-ntruplus768-decap-r1-tobytes.sh
```

This proof remains Keccak-free and stops at the exact serialized `buf2` bytes
before verify semantics. It does not prove the boolean result of `verify`,
fail-mask propagation, fallback shared-secret selection, reencryption
comparison, pointer aliasing, C/Jasmin binary equivalence, or full
decapsulation/KEM correctness.

## Verified NTRU+768 decapsulation serialized-byte comparison seam

The theories under `ntruplus/proof/768/ref/decap_verify/` close the next
decapsulation boundary by assigning an exact array-value meaning to
`verify(buf1, buf2, NTRUPLUS_POLYBYTES)`. The standalone specification is

```text
verify_spec(buf1, buf2) = 0  when buf1 = buf2
verify_spec(buf1, buf2) = 1  otherwise
```

and the procedure model follows the C helper's concrete word shape: a
`W8` accumulator starts at zero, OR-reduces all 1152 bytewise XORs, is
zero-extended to `W64`, negated modulo `2^64`, and logically shifted right by
63. The loop invariant proves that the accumulator is zero exactly when every
processed byte agrees. The resulting Hoare and probability-1 theorems prove
that the procedure returns only zero or one, returns zero exactly for equal
arrays, and returns one exactly when some indexed byte differs.

The comparison bridge accepts typed
`W8.t Array1152.t -> bool` predicates for the two established serialization
frontiers. These predicates are instantiated by callers with closures over
the existing `decap_r2_tobytes_value_flow` and
`decap_r1_tobytes_value_flow` results. Keeping the frontiers parameterized is
intentional: directly importing both complete arithmetic proof trees in one
fresh EasyCrypt process exhausts the practical host-memory path. The milestone
verifier therefore checks the exact `buf1` and `buf2` value equations and runs
both predecessor bridge proofs and focused caller tests independently.

A fail-closed source checker pins the exact C helper body and the concrete
`poly_tobytes(buf2, &r1) -> fail |= verify(buf1, buf2, 1152)` call seam. Its
self-check rejects 12 representative mutations covering the parameter,
signature, accumulator initialization, loop bound, XOR/OR reduction, return
normalization, argument order, length, failure accumulation, call order, and
duplicate comparison. A driver includes the production `kem.c` helper
directly and compares it against array equality on 31 equal, boundary-mismatch,
sparse, multiple-mismatch, and deterministic generated pairs, normally and
under UBSan; it also checks the 0/1 range, determinism, and input immutability.

Run the complete milestone with both serialization-frontier regressions using:

```sh
./scripts/verify-ntruplus768-decap-verify.sh
```

The EasyCrypt procedure is a fixed-array model of the source algorithm, not a
formal C pointer, binary-equivalence, or constant-time theorem. This milestone
also stops before composing the earlier SOTP-decode failure with `fail |=`,
before proving the shared-secret mask/fallback selection, and before full
decapsulation/KEM correctness.

## Verified NTRU+768 decapsulation failure-flag composition seam

The theories under `ntruplus/proof/768/ref/decap_fail/` compose the two
normalized failure sources at the exact caller boundary

```c
fail = poly_sotp_decode(msg, &m1, buf2);
/* ... r1 reconstruction and serialization ... */
fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);
```

The existing SOTP algebra exposes the decode failure as a Boolean, while the
verified byte comparison returns a `W64` zero or one. The standalone fail
theory encodes the decode result as a stored `W8` byte, zero-extends it to
`W64`, ORs it with the comparison result, and truncates the promoted result
back to `W8`. Because both inputs are proved to be in `{0,1}`, the conversion
is lossless and agrees with Boolean OR. Hoare, losslessness, and probability-1
theorems establish

```text
final_fail = 0  <=>  decode succeeded and buf1 = buf2
final_fail = 1  <=>  decode failed or     buf1 <> buf2
```

The bridge keeps the decode and comparison producer trees behind typed
predicates, and explicitly records `compare_failed = (buf1 <> buf2)`. This
preserves the memory-bounded proof structure used by the preceding comparison
milestone while carrying the exact serialized-array equality into the final
failure byte.

The fail-closed source checker fixes the `int8_t fail` declaration, initial
decode assignment, later OR update, 1152-byte comparison length, argument
order, and ordering between r1 serialization, comparison, and the following
shared-secret loop. Its self-check rejects 10 representative parameter,
type, operator, buffer, order, length, and duplicate-call mutations. A driver
includes the production `verify` helper and executes the same 0/1
`int8_t` OR assignment on 32 vectors, covering all four truth-table cases plus
boundary, multiple, and deterministic generated mismatches. Normal and UBSan
runs check the independent Boolean oracle, result ranges, determinism, and
input immutability.

Run this milestone together with the focused decode and comparison frontiers:

```sh
./scripts/verify-ntruplus768-decap-fail.sh
```

The promoted `W64` model is justified only for the proved 0/1 operands; it is
not a general theorem about C integer promotions or a C/binary-equivalence
claim. This milestone stops before the signed `~(-fail)` shared-secret mask,
fallback selection, and full decapsulation/KEM correctness.

## Verified NTRU+768 decapsulation shared-secret mask seam

The theories under `ntruplus/proof/768/ref/decap_mask/` extend the normalized
failure byte through the exact final shared-secret loop

```c
fail |= verify(buf1, buf2, NTRUPLUS_POLYBYTES);

for (size_t i = 0; i < NTRUPLUS_SSBYTES; i++)
    ss[i] = buf3[i] & ~(-fail);

return fail;
```

The word-level model shadows the target C promotion shape at 32 bits. It
sign-extends the stored `int8_t fail` with `MOVSX_u32s8`, applies unary
negation and `invw`, zero-extends each `uint8_t` source byte, performs the
bitwise AND, and truncates the stored result back to `W8`. Reusing the
preceding proof's `fail_byte` definition keeps the only reachable inputs at
zero and one. The resulting mask is therefore all ones on success and zero on
failure, so the fixed 32-iteration procedure proves

```text
ss = if failed then [0; ...; 0] else buf3[0..31].
```

The `hash_h` bridge now exports the projection from its verified 224-byte
output to `hash_h_ss_spec`, the first 32 bytes consumed by this loop. The mask
bridge keeps that shared-secret source and the final failure producer behind
separate typed predicates. This carries both established frontiers into one
Array32 selection theorem without loading the full Keccak, decode, and
reencryption proof trees together.

The fail-closed source checker fixes `NTRUPLUS_SSBYTES == 32`, the `int8_t`
failure type, the exact mask loop and assignment, and the
contiguous `verify -> mask -> return fail` tail. Its self-check rejects twelve
representative parameter, type, operator, bound, source, destination, index,
ordering, and return mutations. A target-ABI driver asserts 8-bit bytes,
32-bit two's-complement `int`, then runs the exact promoted expression and
return on 56 deterministic boundary and generated vectors. Normal and UBSan
runs check copy-on-success, zero-on-failure, return preservation, input
immutability, and determinism.

Run the mask proof together with its `hash_h` source and final-failure
predecessor regressions:

```sh
./scripts/verify-ntruplus768-decap-mask.sh
```

By default this compiles the lightweight typed 224-to-32 projection and runs
the focused `hash_h` source/runtime regression, avoiding a second copy of the
full Keccak proof tree in memory. On a host with sufficient memory, set
`NTRUPLUS768_FULL_HASH_H=1` to recompile the complete `hash_h` bridge during
the same run; its dedicated verifier remains
`./scripts/verify-ntruplus768-decap-hash-h.sh`.

The W32 formula is a target-width shadow justified for the proved 0/1 inputs,
not a formal ISO C integer-representation theorem. The EasyCrypt procedure is
an array-value model and does not prove C pointer/alias behavior, binary
equivalence, or the following C `int` return conversion. The source and runtime
checks cover the concrete return seam, but API-level shared-secret agreement
and full decapsulation/KEM correctness remain out of scope.

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
- a shared-memory proof of the executable `invntt` pointer-overlap behavior; or
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
