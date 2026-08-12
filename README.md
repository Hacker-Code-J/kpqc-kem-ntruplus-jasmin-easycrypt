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
`Z_q[X]/(X^4-zeta_k)` under two assumptions:

- every input coefficient lies in `[-q, q)`;
- each word twiddle is interpreted via the Montgomery-decoded schedule carried
  by the concrete `zetas[96..191]` table.

Under those assumptions, every output coefficient is again in `[-q, q)`, and
each block satisfies the expected four coefficient congruences modulo `q = 3457`.

What this still does not prove:

- that the concrete `zetas[96..191]` table is the intended NTT-root schedule;
- that upstream callers establish the signed-range preconditions for every call;
- the surrounding NTT, inverse NTT, key generation, encryption, or full KEM.

## Formosa ML-KEM reference

The official
[`formosa-crypto/formosa-mlkem`](https://github.com/formosa-crypto/formosa-mlkem)
repository is pinned at `external/formosa-mlkem` as a Git submodule. It provides
reference Jasmin implementations and EasyCrypt proofs for ML-KEM, including
security, specification, correctness, safety, and constant-time artifacts.

The Formosa material is included as an external reference corpus. The NTRU+768
algebra bridge imports its generic signed-Montgomery theory and a generic word
arithmetic-shift lemma, then instantiates and proves the NTRU+-specific
constants, bounds, and quotient-ring semantics locally. Formosa's ML-KEM
verification results do not establish any property of NTRU+.

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
