# NTRU+768 uniform short-relation probability

This family proves the unconditional statistical bound

```text
deltaSR <= 25^768 * 12288^384 / 3457^768 < 2^-244.
```

`deltaSR` is the existing `inj_uniform_bad_mass`: the probability that a
uniform element of the entire quotient ring admits a nonzero pair of
integer coefficient vectors `(v,w)`, each coefficient in `[-2,2]`, with
`a*v+w=0`. The ring is `F_3457[X]/(X^768-X^384+1)`. Uniform sampling includes
zero and nonunits. This result bounds existence itself and needs neither
a hardness assumption nor termination of a relation-search adversary.

## Mathematical argument

The actual integer polynomial multiplication is represented by `M_v`.
Its entries are signed coefficients or signed sums of two coefficients
of `v`. Their absolute values are at most 4; each row squared norm is at
most `12288=16*768`.

The modulus polynomial is proved irreducible over the rationals by a
Schönemann argument at 2. The proof uses `g=X^6+X^3+1`, its irreducibility
over `F_2`, the identity `Phi mod 2 = (g mod 2)^128`, and the exact
remainder `Phi mod g = 2*(X^3+1)`, which excludes `Phi=g*Q+4*R`.
The rational/integer factorization step is also checked.

For nonzero `v`, multiplication has trivial integer kernel, so `det M_v`
is nonzero. Hadamard gives `abs(det M_v)<=12288^384`. Integer Smith normal
form bounds the number of solutions of `M_v*a+w=0 mod 3457` by
`abs(det M_v)`. This step allows a singular matrix modulo 3457 and does
not assume that a nonzero short difference is a unit.

Every canonical coefficient vector has probability `3457^-768` under
the existing uniform ring law. A finite union over the `25^768` possible
short pairs gives the displayed bound. A zero first vector cannot
satisfy the nonzero-pair event. The final numerical comparison uses exact
rational arithmetic, including
`25^768*12288^384/3457^768 = (7680000/11950849)^384`.

## Composition with the original KEM

`sr_uniform_bad_mass_244` establishes the statistical bound.
`sr_original_numerical` composes it with the original classical-ROM
IND-CCA experiment:

```text
AdvCCAOriginal(A) <=
  2*(DeltaNTRU(D_I)+DeltaNTRU(D_O)+epsRLWE(C_O)+2^-244)/alpha_g
  + (130820+512*qE)/2^256
  + (q0+qH,S+d)/2^353 + (qC+d)/2^768.
```

The advantage is the absolute returning-win bias from one half.
Each NTRU term is its own concrete distinguisher's signed
real-minus-uniform probability difference. The two distinguishers are
not identified. The denominator remains
`alpha_g=Pr[g<-psi1 : g is a unit]>=5/8`; the NTRU experiment retains its
explicit unit-conditioned denominator and unconditioned numerator.

All previous private-state exclusions, robust adversary termination,
initial-state conditions and backend-specific query contracts remain.
The statistical theorem adds no losslessness premise. It does not imply
that the original cached-ROM KeyGen is lossless.

## Checked Coq connection

The algebraic helpers use the already installed Coq 8.20.1 and MathComp
2.2.0, including `mathcomp.word.word_ssrZ`. EasyCrypt and Why3 remain on
the September 2026 toolchain. Coq helpers and the required stock Why3
support modules are rebuilt in isolation with the matching Coq compiler.

The default EasyCrypt/Why3 prefix is `~/.opam/cryptotools-2026.09`;
Coq defaults to `~/.opam/ocaml-base-compiler.4.12.0`. The matching
MathComp and word libraries and the retained Why3 1.8.2 Coq sources at
`.opam-switch/sources/why3.1.8.2/lib/coq` under the Why3 prefix are required.
The runner copies the declared support modules into its evidence directory
and changes no installed file or system prover configuration.
Its isolated Why3 configuration sets the actual native Coq limit to
60 seconds and preserves the base memory limit; EasyCrypt's SMT timeout
option alone does not control this native path.

The native EasyCrypt obligations regenerate their actual Coq declarations
and replay the authored prelude and proof. No desired algebraic or
probability law is added as an EasyCrypt axiom. Each declared helper
endpoint is checked for unapproved global assumptions. The assumptions
of a native goal are checked against the declarations of its freshly
exported EasyCrypt context.

A separate kernel check captures the fresh proposition before authored
imports and checks the resulting proof against that captured type. This
also detects changes in the elaborated goal caused by notation scopes.
Source controls and negative tests reject proof escapes, invalid proofs,
changed goals and missing helpers. Logs and hashes identify the checked
sources, generated goals, compiled helpers and tool configuration.

## Reproduction and scope

With the frozen artifact and its required prior evidence available, run from its repository root:

```sh
./scripts/verify-ntruplus768-short-relation-bound.sh \
  --prior-evidence-root /path/to/thesis
```

A successful full run records fresh EasyCrypt and Coq checks.
`--check-only` reports `SOURCE_CHECK_ONLY` and does not replace the full
frozen replay. Imported EasyCrypt
theories are linked to the preceding INJ/SR replay; they are not counted
as newly replayed main files. Proof counts and final evidence digests are
taken from the frozen manifest and replay summary.

The unconditional statement concerns the uniform short-relation event.
The KEM theorem remains a reduction to the specified conditioned-NTRU
and computational RLWE experiments under its existing contracts. It
does not prove those problems hard or supply a complete reduction
running-time/PPT theorem. HAETAE UF-CMA, QROM, fixed SHAKE versus ROM, and
native primitive/C memory/ABI correspondence remain outside this result.
This command does not change or rerun C/Jasmin execution, extraction,
Safety, CT or SCT checks.

## Subsequent resource accounting

The [local resource proof](ntruplus768-reduction-cost.md) instruments the
actual lookup, extractor and raw handler and preserves the original
probability inequality for the corresponding hardness attackers. Its
local counts and explicit finite-trace sums do not establish total
execution time or PPT; concrete map refinement and whole-adversary
resource semantics remain separate obligations.
