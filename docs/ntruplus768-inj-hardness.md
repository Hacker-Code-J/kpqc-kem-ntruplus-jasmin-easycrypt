# NTRU+768 collisions and uniform short relations

This family constructs a concrete reduction from the existing base-PKE
collision experiment to a conditioned-NTRU distinguisher and an explicitly
defined uniform short-relation solver:

```text
epsINJ <= (DeltaNTRU(D_I) + epsSR(C_I)) / alpha_g.
```

This family keeps `epsSR` explicit and introduces no hardness axiom for
the new experiment. The subsequent [statistical bound](ntruplus768-short-relation-bound.md)
proves `epsSR <= deltaSR < 2^-244` and composes that bound into the original
KEM game. It does not identify the INJ experiment with decisional NTRU.

## Integer collision extraction

For a valid collision `(m1,m2,r1,r2)` in the actual PKE specification,
signed word coefficients are decoded and subtracted as unbounded integers:

```text
v = r1-r2, w = m1-m2;
(v,w) != (0,0), h*v+w = 0 mod (3457, X^768-X^384+1);
every coefficient of v,w lies in [-2,2].
```

The bridge uses the actual canonical byte encoding and proved polynomial
encryption semantics. It performs no word-size subtraction, secret-key
operation or exhaustive search. Distinct valid encryption input pairs
give a nonzero integer pair.

Each difference vector has squared coefficient Euclidean norm at most
`3072=4*768`. The ordinary
concatenated pair squared norm is at most `6144=8*768` and is positive.
The pair infinity norm is at most 2. These coefficient norms are not
unsigned field representative norms or canonical-embedding norms.
`2*sqrt(768)` is a bound for each component; the direct bound for their
concatenation is `2*sqrt(2*768)`.

## The exact uniform experiment

`INJShortRelationGame(C)` samples `a` uniformly from **all** of `R_q`,
including nonunits, and gives it to `C`. The returned integer pair must
be nonzero, coefficient-bounded by 2, and satisfy `a*v+w=0` in `R_q`.
The defining row is `[a,1]`, with the second entry fixed.

This is a systematic Ring-SIS-type experiment. It is not literally the
standard experiment with two independent uniform row entries, and no
worst-case lattice theorem is instantiated without checking its sampling,
norm and parameter conditions. See the author version of
[Langlois–Stehlé, Definition 3.3 and Theorem 3.4](https://perso.ens-lyon.fr/damien.stehle/downloads/MSIS.pdf).

`INJNTRUReduction(B)` scales its NTRU input by three, checks invertibility,
and tests the actual collision returned by `B` on the encoded key. Its
real success mass is exactly `alpha_g*epsINJ`, using the existing
unit-conditioned denominator, unconditioned numerator and
`alpha_g=Pr[g<-psi1:unit g]>=5/8`.

`INJShortSolver(B)` uses the same guard and attacker, returning the
integer difference pair on a valid collision and zero otherwise.
The uniform challenge distribution remains unconditioned. The same
auxiliary-oracle simulation stays inside `B`; the hardness challengers
perform no ROM initialization or query. The probability proofs retain
nontermination mass and add no attacker-losslessness premise.

## Original KEM composition and remaining obligation

`inj_original_short_relation` retains all prior private-state, robust
termination, initial-state and query contracts and proves

```text
AdvCCAOriginal(A) <= 2*(DeltaNTRU(D_I)+DeltaNTRU(D_O)
                         +epsSR(C_I)+epsRLWE(C_O))/alpha_g
  + (130820+512*qE)/2^256
  + (q0+qH,S+d)/2^353 + (qC+d)/2^768.
```

The KEM advantage is absolute returning-win bias from one half. Each
NTRU term is its concrete distinguisher's signed real-minus-uniform
probability difference. The INJ and OW reductions have different
distinguishers; their two terms are not silently identified.

The theorem `inj_uniform_existence_bound`
proves that every solver's success probability is bounded by
`deltaSR = Pr[a <- uniform R_q : some accepted integer pair exists]`,
without assuming that the solver terminates. The actual KEM corollary
`inj_original_statistical` substitutes this mass for `epsSR`.
This family's theorem leaves the mass explicit. The subsequent
[statistical proof](ntruplus768-short-relation-bound.md) establishes its
unconditional numerical bound and supplies the new `sr_original_numerical`
corollary. Earlier research diagnostics are retained as diagnostics.
The full reduction cost/PPT analysis, HAETAE UF-CMA, QROM and native
memory/ABI correspondence remain separate obligations.

## Reproduction

```sh
./scripts/verify-ntruplus768-inj-hardness.sh \
  --prior-evidence-root /path/to/thesis
```

The frozen main inventory is compiled using the September 2026 toolchain,
Z3, `Proofs:check`, `-no-eco`, timeout 60, one prover, and GC `o=20`.
Every main has a semantic EOF check and an own-file unfinished-proof
negative check. Inputs are hashed before and after execution. Imported
EC sources are linked to the preceding OW full PASS, not counted as new
main replays. `--check-only` reports `SOURCE_CHECK_ONLY`.

Finite diagnostics and source mutation controls check the experiment and
runner conventions. They do not prove lattice hardness, statistical
injectivity, or the proposed determinant bound. C/Jasmin, native execution,
extraction, Safety, CT and SCT are not changed or rerun by this command.
