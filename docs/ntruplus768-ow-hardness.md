# NTRU+768 one-wayness reduction

The base-PKE one-way success probability is bounded by an explicitly
denominator-conditioned NTRU distinguishing experiment and computational
RLWE secret recovery. The exact key-acceptance factor is retained:

```text
epsOW <= (DeltaNTRU(D) + Pr[RLWE(C): secret recovered]) / alpha_g
alpha_g = Pr[g <- psi1 : g is a unit] >= 5/8.
```

`DeltaNTRU` is the signed real-minus-uniform probability difference.
The constructed distinguisher and solver contain the original base-PKE
attacker, including its auxiliary random-oracle simulation. The hardness
challengers themselves do not initialize or query random oracles.

## Exact experiment conventions

The ring is `F_3457[X]/(X^768-X^384+1)`. Canonical representatives have
ordinary degree below 768 (`deg <= 768` in EasyCrypt's coefficient-list
convention). `psi1` is the 768-coefficient product CBD1 law.

The real NTRU experiment draws `f=1+3*f0` from the existing law conditioned
on invertibility and independently draws `g` from unconditioned `psi1`.
It supplies `g/f`; the comparison experiment supplies a uniform element
of the **entire ring**, including zero and nonunits. The denominator
convention explicitly resolves the undefined inverse left implicit in
Definition 2.6 of the pinned specification. No equality to an entirely
unconditioned experiment with an unspecified inverse default is claimed.

Actual Figure 18 key generation also conditions `g` to be a unit and
sets `h=3*g/f`. The reducer therefore scales the NTRU input by three and
checks invertibility. Its real success probability is exactly
`alpha_g*epsOW`. The factor three preserves the uniform **ring** law;
it is not absorbed into the small-coefficient `psi1` law.

Computational RLWE draws uniform `a` over the whole ring and independent
`s,e` from `psi1`, supplies `(a,a*s+e)`, and checks recovery of `s`.
The OW plaintext corresponds to `e`, not `s`. For unit `a`, the solver
invokes the OW attacker on the corresponding canonical byte inputs and
uses checked public recovery for `a^-1*(b-e_hat)`. Exact error recovery
implies exact secret recovery. Nonunit and rejected-recovery branches
return zero. They may occasionally succeed; the proof requires a success
inequality and does not discard that extra probability.

The polynomial/byte codec is connected to the existing NTT,
serialization, public inversion and linear recovery kernels. RLWE's
challenge equation is proved for all canonical `a`, including nonunits.
No exhaustive search, new abstract game-distance axiom, arbitrary
nonunit inverse, or extra decryption-failure assumption is used.

## Original KEM composition

`ow_original_hardness` substitutes the one-way bound into the preceding
`sec_original_inj_ow` theorem:

```text
AdvCCAOriginal(A) <= 2*epsINJ + 2*(DeltaNTRU(D)+epsRLWE(C))/alpha_g
  + (130820 + 512*qE)/2^256
  + (q0 + qH,S + d)/2^353 + (qC + d)/2^768.
```

The KEM advantage remains the absolute deviation of winning probability
from one half. The prior private-state restrictions, robust attacker
losslessness and distinct query-contract scopes are retained unchanged.
The generic OW reduction itself adds no attacker-losslessness premise.
`d=max(0,budget)` is the existing analysis budget, not a retry limit.
The original cached-ROM key generator is not assumed to terminate.

The INJ term is a computational collision-finding success probability.
The subsequent [collision reduction](ntruplus768-inj-hardness.md) connects
it to a second NTRU distinguisher and an explicit uniform short-relation
experiment. Its [statistical bound](ntruplus768-short-relation-bound.md)
is now proved unconditionally below `2^-244` and included in the original
KEM probability reduction.
Neither mathematical injectivity nor NTRU/RLWE hardness is proved here.
A complete PPT/running-time theorem, HAETAE unforgeability, QROM and
native memory/ABI correspondence remain separate work.

## Reproduction

```sh
./scripts/verify-ntruplus768-ow-hardness.sh \
  --prior-evidence-root /path/to/thesis
```

The explicit frozen inventory is checked with EasyCrypt/Why3 from
`cryptotools-2026.09`, Z3, `Proofs:check`, `-no-eco`, timeout 60,
one prover and OCaml GC `o=20`. The runner compiles every new main with
a semantic EOF theorem and checks that removing each own final `qed`
is rejected in that same file. Source and effective external inputs
are hashed before and after execution. Imported EC files are linked
to the preceding ACWC2 full PASS and are not counted as fresh mains.

`--check-only` reports `SOURCE_CHECK_ONLY`; it never produces a proof
PASS. Source mutation controls and exact finite composite-ring diagnostics
check experiment conventions and harness behavior; they are not substitutes
for the EasyCrypt proofs. C/Jasmin, native execution, extraction,
Safety, CT and SCT are neither changed nor rerun by this proof-only command.
