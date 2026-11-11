# Numerical acceptance bounds for NTRU+768 KeyGen

This development discharges the positive-acceptance premises in the
fresh-buffer KeyGen analysis by proving lower bounds for the actual inverse
predicates. It then specializes the [stopped-ROM comparison](ntruplus768-stopped-rom.md)
to a concrete retry budget. The numerical error bounds a KeyGen distribution
comparison; it is not a decryption-failure or IND-CCA advantage bound.

## Actual acceptance predicates

The input distribution is the existing `uniform192`. CBD1 subtracts the tail
bit from the corresponding head bit for each coefficient. The f candidate is
`1+3*CBD1(buf)` and the g candidate is `3*CBD1(buf)`, followed by the existing
forward NTT and block inverse tests. `fresh_f_accept_mass` and
`fresh_g_accept_mass` retain these actual acceptance predicates.

Each of the 192 terminal quartics splits into two factors `X^2-rho` with
nonsquare rho over F_3457. The word-status/determinant contract and forward-NTT
terminal representation connect every actual rejection to divisibility of the shaped
input polynomial by one of the 384 quadratic factors. The roots and their
connection to the existing Montgomery constants are checked in
`NTRUPlus768AcceptanceRoots.ec`, with the rejection cover supplied by
`NTRUPlus768AcceptanceAlgebra.ec` and `NTRUPlus768AcceptanceCover.ec`.

For each factor, five selected head bits of each parity have injective weighted
binary sums. The exponent sets are 0,1,2,3,4 except for roots
252,974,2483,3205, which use 0,1,2,3,5. All ten bits lie in the first two
bytes; the other 190 bytes remain fixed. At most one assignment to these ten
bits makes both quadratic remainder coordinates zero. The argument compares
the actual post-XOR bits. The common tail, unselected bits and f's constant
term cancel in the polynomial difference; multiplication by 3 is invertible
in the field. No XOR-linearity of CBD1 is assumed.

`NTRUPlus768AcceptanceInput.ec`, `NTRUPlus768AcceptanceHeadReduction.ec` and
`NTRUPlus768AcceptanceMasks.ec` connect this argument to the actual buffer
layout and shaped input polynomial. The finite weighted-sum certificate is in
`NTRUPlus768AcceptanceSlices.ec`. Uniform192 is invariant under each of the
1,024 XOR masks. Their translated bad events are pairwise disjoint, so
`acceptance_bad_probability` bounds each quadratic bad event by 1/1024.
A union bound gives rejection mass at most 384/1024 = 3/8 and hence

```text
fresh_f_accept_mass >= 5/8
fresh_g_accept_mass >= 5/8.
```

The endpoints `fresh_f_accept_lower` and `fresh_g_accept_lower` are in
`NTRUPlus768AcceptanceProbability.ec` and have no positivity premises. The
finite disjoint-event and union calculations are in
`NTRUPlus768UniformOrbitBound.ec`. No independence between different factor
events is assumed.

Acceptance still conditions each entire buffer, preserving dependencies
among its coefficients. `fresh_accepted_pair_normalized` makes the existing
product `dcond uniform192 keygen_f_accept * dcond uniform192 keygen_g_accept`
lossless. The fresh unrestricted caller and its counted version now terminate
without extra positivity premises. A cached real-ROM answer does not inherit
a fresh per-call acceptance rate; the stopped/collision argument handles that
difference.

## Concrete retry and collision error

The comparison retains independent uniform 32-byte seed draws, an initial E
table with at most `a` distinct entries, the same initial F state, and no
interleaved external E queries during the standalone KeyGen call. For
nonnegative f/g budgets,

```text
tau(q_f,q_g) <= (3/8)^q_f + (3/8)^q_g.
```

Choose 256 attempts for each phase in the analysis, so the total budget is
512. A conservative simplification uses `1-p_f, 1-p_g <= 1/2` and gives

```text
tau(256,256) <= 2/2^256
delta(a,512) = (512*a+130816)/2^256
error <= (512*a+130818)/2^256.
```

`NTRUPlus768AcceptanceBudget.ec` supplies the arithmetic certificate.
`certified_keygen_public_distance_256` in
`NTRUPlus768AcceptanceROMBound.ec` applies the bound to every output event
of the pre-existing public `Keygen` procedure. The same file bounds the
instrumented caller's missing mass and the counted actual ROM caller's sum
of late-return and nonreturning mass. Its `certified_keygen_empty_cache_distance`
specialization gives an error strictly less than `2^-239` for an empty initial
E table.

These results do not assert that unrestricted real-ROM KeyGen is lossless.
The implementation's rejection loops are unchanged; the retry budgets occur
only in the analysis. The bound compares KeyGen distributions and does not
measure decapsulation failure.

## Reproduction

Run from the repository root:

```sh
./scripts/verify-ntruplus768-keygen-acceptance.sh \
  --prior-evidence-root /path/to/thesis \
  --output /path/to/new-evidence-directory
```

The evidence directory must be new or empty and outside the checkout. Sources
are in `ntruplus/proof/768/ref/keygen_acceptance/`, and controls are in
`tests/ntruplus768/keygen_acceptance/`. The runner checks each new main with
a semantic EOF theorem and each isolated unfinished-proof negative, audits
source and tool/configuration/library inputs before and after execution, and
links unchanged prior imports to earlier evidence by exact hashes. Use the
completed run's `summary.json` and logs for actual counts and results.
The selected toolchain is September 2026 EasyCrypt/Why3 with Z3, `-no-eco`
and `Proofs:check`.
`--check-only` validates sources and controls without claiming a proof replay.
Finite diagnostics provide independent checks; they do not replace the
EasyCrypt root, mask, probability or actual-caller proofs.

## Remaining obligations

The subsequent [numerical DFR development](ntruplus768-kem-numerical-dfr.md)
connects the accepted-key/encapsulation joint law, actual H/G query freshness
and the integer no-wrap tail for one initialized honest ROM experiment with
uniform seeds and coins. The KeyGen comparison theorem on this page retains
its stated initial-cache and standalone-query scope.

Average-to-worst correctness, public-key-dependent FO reasoning and IND-CCA
still require the appropriate adversarial oracle and decapsulation interfaces
and security reduction. Native SHAKE/RNG, C memory/ABI correspondence and
full-API leakage security retain their existing boundaries. This proof-only
milestone changes no C/Jasmin code and reruns no extraction, native, Safety or
CT/SCT checkpoint. It does not establish a concrete SHAKE-to-ROM theorem.
