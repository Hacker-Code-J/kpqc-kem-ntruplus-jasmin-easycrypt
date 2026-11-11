# Classical ROM contracts for the actual NTRU+768 array callers

This development supplies a classical random-oracle model and bridges its
realized answers to the existing KeyGen, randomized Encaps and CompleteDecaps
array programs. It does not establish a concrete SHAKE-to-random-oracle theorem,
a numerical decryption-failure rate, an IND-CCA reduction, or a QROM result.

## Model and scope

Four distinct lazy tables model seed expansion E and the tagged F, G and H
queries. E maps 32-byte seeds to 192-byte buffers; F maps 1152-byte public keys
to 32 bytes; G maps 1152-byte serialized polynomials to 192 bytes; H maps the
pair of 96-byte coins and a 32-byte public-key digest to 224 bytes. A missing
entry receives a uniform byte array. Every repeated query returns its existing
entry. The raw adapters preserve the actual domain tags and lengths, and the
typed encodings are injective. Their contracts concern the honest caller
domains; these restricted interfaces do not yet model all adversarial hash
queries in an IND-CCA experiment. E is separate from the tagged F/G/H domains.

Uniform arrays are defined from actual uniform bytes. The construction proves
full support, losslessness, uniformity, and point probabilities; it introduces
no new local axioms. Concrete hashes in earlier value specifications are not
silently substituted with unrelated ideal values.

## Actual caller bridge

Hash-free payload specifications retain the existing key arithmetic,
serialization, message recovery and ciphertext calculations. New caller
contracts use answers in the realized F/G/H tables. The public experiment
initializes the four tables and executes the unchanged array KeyGen,
randomized Encaps and CompleteDecaps bodies. Its random-byte ports may share
state, while that state is separated from all four tables.

Private instrumentation reads the accepted-key witness, actual coins and
already-recorded answers. It observes the sufficient integer no-wrap condition
for the actual sampled r and encoded message. A relational proof preserves
the public failure result and corresponding RNG/oracle states. Coin and
workspace clear calls remain in the actual caller path. Under the no-wrap
condition, decapsulation's G and H queries hit the same entries used by
encapsulation, so recovery yields equal shared keys and zero statuses.

Consequently, the public failure probability is bounded by the instrumented
no-wrap-violation probability in this ROM model. This is a returned-event
inequality on subdistributions. No unconditional termination theorem is
asserted for the finite-seed ROM rejection loops: a realized expansion table
can reject every seed. Positive acceptance for an independent fresh-buffer
proposal is insufficient to exclude that case.

## Fresh sampling and collision conditions

For arbitrary fixed 96-byte coins, XORing their mask into the first 96 bytes
of a uniform 192-byte buffer is a bijection. The extracted SOTP encoder
therefore has the same distribution as the extracted CBD1 procedure on a
uniform 192-byte buffer. The actual G-adapter result has this component law
when its serialized-polynomial input is absent from the G table. Cached
queries instead obey the value-consistency contract. This local fresh-query
law is not an unconditional independent law for the complete KEM.

A private seed observer wraps both existing KeyGen rejection loops. It
records every f/g seed draw, including failed attempts, without stopping the
real loops. Previously queried and external E inputs are de-duplicated;
marking an honest seed immediately after drawing it does not count it again
as an external input. Between sampling and expansion, a pending-seed
invariant accounts for the new draw. On return, the actual E-table domain
equals the union of the draws and observed prior inputs. Erasing the observer
preserves the actual public keys and E/F tables.

This separate collision experiment uses independent uniform 32-byte seed
draws. The general correctness inequality allows arbitrary shared-state RNG
laws and does not imply this specialization. For nonnegative draw and
known-input budgets q and a, the proved collision bound on completed
executions is (known inputs comprise distinct initial/prior and externally
marked E inputs not already covered by draws)

```
Pr[seed reuse or hit of an already known E input]
  <= a*q/2^256 + q*(q-1)/(2*2^256)
     + Pr[number of draws > q or number of known inputs > a].
```

The returned-run overrun term is retained. This inequality does not by itself
bound the distribution distance between two unbounded experiments when one
can diverge after a collision. Nor does conditioning on a collision-free
event preserve the original fresh law.

The subsequent [stopped-KeyGen transfer](ntruplus768-stopped-rom.md) resolves
this gap for the standalone KeyGen comparison. Separate f/g budgets, exact
fresh retry tails and an initial-cache collision bound give a two-sided
output-event bound for the actual unrestricted caller, and also bound its
missing mass and late returns. The fresh accepted buffers have the product
of their whole-buffer conditional laws. This continuation uses independent
uniform seeds, a bounded initial E cache and no interleaved external E queries;
its unrestricted transfer requires positive fresh acceptance masses, while
its finite tail formulas do not. It does not assume unconditional real-ROM
termination. Numerical failure, the remaining KEM distribution transitions
including G/H reuse, and IND-CCA remain separate obligations.

## Reproduction

Run `scripts/verify-ntruplus768-kem-classical-rom.sh` with the September 2026
EasyCrypt/Why3 installation and Z3. The runner's `--help` describes the pinned
prior-evidence root and output destination. This proof-only milestone checks
the new mains, semantic end-of-file statements, isolated unfinished-proof
negatives and source/diagnostic controls. It records effective tools,
configuration, imported theories and prover driver hashes before and after.
Prior checked imports are linked by exact source hashes; they are not reported
as newly checked mains. C/Jasmin, native tests, Safety, CT/SCT and extraction
were not changed or rerun here. Native SHAKE/RNG and C memory/ABI correspondence
retain the earlier external boundaries.

Sources are grouped in `kem_rom_oracle/`, `kem_rom_bridge/`,
`kem_rom_sampling/` and `kem_rom_collision/` under
`ntruplus/proof/768/ref/`; controls are in
`tests/ntruplus768/kem_classical_rom/`.
