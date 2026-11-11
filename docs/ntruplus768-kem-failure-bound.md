# NTRU+768 symbolic decryption-failure bound

The new correctness experiment calls the existing Keygen, randomized
EncapRandom and CompleteDecaps array procedures in that order. Its public
result is one failure bit: either API status is nonzero, or the shared keys
differ. For generated valid keys, the Encaps status is proved zero, so the
failure event includes decapsulation rejection and key disagreement.

## Observing the recovery condition

A private instrumented experiment retains the accepted key-generation
witness and the actual 96-byte encapsulation coins long enough to evaluate
the existing integer no-wrap condition. It returns the same failure bit and
a second bit indicating violation of that condition. A projection equivalence
connects the public failure probability to this first private result.
The private copy is made immediately after the real coin draw; the existing
coin-clear procedure still runs. Seeds, accepted buffers, secret intermediate
values and the bad bit are not additional public KEM outputs.

The KeyGen and Encaps RNG calls occur in their original order. The common
KEMRNG interface has seed32 and coins96 ports backed by one mutable state;
the forwarding ports make no independence assumption. Hash-module separation
is explicit in the relational statements. Independently parameterized RNGs
and the iid specialization are stated separately.

## Probability statement

Under the functional hash contracts, failure on a returned execution implies
violation of the sufficient integer recovery condition. The event inclusion
and public projection establish

    Pr[public correctness experiment returns failure]
      <= Pr[instrumented experiment reports no-wrap violation].

Both sides refer to corresponding executions from the same initial state,
not to an independently substituted key or ciphertext distribution. Violation
of no-wrap need not itself cause failure, so the inequality need not be tight.
No numerical estimate for the right-hand side is provided.

The generic inclusion is also valid for subdistributions: nonterminating
executions contribute to neither returned event. A separate theorem gives
probability-one termination in the iid model, requiring a lossless 32-byte
seed law, positive f/g acceptance masses, a lossless encapsulation source,
and the explicit expansion/hash contracts. The mathematical-hash instance
uses the fixed SHAKE256 expansion and an arbitrary lossless 96-byte coin law.
Any independently established bound epsilon on the bad event then transfers
to the public failure probability.

In the iid specialization, the accepted-key distribution is the conditioned 32-byte seed law
followed by fixed SHAKE expansion. Independent uniform 192-byte buffers are
not assumed. A future ROM argument must justify any change of distribution,
including seed/query collision events. Positive acceptance for the chosen
fixed expansion and seed law remains an explicit condition.

## Verification and remaining scope

The development sources are in ntruplus/proof/768/ref/kem_failure_bound/.
The replay entry is scripts/verify-ntruplus768-kem-failure-bound.sh.
The coherent replay checked all four new mains and 21 lemmas with
Proofs:check and semantic EOF witnesses. Four deliberately unfinished proofs
were rejected, and 33 source/proof-policy and diagnostic regression controls passed. Imported
inputs, effective tools and external library/configuration files are fixed
by hashes before and after the run. Earlier imported proofs are reused with
hash-matched evidence.

This change adds a probability experiment and proofs. Native C/Jasmin code,
previous safety/CT/SCT results and compiled regression records retain their
existing scope. Native SHAKE/RNG behavior and C orchestration, memory and ABI
correspondence remain external. The result is neither a numerical
NTRU+768 decryption-failure bound nor an IND-CCA reduction.
