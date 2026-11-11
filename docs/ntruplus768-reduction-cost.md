# NTRU+768 reduction resource accounting

This family proves local resource counts for the **actual** public lookup,
candidate extractor and raw-oracle handler. It also proves that discarding
these local measurements preserves the original hardness-game success
probabilities and the preceding IND-CCA inequality. It does not yet prove
a whole-reduction running-time or PPT theorem.

Run the strict EC-only replay:

```sh
./scripts/verify-ntruplus768-reduction-cost.sh
```

The default prior-evidence root is the sibling thesis directory. Override
it with `--prior-evidence-root '/path/to/thesis'`. Use a new external
`--output` directory. `--check-only` reports `SOURCE_CHECK_ONLY`, not a
fresh proof replay. The runner uses cryptotools-2026.09, Z3, `Proofs:check`,
`-no-eco`, timeout60/max-provers1 and jobs2. It verifies every new main
and requires its own unfinished-final-proof copy to fail at the semantic
EOF sentinel. Imported EC/Coq proofs are hash-linked to the earlier full
short-relation replay; they are not freshly proved in this family.

## What is counted

`CostLookup(G).decap` returns `(reply, visits, encryptions)` using the
same history snapshot, enumeration, suffix test, real `SimEncrypt` call,
early stop and challenge exclusion as `SimLookup`. For an initial
history of length `L`, `0 <= encryptions <= visits <= L`. A blocked
challenge makes both counts zero. With `SecGLogged(FOGActual)`, the
existing G list grows by exactly `encryptions`, including cache hits.
No new global state is introduced. The generic projection has the same
G frame restriction used by the original lookup; the actual logged
backend discharges it without any additional restriction on A.

`CostExtract.run` returns `(answer, visits)` and calls the actual
`SecCandidate` at every visited query. Its first component is the original
answer. Its second component is exactly `find eligible queries + 1`
when an eligible entry exists, otherwise `size queries`. Repeats and
excluded candidates are still inspected; there is no memoization or
full message-space search.

`CostRaw` returns the original response, valid-request input bytes and
returned bytes. Outputs are at most224bytes. A valid output-length-zero
request still calls the real handler and can update H/G state. Invalid
output lengths are rejected before full dispatch. Input byte lists are
unbounded: for every B>=0, one zero-output request with B+1 zero bytes
has input volume greater than B. Payload length is not a count of actual
memory reads or a claim about the decoder's instruction cost.

## Finite-call arithmetic

For nonnegative integers d,h,g and an explicit finite list of at most d
lookup measurements, each with
snapshot size at most h, let V be summed visits and K summed encryptions.
The actual per-call result supplies the local validity predicate. Then:

```text
0 <= K <= V <= d*h
if extraction input length is g+K:
  extraction visits e <= g+d*h
  V+e <= g+2*d*h
```

For nonnegative call weights Cenc,Cext:

```text
K*Cenc + e*Cext <= d*h*Cenc + (g+d*h)*Cext.
```

The trace, history cap and extraction-length equation are **explicit
premises** of the summation theorem. This family does not construct the
complete adaptive operational trace of an abstract A or derive all
of its resource bounds from the previous security query contracts.
The existing qC bounds distinct H entries in a particular CPA phase;
it does not bound every repeated F/G or untyped raw call. Known-backend
qH cannot be silently reused for another backend.

## Connection to the probability theorem

Result-discarding wrappers retain the original oracle interface.
Projection composes through the actual adversary phase, transcript,
INJ/OW reducers, two NTRU distinguishers and RLWE solver. The original
IND-CCA experiment and its hypotheses are unchanged. The numerical
bound is the same as in [the preceding statistical proof](ntruplus768-short-relation-bound.md),
with the three equivalent instrumented attackers in its right-hand side.
The projection wrappers discard the local profiles; the final security
theorem does not return or bound a global accumulated time counter.

## Remaining execution-cost boundary

`elems(fdom log)` is a mathematical finite-set enumeration. The installed
library defines the domain via a choice-based finite conversion, and
neither this operation nor the finite maps have a machine-cost contract.
A concrete representation/refinement and an adversary execution-cost
semantics are needed before asserting a total RAM, bit-cost or CPU bound.
Changing the enumeration order is not an innocuous optimization: the
lookup returns its first match, so preservation must be justified.

The three final hardness attackers contain no KeyGen rejection loop.
They call A at most once after the fixed-size guard/codec operations.
Conditioned sampling and KeyGen retries occur in their challengers or
intermediate games. Probability-one termination does not establish a
worst-case time bound. Fixed768 local counts also do not by themselves
establish an asymptotic security-parameter PPT theorem.

No native C/Jasmin changes, new Safety/CT/SCT claims, new algebraic or
hardness axioms, QROM result or HAETAE UF-CMA result are introduced.

## Subsequent concrete public-history refinement

The [history refinement](ntruplus768-history-refinement.md) supplies
explicit list/byte operations, representation proofs and a finite-history
lookup-order discrepancy bound. It preserves the key distinction above:
local operations and fixed-query experiments are not by themselves a
complete adaptive execution or total-cost theorem. The subsequent
[adaptive-history proof](ntruplus768-adaptive-history.md) connects that
execution, and the [runtime-bound proof](ntruplus768-runtime-bound.md)
closes its fixed-768 source-calibrated cost model. General PPT, native
CPU/bit costs and implementation correspondence remain separate.
