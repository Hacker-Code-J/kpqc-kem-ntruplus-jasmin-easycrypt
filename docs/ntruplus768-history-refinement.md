# Concrete NTRU+768 public H histories

This family replaces the public-history operations with explicit list and
byte loops, proves their map representation and operation counts, and
bounds the effect of lookup order in a **fixed finite H-query sequence
followed by one lookup**. The original adaptive IND-CCA theorem is not
changed by this extension.

```sh
./scripts/verify-ntruplus768-history-refinement.sh
```

Use `--prior-evidence-root '/path/to/thesis'` if the sibling evidence root
has moved. `--check-only` verifies sources and provenance only. A full
replay checks every declared main with `Proofs:check -no-eco`, Z3, timeout
60/max-provers1 and at most2 concurrent mains. Each main also has its own
unfinished-final-proof rejection at an exact semantic EOF sentinel.
Imported proofs are linked to the preceding reduction-cost full PASS;
new native Coq/C/Jasmin or CT/SCT replays are not claimed.

## Representation and actual operations

An H key is a96-byte message plus32-byte suffix. The key is128bytes;
the tagged raw H input is129bytes. Each value is an actual224-byte H
response. The invariant is `uniq(map fst rows) /\ ofassoc rows=table`.
`ofassoc`, filtering and reversal are specifications, not calls in the
concrete history procedures.

`HistKey.equal`, `.suffix`, `.cipher` read individual bytes and compare
all128/32/1152 bytes. They return the mathematical equality and exact
comparison count. Two indexed reads precede each comparison in the
code; this is not a native-load or CT theorem.

`HistTable.put` removes every old occurrence of the key, preserves the
relative order of retained entries via two explicit loops, then prepends
the new pair. It preserves the representation of `table.[key <- value]`.
For an input of length n and m retained entries, it returns exactly n+m
node visits and128n byte comparisons. `get` visits v<=n entries and
makes128v comparisons. No `FMap`, `fdom`, `elems`, `choice`, `filter` or
`rev` call occurs in these executable bodies.

`HistLookup(G)` scans the actual pair list and reads the stored value
directly. Suffix and ciphertext tests call the explicit byte comparators;
the encryption call is the existing real `SimEncrypt(G)`. It returns
`(reply, visits, encryptions, comparisons)` with:

```text
0 <= encryptions <= visits <= length(rows)
comparisons <= 1152 + 32*visits + 1152*encryptions
```

With the existing logged G backend, its list grows by exactly the
number of encryptions. Changing the history order can change this G
call sequence and its length even when the returned key is unchanged.

## Public builder and resource composition

`HistBuildPublic.run(queries)` takes no secret key or error function.
It starts with an empty ROH and local history, makes the actual ROH
requests and calls the concrete `put`. Repeated requests count among
Q=length(queries), but reuse cached H responses. Its history operations
have at most Q(Q-1) node visits and64Q(Q-1) explicit byte comparisons.
It returns these counts and exactly Q H requests.

`HistPublicLookup.run(pk,suffix,queries,ct)` additionally performs one
lookup using the existing G oracle state. Its result includes the reply
and the following bounds:

```text
history-node visits <= Q^2
explicit history/key/ciphertext byte comparisons <= 64Q(Q-1)+1184Q+1152
H calls = Q
SimEncrypt calls <= Q
```

These counters do not include ideal-oracle implementation, encryption
kernel instructions, native allocation or adversary computation. The
public code does not construct an eager G table. Fresh ROH initialization
is part of this experiment, not permission to reset the original KEM's
cached oracle.

## Lookup order and security connection

Under actual key correctness and a prepared G cache, error-free matching
entries with the key's public suffix give the same H input and shared key. List/map refinement turns
this into equality of the original and new lookup replies. The challenge
variant retains the required history inclusion and challenge consistency.
If replies differ, there is an actual `fo_base_bad` entry; an abstract
uniqueness premise is not inserted as an axiom.

`HistBuild` and `HistProofMonitor` are proof-only error monitors coupled
to the public implementation. A cached repetition cannot introduce a
new bad event while the cache is good. A fresh H response contributes
at most `fo_error(w,g)`. Thus the actual Q-request experiment satisfies
`Pr[bad] <= Q*fo_error(w,g)`, and every event on the reply has at most
that probability difference between the two lookups.

The final `hist_public_lookup_setup_distance` invokes the actual
`FOSetupSource` and compares the actual public list implementation with
the original map lookup experiment. It discharges the pointwise key/cache
conditions from setup support and uses the existing setup error average:

```text
|Pr[E(reply_list)] - Pr[E(reply_map)]| <= Q / 2^353.
```

There is no remaining arbitrary-kernel-distance assumption. The query
list and ciphertext are fixed before the experiment. The prepared G
cache belongs to the comparison proof; it is not claimed to be generated
by an efficient reduction implementation.

## Remaining obligations

The fixed-query theorem above is not itself a full adaptive replacement.
The subsequent [adaptive history proof](ntruplus768-adaptive-history.md)
provides the persistent-state access argument, connects the actual changed
G transcript and extraction, and derives an original-game bound for
three actual list-based reductions. The original map theorem remains
available. The later [runtime-bound proof](ntruplus768-runtime-bound.md)
closes source-calibrated fixed-768 costs for those actual word-array
witnesses. General PPT, CPU/bit costs, native memory/ABI correspondence,
HAETAE UF-CMA and QROM remain outside that result.
