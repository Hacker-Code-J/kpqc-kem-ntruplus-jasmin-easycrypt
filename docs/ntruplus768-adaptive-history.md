# Adaptive NTRU+768 list-history reduction

This family connects a persistent concrete H list to the entire adaptive
attacker phase and bounds the **original `CCAOriginalGame(A)`** using
three actual list-based NTRU/RLWE reduction attackers. It extends the
fixed-query/single-lookup result in [history refinement](ntruplus768-history-refinement.md).

```sh
./scripts/verify-ntruplus768-adaptive-history.sh
```

`--prior-evidence-root '/path/to/thesis'` selects the preceding evidence.
`--check-only` checks sources/provenance and never reports a full proof
PASS. The full runner compiles every new main using `Proofs:check`,
`-no-eco`, Z3, timeout 60 and max-provers 1, with at most two concurrent
mains. Each has a semantic EOF check and an own-file unfinished-proof
rejection. It also checks five positive/six negative private-state scope
fixtures and the actual final theorem's printed and independently typed
export. Imported EC and Coq sources are hash-linked to the preceding
history-refinement full PASS; they are not counted as fresh replays.

## Actual persistent implementation

`AHState` defines the list/context representation and procedure-only
`AHStore` interface. `AHAdapter` implements the wrapper, typed/raw H
recording and list decapsulation. Valid raw H calls obtain the full
224-byte H response, record it once, then return the requested prefix;
output length zero follows the same path. Invalid lengths and other raw
requests retain the original forwarding behavior. Repeats reuse the H
cache but still perform the list update. Internal reencryption G calls
use the supplied `O.g`, so actual G recording is preserved.

The final concrete `AHPrivateStore` uses `HistTable.put`, with its explicit
list/byte loops. It is genuinely local and is declared **after** the
original abstract adversary. This gives freshness without adding a new
`-History` exclusion to that adversary. A local alias of old global state
would not suffice. Initialization, snapshot, update and termination
obligations are all discharged for this concrete store.

## Adaptive comparison

`AHFreshBound` uses the actual number of distinct public H entries as
the failure-event rank. A fresh H response contributes at most
`fo_error(w,g)`; a cached repetition introduces no new error while the
cache is good. Empty ROH is justified by the existing CPA initialization.
The original `hoare[CPAPhase(A).run: true ==> fsize SimHistory.h <= qC]`
contract is transported by exact projection. No new total-H query cap,
termination assumption or arbitrary game-distance premise is introduced.

`AHCallbacks`, `AHRawCallbacks` and `AHCoupling` connect every typed/raw
oracle and Decap call through adaptive continuation, up to the actual
correction-error event. Challenge exclusion and physical caches are
preserved. The legacy lookup counter and old/new internal G query order
are not required to be equal. `AHCPAGames` and `AHCPABound` connect this
pointwise comparison to the actual fresh key/G setup and prove:

```text
|Pr[CPA(A)] - Pr[CPA(AHWrapper(S,A))]| <= qC / 2^353.
```

The generic store premises of this intermediate statement are discharged
by the final local store; they are not final assumptions.

## Actual G transcript and final original-game bound

`AHReduction` applies the existing computational-injectivity/one-wayness proof to the
list wrapper. Its own G transcript feeds the existing `SecExtract`.
`AHActualReduction` removes unused outer `SimHistory` and `SimPublic`
bookkeeping by exact projection. Actual final transcripts use `FOGRaw`
and the concrete list lookup; they do not call the old `SimLookup`.
Ideal ROM caches remain in the model.

`AHFinal.ah_original_adaptive_history` exports:

```text
forall A with the original restrictions,
  exists DI DO CO,
    forall initial memory and qE q0 qH qC,
      original contracts => original CCA advantage <=
        2*(DeltaNTRU(DI)+DeltaNTRU(DO)+epsRLWE(CO)+2^-244)/alpha_g
        +(130820+512*qE)/2^256
        +(q0+qH+d+2*qC)/2^353 +(qC+d)/2^768,
where d = max(0,budget).
```

The witnesses are the concrete `AHActual_DI/DO/CO(AHPrivateStore,A)`
constructions, chosen before all memories and budgets. The final
adversary restrictions, robust losslessness, initial-state and original
backend-specific query contracts are unchanged. The additional
`2*qC/2^353` is **outside** the accepted-key denominator `alpha_g`.
The NTRU terms remain signed real-minus-uniform differences.

## Remaining scope

This family proves the full adaptive **probability** reduction with
concrete persistent public history. The subsequent [runtime-bound
proof](ntruplus768-runtime-bound.md) gives the same word-array witnesses
closed source-calibrated fixed-768 costs, including repeats, raw-input
volume and actual arithmetic/copying, with A's own work reserved separately.
The cost frontend, ideal ROM and unit-cost integer operations are explicit
model boundaries. This is not a CPU-cycle, bit-complexity or general PPT
result. Native SHAKE/RNG, C memory/ABI, Safety/CT/SCT, HAETAE UF-CMA and
QROM retain their separate obligations.
