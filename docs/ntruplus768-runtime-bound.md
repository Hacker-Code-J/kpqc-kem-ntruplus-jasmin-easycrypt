# Source-calibrated costs for the NTRU+768 reductions

This family gives the same three concrete word-array reduction witnesses
both the original classical-ROM IND-CCA inequality and a closed resource
bound for dimension 768. It extends the [adaptive persistent-history
reduction](ntruplus768-adaptive-history.md).

```sh
./scripts/verify-ntruplus768-runtime-bound.sh
```

`--check-only` checks source/provenance and calibration controls; it does
not report a full proof replay. `--draft` is restricted to source checks.
`--prior-evidence-root '/path/to/thesis'` selects the preceding evidence.
The full runner uses `Proofs:check`, `-no-eco`, Z3, timeout 60 and one
prover per main. Each new main has a semantic EOF check and an own-file
unfinished-proof rejection. Fresh-state scope fixtures and a separately
typed and printed final export are checked. Imported EC and prior Coq
sources are linked to the preceding adaptive-history full PASS and are
not counted as fresh executions.

## The same executable witnesses

`rt_original_runtime_bound` in `NTRUPlus768RTFinal.ec` exports three modules with actual
`measure` and `run` procedures. The witnesses are
`RTWord_DI/DO/CO(RTPrivateStore,A)`, fixed before all initial memories,
query budgets, represented inputs and self-work reserves. The private
store is created after the original abstract adversary. The original
adversary restrictions and all security termination, initial-state and
backend-specific query contracts are retained.

The executable hardness inputs are coefficient-word arrays. `RTWordCodec`
and `RTWordKernels` use actual scaling, NTT, inverse NTT, checked decoding,
public inversion, recovery, encryption and collision-checking procedures.
Polynomial reification is used in specifications and challenger-side
representation proofs. No exponential enumeration, choice-based history
traversal or abstract polynomial operation is assigned unit runtime.
The internal two CBD1 samples and challenge encryption of the INJ
reducer occur once in its completed kernel profile. The one-way reducer
counts its own corresponding calls; the RLWE solver does not acquire
these calls. `RTPsiSampler` proves the exact CBD1 sampling law from
uniform bytes and calls the actual extracted sampler.

Discarding the returned certificates preserves the result and relevant
state. The new/list execution uses its own actual G transcript throughout
extraction; equality with the old map execution's G trace is unnecessary.
The reduction-internal auxiliary ROM setup is charged. Key generation
and sampling performed by the hardness challengers are excluded from the
reduction's own cost.

## Closed cost bound

For each returned reduction execution, let:

- `Q` count every public typed/raw oracle and decapsulation callback,
  including repeats, rejected raw requests and valid zero-output requests.
- `B` sum the lengths of all supplied raw-input lists, with repetitions.
- `t_A >= 0` reserve a separately supplied bound on A's own instructions,
  excluding the supplied oracle bodies.

`Q` is not the probability theorem's distinct-H budget `qC`. Internal G
calls are counted through actual lookup encryptions and the resulting
G transcript, rather than misclassified as additional public callbacks.
The concrete store maintains these counts throughout the adaptive phase.
No arbitrary finite trace or upper bound on the entire reduction time is
assumed.

The source-calibrated charged cost satisfies:

```text
Cost_R(t_A) <= t_A + 10909917*Q^2 + 32450882*Q + 64*B + C_R,
C_DI = 17679874,
C_DO = 10492283,
C_CO = 18463740.
```

Here `C_R` is the listed fixed contribution, including the actual `run`
dispatcher. Its entry, single call to `measure` and returned result add
2,309 units for DI/DO and 9,222 for CO. Result projection alone does not
remove this cost. The cost clauses use the profiles returned by `measure`
to charge the complete corresponding `run` execution.
`rt_complete_bound_values` in `NTRUPlus768RTCompleteCost.ec` checks these exact coefficients.
Fixed setup is included even when `Q=0`. Fixed branch work is
conservatively reserved, so the bound is not a performance measurement.
Bounds on actual `Q,B` may be substituted using the proved monotonicity results.

The formal result charges the supplied reserve `t_A`; it does not infer
an arbitrary adversary's own computation bound. Interpreting the complete
charge as an execution-cost upper bound requires that reserve to bound
the adversary's own work in the stated model.

## Cost semantics and trust boundary

`RTStepSemantics` fixes scalar word operations, loads, stores, branches,
allocation, random-byte draws and ideal-oracle operations. Owned array
boundaries reserve allocation, read and write per cell. Immutable lists
share tails; node construction and fixed-payload copies are charged.
Fixed array initialization, comparisons and byte slicing have explicit
loop implementations and checked contracts. Integer guards and arithmetic
have unit cost. Proof-only counters, profiles and ledger observations are
erased, while every operation producing an actual answer remains.

`RTFixed*` closes the extracted arithmetic and codec bodies; `RTKernelCosts*`
composes their bounds and exact projections. `RTPhaseCost` prices the
actual history, raw-dispatch, lookup and extraction source blocks.
`RTOuterCost` accounts for the remaining calls, guards, tuple construction,
array copies and fixed initialization. These prices are generated or
reconstructed from the source instruction rules and a closed primitive
allowlist. The checking frontend and those pricing rules are part of the
cost interpretation's trusted base. EasyCrypt checks the procedure
contracts and algebraic composition; it does not by itself assign
runtime to arbitrary source expressions.

The harness checks source-derived charges in addition to source hashes.
Changing a tick, its claimed bound and its pin together must still fail
the instruction-rule controls. Fresh generation is compared with the
frozen measured bodies. Final full PASS requires the complete proof,
negative-control, export and source-calibration checks with unchanged
source and external-input hashes.

## Unchanged probability inequality

For the same three witnesses:

```text
Adv_CCA(A) <=
  2*(DeltaNTRU(DI)+DeltaNTRU(DO)+epsRLWE(CO)+2^-244)/alpha_g
  +(130820+512*qE)/2^256
  +(q0+qH+d+2*qC)/2^353 +(qC+d)/2^768,
where d = max(0,budget).
```

`DeltaNTRU` is the signed real-minus-uniform difference under the existing
unit-conditioned-denominator convention. The acceptance factor and all
previous loss terms are unchanged. Word representation and resource
instrumentation add no probability loss. The same witnesses satisfy the
cost clauses and this security clause; they are not selected separately
for different memories or budgets.

## Scope

This is a closed, source-calibrated bound for fixed NTRU+768 under ideal
ROM primitives and unit-cost integer/word operations. It is not a CPU-cycle
measurement, bit-complexity analysis, or a general PPT theorem for an
asymptotic parameter family. The abstract ROM interfaces do not verify a
native SHAKE/RNG or a native cache implementation. No new C/Jasmin,
Safety/CT/SCT, memory/ABI, HAETAE UF-CMA or QROM result is claimed.
