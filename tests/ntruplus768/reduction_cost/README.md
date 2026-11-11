The shell entry is `scripts/verify-ntruplus768-reduction-cost.sh`.

The final inventory requires six mains: `CostExtract`, `CostLookup`, `CostRaw`,
`CostBounds`, `CostProjection`, and `CostFinal` (all with the `NTRUPlus768`
filename prefix). Draft checks can inspect a partial inventory without claiming
that it is complete. The final theorem declaration is compared with
`sr_original_numerical`, allowing only the three cost-instrumented reduction
algorithm substitutions; original adversary premises and numerical terms must
remain identical.

This family measures local list visits, candidate/hash calls and raw payload
lengths. It does not establish a complete reduction running-time or PPT theorem.
The conditional trace bound does not manufacture a trace of an abstract
adversary, and raw output length zero still processes an unbounded input payload.

Before a reviewed freeze, run:

```sh
bash scripts/verify-ntruplus768-reduction-cost.sh --check-only --draft \
  --prior-evidence-root '/path/to/thesis' --output '/new/evidence/directory'
```

This returns `DRAFT_SOURCE_CHECK_ONLY`: no proof mains or EOF checks are claimed.
The root selects the final inventory, theorem declarations and explicit module
binders in a manifest. After that approval, freeze explicitly:

```sh
python3 tests/ntruplus768/reduction_cost/freeze_manifest.py --manifest /path/to/reviewed-manifest.json
```

The freeze validates the exact last semantic theorem and its EOF reference; it
does not run or approve proofs. Then `--check-only` yields `SOURCE_CHECK_ONLY`,
and omitting both source-only flags performs strict replay. `EC_JOBS` supports
1 or 2, with independent new mains sharing a layer; the timeout is fixed at 60.
Full PASS requires every declared new main, its own missing-final-qed negative,
prior source provenance, overlapping tool/library hashes, and stable inputs.
Evidence directories must be new or empty and outside the checkout.

Imported EC and the previous 14 Coq proof sources are linked to the pinned
`ntruplus-short-relation-bound-20261018/final-replay/summary.json` full PASS.
These imported proofs are not freshly replayed here. New native Coq invocations
in the cost family are rejected. No original tool configuration is changed.
