The entry point is `scripts/verify-ntruplus768-history-refinement.sh`.

The final reviewed inventory has nine mains: `HistKey`, `HistModel`,
`HistTable`, `HistLookup`, `HistOrder`, `HistBuild`, `HistBound`, `HistCosts`, and `HistAverage`,
each with the `NTRUPlus768` filename prefix. Draft inspection can accept a
partial inventory and never reports a proof PASS.

Before the root authorizes a freeze:

```sh
bash scripts/verify-ntruplus768-history-refinement.sh --check-only --draft \
  --prior-evidence-root '/path/to/thesis' --output '/new/evidence/directory'
```

This reports `DRAFT_SOURCE_CHECK_ONLY`, with zero declared proof replays or
missing-qed negatives. After root review, supply the exact semantic EOF
declarations and module binders in a manifest:

```sh
python3 tests/ntruplus768/history_refinement/freeze_manifest.py \
  --manifest /path/to/reviewed-manifest.json
```

The explicit freeze only creates source pins. `--check-only` then reports
`SOURCE_CHECK_ONLY`; omit both source-only flags for strict replay. Each
frozen main must pass `-no-eco -pragmas Proofs:check -p Z3 -timeout 60
-max-provers 1`, and each isolated missing-final-qed copy must fail at its own
unfinished proof. Trailing declarations are retained. Independent mains run
in dependency layers with at most two jobs and OCaml GC parameter `o=20`.

The executable syntax gate supplements source hashes and actual EC proofs.
It rejects abstract map enumeration/lookup, choice, hidden specification
helpers, full-key/cipher comparisons, uncounted filter/reverse operations and
unexpected globals in concrete bodies. Mathematical maps and extensional
equalities remain allowed in specifications and proofs. Indexed reads are
restricted to the reviewed 128/32/1152-byte comparators. Three literal zero
defaults have exact definition checks.

`HistBuild` is a local proof monitor with secret proof data; it is not the
public implementation. Only `HistBound.HistProofMonitor` may declare its
four explicitly reviewed proof globals. `HistBuildPublic` accepts only a
query list. Its `ROH.init/get` calls still use an ideal random oracle; this
does not implement every ROM table or grant an original adversary a reset.
`HistBound.HistLookupAfterBuild` is a proof comparison wrapper: it installs
the prepared G map and copies the resulting H map into the legacy simulator
state before selecting the list or original map scan. That explicit exception
does not permit direct map reads in the public table/key/lookup implementations.
`HistPublicLookup(pk,suffix,qs,ct)` actually calls the public builder and the
list lookup and returns their combined resource annotations. It takes no
secret witness or prepared G function/map. `HistAveragePublicKernel` installs
prepared G only as a setup-comparison wrapper, then invokes that public
procedure. Its matching experiment samples the actual `FOSetupSource`.
The average declarations are checked exactly: their distance is
`size(qs)/2^353` for fixed qs/ct/event, with no arbitrary-kernel premise.
Order agreement is conditional on the proved good-entry/challenge
contracts, not on representation equality alone.

The prior reduction-cost full PASS is hash-pinned. Imported EC and prior
native Coq sources are linked to it, not recompiled as new mains. Current
common prover/library hashes must match. No new native Coq backend is used.
Byte tests, indexed reads and list visits are the stated resource units;
the harness does not establish machine-cycle costs, constant time, PPT or
a complete reduction running-time theorem.
