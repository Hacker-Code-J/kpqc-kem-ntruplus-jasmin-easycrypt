The entry point is `scripts/verify-ntruplus768-adaptive-history.sh`.

The reviewed inventory contains 11 mains and 122 lemma declarations.
The final theorem is `ah_original_adaptive_history`, with actual witnesses
`AHActual_DI/DO/CO(AHPrivateStore,A)`. The manifest pins the exact source,
last semantic theorem of each main, exported type and actual printed type.

```sh
./scripts/verify-ntruplus768-adaptive-history.sh \
  --prior-evidence-root '/path/to/thesis' --output '/new/evidence/directory'
```

`--check-only` reports `SOURCE_CHECK_ONLY` and never proof completion.
Development-only `--check-only --draft` reports `DRAFT_SOURCE_CHECK_ONLY`.
`freeze_manifest.py --manifest /path/to/reviewed-manifest.json` validates
an explicitly reviewed inventory and creates pins; it does not run proofs.

Full replay uses `-no-eco`, `Proofs:check`, Z3, timeout 60, max-provers 1,
jobs at most 2, and GC `o=20`. Every main has an exact semantic EOF and
an isolated missing-final-qed copy that must fail at its own unfinished
proof while retaining trailing declarations. The manifest's `export_audit`
contains the literal expected type, separately captured actual printed type,
import preamble and three concrete witness terms.

The literal type must quantify original A with exactly the old SR restrictions,
then choose three module witnesses before all memories and query budgets. It
must not export the local store or add a store parameter. A fresh import probe
prints the actual theorem and proves that fully quantified literal type by
applying the fully qualified actual theorem. It preserves lexical whitespace
in generated code. Compiler reordering of exclusions is accepted only when
the exact duplicate-free restriction set is unchanged; the complete printed
type is also compared with its frozen snapshot.
The source goal is independently constructed from SRFinal by changing only
the three reducer names and appending `2*qC/2^353` outside `ow_alpha_g`.
This supplements source inspection of the genuinely
local concrete store declared after A and its actual `HistTable.put` call.
Generic store view/losslessness contracts are not final security premises.

The 11 pinned compiler-scope fixtures are copied from the separately reviewed
state-scope audit: five positive and six negative cases. They cover a concrete
local store after A, constructive module witnesses, a view-based store contract,
global aliases, earlier state, old private boundaries and local-state leakage.
Full replay checks each negative's own path, line and cause, not merely a
nonzero exit. The fixture export and the actual NTRU export are distinct checks.

The actual adapter records all 224 H bytes before returning a valid raw prefix,
including a zero-length prefix. Invalid lengths and non-H queries are forwarded.
Internal encryption uses the supplied G port. Actual final transcripts omit
unused old H-map bookkeeping and do not execute old `SimLookup`. Equal replies
alone do not justify reusing the old map scan's G-query transcript.

Imported EC/Coq sources are hash-linked to the pinned history-refinement full
PASS. Imported native Coq proofs are not replayed. Shared prover/library inputs,
new sources, isolated checked copies and final input hashes are audited. The
source scanner handles unnamed sections locally without weakening the shared
axiom/abstract-op/escape checks. No shared helper source is modified.

Finite Python diagnostics and generic scope fixtures are not a new security,
machine-time, constant-time or complete PPT proof.
