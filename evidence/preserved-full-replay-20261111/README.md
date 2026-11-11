# Public preserved-environment runtime-bound PASS

The default `runtime-bound` verifier completed with **PASS** through the public
`env/replay_runtime.py` launcher, without `--check-only`. It used the source
archive for **`359b9279b7718912951a2ce9141d4014f92bbddf`**, its pinned proof
dependencies, the captured toolchain/home files and the explicit historical
evidence bundle. The ordinary-terminal execution is separate from the
[earlier failed attempt](../preserved-replay-attempt-20261111/README.md).

| Check | Verified result |
| --- | --- |
| Main proofs | 37/37 PASS |
| Each main's unfinished-proof control | 37/37 expected rejections |
| Actual exported theorem type | PASS, `rt_original_runtime_bound` |
| All commands and log hashes | 105 expected outcomes, 105 matching log hashes |
| Runner source/external audits | Unchanged; 1,121 source and 286 external entries checked |
| Full source archive manifest | 1,878 file hashes matched |
| Captured environment | All 3,145 file hashes, modes and inventory entries authenticated |
| Historical summary inputs | All 26 authenticated against their declared pins |

The [original runner summary](runner-summary.json) preserves the commands,
proof copies, negative diagnostics, source and tool hashes, calibration and
scope checks. The [subsequent verification record](verification.json) describes
the checks made when accepting this evidence. The exact source is identified
by [its manifest](source-manifest.json).

The complete launcher command took **23:57.69**, with GNU time maximum RSS
**2,694,052 KiB (about 2.57 GiB)**. See [resources](resources.txt). The runner
recorded 2026-11-11 13:56:28–14:20:25 UTC. No selected host override was supplied
in the [recorded launch context](launch-context.json); the verifier kept its
reviewed timeout, prover, concurrency, `Proofs:check` and `-no-eco` settings.

## Scope and preservation

This is a fresh full execution of the **runtime-bound target**. Imported EC and
Coq prerequisites remain linked to authenticated prior proof evidence. It does
not mean every proof in this repository was freshly executed.

The launcher hid the original home inputs behind the preserved files and used
explicit source, evidence and output mounts. Host OS libraries, the dynamic
loader and Python standard library remain dependencies. This was the same
Linux host, not a standalone OS image or an independent-machine reproduction.
The result retains all mathematical/model limits in the [claim map](../../docs/claims.md).

Historical proof manifests and the environment capture's creation-time status
were not rewritten. This new result is bound to their original bytes. The
tested source archive also remains unchanged; a later documentation/evidence
commit records the result without claiming a different tested source.

The full logs, checked copies, negative fixtures, source manifest, launcher
provenance, console output and resources are preserved in the attachment
identified by [archive.json](archive.json). Its filename, size and SHA-256 are
recorded there; no public download URL or DOI has been assigned yet. Namespace
paths under `/tmp/work/results/results/` correspond to `results/` in that archive.

Verify this directory, or the extracted complete evidence archive, with
`sha256sum --check --quiet SHA256SUMS`.
