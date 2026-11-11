# Full preserved-environment attempt

Status: **FAIL — Why3 automatic server connection failed**. This is separate
from the successful earlier runtime-bound replay using the existing host prover
layout. The tested source archive is commit `359b9279b7718912951a2ce9141d4014f92bbddf`.

The public `env/replay_runtime.py` launcher was invoked without `--check-only`.
It authenticated the captured environment and prior evidence, exposed only the
captured home inputs, and used the default runtime-bound verifier. Source policy,
mutation controls, tool identity, calibration and scope checks completed before
proof mains encountered `cannot start & connect to why3server`.
See the original [runner report](runner-summary.json),
[first failing proof log](first-proof-failure.log), [launch command](launch.json)
and [attempt summary](attempt.json).

The recorded source/external audits remained unchanged. A subsequent check also
matched every source-manifest file and all 3,145 captured input hashes, modes
and inventory entries ([integrity check](post-run-integrity.json)). This integrity
result does not convert the failed proof run into PASS.

## Diagnostic boundary

A separate [socket probe](socket-diagnostic.json) using the same launcher mount
layout passed. The captured Why3 server also created a socket and accepted a
connection when launched directly ([server diagnostic](why3-server-diagnostic.json)).
The expected helper exists and matches the recorded binary and executable mode.

EasyCrypt's automatic helper setup involves fork, process-group setup, execution
and connection. The generic error from the failed run does not identify which
operation failed or its errno. A definite socket-creation denial is therefore
not established for this attempt. The diagnostic invocations are separate
execution contexts and do not prove that the full-run context permits every
operation. No helper, proof gate, historical pin or permission policy was changed.

Rerun the unchanged public launcher in a normal supported terminal with a new
output directory. The local preparation directory contains `run-in-terminal.sh`,
which records selected configuration overrides, console output and resources
and reports the output path on the host. Its result must be inspected separately;
this failed record must remain unchanged.

Run `sha256sum --check --quiet SHA256SUMS` here to verify the stored records.
