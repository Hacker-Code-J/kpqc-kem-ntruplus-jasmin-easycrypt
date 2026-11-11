# NTRU+768 Decaps entry guard

The source follows the validation block in official commit
`3991b2ae08d6f0008d37e41b8aceaaab27b4ec89`. It calls the already verified checked
byte decoder; the rest of Decaps remains outside this Jasmin slice.

## Functional contract

Inputs are a 1152-byte ciphertext and a 2304-byte secret-polynomial prefix.
Let `D` be the byte decoder, `C` its canonical-encoding predicate (all decoded
coefficients below 3457), and `F0`, `H0`, `S0` the initial output contents.

| First rejecting block | Polynomial outputs | Shared secret | Guard status |
| --- | --- | --- | --- |
| ct | D(ct), F0, H0 | 32 zero bytes | 1 |
| f (after canonical ct) | D(ct), D(f), H0 | 32 zero bytes | 1 |
| hinv (after canonical ct and f) | D(ct), D(f), D(hinv) | 32 zero bytes | 1 |
| none | D(ct), D(f), D(hinv) | S0, unchanged | 0 |

`NTRUPlus768DecapGuardProof.ec` proves the actual freshly extracted program
satisfies this specification and terminates. The decoder equivalence binds
its namespaced helper to the existing checked-decoder theorem. No new
axioms or admitted proof goals are used in these handwritten proof files.

The native ABI has six pointers: `cp, fp, hp, ss, ct, skpoly`. Each polynomial
output occupies 1536 bytes and is aligned to two bytes. The six regions are
valid and pairwise disjoint. Only ct/skpoly require initially readable values;
no output initialization is needed by the safety check. The final hash bytes
in the official 2336-byte key are not read or modified by this guard.

## Information-flow contract

Ciphertext bytes are public in ordinary execution and transient under the
SCT policy. Secret-key bytes and decoded values remain secret. Short-circuit
branches on malformed secret-key encodings can reveal their validity, so the
implementation explicitly discloses only the two key-validation bits and
uses the declared speculation protections before branching.

`decap_key_validation_bits_zero` proves both disclosed values are zero under
canonical encoding of the two secret-key blocks. `decap_valid_keys_guard_status_equal`
proves equal guard statuses for the same ciphertext across such key prefixes.
These are value-level facts supporting the declared policy, not a separate
proof of trace non-interference. Establishing this encoding premise at actual
key-generation/API callers remains part of full implementation composition.
Canonical encoding is distinct from algebraic key validity.

The replay checks the annotated CT/SCT policy and also requires both checkers
to reject the source with the two disclosures removed, specifically for
secret-to-public flow. This is not a claim that arbitrary malformed keys
satisfy strict CT, nor a proof of full KEM CT/SCT. Safety is established
separately for the same guard and memory conditions.

## Caller and native integration

The abstract caller stops on entry rejection, without invoking the arbitrary
continuation or changing its globals, and without a termination assumption
on that continuation. On guard acceptance it invokes the body once and
propagates both its shared-secret output and final status. The final status
may still report failure from the later Decaps checks.

The native adapter replaces exactly the validation block in pinned official
C. The normal arithmetic, hashes and cleanup remain C. Its regression uses
all official KAT cases plus canonical and malformed inputs. Standalone tests
use an independent bit-stream decoder oracle and check all output values,
skipped-buffer preservation, input preservation and surrounding canaries.
The C reference's decoder counts and the mixed caller's later-operation order
are instrumented; the Jasmin guard itself is one native trace event. Internal
Jasmin short-circuit behavior is established by source/proof structure and
output contracts, not a fabricated count of its inlined calls.

## Reproduce

Run `./scripts/verify-ntruplus768-decap-guard.sh` with a consistent 2026.09
toolchain in PATH, or select binaries with the documented environment
variables used by the existing entry-guard driver. Evidence goes to a new
external directory. A successful full run includes raw nine-file extraction
comparison, source/reference pins, semantic EOF proof probes, the open-proof
negative control, strict-policy negative controls, normal and UBSan native
runs and before/after hashes of verification inputs. `--native-only` reports
`NATIVE_PASS`, never full proof `PASS`.

This does not prove the entire Decaps program or its C/Jasmin equivalence.
The full official arithmetic migration, normal-path caller connections,
recovery failure bounds and IND-CCA reduction remain separate obligations.
