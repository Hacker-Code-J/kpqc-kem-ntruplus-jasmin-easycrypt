# NTRU+768 Decaps entry guard replay

From the repository root, run:

```sh
./scripts/verify-ntruplus768-decap-guard.sh --output /tmp/new-empty-evidence-directory
```

The default run requires fresh extraction, pinned proof sources, EasyCrypt proof
checking with semantic end-of-file guards, Jasmin safety and policy checks, and
normal/UBSan native tests before reporting `PASS`. `--native-only` omits the
EasyCrypt proof replay and reports only `NATIVE_PASS`; it is not a proof result.
Tool overrides follow the existing artifact convention (`JASMINC`, `JASMIN2EC`,
`JASMIN_CHECKSAFETY`, `JASMINCT`, `EASYCRYPT`, `WHY3`, `CC`). The selected toolchain
must include the repository's Jasmin/EasyCrypt model version.

The six-pointer guard takes three writable 768-word polynomial buffers, a
writable 32-byte shared-secret buffer, a 1152-byte ciphertext, and the first
2304 bytes of the secret key. Inputs and outputs are disjoint; polynomial outputs
are 16-bit aligned. The input byte arrays are initialized. A failure zeroes all
32 secret bytes and leaves polynomial outputs after the first rejected decoder
unchanged. Acceptance preserves the incoming secret buffer.

Native coverage includes 87,851 standalone guard vectors, all 100 pinned official
KATs (both complete C and mixed C/Jasmin APIs), 4,622 malformed ciphertext/key
pairs, and 356 canonical-encoding pairs including 32 fresh keypairs. Every
coefficient is tested at canonical/noncanonical boundaries; selected first,
middle and last positions cover all 4096 encoded values. Multiple simultaneous
invalid inputs test short-circuit behavior. Tests check output canaries and input
preservation, including all 2336 full secret-key bytes in API tests.

The reference files and their license are copied byte-for-byte from the pinned
official commit named in `reference-manifest.json`. Only the generated mixed
copy replaces the exact Decaps validation block. The original success body,
shared-secret failure masking, cleanup, and return statement remain unchanged.
Shared instrumentation namespaces both C APIs and observes calls to their real
dependencies. It observes individual decoder calls in the official C version
and a single guard call in the mixed version. Native tests do not instrument
Jasmin's internal loads or decoder calls.

The CT/SCT policy keeps key bytes secret and explicitly discloses two
canonical-encoding predicates. The specification proves those predicates are
zero on canonical secret-key encodings. Both checkers must reject a temporary
variant without those disclosures. This does not establish unconditional
constant-time behavior for malformed secret keys, algebraic key validity,
whole-Decaps correctness, or IND-CCA security.

The caller theorem models the extracted guard composed with an abstract body;
it propagates the body's shared secret and final status. It is not a theorem
about the official C AST or the complete extracted KEM. Native and UBSan tests
provide finite differential regressions, not formal C-to-Jasmin equivalence.
UBSan does not instrument the assembled Jasmin code or detect every invalid
memory access; Jasmin's safety result has its own explicit calling conditions.
