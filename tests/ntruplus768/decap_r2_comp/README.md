# NTRU+768 Decaps r2 calculation

Run from the repository root:

```sh
./scripts/verify-ntruplus768-decap-r2-comp.sh
```

The entry point checks the actual `decap_r2.jazz` composition
`basemul(c - NTT(m1), hinv)` and its extracted EasyCrypt procedure. Four
1536-byte, 2-byte-aligned native buffers must be disjoint. Inputs `c` and
`hinv` have canonical coefficients in `[0,3457)`; `m1` has signed coefficients
in `{-1,0,1}`. The returned polynomial has signed coefficients in
`[-3457,3457)`. The source writes the output without reading its incoming
contents, and the functional theorem quantifies over every incoming array.
The default safety checker assumes initialized exported arrays; a successful
default analysis is not evidence that this checker assumption was removed.
All four values are secret under CT/SCT, with no new declassification.

The immutable official C/KAT fixture is reused from
`../decap_guard/reference`, at commit
`3991b2ae08d6f0008d37e41b8aceaaab27b4ec89`. No second fixture is vendored.
The NTT kernel remains the frozen implementation with Barrett reductions at
each radix-2 butterfly. The official C implementation performs the final
Barrett sweep instead. `audit_compatibility.py` identifies this exact source
difference and checks the reducers, twiddles, subtraction and multiplication
dependencies. This source audit is not a proof that the two C programs are
equivalent. Native comparison verifies exact final words on the tested
inputs; the machine proof concerns the extracted Jasmin composition.

The replay includes:

- Pinned source/dependency and official-fixture checks; byte-for-byte fresh
  r2, guard and candidate extraction checks; eight negative gate controls.
- Individually compiled generated and handwritten EasyCrypt mains with
  `Proofs:check`, no `.eco` cache and semantic EOF guards. An unfinished final
  proof must be rejected. Reviewed proof hashes and all input hashes are
  recorded before and after execution.
- Native compilation, safety analysis, CT and SCT checks of the r2 source.
- Exact C/Jasmin output comparison for 14,444 cases: constant boundary
  combinations, every coefficient of all three inputs at their boundaries,
  sparse trits and 2,048 deterministic random triples. Inputs and canaries
  are checked along with output range and native buffer conditions.
- 100 official KATs against three implementations: official C, an exact
  r2-block splice, and exact guard/candidate/r2 block splices. All other C
  bytes, including later rejection, secret masking and cleanup, remain
  unchanged. The standalone r2 export preserves its inputs, so the splice
  leaves C's dead `c`/`m2` values unchanged until cleanup; it does not claim
  erasure equivalence for Jasmin scratch storage.
- 4,622 malformed-encoding triples and 356 canonical-encoding triples,
  including 32 fresh keypairs and 224 cases rejected after the encoding
  guard. Malformed encodings invoke no candidate/r2 or normal continuation
  calls. Accepted encodings invoke the selected normal calls exactly once,
  and later failures preserve their status and zero shared-secret result.
- Both ordinary and UBSan builds. UBSan instruments C only. Each Jasmin
  export contributes one call event; these events are not internal memory
  access traces or a whole mixed-C API CT/SCT proof.

`--native-only` omits EasyCrypt and reports `NATIVE_PASS`, never full `PASS`.
`--defer-safety` omits the costly safety run and adds `_EXCEPT_SAFETY` to the
result. Combining both therefore reports `NATIVE_PASS_EXCEPT_SAFETY`.
An output directory must be empty and outside the checkout. Tool overrides
include `EASYCRYPT`, `WHY3`, `JASMINC`, `JASMIN2EC`, `JASMIN_CHECKSAFETY`,
`JASMINCT`/`JASMIN_CT`, and `CC`; tool paths, hashes, commands and logs are
recorded in `summary.json`.
EasyCrypt subprocesses default to `OCAMLRUNPARAM=o=20`, as required by the
previously verified large subtraction/recovery bridge files on this machine.
This changes the OCaml heap policy, not the proof statements or checking mode;
its selected value is recorded for each proof command. An explicit environment
value overrides this default.

This component computes r2 under its input contract. It is not a complete
Decaps implementation, an unconditional original-randomness recovery theorem,
a C-AST equivalence proof, a full API CT/SCT result, or an IND-CCA reduction.

The replay also checks an executable integer interval certificate for all
trit inputs. A strict token comparison binds both source schedules, twiddles
and reducers. The official pre-final coefficients lie in [-14821,14821],
inside the exhaustively checked Barrett centered domain [-22470,22470].
All butterfly argument/store narrowings fit int16 and all arithmetic
intermediates fit int32; intentional Montgomery low-word truncation is
modeled separately. Both final arrays have coefficients in [-1728,1728].
Modular preservation and uniqueness then explain their final word equality.
This is a source-audited arithmetic argument supported by an executable
certificate, not an EasyCrypt theorem about a C-AST semantics.
