# NTRU+768 classical-ROM reduction to concrete ACWC2 IND-CPA

This family constructs a CPA attacker from the original KEM attacker.
The theorem `cpa_original_indcca` in
[`NTRUPlus768CPAFinal.ec`](../ntruplus/proof/768/ref/kem_indcpa_reduction/NTRUPlus768CPAFinal.ec)
proves the following bound, with advantage defined as the absolute
deviation of returning winning probability from one half:

```text
AdvCCAOriginal(A)
  <= 2 AdvCPAGame(CPAReduction(A))
     + (130820 + 512 qE) / 2^256
     + (q0 + qH,S + d) / 2^353
     + (qC + d) / 2^768.
```

Using the normalized convention `|2 Pr[win] - 1|` for both advantages
would double the additive losses in this display.

The CPA term refers to the concrete ACWC2 experiment with fresh KeyGen,
the actual CBD/SOTP/PKE encryption calls, and the same G state for
challenge encryption and all later typed/raw/simulator queries. Auxiliary
E, F and raw-stream state is retained. The F cache populated by KeyGen is
not deleted. The subsequent [base-PKE reduction](ntruplus768-acwc2-security.md)
connects this CPA advantage to concrete INJ and OW-CPA success probabilities,
with auxiliary oracles simulated inside the attackers. NTRU/RLWE assumption
reductions remain open.

## The concrete attacker

`CPAReduction(A).choose` samples independent uniform 96-byte messages
`m0,m1`, retaining `m0` privately. Equal messages are allowed.
Its `guess` runs `A` with the CPA challenge ciphertext, an independently
sampled uniform 32-byte key, the existing public hash interfaces, and
`SimLookup` for decapsulation. It returns false exactly when the public
H history contains `(m0,F(pk))`. The reduction has no secret-key or
challenge-bit access. The theorem excludes its private target state from
the underlying attacker and all relevant oracle callbacks.
The generic `CPAAdversary` module type does not itself impose global-state
restrictions. The theorem concerns this concrete `CPAReduction(A)` with
the stated exclusions; it does not assert security of arbitrary modules
inhabiting that unrestricted type.

`CPACipher` draws a uniform 224-byte buffer and uses its 192-byte tail
for the actual CBD/SOTP/PKE computation. The head does not affect
encryption. The actual Encaps bridge establishes successful ciphertext
production on the generated valid keys before its option result is
projected to bytes.

## Challenge programming and the query bound

The actual public-simulation challenge first becomes an experiment with
an H entry programmed at the challenge message and `F(pk)`. The H
response splits exactly into independent uniform head and tail buffers.
Removing this entry changes observations only when an external H request
reaches that input. A private monotone flag records the request before
the answer is returned. The tables agree outside the target until the
flag is set; equality of complete oracle tables after a hit is not used.

The wrapper serves both typed and valid raw H requests. A request for
zero output bytes still records the complete internal reply, while the
caller receives an empty prefix. Repeated requests keep cached answers.
Invalid output lengths and other domains do not record H requests.
`SimLookup` uses the public history and G without making H calls.

In the unprogrammed experiment, the head/tail independence makes the
KEM bit independent of the adversary's observation. Its winning
probability is one half under the stated termination contract. Writing
`p_hit` for the target-history probability in this experiment, and
`p_cross` for target-history membership when the CPA challenge encrypts
the other independently sampled message, the proof establishes

```text
Pr[CPAGame(CPAReduction(A)).run(): win] = (1 + p_hit - p_cross) / 2,
p_cross <= qC / 2^768,
|Pr[SimPublicFreshGame(A).run(): win] - 1/2|
    <= 2 AdvCPAGame(CPAReduction(A)) + qC / 2^768.
```

The cross bound moves the unused target-message sample after the adaptive
transcript and applies the uniform message point mass. Its premise is
`hoare[CPAPhase(A).run: true ==> fsize SimHistory.h <= qC]`, over every
initial phase state. It bounds distinct H input pairs, not all calls.
The public phase initializes its own history. A repeated or zero-output
request still reaches the underlying H oracle, even when it adds no new
distinct input.

## Contracts retained in the final composition

- The listed private-state restrictions and robust adversary losslessness
  for every permitted collection of lossless typed/raw hash and Decaps
  backends. Query limits alone do not establish termination.
- `qE` and the specified initial E counters, from the earlier actual-ROM
  setup/erasure comparison.
- `q0`, the combined H-plus-Decaps request limit for each concrete native
  and full-FO backend, including their prescribed initial counter states.
- `d = max(0, SimSelectedBudget.budget)`, the universal Decaps bound over
  all permitted H/D backends excluding the private counter state.
- `qH,S`, the public H-request bound for the concrete Known backend in
  the public-simulation theorem.
- `qC`, the distinct-H-history contract for the concrete CPA phase above.

These scopes are separate. In particular, the Known backend's H bound
is not automatically a bound for the CPA transcript. The final theorem
composes the existing original-to-FO and FO-to-public bounds by the
triangle inequality. It does not introduce a runtime retry/query cap,
condition probabilities on return, or assume termination of the original
unlimited cached-ROM KeyGen. Fresh KeyGen's losslessness was proved in
the acceptance analysis and is reused.

## Reproduction

```sh
./scripts/verify-ntruplus768-indcpa-reduction.sh
./scripts/verify-ntruplus768-indcpa-reduction.sh --check-only
```

The runner accepts the explicit frozen main inventory and source pins.
Every main receives a semantic EOF theorem and an isolated negative copy
with its own final proof left unfinished. The negative must fail at that
proof rather than while importing another theory. Structural/trust
controls reject local proof escapes and changed reduction interfaces;
finite diagnostics separately exercise the membership identity, equal
challenge messages, empty lists and typed/raw history behavior.

The full replay uses `compile -no-eco -pragmas Proofs:check -p Z3
-timeout 60 -max-provers 1` and `OCAMLRUNPARAM=o=20`. The default
`EC_JOBS=2` can be reduced to one. `--output` selects a new or empty
evidence directory outside the checkout. `--prior-evidence-root` locates
the earlier thesis evidence after relocation. Source, external-tool and
configuration hashes are compared before and after execution. Imported
theories are linked to the prior FO-simulation PASS and are not counted
as freshly replayed mains. `--check-only` reports `SOURCE_CHECK_ONLY`.

Evidence is retained under
`handoff/verification/ntruplus-indcpa-reduction-20261018/` in the thesis
workspace. This family changes no native C/Jasmin implementation and
does not rerun native tests, extraction, Safety, CT or SCT. HAETAE
unforgeability, QROM, native SHAKE/RNG correspondence and C memory/ABI
correspondence remain outside this reduction.
The public lookup is a finite history scan for each decapsulation request.
The development proves the probability relation and does not mechanize a
PPT or running-time bound for the complete reduction.
