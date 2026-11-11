# Classical-ROM IND-CCA game and actual API for NTRU+768

This proof-only layer defines a challenge-first CCA experiment around the
existing KeyGen, randomized Encaps and CompleteDecaps array callers. It
connects their status-bearing API to option-valued responses, shares the
honest E/F/G/H tables with adversarial queries, and records how setup
nonreturn and finite setup exhaustion affect winning probabilities.

The existing honest-ROM correctness bound remains
`returned failure + missing mass < 2^-238`; see
[the numerical DFR guide](ntruplus768-kem-numerical-dfr.md). That bound
concerns one honest Encaps--Decaps execution without external queries.
The new adversarial interface does not turn it into an IND-CCA security
bound or a correctness bound after arbitrary adversarial queries.

## Game and capabilities

`CCAOriginalGame(A)` initializes the four typed tables and auxiliary raw
stream tables once and resets the private decapsulation oracle. It runs
the actual public KeyGen and randomized Encaps, then samples an independent
uniform 32-byte candidate key and a fair challenge bit. It installs the
secret key and challenge ciphertext in the private oracle before calling
the adversary. The adversary receives the public key, challenge ciphertext
and the selected key: `false` selects the real shared key and `true` the
independent random key. Its returned guess is compared with that bit.
Actual random-byte, guard, arithmetic, hash and clearing calls remain in
the callers.

This is a single adversarial phase after the challenge is formed.
`CCAExtendedAdversary(H,D).guess(pk,ct,key)` receives query capabilities for
typed E/F/G/H, bounded-output raw XOF requests, and decapsulation. A lift
wrapper retains a typed-only adversary interface. Module restrictions
exclude direct access to the concrete oracle tables and private
decapsulation globals. Initializers and the stored secret key are not
adversarial capabilities.

`CCAOptionGame` uses the status-to-option API. Its connection to the
original caller uses the generated-key Encaps status contract. It does not
assume that encapsulation succeeds on an arbitrary supplied public key.
There is no pre-challenge query phase or imposed adversarial query-count
budget in these game definitions.

## Decapsulation and status

[`NTRUPlus768CCAStatusAdapter.ec`](../ntruplus/proof/768/ref/kem_indcca_game/NTRUPlus768CCAStatusAdapter.ec)
calls `CompleteDecaps(SHAKEGROM,SHAKEHROM).run(ct,sk,witness)` and returns
`Some(ss)` exactly when the actual status is `W32.zero`; every other status
returns `None`. An accepted all-zero shared secret is still `Some(zero)`.
The projection preserves the actual G/H table updates. Noncanonical entry
bytes are passed through the actual guard and clear calls; their rejection
contract returns `None` while retaining both hash tables.

[`NTRUPlus768CCADecapOracle.ec`](../ntruplus/proof/768/ref/kem_indcca_game/NTRUPlus768CCADecapOracle.ec)
stores a private secret key, optional challenge ciphertext and request
counter. `reset()` clears the challenge marker and counter;
`init(sk,ct)` installs `Some(ct)` and resets the counter. Only `decap` is
present in the adversary-facing `CCADecapPort`.

Every `decap` request increments the counter, including a repeated
challenge request or a noncanonical ciphertext. The oracle first compares
the complete 1152-byte ciphertext with the stored challenge. A match
returns `None` without calling Decaps or any hash and preserves all four
hash tables. Every other 1152-byte value is passed to the actual Decaps
adapter, including invalid encodings. The relational projection retains
its result and shared G/H state. The per-call losslessness result uses the
existing Decaps and ROM-oracle losslessness contracts.

The counter measures requests, not successful decryptions. It does not
enforce a query cap. A query bound, if needed by a later reduction, must be
stated separately.

## Shared typed and raw hash queries

`SharedCCAOracles` delegates directly to the same `ROE`, `ROF`, `ROG` and
`ROH` tables used by the honest callers. Repeated inputs return cached
answers. The raw codec checks both the complete input length and the tag;
it does not discard the first byte unconditionally.

| Domain | Complete raw input | Typed output |
| --- | --- | ---: |
| E | 32 unprefixed seed bytes | 192 bytes |
| F | `0x00` followed by 1152 public-key bytes | 32 bytes |
| G | `0x01` followed by 1152 serialized bytes | 192 bytes |
| H | `0x02` followed by 96 coin/message bytes and a 32-byte suffix | 224 bytes |

`decode_typed` recognizes precisely these encoded inputs. Any byte list
outside all four shapes belongs to the untyped domain, keyed by the entire
list. The codec proves exact encoding/decoding and absence of cross-domain
aliases.

`RawXOF.get(input,outlen)` returns an optional byte list. For
`0 <= outlen <= 224`, it returns the requested prefix of a persistent
224-byte stream for that complete input. An out-of-range length returns
`None` without changing any cache. The maximum output of this interface is
224 bytes; it is not an unbounded SHAKE interface.

For typed inputs, the stream reuses the existing typed answer. E and G add
a persistent independent 32-byte suffix; F adds a persistent independent
192-byte suffix; H already supplies 224 bytes. Thus requests longer than a
domain's usual typed output, up to 224 bytes, retain the same prefix.
Typed calls before or after raw calls use the same underlying typed entry.
An untyped input has its own persistent uniform 224-byte answer.

A full fresh 224-byte uniform law applies when both the typed prefix and
its extension are absent. If the prefix is already cached, it remains
fixed and only the missing suffix is sampled. The results cover these
shared-table procedures and their stated projections. An arbitrary-context
equivalence to a separate eager, single-table XOF implementation remains
unproved. Neither the output-length bound nor per-query losslessness
implies that an arbitrary adversary terminates.

The games supply `SharedCCAExtendedOracles.raw`, which delegates directly
to `RawXOF.get`. A separate optional `BudgetRawXOF` policy configures a
request limit and maximum input length, each clamped to a nonnegative
integer. Its `attempts` counter increases on every request, including
repeats, invalid lengths and requests after exhaustion. It forwards only
requests whose previous attempt count is below the limit and whose input
and output lengths satisfy the configured limits. `forwarded` counts those
actual raw-oracle calls. A refused request returns `None` and leaves all
hash caches unchanged. This optional policy does not impose a budget on
the game modules or establish adversary termination.

## Partial probability and finite fair completion

The unrestricted KeyGen may fail to return. For a boolean game, let `w`
be the winning mass, `l` the losing mass and `t` the returning mass. The
probability layer keeps

```text
w + l = t,
w - 1/2 = (w - l)/2 - (1 - t)/2.
```

In particular, centering the winning mass at `1/2` is not automatically a
fair guessing experiment when `t < 1`. The partial game is not silently
normalized, and a losslessness assumption for unrestricted ROM KeyGen is
not introduced.

`CCAStoppedBody(A).run(qf,qg)` uses the existing finite f/g retry prefixes.
It returns `None` on setup exhaustion and `Some(win)` after a successful
setup and adversary call. The setup budgets count proposal attempts and
are separate from adversarial query counts. These cutoffs are parameters
of the analysis game and do not change the production retry loops.

`CCAFiniteGame(A)` applies `CompleteFallback` to that body. After the body
returns, it samples an independent fair bit and uses it only for `None`.
The established identities are

```text
Pr[finite game wins]
  = Pr[body = Some true] + Pr[body = None]/2,
Pr[finite game returns] = Pr[body returns].
```

Returned setup exhaustion is therefore completed fairly. Divergence of
the body is still missing mass; the completion assigns it no result.
Finite-game losslessness requires an explicit adversary losslessness
premise for lossless query ports. Finite retry budgets alone do not supply
that premise. These are game and probability identities, not a bound on
the adversary's distinguishing advantage.

## Reproduction and remaining proof boundary

Run from the repository root:

```sh
./scripts/verify-ntruplus768-kem-indcca-game.sh \
  --prior-evidence-root /path/to/thesis \
  --output /path/to/new-evidence-directory
```

The output directory must be new or empty and outside the checkout. The
family is in [`ntruplus/proof/768/ref/kem_indcca_game/`](../ntruplus/proof/768/ref/kem_indcca_game/),
with controls in [`tests/ntruplus768/kem_indcca_game/`](../tests/ntruplus768/kem_indcca_game/).
The runner selects September 2026 EasyCrypt/Why3 with Z3, `-no-eco`,
`Proofs:check`, one prover and `OCAMLRUNPARAM=o=20`. It checks source
contracts, the new mains, semantic EOF obligations and isolated unfinished
proof negatives, and binds unchanged imports to prior evidence by hash.
`--check-only` does not claim a proof replay.

Individual main checks do not establish a full-suite status or totals.
Use the completed runner's `summary.json`, matching source hashes and
logs for the actual result and counts.

The subsequent [underlying PKE development](ntruplus768-pke-average.md)
composes the existing extracted encryption/decryption kernels and bounds
average failure below `2^-354` for the actual fresh acceptance-conditioned
key law and independent CBD1 message/randomness. It keeps whole-array key
conditioning and separates general terminal-representation premises from
the generated-key c*f identity. It does not identify the actual Gen law
with the paper's quotient-ring-unit-conditioned law in both directions.
A separate initialized cached-ROM PKE experiment bounds returned failure
plus missing mass below `2^-238`; it has no adversarial continuation.

The remaining security obligations include that Gen-law identification,
the average-to-worst/ACWC2 correctness argument, a public-key-dependent FO
reduction, its adversarial oracle reasoning and the required hardness
assumptions. No quantitative IND-CCA bound, full IND-CCA theorem or QROM
result follows from these layers. The existing `2^-238` initialized honest
KEM correctness result is unchanged.

This development changes no C/Jasmin implementation or extraction. Native
SHAKE/RNG, concrete SHAKE-to-ROM correspondence, C memory/ABI, binary
execution and full-API leakage retain their existing boundaries. It adds
no native, Safety, CT or SCT replay claim.
