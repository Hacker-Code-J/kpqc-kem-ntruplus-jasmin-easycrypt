# NTRU+768 instance of the shared NTT composition theorem

`NTTComposition.ec` is byte-identical to the shared theory vendored in the
HAETAE artifact. It proves total correctness of four procedure calls from
three checked premises: forward correctness (called twice), transformed
multiplication correctness, and inverse correctness. Representation and
bound predicates are separate, including a distinct representation after
multiplication so an implementation's scaling is not suppressed.

`NTRUPlus768NTTComposition.ec` instantiates the shared theory with the actual
extracted NTRU+768 kernels. Forward and product arrays use
`terminal_represents`: each four-coefficient block represents a remainder
of the global polynomial. The forward output is in `in_qrange768`; the
product output satisfies the actual inverse input shape.

`ntruplus768_ntt_product_total` states that, for inputs satisfying the
existing `input_qrange` condition and representing `p` and `q`, the result
is congruent to their product modulo the global polynomial modulus, every
signed output coefficient lies in `[-3457,3457)`, and execution terminates
with probability 1. The proof applies `Common.composition_total` to the
three proved adapter results. Initial output buffers are arbitrary witness
values allowed by the original kernel theorems.

The composition is a verification program that calls extracted kernels;
it is not a newly implemented native entry point. Existing arithmetic,
extraction, library, and solver trust boundaries are retained. No new
algorithm-correctness or termination assumption is introduced.

From the repository root, run:

```sh
python3 scripts/verify-ntruplus768-ntt-common.py
```

Set `EASYCRYPT` to the executable in the intended installed toolchain when
it is not on PATH. The runner checks the compatibility shim, shared-source
digest, both new proof files, and unfinished-proof rejection. Its optional
`--dependencies` flag also checks each local proof in the imported closure.
The default run does not claim a fresh replay of imported proofs. The output
records all resolved input hashes and rejects inputs changing during checks.
