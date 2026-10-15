# HexPosDefTheory

Soundness of arbitrary accepted HexPosDef certificates over integers,
rationals, reals, and complex numbers, positive-scaling transport, and
the proof-producing `pos_def` tactic.

The tactic recognizes closed square matrices and proves `A.PosDef` or
`¬ A.PosDef` using one kernel certificate check. Entry quotation proves
scalar equalities and does not evaluate classical real or complex equality.
The default method is general triangular elimination; the positive-vector
method is selected with `pos_def (method := .positiveVector)`.

See [the SPEC](SPEC/hex-pos-def-theory.md) and the shared Manual chapter
[`HexManual/Chapters/HexPosDef.lean`](../HexManual/Chapters/HexPosDef.lean).

The unrestricted producers are total: `Int.certify_complete` and
`Gaussian.certify_complete` identify positive outcomes with `Matrix.PosDef`
over integers and complex numbers, respectively. The proof tracks both
blocks of the actual fraction-free recurrence using the existing Bareiss
bordered-minor invariant; it also proves exact division and reality of pivots.

Complete-call observations on the shared host `chungus2`, pinned to leased
CPU 44, use three trials in fixed trial-major order. Each fresh-module
`lake build :olean` includes process startup and imports as well as entry
quotation, native certificate production, and kernel checking. All four probes use Lean’s default heartbeat budget. The Gram
inputs are the same deterministic small-integer `Cᵀ*C + I` family used by
the computational benchmark.

| Input | Median elapsed seconds | All three samples (seconds) |
| --- | ---: | --- |
| E₈ | 3.809 | 5.053, 3.809, 3.138 |
| Gram 8 | 3.050 | 3.602, 2.963, 3.050 |
| Gram 16 | 3.324 | 3.816, 3.204, 3.324 |
| Gram 32 | 6.449 | 6.449, 4.736, 6.948 |

[Raw observations](../reports/data/pos-def/complete-calls.json) include source
hashes, compiler output, axiom inventories, CPU accounting, and host activity.
[All collected samples](../reports/data/pos-def/) are retained. These are
host-specific complete-call observations, not elapsed-time complexity laws
or CI thresholds. The cubic scalar-operation model also incurs the cost of
growing integer operands.
