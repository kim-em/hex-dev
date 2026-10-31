# HexGroebner

Mathlib-free finite-field F4 operations under
[the F4 contract](../SPEC/Libraries/hex-groebner.md).

The implemented API is the deterministic Macaulay matrix kernel
`Hex.Groebner.eliminateWith`. It accepts a prime-field context, a fixed column
count, sparse reducer rows and sparse target rows. Supply columns in decreasing
order of the intended monomials; the matrix kernel preserves their positions.
`PrimeField.ofZMod64` reuses the existing bounds and primality evidence. The
supported modulus range is every prime `2 ≤ p < 2^31`.

Rows store increasing 32-bit column indices and canonical residues in separate
little-endian byte buffers. Moduli below 256 use one byte per coefficient,
moduli below 65536 use two, and larger supported primes use four. Raw buffers
are validated before use; `SparseRow.ofEntries` also provides a checked
interchange constructor. There is no implicit reduction of malformed residues.

Elimination retains sparse monic pivots and reuses one packed dense accumulator
and one packed pivot table. Reducers with a free leading column install directly
from sparse storage; other rows scan from their first stored column through an
active upper bound, extended when a pivot introduces a later column. Empty
rows bypass the accumulator. Reducers are processed first. Target rows reduce
against both reducer and preceding target pivots. Output is echelon in the
original columns, sorted by leading column; rows marked `fromTarget` supply the
additional row-space dimension. The reducer rows retained in the output span
the original reducer subspace. This is forward elimination, so tails may still
contain later pivot columns. Multiplication uses HexArith's Barrett reciprocal,
hoisted outside coefficient loops. Every product is below `p² < 2^62`.

`MatrixLimits` bounds columns, rows, input/output nonzeros, packed payload bytes,
work and optional provenance nodes. Packed bytes count all input buffers, the
two workspaces and retained output buffers; they exclude allocator capacity,
object headers and provenance objects, which have a separate node limit. This
is a logical payload bound, not a bound on process memory; short rows can have
more metadata than payload, and shared input/output columns are counted twice.
One work unit covers each row header/processing visit, each sparse entry
validated, scattered or updated (the update includes its modular product),
each dense column inspected, each normalization or inversion product, and each
workspace byte initialized. Direct sparse normalization charges one unit per
nonmonic entry; monic sparse rows reuse their buffers and derivation node,
with no identity scaling or coefficient multiplication. Scan blocks of at most
64 positions and other loops' allowances are
charged before execution. Exhaustion and invalid input
are different errors. Counters survive either error. There is no resumable
state or implicit fallback in this matrix API.

Optional `RowOp` provenance shares input, scaled-addition and scaling nodes.
References point backward and each output pivot references its derivation.
This data does not certify a Gröbner basis: both polynomial ideal containments,
final S-pair reductions, reducedness and the theory soundness proofs are
separate requirements.

Verification:

```sh
lake build HexGroebner +HexGroebner.Conformance hexgroebner_emit_fixtures hexgroebner_bench
HEX_LIBRARY_FILTER=HexGroebner bash scripts/ci/run_oracles.sh
lake exe hexgroebner_bench verify
```

The committed matrix corpus covers characteristic two, both storage-width
boundaries, `2^31 - 1`, zero shapes, dependent rows, 40-by-60 rank defects,
later reducer pivots and active-range extension across scan blocks.
An independent Python integer RREF checks row-space equality and reducer-space
preservation; separate replay checks the shared derivations. Core Lean checks
cover malformed representations at every width, every resource category and
exact inclusive budget boundaries, counters retained on failure, provenance
agreement across the corpus, and a 100,000-column sparse work bound. Packed
byte encoding also has an ordinary-kernel example.

The Hilbert-matrix (Cauchy family) lean-bench kernels include validation,
allocation, elimination, decoding and structural output hashing, with separate
provenance-off and provenance-on registrations; input preparation is excluded. Their
registered domain has full rank and dense trailing supports, giving cubic
fixed-word update work and quadratic scans/output work. A sparse rectangular
rank-deficient family has constant clustered row support and both dimensions
proportional to its parameter, with linear setup/support work. A separate
spread-support family reaches the last column and exposes quadratic interval
scanning despite having only three entries per row. These make no claim about
complete F4 systems or comparative performance leadership. Portable accessors
retain checked byte operations and `Nat` indices. The active interval can still
contain large internal gaps; it is not a sparse support queue. Performance
evidence and unresolved fitted verdicts are in the
[matrix report](../reports/bench-results/hexgroebner-cauchy.md).

Full polynomial input/output, monomial interning, symbolic preprocessing,
critical pairs, basis computation/certification, extension adapters, delayed
reduction, SIMD/parallel kernels and `HexGroebnerTheory` remain unimplemented.
Issue [#10987](https://github.com/kim-em/hex-dev/issues/10987) tracks these
requirements and the full-system comparator sweeps. The gap to both
fastest-open-source and overall-fastest F4 is unmeasured; no such milestone
has been demonstrated. No library phase completion is claimed.
