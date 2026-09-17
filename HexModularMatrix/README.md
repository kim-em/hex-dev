# Modular integer determinants and rational solves

Import `HexModularMatrix` for Mathlib-free computation and
`HexModularMatrixMathlib` for the Hadamard bound instance and total correctness.
The contract is [hex-modular-matrix](SPEC/hex-modular-matrix.md).

- `A.detMod?` eliminates below unit pivots over `ZMod64 m`. An all-zero pivot
  column returns `some 0`; a nonzero column without a unit returns `none`.
- `A.detBounded? bound fuel` reconstructs with CRT only after its modulus is
  strictly greater than twice `bound`. Its correctness theorem takes the
  determinant bound as a hypothesis. `A.rowNormBound` supplies a bound with
  an unconditional Mathlib-free proof.
- `A.detModular? fuel` uses the smaller row/column Hadamard bound. Its
  correctness theorem takes `LawfulDetBound`, supplied by the companion.
- `Hex.ModularMatrix.detWith A fuel` records the modular attempt and any
  Bareiss fallback. `Hex.ModularMatrix.det A` chooses capped adaptive fuel
  and returns the integer result. Finite prime supply cannot make it partial.

- `A.decomp? fuel` finds a reusable modular inverse and nonzero determinant
  residue; `A.decompAt? p hp` tries one modulus, including composite moduli
  with unit pivots. `D.lift b k` uses exact residual division to lift through
  `p^k`. `Matrix.solveWith D b` returns a reduced numerator vector and a
  positive common denominator, checked against the original integer system.
- `A.solve? b fuel` includes decomposition; `A.solveWitness? b fuel` also
  returns the nonzero determinant residue. A `none` result can mean exhausted
  prime-search resources; it is not a certificate that the system is inconsistent.
- `Matrix.solveMatWith D C` lifts multiple right-hand sides through the same
  inverse and reduces one common denominator across the whole matrix.
- `Hex.ModularMatrix.detViaDivisor A seed` uses a seeded right-hand side to
  obtain a determinant divisor, then reconstructs its cofactor. It uses Bareiss
  below dimension 192, the measured structured crossover. `detWith A fuel seed true`
  forces a divisor attempt at any dimension; failures fall through to ordinary CRT
  and then Bareiss. Seed changes cost but never the result.

- `A.rankCert? fuel` selects a minor modulo primes, completes its determinant
  and adjugate through one Dixon decomposition, then uses hex-rank's checker.
  `fuel` bounds prime attempts and determinant images; lifting uses its own
  bound-derived precision. Zero fuel and exhausted search return `none`.
- `A.rankModular` tries eight primes and returns the certified rank, or uses
  hex-rank's total integer `A.rank` on failure.
- `A.kernel? fuel` returns integer numerators for a rational kernel basis,
  with the certificate denominator and free-column indices. Its free block
  is negative identity after division by the denominator. The core proves
  annihilation and full column rank; the companion proves independence and
  spanning of Mathlib's rational kernel. Search failure propagates as `none`.

This implements milestones 1–5.
The companion proves rational solve/inverse correspondence and nonsingularity
of returned witnesses. Search and reconstruction completeness use
`LawfulDetBound`; soundness and reduction do not require it.

The conformance suite includes unreduced divisor candidates, skipped nonunit
moduli, exact lifting precision, repeated solves, empty right-hand sides,
unlucky initial primes and forced fallback. FLINT checks full canonical
solutions and every determinant route. `hexmodularmatrix_bench verify` runs
small hash anchors; `scripts/bench/modmat_flint.py` collects the determinant,
solve, repeated-solve and rank (`--mode rank`) comparison ladders on the shared host. Measurements
and limitations are recorded in the [performance report](../reports/hex-modular-matrix-performance.md).

The [rank comparison](../reports/hex-modular-matrix-rank-performance.md) records
all four rank arms and the bad-prime recovery checks.

The default determinant fuel cap is 16384 primes below 2³¹. A Hadamard bound of at least
2⁵⁰⁷⁹⁰³ therefore cannot be reconstructed within that budget and reaches
Bareiss fallback. The baseline also includes two evaluations of the Hadamard
bound in the default route and the relocated square-root routine's conservative
Newton starting value. Bound reuse, square-root initialization and elimination
buffer specialization remain opportunities for performance work.
