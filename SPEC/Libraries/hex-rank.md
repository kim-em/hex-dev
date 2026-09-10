# hex-rank (rank over an integral domain with a two-sided certificate)

The rank of a matrix over any nontrivial integral domain, with a certificate
that bounds the rank from both sides and a checker that needs only ring
arithmetic and equality tests. The certificate names an `r × r` submatrix `B`
of `A` and carries the adjugate of `B` together with `d = det B`. From those
the checker verifies that `B` is nonsingular (so the rank is at least `r`)
and that `d • A` is a combination of the `r` selected columns of `A` (so the
rank is at most `r`). The producer is rectangular fraction-free Gauss-Jordan
elimination with column pivoting and skipped columns, which also returns the
row and column rank profiles. Mathlib-free. The companion
[hex-rank-mathlib](hex-rank-mathlib.md) proves that a checked certificate
determines `Matrix.rank` over the domain itself and over any fraction field,
proves that the producer's certificate checks, and relates the certificate
to Mathlib's `Echelon.Decomposition`.

This is the shared foundation for certified integer rank in
[hex-modular-matrix](hex-modular-matrix.md), for the generic rank of
polynomial matrices, and for the symbolic `rank` tactic of the planned
`hex-matrix-tactic` (https://github.com/kim-em/hex-dev/issues/10151).

## Why this library exists

Rank is executable in the tree in exactly three settings, and none of them
is a general domain:

- Over a field, `Hex.Matrix.rowReduce` (Gauss-Jordan to reduced row
  echelon form, `[Lean.Grind.Field R]`) with `rowReduce_rank`, and the
  companion theorem `HexMatrixMathlib.rank_eq` against `Matrix.rank`.
- Over `Int`, through the Hermite form (`hnfRank`, with `hnfRank_eq_rank` in
  `HexHermiteMathlib/Rank.lean`) and the Smith form (`snfRank`, with
  `snfRank_eq_hnfRank` in `HexSmith/Structure.lean`).
- Over `F[x]`, `Hex.PolyMatrix.snfRank` in hex-poly-smith, with
  `HexPolySmithMathlib.rank_eq_ratFunc_rank` identifying it with the rank
  over `RatFunc F`.

Nothing computes the rank of a matrix over `MvPoly`, over `ZPoly`, or over
an arbitrary domain, and none of the three above returns a witness a
consumer can re-check.

`HexBareiss.bareissWith` is generic (any `quot : R → R → R` satisfying
`quot (a * b) b = a` for `b ≠ 0`, with laws over
`[Lean.Grind.CommRing R] [DecidableEq R]`), but it is square in its types
and it records an early singular stop: on `[[0, 1], [0, 0]]` the pivot search
in column `0` finds nothing, `singularStep := some 0` is recorded, and the
run ends. That is the right behaviour for a determinant and the wrong one
for a rank, whose answer here is `1` with pivot column `1`. Rectangular
elimination that skips an empty column and continues is a new algorithmic
contract, not an extra return field on `BareissData`. The section
[What is new relative to hex-bareiss](#what-is-new-relative-to-hex-bareiss)
lists the differences against `bareissDataWith` and `pivotLoopWith`.

[hex-modular-matrix](hex-modular-matrix.md) specifies a two-sided rank
certificate over `Int` for its multi-modular route. That certificate is the
`Int` instance of the one here, and the section
[Int](#int) records the amendment that makes the two coincide.

The pinned Mathlib proves `Echelon.Decomposition.rank_eq` in
`Mathlib/LinearAlgebra/Matrix/Echelon/Decomposition.lean` directly over
`[CommRing R] [IsDomain R]`, and `norm_rank` is built on it. Mathlib's
certificate is an echelon transform, and its checker is `decide` on a
matrix product and an echelon predicate. The certificate here is a
different object with a smaller checker, and the companion states how to
pass between them.

## Scope and dependencies

`HexRank` is Mathlib-free. Its dependency list is `HexBareiss`,
`HexDeterminant`, `HexMatrix`, `HexArith`, `HexBasic`:

- `HexMatrix` for `Matrix`, `selectRows`, `selectCols`, `identity`, scalar
  multiplication and the linear-buffer discipline;
- `HexDeterminant` for `selectedSubmatrix`, `det`, `det_mul`,
  `det_identity`, `det_rowScale`, and the rectangular Cauchy-Binet
  expansion `det_minor_mul` in `HexDeterminant/Gram.lean`, which is what
  the Mathlib-free upper-bound proof uses;
- `HexBareiss` for the array-storage layer (`matrixToRows`, `rowsToMatrix`,
  `getEntry`) that the producer's in-place implementation reuses, and so
  that this library sits above the square determinant algorithm in the
  graph, as the companion sits above `HexBareissMathlib`;
- `HexArith` for `HexArith.Int.exactDiv`, the GMP-backed exact quotient
  that the `Int` instantiation passes as `quot`;
- `HexBasic` for `Hex.ExactDivLaws`, `Hex.exactDiv` and the domain law
  package below.

It does not depend on `hex-row-reduce`: the field algorithm is a different
algorithm, and the rank-versus-minors theorem that would identify the two
over a field is [hex-determinantal-ideal](hex-determinantal-ideal.md)'s.
It does not depend on `hex-determinantal-ideal` either. That SPEC states
the relationship: the two are independent siblings, and this library's
certificate is an instance of the nonzero-minor direction proved there,
not a dependency of it. It does not depend on `hex-mv-poly`, `hex-poly`
or `hex-mv-gcd`: the polynomial carriers are instantiated outside the
production library, see [Placement](#placement).

In scope: the certificate and its checker, the soundness and completeness
statements, the rectangular fraction-free producer, the rank profile, the
`Int` specialisation, and the carrier instantiations named below.

Not in scope: a rational or integer kernel basis (hex-modular-matrix and
hex-hermite), the rank of a specialised polynomial matrix at a point and
the rank-drop locus (hex-determinantal-ideal), a modular or multi-modular
rank over `Int` (hex-modular-matrix, which will produce this library's
certificate by a faster route), and any tactic frontend
(hex-matrix-tactic).

The namespace is `Hex.Matrix`, beside `det`, `bareissWith` and
`rowReduce`.

## Coefficient contract

Operations and laws are kept apart, exactly as in
[hex-bareiss](../../HexBareiss/SPEC/hex-bareiss.md).

**Operations.** The checker takes `[Lean.Grind.CommRing R] [DecidableEq R]`
and nothing else: it multiplies, subtracts and compares. The producer takes
the unbundled operation classes its loop calls
(`[Zero R] [One R] [Sub R] [Mul R] [DecidableEq R]`) and the exact quotient
as a plain function argument `quot : R → R → R`, never as a `Div R`. The
reasons are those of
[hex-bareiss §Exact quotients](../../HexBareiss/SPEC/hex-bareiss.md#exact-quotients-obligation-totality-and-the-int-fast-path):
`Int` passes its GMP-backed `HexArith.Int.exactDiv`, every other carrier
passes `Hex.exactDiv`, and no generic `Div`-derived alias is introduced.

**Laws for the checker.** Soundness needs that `R` has no zero divisors.
Lean core has no such class, and neither does `HexBasic`, so this SPEC adds
one beside `Hex.ExactDivLaws` in `HexBasic/ExactDiv.lean`:

```lean
namespace Hex

/-- A nontrivial ring without zero divisors. Proof-only. -/
class DomainLaws (R : Type u) [Zero R] [One R] [Mul R] : Prop where
  one_ne_zero : (1 : R) ≠ 0
  no_zero_div : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0

instance : DomainLaws Int
instance [Lean.Grind.Field K] : DomainLaws K
theorem DomainLaws.of_exactDivLaws [Lean.Grind.CommRing R] [Div R] [ExactDivLaws R]
    (h1 : (1 : R) ≠ 0) : DomainLaws R
```

The field instance is `Lean.Grind.Field.of_mul_eq_zero` and
`Lean.Grind.Field.zero_ne_one`. The last theorem is
`Hex.ExactDivLaws.mul_ne_zero` and is how every carrier with an exact
quotient discharges the class. It is a theorem, not an instance, because
`ExactDivLaws` does not imply nontriviality: the trivial ring satisfies it
vacuously.

`DomainLaws` is deliberately not `ExactDivLaws`. **Exact division is a
producer requirement, never a checker requirement.** A consumer that only
re-checks a certificate (a tactic replaying it in the kernel, an oracle
verifying a stored witness) must not need a quotient operation on `R`, and
the soundness theorems must not name one.

**Laws for the producer.** Producer correctness takes
`[Lean.Grind.CommRing R] [DecidableEq R]`, `(1 : R) ≠ 0`, and the single
hypothesis

```lean
(quot : R → R → R) (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
```

The no-zero-divisor and cancellation facts it needs are consequences of
`hquot`, through `Hex.ExactDivLaws.mul_ne_zero` and `mul_right_cancel`
after the local `letI : Div R := ⟨quot⟩` that hex-bareiss also uses.
Nontriviality is a genuine extra hypothesis: over the trivial ring no
certificate checks (`denom ≠ 0` is unsatisfiable), so the producer cannot
emit one. Over `Int` and over every polynomial carrier it is `decide` or
a coefficient fact.

## The certificate

### Shape

For `A : Matrix R n m` (`n` rows, `m` columns, the `Hex.Matrix` convention):

```lean
namespace Hex.Matrix

/-- A two-sided rank certificate: an `rank × rank` submatrix of `A` at
`rows × cols`, its adjugate `adj`, and its determinant `denom`. -/
structure RankCert (R : Type u) (n m : Nat) where
  rank : Nat
  rows : Vector (Fin n) rank
  cols : Vector (Fin m) rank
  denom : R
  adj : Matrix R rank rank
```

Writing `B := selectedSubmatrix A c.rows c.cols` (`rank × rank`),
`C := selectCols A c.cols` (`n × rank`) and `P := selectRows A c.rows`
(`rank × m`), the certificate asserts three things:

1. `c.denom ≠ 0`;
2. `B * c.adj = c.denom • identity c.rank`, so `B` is nonsingular;
3. `c.denom • A = C * (c.adj * P)`, so every column of `A` is, after
   clearing the denominator, a combination of the columns of `C`.

The matrix `U := c.adj * P` (`rank × m`) is the coefficient matrix of the
all-column identity `d • A = C * U` that the certificate establishes. It
is derived by the checker rather than stored, see
[Why the certificate stores the adjugate](#why-the-certificate-stores-the-adjugate-and-not-the-coefficients).

The vectors `rows` and `cols` are index selections, not sets: they may be
in any order, and the checker imposes no ordering or distinctness
condition on them. None is needed. A repeated row or column index makes
`B` have two equal rows or columns, hence `det B = 0`, hence identity 2
fails (`det B · det adj = d ^ rank ≠ 0`). Distinctness is a consequence of
a passing check, not a precondition of it. This is one difference from
the certificate in hex-modular-matrix, whose complement-of-`cols`
indexing forced a strictly-increasing check.

The producer returns `rows` in elimination order and `cols` strictly
increasing, and `denom` is the determinant of `B` with its rows in that
order. A consumer that sorts `rows` must negate `denom` and `adj` by the
sign of the sorting permutation, or simply not sort: nothing in the
checker cares.

### The checker

```lean
/-- Check a rank certificate. Ring arithmetic and equality tests only. -/
def checkRank [Lean.Grind.CommRing R] [DecidableEq R]
    (A : Matrix R n m) (c : RankCert R n m) : Bool :=
  let B := selectedSubmatrix A c.rows c.cols
  let C := selectCols A c.cols
  let P := selectRows A c.rows
  decide (c.denom ≠ 0) &&
  decide (B * c.adj = c.denom • Matrix.identity c.rank) &&
  decide (c.denom • A = C * (c.adj * P))
```

Cost, in ring multiplications: `rank³` for `B * adj`, `rank² · m` for
`adj * P`, `n · rank · m` for `C * U`, and `n · m` scalar products for
`denom • A`. No division, no determinant, no search. The dominant term
`n · rank · m` is one matrix product, which is what a consumer replaying
the certificate in the kernel pays. `Matrix` derives `DecidableEq`, so
the two matrix equalities are entrywise comparisons.

`checkRank` is `@[expose]` and kernel-reducible on closed inputs, per
design principle 11, because the kernel is one of its two intended
callers. The compiled path uses `Matrix.mul`'s existing `@[csimp]`
implementation.

### Boundary cases

- **`rank = 0`.** `rows` and `cols` are empty, `adj` is the `0 × 0`
  matrix, `B * adj` and `denom • identity 0` are both the empty matrix,
  so identity 2 holds for any `denom`. `C` is `n × 0` and `U` is `0 × m`,
  so `C * U` is the `n × m` zero matrix and identity 3 reads
  `denom • A = 0`. With `denom ≠ 0` and no zero divisors, a certificate of
  rank `0` checks exactly when `A = 0`. The canonical such certificate
  has `denom = 1`.
- **`n = 0` or `m = 0`.** `A` has no entries and is the zero matrix of its
  shape. The rank-`0` certificate with `denom = 1` checks, and no
  certificate of positive rank does, since `Vector (Fin 0) rank` is empty
  for `rank > 0`.
- **`rank > min n m`.** A passing check forces the entries of `rows` and
  of `cols` to be distinct, so `rank ≤ n` and `rank ≤ m`. No certificate
  of larger rank checks.

The general soundness and completeness proofs below cover all three
without a case split. They are listed so that the conformance suite tests
them and so that an implementation which special-cases any of them is seen
to be unnecessary.

### Why the certificate stores the adjugate and not the coefficients

The directive for this SPEC described the upper bound as the all-column
identity `d • A = C * U` and the lower bound as a nonzero `r × r` minor of
`C`, with `U` read off `adj B`. That is exactly what is checked. The
question is what the certificate *stores*, and the answer is `adj B`
alone, for three reasons.

**The checker must not compute a determinant.** Establishing that the
minor is nonzero by evaluating it means choosing a determinant algorithm
for the checker. Over a general domain the division-free options are the
Leibniz `det` (`r!` terms) and Berkowitz (`O(r⁴)`, and a dependency on
hex-char-poly for a constant coefficient); Bareiss needs the exact
quotient that the checker must not require. Carrying the adjugate turns
the nonsingularity test into one `r × r` matrix product, and its
soundness into `det B · det (adj B) = d ^ r ≠ 0`.

**Given `adj B`, `U` is one small product.** `U = adj B · P` costs
`r² · m` multiplications to form, against the `n · r · m` of the main
identity, so storing `U` would enlarge the certificate by `r · m` entries
to save a lower-order term. A certificate is embedded in a proof term by
the tactic consumer, where size is the cost that matters.

**`d` and `adj B` are what the producer has.** Fraction-free Gauss-Jordan
on `[B | identity r]` produces `[d • identity r | adj B]` directly. The
alternative producer that solves for `U` column by column (the shape the
hex-modular-matrix draft took) does `m - r` solves where this one does
`r`.

Storing `U` as well as `adj B` is sound and was considered. It is not
adopted because the checker would then either trust the stored `U` (and
verify the identity with it, at no saving) or recompute it (and never read
the stored one).

## Soundness

Both statements are Mathlib-free and live in `HexRank/Check.lean`, over
`[Lean.Grind.CommRing R] [DecidableEq R] [Hex.DomainLaws R]`. Write
`B`, `C`, `P`, `U` as above and `d := c.denom`, `r := c.rank`.

```lean
theorem checkRank_minor_ne_zero (h : checkRank A c = true) :
    det (selectedSubmatrix A c.rows c.cols) ≠ 0
theorem checkRank_minor_succ_eq_zero (h : checkRank A c = true)
    (rows : Vector (Fin n) (c.rank + 1)) (cols : Vector (Fin m) (c.rank + 1)) :
    det (selectedSubmatrix A rows cols) = 0
theorem checkRank_eq_zero_of_rank_zero (h : checkRank A c = true) (hr : c.rank = 0) :
    A = Matrix.zero n m
```

Together the first two say that `r` is the largest size of a nonzero
minor of `A`, which is the meaning of "rank over the fraction field"
that a Mathlib-free library can state. The companion turns them into
`Matrix.rank`; hex-determinantal-ideal's `rank_eq_iff_minors` is the same
characterisation for `rowReduce_rank` over a field, and a consumer holding
both gets `rowReduce_rank A = c.rank` over a field with no new proof.

**Lower bound (`checkRank_minor_ne_zero`).** From identity 2,
`det (B * adj) = det (d • identity r)`. The left side is `det B · det adj`
by `det_mul`. The right side is `d ^ r` by `det_rowScale` applied `r`
times to `det_identity` (a lemma `det_smul : det (c • M) = c ^ k * det M`
for `M : Matrix R k k`, new in `HexDeterminant/RowOps.lean` if absent).
`d ≠ 0` and `DomainLaws.no_zero_div` give `d ^ r ≠ 0` by induction on `r`,
and then `det B ≠ 0`. At `r = 0` the right side is `1`, and `1 ≠ 0` is
`DomainLaws.one_ne_zero`; nothing else changes.

**Upper bound (`checkRank_minor_succ_eq_zero`).** Fix `rows`, `cols` of
length `r + 1`. From identity 3 and `selectedSubmatrix` commuting with
scalar multiplication and with products of the shape `C * U`
(`selectedSubmatrix (C * U) rows cols = selectRows C rows * selectCols U cols`,
entrywise),

```text
d ^ (r + 1) · det (selectedSubmatrix A rows cols)
  = det (selectedSubmatrix (d • A) rows cols)
  = det (selectRows C rows * selectCols U cols).
```

The last matrix is a product of an `(r + 1) × r` and an `r × (r + 1)`
matrix. `det_minor_mul` (`HexDeterminant/Gram.lean`) expands its
determinant as a sum over `middle ∈ selectedColumnTuples (r + 1) r`, and
that list is empty (`selectedColumnTuples_eq_nil_of_lt`, a strictly
increasing `(r + 1)`-tuple in `Fin r` does not exist), so the sum is `0`.
Hence `d ^ (r + 1) · det (…) = 0`, and `d ^ (r + 1) ≠ 0` gives
`det (…) = 0`. This is the same "empty middle sum" step that
hex-determinantal-ideal's vanishing direction uses.

**`rank = 0` (`checkRank_eq_zero_of_rank_zero`).** Identity 3 is
`d • A = 0` entrywise, `d ≠ 0`, and `no_zero_div`. This is the upper bound
at `r = 0` read directly, since `minors 1 A` are the entries.

Neither proof mentions `quot`, `ExactDivLaws`, or how the certificate was
produced.

## Completeness

Every matrix over a nontrivial integral domain has a certificate that
checks. The constructive form is
[producer correctness](#exactness-and-producer-correctness); the
existence argument is recorded here so that the certificate shape is seen
to be complete independently of the elimination.

Let `r` be the largest size of a nonzero minor of `A`, and let
`rows`, `cols` index one such minor, `B := selectedSubmatrix A rows cols`,
`d := det B ≠ 0`, and `adj := adjugate B`. Then:

- Identity 1: `d ≠ 0` by choice.
- Identity 2: `B * adjugate B = det B • identity r` is the adjugate
  identity (`Hex.Matrix.mul_adjugate` in `HexDeterminant/Adjugate.lean`
  for `r = k + 1`; Mathlib's `Matrix.mul_adjugate` at every `r` including
  `0`).
- Identity 3: `d • A = C * (adj * P)`. For a row index `i ∈ rows` this is
  `d • A[i, :] = B[i-block] * adj * P = d • P[i-block]`, the adjugate
  identity again. For a row index `i ∉ rows`, the `(r + 1) × (r + 1)`
  minor on rows `rows ++ [i]` and columns `cols ++ [j]` vanishes for every
  `j` (by maximality of `r`), and Laplace expansion of that bordered minor
  along its last row (`det_eq_foldl_laplace_col` transposed, or
  `HexDeterminant/LastRow.lean`) reads
  `d · A[i, j] = Σ_k A[i, cols[k]] · (adj * P)[k, j]`, which is entry
  `(i, j)` of identity 3.

At `r = 0` the maximal nonzero minor is the empty one (`det` of the
`0 × 0` matrix is `1`), every entry of `A` is a vanishing `1 × 1` minor,
`d = 1` and identity 3 is `A = 0`. At `n = 0` or `m = 0` there are no
entries and the same certificate applies.

The argument needs `1 ≠ 0` (so that the empty minor is nonzero) and no
zero divisors (so that "largest size of a nonzero minor" is a rank). It
does not need an exact quotient: `adjugate` is polynomial in the entries.
That is why the certificate is complete over every nontrivial domain even
though the producer below is only defined over carriers with an executable
exact quotient.

## The producer

### Fraction-free Gauss-Jordan with column pivoting

```lean
/-- The pivot rows, in elimination order, and the pivot columns, strictly
increasing. -/
structure RankProfile (n m : Nat) where
  rank : Nat
  rows : Vector (Fin n) rank
  cols : Vector (Fin m) rank

/-- Output of one fraction-free Gauss-Jordan pass. -/
structure ReducedForm (R : Type u) (n m : Nat) where
  profile : RankProfile n m
  denom : R
  matrix : Matrix R n m

def rowReduceWith [Zero R] [One R] [Sub R] [Mul R] [DecidableEq R]
    (quot : R → R → R) (A : Matrix R n m) : ReducedForm R n m
```

The state carries the current matrix, the previous pivot `prev` (seed
`1`), the pivot rows found so far, and the pivot columns found so far.
Columns are scanned from `0` to `m - 1`. At column `j`:

1. **Search.** Among the rows that are not yet pivot rows, in increasing
   index order, find the first row `p` with `M[p, j] ≠ 0`. This is a
   membership test on the pivot-row list and an equality test on entries,
   and needs `[Zero R] [DecidableEq R]`.
2. **Skip.** If there is none, column `j` is not a pivot column. Nothing
   in the matrix changes, `prev` does not change, and the scan moves to
   `j + 1`. The entries of the pivot rows in column `j` are kept: they are
   the coefficients the reduced form reports for that column.
3. **Eliminate.** Otherwise `p` is appended to the pivot rows and `j` to
   the pivot columns, `pivot := M[p, j]`, and every row `i ≠ p` is updated
   in the columns `j' > j`:

   ```text
   M[i, j'] ← quot (pivot · M[i, j'] − M[i, j] · M[p, j']) prev
   ```

   after which `M[i, j] ← 0` for `i ≠ p`. Columns before `j` are
   untouched: in a pivot row they hold earlier reduced entries, in a
   non-pivot row they are already zero at pivot columns and are never
   read again at skipped columns. Then `prev := pivot`.

**Rows are not moved.** The pivot row stays where it is, the search order
in step 1 is the original row order, and the state records which rows are
pivot rows. This is the one choice that makes the row profile canonical,
see [The rank profile](#the-rank-profile). It costs nothing: Gauss-Jordan
eliminates every other row anyway, so a pivot row has no reason to be at a
particular position.

**Every row, not only the rows below.** Step 3 updates the earlier pivot
rows as well as the non-pivot rows. This is what makes the pass
Gauss-Jordan rather than Gaussian, and it is what makes the reported
`matrix` a reduced form. After the pass, with `B` the `rank × rank` block
at `rows × cols` in elimination order and `d` the last pivot:

- `denom = d = det B`;
- for each `k`, row `rows[k]` of `matrix` is row `k` of `adjugate B * P`,
  where `P = selectRows A rows`; in particular
  `matrix[rows[k], cols[l]] = if k = l then d else 0`;
- every non-pivot row of `matrix` is zero.

So `matrix` is `d` times the reduced row echelon form of `A` over the
fraction field, with its rows left in place. At `rank = 0` the seed is
returned: `denom = 1` and `matrix = A`, which is the zero matrix.

The pass takes `[Zero R] [One R] [Sub R] [Mul R] [DecidableEq R]` and
`quot`, the same operation classes as `bareissWith`. `One R` is for the
seed. There is an in-place `rowReduceWithImpl` on `Array (Array R)`
registered by `@[csimp]`, reusing `matrixToRows`, `rowsToMatrix` and
`getEntry` from `HexBareiss/Bareiss.lean`; the public definition is the
kernel-facing one, per design principle 11.

### The rank profile

Two canonical index sets are attached to a matrix over a field, and this
producer computes both.

- The **column rank profile** is the set of `j` such that column `j` is
  not in the span of columns `0 … j - 1`: the pivot columns of the reduced
  row echelon form.
- The **row rank profile** is the set of `i` such that row `i` is not in
  the span of rows `0 … i - 1`.

Each is a lexicographically first independent set, and each is an
invariant of the matrix.

**What the producer guarantees.** `cols` is the column rank profile. This
holds for any pivot-row rule: whether column `j` gains a pivot depends
only on whether some non-pivot row has a nonzero entry there after
elimination, which is whether column `j` lies outside the span of the
earlier pivot columns. `rows`, as a set, is the row rank profile. This
holds *because* step 1 searches the original row order among non-pivot
rows and rows are never moved: if a dependent row `i'` had a nonzero
eliminated entry at column `j`, that entry is a combination of the
eliminated entries of the non-pivot rows below `i'` in index order, so
some smaller-index non-pivot row also has a nonzero entry there and is
chosen first. The row chosen is therefore always a profile row, and since
`rank` rows are chosen, all profile rows are.

**What swapping loses.** With `findPivot?`-style row swaps, the search
order is the permuted order and the row set is *some* set of independent
rows, not the profile. On

```text
[[0, 1, 0],
 [0, 2, 0],
 [1, 0, 0]]
```

the row rank profile is `{0, 2}`. Column `0`: the first nonzero row is
`2`. With a swap of rows `0` and `2`, the search at column `1` runs over
the swapped order and finds original row `1` first, giving `{2, 1}`.
Without a swap, the search at column `1` runs over the non-pivot rows
`0, 1` in index order and finds row `0`, giving `{2, 0}`. The order
`rows = [2, 0]` is elimination order and is what the certificate uses; the
set is the profile.

The producer therefore guarantees the canonical profile in both
directions, and the companion states both facts as theorems
(`rowReduceWith_cols_eq_colProfile`, `rowReduceWith_rows_eq_rowProfile`).
A consumer that wants "some nonsingular `r × r` block" gets it from
`rows`, `cols`; a consumer that wants the profile gets it from the same
fields. This SPEC does not promise the full rank profile matrix of
Dumas, Pernet and Sultan ("Computing the rank profile matrix", ISSAC
2015), which records more than the two sets, and no consumer asks for it.

### What is new relative to hex-bareiss

Checked against `bareissDataWith` and `pivotLoopWith` in
`HexBareiss/Bareiss.lean`:

| aspect | `pivotLoopWith` / `bareissDataWith` | `rowReduceWith` |
|---|---|---|
| shape | `Matrix R n n`, square in the types | `Matrix R n m` |
| loop | `n - 1` steps, one per diagonal position | one step per column `0 … m - 1` |
| pivot column | the diagonal column `k` | the current column `j`, if any non-pivot row is nonzero there |
| empty pivot column | `singularStep := some k`, run stops | column skipped, run continues |
| pivot row | first nonzero at or below the diagonal, moved by `rowSwap` | first nonzero non-pivot row in index order, not moved |
| rows updated | rows below the pivot (Gaussian) | every row but the pivot row (Gauss-Jordan) |
| bookkeeping | `rowSwaps : Nat`, `singularStep : Option Nat` | `rows : Vector (Fin n) rank`, `cols : Vector (Fin m) rank` |
| output | terminal matrix, sign, last diagonal entry | `profile`, `denom = det B`, `d ·` reduced echelon form |
| determinant | `sign * lastDiag` | `denom` is `det B`, with `B` in elimination row order; on a square full-rank input this is `det A` up to the sign of the row order |

The update formula in step 3 is the Bareiss recurrence of
`stepMatrixWith`, so the fraction-free property and the exact-quotient
obligation are the same. Everything in the left column that concerns the
determinant (`sign`, `lastDiag?`, `singularStep`, `BareissData.det`) has
no counterpart here, and nothing here is a field added to `BareissData`.
`bareissWith` stays the determinant algorithm: on a square full-rank
matrix `rowReduceWith` does about half again the work of `bareissWith`
(it updates rows above the pivot and never stops early), and a consumer
that wants a determinant should not call it.

`findPivot?` is not reused, because it scans a contiguous row range and
the producer scans a filtered one. The array-storage layer is reused.

### Exactness and producer correctness

Every division in step 3 is by `prev`, which is `1` or a pivot already
tested nonzero, and every numerator is an exact multiple of `prev`.
Exactness is not tested at run time and is not a hypothesis on the input.
The invariant that establishes it, and with it the reduced-form contract
above, is:

> After the pivots `(rows[0], cols[0]) … (rows[k-1], cols[k-1])` have been
> processed, with `B_k := selectedSubmatrix A rows cols` (the `k × k`
> block, rows in elimination order) and `p := det B_k` (`p = 1` at
> `k = 0`):
>
> - the pivot rows of the state are the rows of `adjugate B_k * P_k`,
>   where `P_k := selectRows A rows`, equivalently the unique `U` with
>   `B_k * U = p • P_k`;
> - every non-pivot row `i` of the state is
>   `p • A[i, :] − A[i, cols] * U`;
> - `prev = p`.

Under the invariant, the entry the update produces at a pivot row is
`p · U'` and at a non-pivot row is `p · (p' • A[i,:] − A[i, cols'] * U')`
where primes denote the next block, so `hquot` returns the primed value.
The two identities are verified by left-multiplying by the nonsingular
`B_{k+1}` and cancelling, using only `B_k * U = p • P_k` and
`Matrix.mul_adjugate`. No Desnanot-Jacobi or Sylvester identity is used:
characterising the pivot rows as the unique solution of a linear system
over a domain replaces the bordered-minor recurrence that
hex-bareiss-mathlib proves. This is a proof-route choice, not a claim that
the entries are not minors (they are: the invariant says each non-pivot
entry is a bordered minor and each pivot-row entry is a minor with one
column replaced).

The route uses the adjugate and cancellation over a domain, which per
[hex-bareiss §Mathlib-free vs. Mathlib-bridge proof surface](../../HexBareiss/SPEC/hex-bareiss.md#mathlib-free-vs-mathlib-bridge-proof-surface)
places the invariant proof in the companion, not here. The Mathlib-free
layer ships the definitions, the loop-step equations
(`rowReduceWith_step_pivot`, `rowReduceWith_step_skip`, structural, no
`hquot`), and the checker theorems. The companion proves:

```lean
theorem rankCertWith_check [CommRing R] [DecidableEq R] [Nontrivial R]
    (quot : R → R → R) (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (A : Hex.Matrix R n m) :
    Hex.Matrix.checkRank A (Hex.Matrix.rankCertWith quot A) = true
```

This is producer correctness in the form the issue asks for: the producer
emits a certificate that checks. Everything about `Matrix.rank` then
follows from soundness and is stated in the companion.

### Entry points

```lean
/-- The rank profile. -/
def rankProfileWith (quot : R → R → R) (A : Matrix R n m) : RankProfile n m :=
  (rowReduceWith quot A).profile

/-- The certificate: the profile and denominator of one pass over `A`,
and the adjugate of the pivot block from one pass over `[B | identity]`. -/
def rankCertWith (quot : R → R → R) (A : Matrix R n m) : RankCert R n m

/-- The certificate, checked. -/
def certifyRankWith [Lean.Grind.CommRing R] [DecidableEq R]
    (quot : R → R → R) (A : Matrix R n m) : Option (RankCert R n m) :=
  let c := rankCertWith quot A
  if checkRank A c then some c else none

/-- The rank. -/
def rankWith (quot : R → R → R) (A : Matrix R n m) : Nat :=
  (rankProfileWith quot A).rank

-- Int specialisations, all through HexArith.Int.exactDiv.
def rowReduceFF (A : Matrix Int n m) : ReducedForm Int n m
def rankProfile (A : Matrix Int n m) : RankProfile n m
def rankCert (A : Matrix Int n m) : RankCert Int n m
def certifyRank (A : Matrix Int n m) : Option (RankCert Int n m)
def rank (A : Matrix Int n m) : Nat
```

`rankCertWith` runs `rowReduceWith` on `A` to obtain `rows`, `cols` and
`denom`, forms `[B | identity rank]` (`rank × 2·rank`, by `ofFn`), runs
`rowReduceWith` on it, and reads `adj` off the right block of the pivot
rows. The second pass finds every column of `B` a pivot column and every
row a pivot row, in some order `π`; its pivot rows, restricted to the
right block and taken in the order of `π`, are `sign π · adjugate B`, and
its `denom` is `sign π · det B`. The certificate takes both from the
second pass, so the pair is consistent whatever `π` is. (`rankCertWith`
does not use the first pass's `denom`; it is reported by `rowReduceWith`
for consumers that want `det B` without the adjugate.)

The two-pass shape costs `O(n · r · m + r³)`. One pass over
`[A | identity n]` also yields `adj B` (as the `rows × rows` block of the
right half's pivot rows) and, in addition, the whole fraction-free
transform, at `O(n · r · (m + n))`. It is never asymptotically cheaper
and is worse for tall low-rank input, so it is not the default; a
consumer that wants the transform (the `Decomposition` adapter in the
companion is one) calls `rowReduceWith` on the augmented matrix itself.

`rankWith` and `rankProfileWith` are unchecked and fast, like `bareiss`;
their correctness is `rankCertWith_check` plus soundness, in the
companion. `certifyRankWith` is for a consumer that wants the witness and
the check in one call, and its `none` branch is
`unreachable-by-pipeline-invariant` under design principle 8, with
`rankCertWith_check` as the witness theorem; the compiled `rank` does not
route through it, so no fallback value is ever chosen. A caller that
wants both the profile and the certificate calls `rankCertWith` once: the
certificate's `rows`, `cols` *are* the profile.

## Carriers

The producer is one function. Each carrier supplies its quotient and its
law term, exactly as in
[hex-bareiss §Supported coefficient carriers](../../HexBareiss/SPEC/hex-bareiss.md#supported-coefficient-carriers):

| carrier | quotient | law term for `hquot` | `DomainLaws` |
|---|---|---|---|
| `Int` | `HexArith.Int.exactDiv` | `Int.mul_ediv_cancel` | `instance` |
| `Rat`, `ZMod64 p` (field) | `Hex.exactDiv` | `fun a b hb => Hex.exactDiv_mul_right a hb` via `Hex.instExactDivLawsField` | field instance |
| `DensePoly F`, `[Lean.Grind.Field F] [DecidableEq F]` | `Hex.exactDiv` with `HexResultant.ExactDiv`'s `Hex.instExactDivLawsDensePoly` | same | `of_exactDivLaws` |
| `ZPoly` (`DensePoly Int`) | `Hex.exactDiv` with the same recursive instance over `Hex.instExactDivLawsInt` | same | `of_exactDivLaws` |
| `MvPoly n R cmp` under the `HexMvGcd.Divide` context | `Hex.exactDiv` with `Hex.MvPoly.instDiv` and `Hex.MvPoly.instExactDivLaws` | same | `of_exactDivLaws` |

### Int

`Int` is the production instantiation and lives in `HexRank/Int.lean`,
through `HexArith.Int.exactDiv` (which `Hex.Matrix.exactDiv` in
hex-bareiss now aliases). The names `rank`, `rankProfile`, `rankCert`,
`certifyRank` are the `Int` forms.

**Coincidence with hex-modular-matrix.** The certificate there
(`RankCert n m` with `rows`, `cols`, `modulus`, `coeffs : Matrix Int r (m - r)`,
`denom`) is amended to *be* `Hex.Matrix.RankCert Int n m`, and its
`checkRank` to be this library's, with these consequences, recorded in
[hex-modular-matrix §Rank](hex-modular-matrix.md#rank):

- the `modulus` field and the "minor nonzero modulo `modulus`" test go
  away, replaced by the adjugate identity, which is a big-integer product
  the multi-modular route also has to produce; the completeness argument
  that motivated a bare `Nat` modulus there (the `1 × 1` matrix `[L]`) is
  moot, because the adjugate certificate is complete over `Int` with no
  modulus at all;
- the strictly-increasing check on `rows`, `cols` goes away, since the
  all-column identity does not index a complement;
- the producer there (`rankCert?`) keeps its modular route for finding
  `rows`, `cols`, and obtains `adj B` and `det B` by Dixon solves of
  `B * X = det B • identity r` (`r` solves, against the `m - r` the draft
  did), with the whole certificate then passed to `checkRank`;
- `checkRank_sound` there is this library's soundness, and its
  `rank_eq` in the companion is this library's `checkRank_sound` at
  `R = Int`, so hex-modular-matrix-mathlib inherits rather than reproves
  it;
- its unchecked `rank : Matrix Int n m → Nat` is renamed
  `rankModular`, since `Hex.Matrix.rank` is this library's `Int`
  entry point and both libraries are imported together by
  hex-matrix-tactic.

hex-modular-matrix is unimplemented, so this is a SPEC amendment with no
code to migrate.

### `DensePoly F` and `ZPoly`

Over `F[x]` the certificate's `denom` is a polynomial and `adj` a
polynomial matrix. The rank it certifies is the rank over `F(x)`, and the
companion's `rank_map_eq` at `IsFractionRing (Polynomial F) (RatFunc F)`
is the statement `HexPolySmithMathlib.rank_eq_ratFunc_rank` already makes
for `snfRank`, now with a witness. `ZPoly` is `DensePoly Int` through the
recursive exact-division instance; its rank is over `ℚ(x)`.

### `MvPoly`

Over `MvPoly k R cmp` with `R` a domain, the rank is the rank over the
fraction field `Frac(R)(x_1, …, x_k)`, the *generic rank* of the
polynomial matrix. The certificate's `denom` is a polynomial `d` with
`d ≠ 0`, and `adj` is a polynomial matrix.

### Generic rank is not a specialised rank

A polynomial matrix `A` of generic rank `r` specialised at a point `p`
has rank at most `r` (hex-determinantal-ideal-mathlib's
`rank_map_le_rank_fractionRing`), and has rank exactly `r` at every `p`
where the certificate's `denom` does not vanish, since then `det B (p) ≠ 0`
and the lower bound survives specialisation. Nothing says such a `p`
exists. Over a finite field it need not: the `1 × 1` matrix `[X^q − X]`
over `𝔽_q[X]` has generic rank `1`, and `X^q − X` vanishes at every
`a ∈ 𝔽_q`, so the specialised rank is `0` at every base-field point.
The same happens for any polynomial in the ideal of the finite point set.

A downstream tactic must therefore treat the generic rank as one of three
distinct outputs and never present it as an unconditional specialised
rank:

1. **Generic rank**: `rank = r` as a statement about `A` over `R` or over
   its fraction field. Unconditional. This library.
2. **Conditional rank**: `rank (A.map (eval p)) = r` under the hypothesis
   `eval p denom ≠ 0`, or more generally under a nonvanishing hypothesis
   on the minor the certificate names. The hypothesis is a `Condition`
   in the sense of [hex-reflect §Shared results and conditions](hex-reflect.md#shared-results-and-conditions),
   returned to the caller rather than discharged. The certificate supplies
   the condition as data: it is `denom`.
3. **Rank locus**: the set of points where the rank drops below `r`, the
   zero set of the determinantal ideal `I_r(A)`, from
   hex-determinantal-ideal. The tactic that produces it is `rank_locus`,
   and it takes `r` from this library only when the user asks for the
   generic rank as the default `r`.

### Placement

`scripts/check_dag.py` enforces the production graph from
`libraries.yml`, and `HexBareiss`, hence `HexRank`, cannot depend on
`HexMvPoly`, `HexPoly` or `HexMvGcd`. So:

- the `Int` instantiation is production code in `HexRank/Int.lean`;
- the `Rat`, `ZMod64 p`, `DensePoly F`, `ZPoly` and `MvPoly`
  instantiations live in `conformance/HexRank/Conformance.lean`, the
  emitter `conformance/HexRank/EmitFixtures.lean` and
  `bench/HexRank/Bench.lean`, which may import `HexPolyFp.PrimeField`,
  `HexResultant.ExactDiv` and `HexMvGcd.Divide` and have no production
  owner under `check_dag.py`, exactly as hex-bareiss's carrier table
  places its own instantiations;
- a production consumer that wants a named `MvPoly` rank defines it
  itself, as `rankWith Hex.exactDiv` under the `HexMvGcd.Divide` context,
  in a library already above `HexMvGcd`. The `rank_locus` and symbolic
  `rank` tactics are the expected first such consumers, through
  hex-matrix-tactic, and that one-line instantiation is theirs to make.
  Nothing carrier-specific is added to `HexRank/*`.

## Complexity

`A` is `n × m` of rank `r`; counts are ring operations.

| operation | multiplications | exact divisions | notes |
|---|---|---|---|
| `rowReduceWith` | `≤ 2 · r · n · m` | `≤ r · n · m` | one Gauss-Jordan step per pivot column, every row updated; skipped columns cost `O(n)` zero tests each |
| `rankCertWith` | `rowReduceWith` plus `O(r³)` | plus `O(r³)` | the second pass on `[B \| identity r]` |
| `checkRank` | `n · r · m + r² · m + r³ + n · m` | none | one product dominates; no determinant |
| `rankWith`, `rankProfileWith` | as `rowReduceWith` | | |

**Growth.** The invariant says every stored entry is a minor of `A` (a
bordered `(k + 1) × (k + 1)` minor in a non-pivot row, a `k × k` minor with
one column replaced in a pivot row), and every certificate entry is a
minor (`denom` an `r × r` minor, `adj` entries `(r − 1) × (r − 1)` minors).
Over `Int` with `‖A‖∞ ≤ B` Hadamard's bound gives `O(r · (log r + log B))`
bits per entry, so `rowReduceWith` costs `O(r · n · m)` operations on
integers of that size and `checkRank` costs `O(n · r · m)` multiplications
of numbers of that size. This is the fraction-free contract of
[hex-bareiss §Complexity](../../HexBareiss/SPEC/hex-bareiss.md#complexity),
with `n³/3` replaced by `r · n · m`: on a low-rank matrix the run is short
in the rank, not in the dimension. Over a polynomial carrier there is no
bit bound; the minor identity is the only size statement, and expression
swell in a minor is outside this SPEC as it is outside hex-bareiss's.

The checker's `n · r · m` is the number a kernel replay pays. It is not
smaller than the producer's count in the worst case (`r = min n m`), and
this SPEC does not claim it is; what the certificate saves the kernel is
the search, the divisions, and any determinant.

## Relationship to the other rank computations in the tree

- **`rowReduce` (hex-row-reduce).** Over a field both compute the reduced
  row echelon form; `rowReduce` divides by the pivot and `rowReduceWith`
  multiplies through and divides by the previous pivot. Over a field a
  consumer should use `rowReduce`. This library does not import
  hex-row-reduce, and the theorem that the two ranks agree over a field is
  a corollary of hex-determinantal-ideal's `rank_eq_iff_minors` and the
  two soundness theorems here, to be stated wherever both are imported.
- **`hnfRank`, `snfRank` over `Int`** compute the rank as a by-product of a
  normal form and carry no witness. `rank` here is the direct algorithm.
  hex-hermite's modular route and hex-modular-matrix's multi-modular
  route are the fast paths at large size, and both should return this
  certificate.
- **`Hex.PolyMatrix.snfRank` over `F[x]`** is the polynomial Smith form's
  rank. `rankWith Hex.exactDiv` over `DensePoly F` is the direct
  algorithm with a witness, and the two agree through the companion's
  `rank_map_eq` and `rank_eq_ratFunc_rank`.
- **hex-determinantal-ideal** enumerates all `r × r` minors and proves
  the rank-versus-minors theorem for every `r`; it takes `r` as an input.
  This library finds one nonzero `r × r` minor and its adjugate. The two
  are independent, and the soundness theorems here are the instance of
  the nonzero-minor direction at the certificate's minor.
- **`Echelon.Decomposition` (Mathlib)**, see the companion.

## Prerequisite changes in other libraries

None blocks starting work here; each is an ordinary change to a repo
regenerated from this monorepo.

- **`Hex.DomainLaws` in `HexBasic/ExactDiv.lean`**, with the `Int` and
  field instances and `DomainLaws.of_exactDivLaws`, as specified under
  [Coefficient contract](#coefficient-contract). If landing it in
  hex-basic is deferred, the class starts in `HexRank/Domain.lean` and
  moves down when a second consumer appears.
- **`det_smul` in `HexDeterminant/RowOps.lean`**,
  `det (c • M) = c ^ k * det M` for `M : Matrix R k k`, by `det_rowScale`
  iterated, and `selectedSubmatrix_smul`,
  `selectedSubmatrix_mul_eq_selectRows_mul_selectCols` in
  `HexDeterminant/Minor.lean`, both entrywise. hex-determinantal-ideal
  asks for the column analogue `selectCols_mul`; these are of the same
  kind and whichever library lands first adds them.
- **hex-modular-matrix SPEC amendment**, as listed under [Int](#int).
- **`HexHermite`** may later return this certificate from its modular
  path; nothing is required now.

## Conformance

Fixtures follow [SPEC/testing.md](../testing.md). Lean drivers at
`conformance/HexRank/Conformance.lean` and
`conformance/HexRank/EmitFixtures.lean`, the latter exposed as
`lean_exe hexrank_emit_fixtures`, a committed snapshot at
`conformance-fixtures/HexRank/rank.jsonl`, and an oracle driver at
`scripts/oracle/rank_carriers.py`. One tuple appended to `ORACLES` in
`scripts/ci/run_oracles.sh`:

```
"HexRank|hexrank_emit_fixtures|scripts/oracle/rank_carriers.py|conformance-fixtures/HexRank/rank.jsonl"
```

The driver follows `scripts/oracle/matrix_carriers.py` in shape:
python-flint for `Int` (`fmpz_mat`), `Rat` (`fmpq_mat`) and `ZMod64 p`
(`nmod_mat`) records, SymPy for `DensePoly` and `MvPoly` records with the
exact domain (`ZZ[x]`, `QQ[x]`, `GF(p)[x]`, `ZZ[x0, …]`, `QQ[x0, …]`)
stated explicitly. Both are already installed and preflighted by the
single oracle job; no install line changes.

**Record format and operations.** A record carries the carrier, the
matrix (integers, rationals, residues normalised to `[0, p)`, ascending
coefficient arrays for `DensePoly`, ordered exponent-vector terms for
`MvPoly`), and one of:

| `op` | Lean value | oracle recomputation and comparison |
|---|---|---|
| `rank` | `rankWith quot A` | `fmpz_mat.rank()` / `fmpq_mat.rank()` / `nmod_mat.rank()`; SymPy `Matrix.rank()` over the exact domain, compared as integers |
| `colProfile` | `(rankProfileWith quot A).cols` | the pivot columns of the oracle's own reduced row echelon form (`fmpz_mat.rref()`, `fmpq_mat.rref()`, SymPy `Matrix.rref()`), compared as lists |
| `rowProfile` | `(rankProfileWith quot A).rows` sorted | the rows `i` with `rank(A[0..i]) = rank(A[0..i-1]) + 1`, recomputed by the oracle with its own rank on row prefixes, compared as sorted lists |
| `denom` | `(rowReduceWith quot A).denom` | the determinant of the oracle's submatrix at the Lean-reported `rows × cols`, compared exactly (this re-uses Lean's index selection, which is permitted canonicalisation: the value compared is the oracle's determinant) |
| `cert` | `rankCertWith quot A`, with `checkRank A c` asserted `true` by `#guard` in `Conformance.lean` | the oracle re-verifies identities 1 to 3 with its own arithmetic (`fmpz_mat`/`fmpq_mat`/SymPy products) and re-checks `rank` against its own rank; a certificate that passes `checkRank` but fails the oracle's identities is a checker bug |

The `cert` row is the requirement that the certificate be checked by the
oracle-independent checker: `checkRank` is asserted in Lean on every
emitted certificate, and the oracle's verification of the same identities
is the cross-check on `checkRank` itself, not a substitute for it.

**Cases that must be present**, since these are what a plausible
implementation gets wrong:

- `0 × 0`, `0 × m`, `n × 0`: rank `0`, `denom = 1`, empty profile, and
  the certificate checks;
- the zero matrix at several shapes: rank `0`, `denom = 1`, and
  `checkRank_eq_zero_of_rank_zero` by `decide` in `Conformance.lean`;
- `1 × 1` `[0]` and `[c]` for `c ≠ 0`, including negative `c` (so
  `denom = c` and `adj = [1]`);
- `[[0, 1], [0, 0]]`: rank `1`, `cols = [1]`, `rows = [0]`, the matrix
  on which `bareissDataWith` stops;
- a matrix with a skipped column in the middle and a pivot after it;
- the `3 × 3` example under [The rank profile](#the-rank-profile), whose
  row profile `{0, 2}` differs from the swap-order set `{1, 2}`;
- wide and tall matrices of every rank from `0` to `min n m`, built as
  products of an `n × r` and an `r × m` matrix so that the rank is known
  by construction;
- a full-rank square matrix whose elimination order is not the identity
  (so `denom = ± det A` with the sign determined by `rows`), checked
  against the oracle's determinant of the reordered submatrix;
- a matrix with entries of several hundred bits, where the minors in the
  certificate are much larger than the input;
- for every certificate case, a mutated certificate (wrong `rank`, one
  entry of `adj` changed, `denom := 0`, a repeated index in `rows`) with
  `checkRank` asserted `false` in `Conformance.lean`, so that the checker
  is seen to reject as well as accept;
- `DensePoly Rat` and `ZPoly` matrices whose second pivot is nonconstant,
  so the exact division is by a nonconstant polynomial, and a singular one;
- `DensePoly (ZMod64 p)`: the `1 × 1` matrix `[X^p − X]`, rank `1`, with
  `checkRank` true, beside the `rankAt`-style observation (in the
  docstring of the case, not as an oracle op) that it is `0` at every
  point of `𝔽_p`;
- `MvPoly` in two and three variables with mixed monomials, including a
  generic `2 × 3` matrix of six indeterminates (rank `2`, `denom` one of
  the classical `2 × 2` minors) and a rank-deficient one built as a
  product.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), with drivers at
`bench/HexRank/Bench.lean`, Mathlib-free, no import of any `Hex*Mathlib`
module. The registrations extend the existing single bench job.

**Input families**, each seeded and deterministic:

- `dense-full-rank`: square `n × n` matrices of small random entries,
  `n = 16 … 256`, rank `n` with overwhelming probability and checked at
  generation. This is the family where the rank profile route does the
  most work per row and is comparable to `bareiss`.
- `low-rank-large-coefficients`: `n × n` matrices formed as a product of
  an `n × r` and an `r × n` matrix with `r ∈ {2, 8}` fixed and entries of
  `64` and `1024` bits, `n = 16 … 256`. The run should be linear in `n²`
  at fixed `r`, and the coefficient size is where the fraction-free
  growth is measured.
- `rank-deficient-by-construction`: `n × n` matrices of rank `n − 1` and
  of rank `n / 2`, built as products with small entries, `n = 16 … 256`,
  including a variant whose pivot columns are not the first `r` columns,
  so that the skip path is on the measured route.
- `polynomial`: `DensePoly Rat` and `MvPoly 2 Int` matrices of dimension
  `4 … 12` with entries of fixed small support, full rank and rank
  deficient, for the carrier instantiations.

**Registrations**, per the Attribution rule: `rowReduceWith` (the
producer's first pass), `rankCertWith` (both passes), and `checkRank`
(on the certificate the producer emitted, with certificate construction
hoisted into `prep`) are separate `setup_benchmark` targets on every
family, so that the ratio between producer and checker is a recorded
number and not an assumption of the tactic SPEC.

**Complexity claim**, mode 1 (two-sided parametric): on
`low-rank-large-coefficients` at fixed `r`, `rowReduceWith` and
`checkRank` are `Θ(n²)` big-integer operations at an entry size that does
not grow with `n`, so the declared scaling is `n²` in `n`. On
`dense-full-rank`, the declared scaling is the one hex-bareiss declares
for `bareiss` on its dense family (cubic count at Hadamard-bounded entry
size), because the operation count differs by a constant. The
derivations are the operation counts in [Complexity](#complexity); they
are written before measurement and are not fitted.

**Comparators**, all `informational`, with the rationale recorded here
and in `libraries.yml`:

| comparator | scope | rationale |
|---|---|---|
| python-flint `fmpz_mat.rank()` | `Int` families | FLINT selects between fraction-free and multi-modular rank by size, so the ratio compares algorithms, and no shared fixture history anchors a required ratio |
| python-flint `fmpq_mat.rank()` | `Rat` variants of the `Int` families | as above, over `ℚ` |
| SymPy `Matrix.rank()` over the exact polynomial domain | `polynomial` family | SymPy's rank chooses its own elimination and includes Python overhead |

Wired as persistent-subprocess drivers following `Hex.BenchOracle.Flint`,
with trivial-request overhead recorded in
`reports/hex-rank-performance.md §Comparator ratios`. The external rungs
are scheduled-only; the Hex registrations build and verify in the ordinary
bench target and stay under the `Bench verify` budget by registering the
verify path at the smallest rung of each family.

## File organisation

```text
HexRank.lean                     umbrella
HexRank/
  Cert.lean        RankCert, checkRank
  Check.lean       checkRank_minor_ne_zero, checkRank_minor_succ_eq_zero, checkRank_eq_zero_of_rank_zero
  Reduce.lean      RankProfile, ReducedForm, rowReduceWith, rowReduceWithImpl, loop-step lemmas
  Produce.lean     rankProfileWith, rankCertWith, certifyRankWith, rankWith
  Int.lean         rowReduceFF, rankProfile, rankCert, certifyRank, rank
  SPEC/hex-rank.md
  README.md
conformance/HexRank/{Conformance,EmitFixtures}.lean
conformance-fixtures/HexRank/rank.jsonl
scripts/oracle/rank_carriers.py
bench/HexRank/Bench.lean
```

`libraries.yml` gains:

```yaml
  HexRank:
    deps: [HexBareiss, HexDeterminant, HexMatrix, HexArith, HexBasic]
    mathlib: false
    done_through: 0
    status: planned
    phase4:
      comparators:
        - tool: FLINT fmpz_mat.rank via python-flint
          class: informational
          rationale: FLINT selects fraction-free or multi-modular rank by size, so the ratio compares algorithms; no shared fixture history anchors a required ratio.
        - tool: FLINT fmpq_mat.rank via python-flint
          class: informational
          rationale: the same over the rationals.
        - tool: SymPy Matrix.rank over the exact polynomial domain
          class: informational
          rationale: SymPy chooses its own elimination and includes interpreter overhead; it orients the polynomial carriers only.
      input_families:
        - name: dense-full-rank
          description: square matrices of small random entries at full rank, n = 16 to 256.
        - name: low-rank-large-coefficients
          description: products of n by r and r by n matrices at r = 2 and 8 with 64- and 1024-bit entries, n = 16 to 256.
        - name: rank-deficient-by-construction
          description: square products of rank n - 1 and n / 2 with small entries, including pivot columns that are not the leading columns.
        - name: polynomial
          description: DensePoly Rat and MvPoly 2 Int matrices of dimension 4 to 12 at fixed support, full rank and rank deficient.
  HexRankMathlib:
    deps: [HexRank, HexBareissMathlib, HexDeterminantMathlib, HexMatrixMathlib]
    mathlib: true
    correspondence_only: true
    done_through: 0
    status: planned
```

## Milestones

1. **The certificate.** `Hex.DomainLaws`, `RankCert`, `checkRank`, and
   the three soundness theorems with their `HexDeterminant` lemmas. At the
   end of this milestone a hand-written certificate can be checked and
   the checker is proved sound, with no producer.
2. **The producer.** `RankProfile`, `ReducedForm`, `rowReduceWith`, the
   in-place implementation and its `@[csimp]`, the loop-step lemmas, and
   the entry points. Conformance against the oracle for `rank`,
   `colProfile`, `rowProfile`, `denom` and `cert`.
3. **The `Int` layer and the amendment to hex-modular-matrix.**
4. **The companion.** `checkRank_sound`, `rankCertWith_check`, the
   profile theorems, `rank_map_eq`, and the `Decomposition` adapters.
   Begins after milestone 1.
5. **Carriers and benchmarks.** The polynomial instantiations in the
   conformance and bench modules, the families above, and the headline
   report.

## Open questions

- **Whether `rowReduceWith`'s first pass should be Gaussian rather than
  Gauss-Jordan.** `rankCertWith` uses only `rows`, `cols` from the first
  pass, which a below-only elimination computes at a smaller constant. The
  reduced form is what `rowReduceWith` is for, and a second, below-only
  loop is a second loop to prove. Measure on `dense-full-rank` before
  adding one.
- **Whether `Hex.DomainLaws` should subsume `Hex.GcdDomainLaws`'s
  `one_ne_zero` and `no_zero_div` fields** in hex-mv-gcd. The two classes
  state the same two facts; making `GcdDomainLaws` extend `DomainLaws` is
  a hex-mv-gcd change and is not required by this library.
- **Whether the certificate should record the sign of the row order.**
  The producer's `denom` is `det B` with rows in elimination order. A
  consumer that wants `det` of the sorted block must compute the sign.
  Adding a `sortedSign` field is cheap for the producer and not needed by
  any consumer named here.
- **The crossover with `hnfRank` and with the multi-modular route over
  `Int`.** Both are expected to win at large size; the benchmark decides
  the size, and this SPEC does not guess it.
