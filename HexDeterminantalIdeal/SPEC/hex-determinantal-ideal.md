# hex-determinantal-ideal

Executable minors and determinantal ideals of a matrix over a commutative
ring, and the theorem that a matrix over a field has rank below `r` exactly
when every `r × r` minor vanishes. Applied to a matrix of polynomials and a
point, the theorem says where the rank of the specialised matrix drops: the
set of points at which every `r × r` minor vanishes. That set is the zero set
of the `r`-th determinantal ideal `I_r(A)`. This library computes the
generators of that ideal and proves the theorem. The `rank_locus` tactic, a
later SPEC, packages the theorem for Mathlib goals and adds nothing to its
mathematics.

## Why this library exists

Minors already appear in four places in the repository, all as proof devices
rather than as a computation a user can run:

- `Hex.Matrix.selectedSubmatrix`, `deleteRowCol` and `cofactor` in
  `HexDeterminant/Minor.lean`, used by the Laplace expansion and the
  adjugate;
- `Hex.Matrix.borderedMinor` in `HexBareiss/BorderedMinor.lean`, used by the
  Bareiss invariant;
- `Hex.Matrix.detDivisor` in `HexSmith/Divisor.lean` and
  `Hex.PolyMatrix.minors`/`detDivisor` in `HexPolySmith/Divisor.lean`, both
  `noncomputable`, each enumerating all `k × k` minors through
  `selectedColumnTuples` and used only to prove that the Smith form is
  unique.

Cauchy-Binet for an arbitrary selected minor of a product
(`det_minor_mul` in `HexDeterminant/Gram.lean`) and the Laplace expansion
(`det_eq_foldl_laplace_col` in `HexDeterminant/Laplace.lean`) are proved, but
no statement relates the vanishing of minors to the rank, and the only fact
about a symbolic matrix's rank is
`HexPolySmithMathlib.rank_eq_ratFunc_rank`, which identifies the executable
Smith rank over `F[x]` with the rank over `RatFunc F` and says nothing about
specialisation.

This library turns the enumeration into an executable function with fixed
conventions at every size, proves the rank-versus-minors theorem once, over
any field and with a Mathlib-free proof, and leaves the consumers (the
`rank_locus` tactic and, through its companion, any Mathlib development) to
instantiate it.

## Scope and dependencies

`HexDeterminantalIdeal` is Mathlib-free. Its modules import, in this order:

- `Minors.lean`: `HexDeterminant` (and through it `HexMatrix`, `HexBasic`),
  and `HexArith` for `Hex.Nat.choose`, which `length_minors` needs
  (`Nat.choose` is not in core Lean).
- `Rank.lean`: additionally `HexRowReduce`, for `rowReduce_rank` and the
  row-reduced echelon certificate the nonzero-minor direction is built from.
- `MvPoly.lean`: additionally `HexMvPoly`, for the specialisation of a
  polynomial matrix at a point.

The library's dependency list is therefore `HexBasic`, `HexArith`,
`HexMatrix`, `HexDeterminant`, `HexRowReduce`, `HexMvPoly`. It does not
depend on `hex-bareiss`, `hex-rank`, `hex-poly-smith`, `hex-mv-gcd` or
anything that computes a generic rank. Those libraries only choose a
default `r`; the theorem here is stated for every `r`. `hex-rank` and
this library are independent siblings: neither imports the other, and
`hex-rank`'s certificate (a nonzero `r × r` minor plus a column
expression) is an instance of the nonzero-minor direction proved here,
not a dependency of it.

The companion `HexDeterminantalIdealMathlib` depends on this library,
`HexDeterminantMathlib`, `HexRowReduceMathlib` and `HexMvPolyMathlib`, plus
Mathlib. It is specified in
[hex-determinantal-ideal-mathlib](../../HexDeterminantalIdealMathlib/SPEC/hex-determinantal-ideal-mathlib.md).

Gröbner bases, ideal membership, radicals, primary decomposition and
Fitting ideals are outside this library. The ideal `I_r(A)` is presented by
its generating minors and nothing else. See
[What this library does not claim](#what-this-library-does-not-claim).

The namespace is `Hex.Matrix`, beside `det` and `selectedSubmatrix`. The
names `Hex.Matrix.minorSelections`, `minorValue` and `detDivisor` are
already taken by `HexSmith/Divisor.lean`, and this library does not reuse
them.

## Conventions: a minor of every size

For `A : Matrix R n m` and `r : Nat`, an `r × r` minor of `A` is the
determinant of `selectedSubmatrix A rows cols` for strictly increasing
`rows : Vector (Fin n) r` and `cols : Vector (Fin m) r`. The strictly
increasing tuples are exactly the members of `selectedColumnTuples r n` and
`selectedColumnTuples r m` (`mem_selectedColumnTuples_iff` in
`HexDeterminant/Gram.lean`), so every row set and column set is listed once.
The order is the one `selectedColumnTuplesUpTo` produces: tuples are grouped
by their last entry in increasing order, and within a group the prefixes
recur in the same order, so `selectedColumnTuples 2 4` is
`01, 02, 12, 03, 13, 23`. This is colexicographic order, not the
lexicographic order `itertools.combinations` produces, and the oracle
below sorts its combinations by reversed tuple to match.

The two boundary cases are fixed by the definitions rather than by special
cases in the code:

- **`r = 0`.** `selectedColumnTuples 0 n = [#v[]]` for every `n`, and the
  determinant of the `0 × 0` matrix is `1` (the Leibniz sum over the single
  empty permutation). So `minors 0 A = [1]`: there is one zero-sized minor
  and it is `1`. The ideal `I_0(A)` is the unit ideal.
- **`r > min n m`.** A strictly increasing `r`-tuple in `Fin n` requires
  `r ≤ n` (its last entry is at least `r - 1`), so
  `selectedColumnTuples r n = []` when `n < r`, and `minors r A = []`. The
  ideal `I_r(A)` is the zero ideal.

These conventions make the chain

```text
R = I_0(A) ⊇ I_1(A) ⊇ ... ⊇ I_{min n m}(A) ⊇ I_{min n m + 1}(A) = 0
```

hold with no side conditions, and they make the main theorem true at
`r = 0` and at `r > min n m` without separate clauses.

## API

All definitions are executable and `@[expose]`d so that `decide +kernel`
can evaluate them on closed inputs. The `MvPoly` rows assume the instances
every `HexMvPoly` operation assumes: `[Std.TransCmp cmp]`,
`[Std.LawfulEqCmp cmp]` and `[DecidableEq R]` on the coefficient ring.

| Operation | Type and contract |
| --- | --- |
| `minors r A` | `[Lean.Grind.Ring R] (A : Matrix R n m) (r : Nat) : List R`. Every `r × r` minor of `A`, rows outer and columns inner, both in the order of `selectedColumnTuples`. Length `n.choose r * m.choose r`. |
| `detIdealGens r A` | `[Lean.Grind.Ring R] [DecidableEq R] : List R`. `minors r A` with the zero entries removed and exact duplicates removed, keeping first occurrences. A generating list for `I_r(A)`. |
| `Matrix.map A f` | `(A : Matrix R n m) (f : R → S) : Matrix S n m`, entrywise. Added to `HexMatrix/Basic.lean` if still absent when this library is implemented (at the time of writing `HexMatrix` has `mapRows` and `mapRowsIdx` but no entrywise map), with `getElem_map`. |
| `specialize A p` | `[Lean.Grind.CommRing R] (A : Matrix (MvPoly k R cmp) n m) (p : Fin k → R) : Matrix R n m`, defined as `A.map (MvPoly.eval p)`. The point is a function, as `MvPoly.eval` takes it. |
| `rankAt A p` | `[Lean.Grind.Field F] [DecidableEq F] : Nat`, defined as `rowReduce_rank (specialize A p)`. The rank of the polynomial matrix at the point `p`. |
| `InLocus r A p` | `Prop`, `∀ M ∈ minors r A, MvPoly.eval p M = 0`, with a `Decidable` instance. The point `p` lies in the zero set of `I_r(A)`. |

`detIdealGens` is a convenience for display and for fixtures. Every theorem
is stated about `minors`, and the companion proves that the two lists
generate the same ideal. No normalisation beyond dropping zeros and exact
duplicates is performed: `M` and `-M` both stay, and no leading-coefficient
or sign convention is imposed, because any such convention would be
ring-specific and the library is generic.

## Enumeration theorems

Proved in `Minors.lean`, all Mathlib-free:

```lean
theorem mem_minors_iff (A : Matrix R n m) (r : Nat) (x : R) :
    x ∈ minors r A ↔ ∃ rows ∈ selectedColumnTuples r n, ∃ cols ∈ selectedColumnTuples r m,
      x = det (selectedSubmatrix A rows cols)
theorem length_minors (A : Matrix R n m) (r : Nat) :
    (minors r A).length = n.choose r * m.choose r
theorem minors_zero (A : Matrix R n m) : minors 0 A = [1]
theorem minors_eq_nil_iff (A : Matrix R n m) (r : Nat) :
    minors r A = [] ↔ n < r ∨ m < r
theorem selectedColumnTuples_eq_nil_of_lt (h : n < r) : selectedColumnTuples r n = []
theorem minors_transpose [Lean.Grind.CommRing R] (A : Matrix R n m) (r : Nat) :
    (minors r A.transpose).Perm (minors r A)
theorem mem_detIdealGens_iff [DecidableEq R] (x : R) :
    x ∈ detIdealGens r A ↔ x ∈ minors r A ∧ x ≠ 0
theorem deleteRowCol_selectedSubmatrix (A : Matrix R n m)
    (rows : Vector (Fin n) (k + 1)) (cols : Vector (Fin m) (k + 1)) (i j : Fin (k + 1)) :
    deleteRowCol (selectedSubmatrix A rows cols) i j =
      selectedSubmatrix A (rows.eraseIdx i) (cols.eraseIdx j)
theorem isStrictlyIncreasingColumnTuple_eraseIdx (h : IsStrictlyIncreasingColumnTuple cols)
    (i : Fin (k + 1)) : IsStrictlyIncreasingColumnTuple (cols.eraseIdx i)
```

`minors_transpose` is a permutation, not an equality, because the transpose
swaps the roles of the outer and inner loops. It comes from
`selectedSubmatrix_transpose` and `det_transpose`.

## The rank-versus-minors theorem

Proved in `Rank.lean`, over a `Lean.Grind.Field K` with `DecidableEq K`,
about the rank computed by `Hex.Matrix.rowReduce` (library `HexRowReduce`):

```lean
theorem rank_lt_iff_minors_eq_zero (A : Matrix K n m) (r : Nat) :
    rowReduce_rank A < r ↔ ∀ M ∈ minors r A, M = 0
theorem le_rank_iff_exists_minor_ne_zero (A : Matrix K n m) (r : Nat) :
    r ≤ rowReduce_rank A ↔ ∃ M ∈ minors r A, M ≠ 0
theorem rank_le_iff_minors_succ_eq_zero (A : Matrix K n m) (r : Nat) :
    rowReduce_rank A ≤ r ↔ ∀ M ∈ minors (r + 1) A, M = 0
theorem rank_eq_iff_minors (A : Matrix K n m) (r : Nat) :
    rowReduce_rank A = r ↔ (∃ M ∈ minors r A, M ≠ 0) ∧ ∀ M ∈ minors (r + 1) A, M = 0
```

The three corollaries are restatements of the first theorem. The companion
replaces `rowReduce_rank A` by `Matrix.rank` through
`HexRowReduceMathlib.rank_eq`.

### Both boundary cases, checked against the statement

- `r = 0`: the left side `rowReduce_rank A < 0` is false. The right side
  says every member of `minors 0 A = [1]` is zero, which is `1 = 0`, false
  by `Lean.Grind.Field.zero_ne_one`. Both sides false.
- `r > min n m`: the left side holds by `IsEchelonForm.rank_le_n` and
  `rank_le_m`. The right side is vacuous because `minors r A = []`. Both
  sides true.

The general proof below covers both cases without a case split. They are
listed so that an implementation that special-cases either one is seen to be
unnecessary, and so that the conformance suite tests them.

### Proof route

The proof is Mathlib-free and uses three existing results: the row-reduced
echelon certificate (`rowReduce_isRowReduced`, giving
`IsRowReduced A (Hex.Matrix.rowReduce A)`),
rectangular Cauchy-Binet (`det_mul_rectangular` and `det_minor_mul` in
`HexDeterminant/Gram.lean`) and the Laplace expansion
(`det_eq_foldl_laplace_col`). Mathlib's
`Mathlib/LinearAlgebra/Matrix/Echelon/Pivot.lean` proves the corresponding
step for a matrix already in echelon form (`IsPivotedBy.rank_eq` builds an
upper-triangular nonsingular `submatrix` of size equal to the rank), but
Mathlib has no theorem producing an echelon form of an arbitrary matrix, so
the executable certificate from `HexRowReduce` is the route that closes the
argument. Write `ρ := rowReduce_rank A`, `D := rowReduce A`, `T :=
D.transform`, `E := D.echelon`, `J := D.pivotCols`.

**Vanishing direction (`ρ < r` implies every `r × r` minor is zero).**
`rowReduce_rank_factorization` gives `C : Matrix K n ρ` and
`B : Matrix K ρ m` with `A = C * B`. For any `rows, cols` of length `r`,
`det_minor_mul` expands `det (selectedSubmatrix (C * B) rows cols)` as a sum
over `middle ∈ selectedColumnTuples r ρ`. Since `ρ < r`, that list is empty
(`selectedColumnTuples_eq_nil_of_lt`) and the sum is `0`.

**Nonzero-minor direction (`r ≤ ρ` implies some `r × r` minor is
nonzero).** First a nonzero `ρ × ρ` minor, then a descent to size `r`.

1. *The pivot columns of `A` are sent to a padded identity by `T`.*
   `pivotCols_sorted` says `J` is strictly increasing, so
   `J ∈ selectedColumnTuples ρ m`. Let `C := selectCols A J : Matrix K n ρ`.
   Column selection commutes with left multiplication
   (a new lemma `selectCols_mul : selectCols (P * X) cols = P * selectCols X cols`,
   the column analogue of `selectedSubmatrix_mul`), so `transform_mul`
   (`T * A = E`) gives `T * C = selectCols E J`. In the reduced echelon
   form, `selectCols E J = pad (identity ρ) n ρ`: rows at or below `ρ` are
   zero (`zero_row`), and within the first `ρ` rows the pivot entries are
   `1` (`pivot_one`) and the other entries of a pivot column are `0`
   (`above_pivot_zero`, `below_pivot_zero`). No inverse of `T` is used.
2. *The first `ρ` rows of `T` are a left inverse of `C`.* With
   `hρ : ρ ≤ n` from `rank_le_n`, `takeRows_mul` gives
   `takeRows T ρ hρ * C = takeRows (T * C) ρ hρ = takeRows (pad (identity ρ) n ρ) ρ hρ`,
   and the last matrix is `identity ρ` (a new lemma
   `takeRows_pad_identity`; the private `pad_identity_mul` in
   `HexRowReduce/Api.lean` is about a padded identity on the left and does
   not apply). Hence `det (takeRows T ρ hρ * C) = 1`.
3. *Cauchy-Binet produces a nonzero `ρ × ρ` minor of `A`.*
   `det_mul_rectangular` applied to `takeRows T ρ hρ : Matrix K ρ n` and
   `C : Matrix K n ρ` writes `1` as a `foldl` sum over
   `I ∈ selectedColumnTuples ρ n` of
   `det (columnTupleMatrix C.transpose (columnTupleVectorFn I)) * det (columnTupleMatrix (takeRows T ρ hρ) (columnTupleVectorFn I))`.
   Since `1 ≠ 0`, some summand is nonzero (a small lemma: a `foldl` of
   additions from `0` whose summands are all zero is zero), hence
   `det (columnTupleMatrix C.transpose (columnTupleVectorFn I)) ≠ 0` for
   some strictly increasing `I`. Entrywise, that matrix is the transpose of
   `selectedSubmatrix A I J` (its `(i, j)` entry is `C[I[j]][i] = A[I[j]][J[i]]`),
   so by `det_transpose` `det (selectedSubmatrix A I J) ≠ 0`, and this
   value is a member of `minors ρ A` by `mem_minors_iff`.
4. *Descent by one.* If `det (selectedSubmatrix A rows cols) ≠ 0` with
   `rows, cols` strictly increasing of length `k + 1`, then Laplace
   expansion along column `0` (`det_eq_foldl_laplace_col`) writes the
   determinant as a sum over `i` of `B[i][0] * cofactor B i 0`; some
   summand is nonzero, so `det (deleteRowCol B i 0) ≠ 0` (the cofactor is
   `±1` times that determinant). By `deleteRowCol_selectedSubmatrix` and
   `isStrictlyIncreasingColumnTuple_eraseIdx`, that is a nonzero `k × k`
   minor of `A` indexed by strictly increasing tuples.
5. *Iterate.* Induction on `ρ - r` starting from step 3 and applying
   step 4 gives a nonzero member of `minors r A` for every `r ≤ ρ`.

The contrapositive of the nonzero-minor direction is the right-to-left
implication of `rank_lt_iff_minors_eq_zero`.

An alternative for step 4 is the generalised Laplace expansion along `r`
rows, which would give the descent in one step. It is not in
`HexDeterminant` and is not needed, since the single-column expansion
iterated is enough.

## Invariance under multiplication

Proved in `Minors.lean` over a `Lean.Grind.CommRing R`:

```lean
theorem minor_mul_left_expand (P : Matrix R q n) (A : Matrix R n m)
    (rows : Vector (Fin q) r) (cols : Vector (Fin m) r) :
    det (selectedSubmatrix (P * A) rows cols) =
      (selectedColumnTuples r n).foldl (fun acc middle => acc +
        det (selectedSubmatrix A middle cols) * det (selectedSubmatrix P rows middle)) 0
theorem minor_mul_right_expand (A : Matrix R n m) (Q : Matrix R m q)
    (rows : Vector (Fin n) r) (cols : Vector (Fin q) r) :
    det (selectedSubmatrix (A * Q) rows cols) =
      (selectedColumnTuples r m).foldl (fun acc middle => acc +
        det (selectedSubmatrix Q middle cols) * det (selectedSubmatrix A rows middle)) 0
```

Both are `det_minor_mul` with the factors named. They say that every
`r × r` minor of `P * A` or `A * Q` is an `R`-linear combination of
`r × r` minors of `A`, which is the Mathlib-free content of
`I_r(P * A) ⊆ I_r(A)` and `I_r(A * Q) ⊆ I_r(A)`. Equality for invertible
`P` and `Q`, the descending chain `I_{r+1}(A) ⊆ I_r(A)` (each
`(r+1) × (r+1)` minor is a combination of `r × r` minors by Laplace
expansion), and the statement that `minors` and `detIdealGens` generate the
same ideal, all need `Ideal.span` and are theorems of the companion.

## Specialisation and rank loci

`MvPoly.lean` provides `specialize`, `rankAt` and `InLocus` as executable
operations. Their theorem is the main theorem read at a point:

```text
rankAt A p < r  ↔  InLocus r A p
```

This requires that `MvPoly.eval p` commutes with `det`, which is a ring
homomorphism property. `HexMvPoly` does not state `eval_add`/`eval_mul` in
the Mathlib-free layer, so the theorem `rankAt_lt_iff_inLocus` is proved in
the companion: `HexMvPolyMathlib.aeval p` is an `AlgHom` whose underlying
function is `MvPoly.eval p` (`HexMvPolyMathlib.aeval_eq_eval`), and
`RingHom.map_det` applies to its `toRingHom`. The Mathlib-free layer ships the definitions, the
`Decidable` instance, and the unfolding lemmas `specialize_getElem`,
`rankAt_eq` and `inLocus_iff`, so that a kernel evaluation of
`InLocus r A p` on closed inputs is available without Mathlib.

The consequences a consumer wants are all instances of the one theorem
with a particular `r`:

- the locus where the rank of `A` drops below `r` is the zero set of
  `I_r(A)`;
- "rank at most `r`" at a point is `InLocus (r + 1) A p`;
- "rank drops below the generic rank" is `InLocus g A p` where `g` is the
  rank of `A` over the fraction field of the coefficient ring. Computing
  `g` is the job of `hex-rank` (over a general domain) or
  `Hex.PolyMatrix.snfRank` in `hex-poly-smith` (over `F[x]`); this library
  takes `g` as an input.
  The companion proves that no specialisation has rank above `g`.

Nothing here asserts that the complement of the locus is nonempty. Over a
finite field every point may lie in the locus while the generic rank is
larger (the `hex-rank` SPEC, https://github.com/kim-em/hex-dev/issues/10153,
gives the example `[X^q - X]` over `𝔽_q[X]`), and the theorem is consistent with that: it is an equivalence
at each point, not an existence statement.

## What this library does not claim

**Not Fitting ideals.** For a finitely presented module `M` with
presentation matrix `A` (`n` generators, `m` relations), the Fitting ideals
`Fitt_j(M) = I_{n-j}(A)` are independent of the presentation. That
independence is a theorem about modules, not about matrices, and its proof
goes through comparing two presentations of the same module, not through
`I_r(P * A) = I_r(A)` for invertible `P`. This library proves only the
latter. The object here is called a *determinantal ideal* throughout, and
Fitting ideals are deferred to a later module-theoretic library. The
pinned Mathlib has no Fitting ideals either (see the next section), so
there is nothing to transport to.

**Not a Gröbner computation.** `I_r(A)` is presented by a generating list.
Membership, equality of ideals, radicals, minimal generators and dimension
of the zero set are out of scope; the planned `hex-groebner`
([SPEC/future-work.md §Gröbner bases](../../SPEC/future-work.md#gröbner-bases))
is the consumer that would decide them. In particular `detIdealGens` is
*a* generating list, not a reduced one.

**Not a rank algorithm.** Over a field the rank is `rowReduce_rank`. Over a
domain or a polynomial ring, rank with a certificate is `hex-rank`
(https://github.com/kim-em/hex-dev/issues/10153). This library's `rankAt` is row reduction over the
field after specialisation and exists to state the locus theorem
executably, not as a general rank entry point.

**No pruning.** `minors` enumerates every selection. Row-selection sharing
(computing the minors of a fixed row set for all column sets from one
elimination), the Bareiss-style recurrence between bordered minors, and
early exit when a unit minor is found are all possible later
optimisations. None is promised, and none changes the API or the theorems
because `minors` is the specification.

## Mathlib inventory

Checked against the pinned Mathlib, `v4.34.0-rc2` (Mathlib commit
`85e3a25e006c35636f0e53b0e9296caca2685bc0`, 2026-08-21):

- **Fitting ideals: absent.** No declaration named `FittingIdeal` or
  `fittingIdeal`, and no definition of the ideals generated by the minors
  of a presentation matrix. The occurrences of "Fitting" in
  `Mathlib/Algebra/Lie/` and `Mathlib/RingTheory/Artinian/Module.lean`
  are the Fitting lemma and Fitting decomposition, unrelated.
- **Rank versus minors: absent.** No lemma of the form "`r ≤ A.rank` iff
  some `r × r` minor is nonzero", nor its negation. The closest
  statements are:
  - `Matrix.IsPivotedBy.rank_eq`
    (`Mathlib/LinearAlgebra/Matrix/Echelon/Pivot.lean`): for a matrix
    already in echelon form with pivot map `l`, `A.rank = #{i | l i ≠ ⊤}`;
    its proof builds the `submatrix` on the pivot rows and columns, shows
    it is upper triangular with nonzero diagonal, and uses
    `rank_of_det_ne_zero` and `rank_submatrix_le`. That is the
    nonzero-minor direction for an echelon matrix, with no theorem
    producing an echelon form of an arbitrary matrix.
  - `Echelon.Decomposition.rank_eq`
    (`Mathlib/LinearAlgebra/Matrix/Echelon/Decomposition.lean`, in the
    top-level namespace `Echelon`, not `Matrix.Echelon`): rank from
    a certificate `L * A.submatrix σ id` pivoted, over `[CommRing R]
    [IsDomain R]`; this is the checker `norm_rank` uses, and the
    certificate is produced by meta code, not by a theorem.
  - `Matrix.rank_submatrix_le`, `Matrix.rank_of_det_ne_zero`
    (`Mathlib/LinearAlgebra/Matrix/Rank.lean`) and
    `Matrix.det_eq_zero_of_not_linearIndependent_cols`
    (`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`): the
    ingredients of both directions, without the assembly.
- **Present and used by the companion.** `Matrix.map`, `RingHom.map_det`
  (`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`),
  `Matrix.rank` (`Mathlib/LinearAlgebra/Matrix/Rank.lean`),
  `MvPolynomial.zeroLocus` (`Mathlib/RingTheory/Nullstellensatz.lean`),
  `Field.toGrindField` (`Mathlib/Algebra/Field/Basic.lean`, which lets
  `rowReduce` run over a Mathlib `Field`).

An implementer must re-run these searches when the Mathlib pin moves. If
Mathlib gains either absent item, the companion should state agreement with
it rather than a second copy.

## Complexity

`minors r A` computes `n.choose r * m.choose r` determinants, each by
`Hex.Matrix.det`, the Leibniz sum with `r!` terms of `r` factors. The ring
operation count is therefore

```text
Θ( n.choose r · m.choose r · r! · r )
```

and over `MvPoly` each ring operation is a polynomial product whose cost
depends on the supports. This is the specification cost and the shipped
cost, and no pruning is promised (see above). The function is intended for the
small symbolic matrices a tactic meets, typically `n, m ≤ 6`, where the
count is in the thousands. The conformance and benchmark sizes below are
chosen so that the cap in `SPEC/benchmarking.md` is met with this count.

A later per-minor determinant that is faster than Leibniz (Bareiss with an
exact quotient from `hex-mv-gcd`, or Berkowitz from `hex-char-poly`) must be
proved equal to `det` and plugged in behind the same `minors`; it would
change the library's dependency list and is not part of this SPEC.

## Conformance

Per [SPEC/testing.md](../../SPEC/testing.md). The Lean drivers are
`conformance/HexDeterminantalIdeal/Conformance.lean` and
`conformance/HexDeterminantalIdeal/EmitFixtures.lean`, the latter exposed as
`lean_exe hexdeterminantalideal_emit_fixtures`. The committed snapshot is
`conformance-fixtures/HexDeterminantalIdeal/detideal.jsonl` and the oracle
driver is `scripts/oracle/detideal_sympy.py`. Adding it extends the existing
single conformance job: append `HexDeterminantalIdeal.Conformance` to the
`HexConformance` globs in `lakefile.lean`, and append one tuple to `ORACLES`
in `scripts/ci/run_oracles.sh`:

```
"HexDeterminantalIdeal|hexdeterminantalideal_emit_fixtures|scripts/oracle/detideal_sympy.py|conformance-fixtures/HexDeterminantalIdeal/detideal.jsonl"
```

SymPy is already installed and preflighted for `hex-mv-poly`, so no install
or preflight line changes.

**Record format.** A record carries the arity and comparator name of the
entry ring, the matrix as a list of rows of polynomials, each polynomial in
the `(exponent vector, coefficient)` encoding of the `mvpoly` fixture kind,
the size `r`, and one of the operations below with its Lean `value`.
Matrices over `Int` are arity-`0` polynomial matrices, so one stream covers
both.

| `op` | Lean value | Oracle recomputation and comparison |
| --- | --- | --- |
| `minors` | the list `minors r A` in enumeration order | `itertools.combinations` of rows and of columns, each sorted by reversed tuple to reproduce the colexicographic order of `selectedColumnTuples`, `Matrix.extract(...).det()`, compared polynomial by polynomial after `expand`, in the same order |
| `detIdealGens` | `detIdealGens r A` | the nonzero distinct minors, compared as sets of expanded polynomials |
| `rankAt` | `rankAt A p` for a point `p` over `Rat` | `Matrix.subs(...).rank()` over `QQ` |
| `inLocus` | `decide (InLocus r A p)` | every minor evaluates to zero at `p` |

**Cases that must be present**, since these are what a plausible
implementation gets wrong:

- `r = 0` on every matrix shape, including `0 × 0`, `0 × m` and `n × 0`,
  checking `minors 0 A = [1]`;
- `r > min n m`, checking `minors r A = []`, for square and for both
  rectangular orientations;
- the zero matrix at `r = 1`, checking that `minors` is a list of zeros of
  the right length and `detIdealGens` is empty;
- a `2 × 4` matrix of eight distinct integers at `r = 2`, whose six minors
  are pairwise distinct, so that the colexicographic order of the column
  selections is checked against the oracle and a lexicographic enumeration
  fails;
- the generic `2 × 3` matrix of six indeterminates at `r = 2`, whose three
  minors are the classical generators, and its transpose, checking
  `minors_transpose` as a permutation;
- a matrix with repeated minors (two equal columns of indeterminates),
  checking that `detIdealGens` keeps one copy and that `minors` keeps both;
- the Vandermonde matrices `V_2` and `V_3` in indeterminates
  `x_1, ..., x_k`: at `r = k` the single minor is `∏_{i<j} (x_j - x_i)`,
  and `rankAt`/`inLocus` are checked at points with two equal coordinates
  (rank drop) and with distinct coordinates (full rank), and at `r = k - 1`
  at points where all coordinates coincide;
- the bordered identity `[[identity k, u], [vᵀ, t]]` of size `k + 1` with
  indeterminate `u`, `v`, `t`, for `k = 1, 2`: `minors k` contains `1`, so
  no point is in the locus at `r = k` and `rankAt ≥ k` everywhere, while
  `detIdealGens (k + 1)` is the single polynomial `t - v · u` up to sign,
  with points on and off the hypersurface `t = v · u`;
- a `3 × 3` matrix over `Rat` with integer entries and rank `2`, checking
  `rank_eq_iff_minors` by `decide +kernel` in `Conformance.lean`: some
  `2 × 2` minor is nonzero and the determinant is zero. `Int` is not a
  `Lean.Grind.Field`, so the rank theorem is exercised over `Rat` here and
  over `Int.castRingHom ℚ` in the companion's tests;
- invariance on one fixture: for an explicit unimodular integer `P`,
  `rankAt (P * A) p = rankAt A p` and `InLocus r (P * A) p ↔ InLocus r A p`
  at two points.

The companion adds build-only transport checks in
`HexDeterminantalIdealMathlib/Tests.lean`: the headline theorem applied to a
closed `Matrix (Fin 2) (Fin 3) ℤ` through `Int.castRingHom ℚ`, and the
locus corollary applied to `V_2` at one point on and one point off the
diagonal. These are not an independent oracle. The SymPy stream is.

## Benchmarking

Per [SPEC/benchmarking.md](../../SPEC/benchmarking.md), a driver at
`bench/HexDeterminantalIdeal/Bench.lean` with no Mathlib import.

**Input families.**

- `dense-int-minors`: `n = m ∈ {4, 5, 6}`, every `r` from `1` to `n`,
  small random integer entries. The purpose is the shape of the curve in
  `r`, which must follow `n.choose r ^ 2 · r!`.
- `symbolic-2var`: `4 × 4` matrices whose entries are random linear forms
  in two indeterminates over `Int`, `r ∈ {2, 3, 4}`, isolating the cost of
  polynomial arithmetic inside the same enumeration.

**Comparator.** SymPy, the same `combinations` and `det` loop the oracle
runs, `informational`: SymPy chooses its own per-minor determinant
algorithm (Bareiss or Berkowitz) and a ratio against a Leibniz sum compares
algorithms, not implementations.

**What the curve is for.** The operation count above is the model the
measurements are compared with, not an acceptance threshold. The
`dense-int-minors` family isolates the enumeration, since integer
operations at these sizes cost about the same at every `r`; the
`symbolic-2var` family adds polynomial arithmetic whose per-operation cost
grows with the supports, so its curve is expected to rise faster than the
count. A `dense-int-minors` curve that departs from the model by more than
the noise between adjacent arms is a result to explain by profiling
(per-minor allocation beyond the `r × r` submatrix, permutation-sign
computation, host activity recorded as context), per
[SPEC/benchmarking.md](../../SPEC/benchmarking.md); it is not by itself a bug
verdict.

## File organisation

```text
HexDeterminantalIdeal.lean              umbrella
HexDeterminantalIdeal/
  Choose.lean        length_selectedColumnTuples, the count of strictly increasing tuples
  Minors.lean        minors, detIdealGens, enumeration theorems, invariance expansions
  Rank.lean          rank_lt_iff_minors_eq_zero and its three corollaries
  MvPoly.lean        Matrix.map (if not yet in HexMatrix), specialize, rankAt, InLocus
  SPEC/hex-determinantal-ideal.md
  README.md
conformance/HexDeterminantalIdeal/{Conformance,EmitFixtures}.lean
conformance-fixtures/HexDeterminantalIdeal/detideal.jsonl
scripts/oracle/detideal_sympy.py
bench/HexDeterminantalIdeal/Bench.lean
```

## Kernel form

[SPEC/matrix-tactics.md](../../SPEC/matrix-tactics.md) §Kernel discipline
forbids evaluating `minors` or `detIdealGens` in the kernel on
`Hex.Matrix` values: the enumeration goes through `selectedColumnTuples`
on `Vector` and `Fin`, and `det` through `permutationVectors`. For the
`rank_locus` tactic the library therefore also ships, in
`HexDeterminantalIdeal/Kernel.lean`, a list form written for kernel
reduction, in the style of hex-rank's `RankWitness`:

- `indexTuples r n : List (List Nat)`, the strictly increasing `r`-tuples
  in `0 … n - 1` in the order of `selectedColumnTuples`, by structural
  recursion;
- `minorList rows cols L`, the determinant of the selected block of a row
  list `L : List (List α)` by Laplace expansion along the first row, by
  structural recursion on `rows`, over the list form of the entry
  arithmetic;
- `minorsList r L` and `detIdealGensList r L`, the enumeration and the
  zero-and-duplicate-free list, over `indexTuples`.

The entry arithmetic is abstract over the carrier's list form: for
`MvPoly` entries it is the list form of `MvPoly` arithmetic that
hex-mv-poly supplies (a prerequisite of the tactic, recorded in
[hex-generic-rank-mathlib](../../SPEC/Libraries/hex-generic-rank-mathlib.md#prerequisite-changes-in-other-libraries)),
and for integer entries it is `Int`. Every definition is `@[expose]`,
recurses structurally, and puts no `Array`, `Vector`, `Fin` or `Hex.Matrix`
on the kernel's path. The Mathlib-free theorems are the enumeration facts
(`indexTuples_eq_selectedColumnTuples` up to the index encoding,
`length_minorsList`) and `minorList_eq_det_laplace`, identifying the
list determinant with `det_eq_foldl_laplace_col` on the denoted block; the
identification `detIdealGensList r (rows A) = detIdealGens r A` on denoted
`MvPoly` values is the companion's, since it needs the denotation theorem.

Cost is `n.choose r * m.choose r` determinants of `r!` products each, the
same as the compiled enumeration; it is the price of a complete
certificate that a list is all the minors, and the tactic budgets it.

## Consumers

- The `rank_locus` tactic, specified in
  [hex-determinantal-ideal-mathlib §The `rank_locus` tactic](../../HexDeterminantalIdealMathlib/SPEC/hex-determinantal-ideal-mathlib.md#the-rank_locus-tactic):
  it reifies a Mathlib matrix with symbolic entries through hex-reflect
  into a `Matrix (MvPoly k C cmp) n m`, runs `detIdealGens r A` in
  compiled code, certifies the list through the kernel form above, and
  states "the rank is below `r` iff every generator vanishes" through the
  companion's `mem_zeroLocus_iff_rank_lt'`. Its default `r` is the generic
  rank, supplied by hex-generic-rank-mathlib's handler on its syntax kind.
- the matrix tactics ([SPEC/matrix-tactics.md](../../SPEC/matrix-tactics.md))
  may use `le_rank_iff_exists_minor_ne_zero` as the lower-bound half of a
  rank certificate. It is not required to.
- `hex-smith` and `hex-poly-smith` keep their `noncomputable`
  determinantal-divisor copies. Replacing them by an import of this
  library would add the whole package, and with it `hex-row-reduce` and
  `hex-mv-poly`, to their dependency closures for the sake of a
  specification function. Importing only `Minors.lean` avoids the Lean
  imports but not the package requirement, so the duplication stays until
  the enumeration is worth its own package.

## Open questions

- Whether `Matrix.map` belongs in `HexMatrix` (released) or here. The
  SPEC says `HexMatrix`, because `selectRows`/`selectCols` are there and an
  entrywise map is a basic operation. The released repo is regenerated from
  this monorepo, so the addition is an ordinary change.
- Whether to ship a `Bool`-valued `rankDropsBelow r A p` beside the
  `Decidable` instance on `InLocus`. The instance is enough for `decide
  +kernel` and for the fixtures; a named Boolean is only worth adding if
  the tactic wants it.
