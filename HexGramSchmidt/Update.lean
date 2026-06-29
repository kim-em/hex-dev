/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGramSchmidt.Int
public import HexRowReduce.RowEchelon

public section

/-!
Row-operation update formulas for `hex-gram-schmidt`.

This module packages the elementary row operations used by LLL and states the
resulting update formulas for the Gram-Schmidt basis, coefficient, scaled
coefficient, and Gram-determinant surfaces. The executable row operations live
in `HexMatrix`; this file supplies the `HexGramSchmidt`-level API that later
libraries use to reason about size reduction and adjacent swaps.
-/
namespace Hex

namespace GramSchmidt

/-- The row immediately preceding `k`. -/
@[expose]
def prevRow (k : Fin n) (hk : 0 < k.val) : Fin n := by
  refine ⟨k.val - 1, ?_⟩
  omega

end GramSchmidt

namespace GramSchmidt.Int

/-- Size-reduce row `k` against an earlier row `j` by replacing
`b[k]` with `b[k] - r * b[j]`. -/
@[expose]
def sizeReduce (b : Matrix Int n m) (j k : Fin n) (r : Int) : Matrix Int n m :=
  Matrix.rowAdd b j k (-r)

/-- Swap adjacent rows `k - 1` and `k`. -/
@[expose]
def adjacentSwap (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val) : Matrix Int n m :=
  Matrix.rowSwap b (GramSchmidt.prevRow k hk) k

/-- The old `d[k]` denominator used by exact adjacent-swap updates. -/
@[expose]
def adjacentSwapDenom (b : Matrix Int n m) (k : Fin n) : Int :=
  ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int)

/-- The old `B = nu[k][k-1]` pivot coefficient used by adjacent swaps. -/
@[expose]
def adjacentSwapPivotCoeff (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val) : Int :=
  let km1 := GramSchmidt.prevRow k hk
  GramSchmidt.entry (scaledCoeffs b) k km1

/-- Numerator of the adjacent-swap `d[k]'` update. -/
@[expose]
def adjacentSwapGramDetNumerator (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val) :
    Int :=
  let km1 := GramSchmidt.prevRow k hk
  let B := adjacentSwapPivotCoeff b k hk
  ((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
      ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) + B ^ 2

/-- The integer quotient used as `d[k]'` in the adjacent-swap update formulas. -/
@[expose]
def adjacentSwapGramDetQuotient (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val) :
    Int :=
  adjacentSwapGramDetNumerator b k hk / adjacentSwapDenom b k

/-- Numerator of the adjacent-swap `nu[i][k-1]'` update for rows above `k`. -/
@[expose]
def adjacentSwapScaledCoeffAbovePrevNumerator (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (i : Fin n) : Int :=
  let km1 := GramSchmidt.prevRow k hk
  let B := adjacentSwapPivotCoeff b k hk
  ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) *
      GramSchmidt.entry (scaledCoeffs b) i k +
    B * GramSchmidt.entry (scaledCoeffs b) i km1

/-- Numerator of the adjacent-swap `nu[i][k]'` update for rows above `k`. -/
@[expose]
def adjacentSwapScaledCoeffAboveCurrNumerator (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (i : Fin n) : Int :=
  let km1 := GramSchmidt.prevRow k hk
  let B := adjacentSwapPivotCoeff b k hk
  ((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
      GramSchmidt.entry (scaledCoeffs b) i km1 -
    B * GramSchmidt.entry (scaledCoeffs b) i k

/-- Size-reducing row `k` against an earlier row `j` leaves the entire
Gram-Schmidt basis unchanged. Subtracting an integer multiple of an earlier
row from a later one is a unimodular operation that preserves the orthogonal
profile, so LLL can size-reduce freely without disturbing the orthogonalised
vectors, their norms, or the Gram determinants the swap step depends on. -/
theorem basis_sizeReduce (b : Matrix Int n m) (j k : Fin n) (hjk : j.val < k.val)
    (r : Int) :
    basis (sizeReduce b j k r) = basis b := by
  simpa [sizeReduce] using basis_rowAdd (b := b) (src := j) (dst := k) (c := -r) hjk

/-- The defining effect of size reduction on the pivot coefficient: the `(k, j)`
Gram-Schmidt coefficient drops by exactly `r`. Choosing `r` to be the nearest
integer to `μ[k][j]` is precisely how LLL brings `|μ[k][j]| ≤ 1/2`, so this is
the identity that certifies the size-reduction step achieves its bound. The
nondegeneracy hypothesis `hnorm` records that row `j` of the basis is nonzero,
so its coefficient is well defined. -/
theorem coeffs_sizeReduce_pivot (b : Matrix Int n m) (j k : Fin n) (hjk : j.val < k.val)
    (r : Int)
    (hnorm : ((basis b).row j).dotProduct ((basis b).row j) ≠ 0) :
    GramSchmidt.entry (coeffs (sizeReduce b j k r)) k j =
      GramSchmidt.entry (coeffs b) k j - (r : Rat) := by
  rw [sizeReduce, coeffs_rowAdd_pivot (b := b) (src := j) (dst := k) hjk (c := -r) hnorm]
  grind

/-- How size reduction propagates to coefficients below the pivot: for a column
`l` earlier than `j`, the `(k, l)` coefficient decreases by `r * μ[j][l]`. A
caller tracking the full coefficient row of `k` after a size reduction needs
this to predict the side effect on already-reduced lower columns (and to see
why size reduction is performed from the largest index downward). -/
theorem coeffs_sizeReduce_lower (b : Matrix Int n m) (l j k : Fin n)
    (hlj : l.val < j.val) (hjk : j.val < k.val) (r : Int) :
    GramSchmidt.entry (coeffs (sizeReduce b j k r)) k l =
      GramSchmidt.entry (coeffs b) k l -
        (r : Rat) * GramSchmidt.entry (coeffs b) j l := by
  rw [sizeReduce, coeffs_rowAdd_lower (b := b) (col := l) (src := j) (dst := k) hlj hjk (c := -r)]
  grind

/-- Size reduction is local to the row being reduced: every coefficient row
other than `k` is left untouched. This is the locality guarantee LLL relies on
to argue that reducing row `k` cannot invalidate the size-reduced or
Lovász-ordered state of any other row. -/
theorem coeffs_sizeReduce_other_row (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (r : Int) (i : Fin n) (hik : i ≠ k) :
    (coeffs (sizeReduce b j k r)).row i = (coeffs b).row i := by
  simpa [sizeReduce] using
    coeffs_rowAdd_other_row (b := b) (src := j) (dst := k) (c := -r) hjk i hik

/-- Size-reducing row `k` against `j` does not touch coefficients at columns
strictly between `j` and `k`: for `j < l < k` the `(k, l)` coefficient is
unchanged. Together with `coeffs_sizeReduce_lower` and
`coeffs_sizeReduce_pivot`, this pins down exactly which coefficients move, which
is what lets LLL reduce columns one at a time without re-disturbing the columns
above the current pivot. -/
theorem coeffs_sizeReduce_above_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (r : Int) (l : Fin n)
    (hjl : j.val < l.val) (hlk : l.val < k.val) :
    GramSchmidt.entry (coeffs (sizeReduce b j k r)) k l =
      GramSchmidt.entry (coeffs b) k l := by
  have _ : j.val < k.val := hjk
  simpa [sizeReduce] using
    coeffs_rowAdd_above_pivot (b := b) (src := j) (col := l) (dst := k) hjl hlk
      (c := -r)

/-- An adjacent swap at `k` leaves the Gram-Schmidt basis vector of every row
strictly before the swapped pair unchanged (`i + 1 < k`, i.e. `i < k - 1`).
Only the orthogonalisation of the two swapped rows and the rows above them can
change, so a caller need only recompute the basis from index `k - 1` onward
after a Lovász swap. -/
theorem basis_adjacentSwap_of_lt (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (i : Fin n) (hi : i.val + 1 < k.val) :
    (basis (adjacentSwap b k hk)).row i = (basis b).row i := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1k : km1.val < k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hikm1 : i.val < km1.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  simpa [adjacentSwap, km1] using
    GramSchmidt.Int.basis_rowSwap_of_before
      (b := b) (km1 := km1) (k := k) (i := i) hkm1k hikm1

/-- An adjacent swap at `k` leaves the Gram-Schmidt basis vector of every row
strictly after the swapped pair unchanged. The span of the first `k + 1` rows is
invariant under swapping rows `k - 1` and `k`, so the orthogonalisation of any
later row, which projects against that span, is unaffected; only rows `k - 1`
and `k` move. -/
theorem basis_adjacentSwap_of_gt (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (i : Fin n) (hi : k.val < i.val) :
    (basis (adjacentSwap b k hk)).row i = (basis b).row i := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  simpa [adjacentSwap, km1] using
    GramSchmidt.Int.basis_rowSwap_of_after
      (b := b) (km1 := km1) (k := k) (i := i) hkm1 hi

/-- The new Gram-Schmidt vector at row `k - 1` after an adjacent swap: it is the
old projection `b_k + μ[k][k-1] • b_{k-1}` of the swapped-in row against the rows
below it. This is the orthogonal component that becomes the new shorter pivot,
and whose norm LLL compares to the old one to decide whether the Lovász
condition was violated. -/
theorem basis_adjacentSwap_prev (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    (basis (adjacentSwap b k hk)).row km1 =
      (basis b).row k +
        GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1 := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  simpa [adjacentSwap, km1] using
    GramSchmidt.Int.basis_rowSwap_adjacent_prev (b := b) (km1 := km1) (k := k) hkm1

/-- The new Gram-Schmidt vector at row `k` after an adjacent swap, given as an
explicit linear combination of the old vectors `b_{k-1}` (`prev`) and `b_k`
(`curr`). After the swap, row `k` carries the residual of the old `prev` against
the new pivot `swappedPrev`; this closed form is what lets a caller recompute the
updated orthogonal vector and its norm without rerunning Gram-Schmidt. The
hypothesis `hdenom` records that the new pivot is nonzero, so the dividing inner
products are well defined. -/
theorem basis_adjacentSwap_curr (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (hdenom :
      let km1 := GramSchmidt.prevRow k hk
      let swappedPrev :=
        (basis b).row k + GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1
      swappedPrev.dotProduct swappedPrev ≠ 0) :
    let km1 := GramSchmidt.prevRow k hk
    let μ := GramSchmidt.entry (coeffs b) k km1
    let prev := (basis b).row km1
    let curr := (basis b).row k
    let swappedPrev := curr + μ • prev
    (basis (adjacentSwap b k hk)).row k =
      (curr.dotProduct curr / swappedPrev.dotProduct swappedPrev) • prev -
        (μ * prev.dotProduct prev / swappedPrev.dotProduct swappedPrev) • curr := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  simpa [adjacentSwap, km1] using
    GramSchmidt.Int.basis_rowSwap_adjacent_curr
      (b := b) (km1 := km1) (k := k) hkm1 hdenom

/-- Effect of an adjacent swap on the lower coefficients of the new row `k - 1`:
for a column `j` below the swapped pair (`j + 1 < k`), the new `(k-1, j)`
coefficient equals the old `(k, j)` coefficient. Because the swap moves the old
row `k` into position `k - 1`, its coefficients against the unchanged lower rows
come along unchanged: the bookkeeping a caller needs to update the `μ` table in
place rather than recomputing it. -/
theorem coeffs_adjacentSwap_lower_prev (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (j : Fin n) (hj : j.val + 1 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (coeffs (adjacentSwap b k hk)) km1 j =
      GramSchmidt.entry (coeffs b) k j := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hjkm1 : j.val < km1.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  simpa [adjacentSwap, km1] using
    GramSchmidt.Int.coeffs_rowSwap_adjacent_lower_prev
      (b := b) (km1 := km1) (k := k) (j := j) hkm1 hjkm1

/-- Companion to `coeffs_adjacentSwap_lower_prev` for the other swapped row: for
a column `j` below the swapped pair (`j + 1 < k`), the new `(k, j)` coefficient
equals the old `(k-1, j)` coefficient. The two rows exchange their lower
coefficient vectors wholesale, so a caller can swap the corresponding `μ`-rows in
the columns below `k - 1` instead of recomputing them. -/
theorem coeffs_adjacentSwap_lower_curr (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (j : Fin n) (hj : j.val + 1 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (coeffs (adjacentSwap b k hk)) k j =
      GramSchmidt.entry (coeffs b) km1 j := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hjkm1 : j.val < km1.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  simpa [adjacentSwap, km1] using
    GramSchmidt.Int.coeffs_rowSwap_adjacent_lower_curr
      (b := b) (km1 := km1) (k := k) (j := j) hkm1 hjkm1

/-- The updated pivot coefficient after an adjacent swap: the new `μ[k][k-1]`
equals `μ * ⟨prev, prev⟩ / ⟨swappedPrev, swappedPrev⟩`, where `μ` is the old
pivot coefficient and `swappedPrev` the new shorter pivot. This is the `μ'`
entry of the standard LLL swap update; a caller uses it to refresh the pivot
coefficient in place. The hypothesis `hdenom` records that the new pivot is
nonzero, so the quotient is well defined. -/
theorem coeffs_adjacentSwap_pivot (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (hdenom :
      let km1 := GramSchmidt.prevRow k hk
      let swappedPrev :=
        (basis b).row k + GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1
      swappedPrev.dotProduct swappedPrev ≠ 0) :
    let km1 := GramSchmidt.prevRow k hk
    let μ := GramSchmidt.entry (coeffs b) k km1
    let prev := (basis b).row km1
    let curr := (basis b).row k
    let swappedPrev := curr + μ • prev
    GramSchmidt.entry (coeffs (adjacentSwap b k hk)) k km1 =
      μ * prev.dotProduct prev / swappedPrev.dotProduct swappedPrev := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  simpa [adjacentSwap, km1] using
    GramSchmidt.Int.coeffs_rowSwap_adjacent_pivot
      (b := b) (km1 := km1) (k := k) hkm1 hdenom


/-! The four `adjacentSwap` scaled-coefficient identities for rows above the
pivot (`scaledCoeffs_adjacentSwap_above_prev`, `_above_curr`, and the two
`_dvd` companions) live in `HexGramSchmidtMathlib/Update.lean`. Their proof
path goes through `bareiss_scaledCoeffMatrix_rowSwap_above_prev` /
`_above_curr` (the bordered-minor identities), which cross the Bareiss / det
correspondence and so cannot be proved in the Mathlib-free core per
[SPEC/Libraries/hex-gram-schmidt.md "Proof path governs placement, not just
statement"]. -/

end GramSchmidt.Int

end Hex
