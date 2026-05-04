import HexGramSchmidt.Int
import HexMatrix.RowEchelon

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
def prevRow (k : Fin n) (hk : 0 < k.val) : Fin n := by
  refine ⟨k.val - 1, ?_⟩
  omega

end GramSchmidt

namespace GramSchmidt.Int

/-- Size-reduce row `k` against an earlier row `j` by replacing
`b[k]` with `b[k] - r * b[j]`. -/
def sizeReduce (b : Matrix Int n m) (j k : Fin n) (r : Int) : Matrix Int n m :=
  Matrix.rowAdd b j k (-r)

/-- Swap adjacent rows `k - 1` and `k`. -/
def adjacentSwap (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val) : Matrix Int n m :=
  Matrix.rowSwap b (GramSchmidt.prevRow k hk) k

/-- The old `d[k]` denominator used by exact adjacent-swap updates. -/
def adjacentSwapDenom (b : Matrix Int n m) (k : Fin n) : Int :=
  ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int)

/-- The old `B = nu[k][k-1]` pivot coefficient used by adjacent swaps. -/
def adjacentSwapPivotCoeff (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val) : Int :=
  let km1 := GramSchmidt.prevRow k hk
  GramSchmidt.entry (scaledCoeffs b) k km1

/-- Numerator of the adjacent-swap `d[k]'` update. -/
def adjacentSwapGramDetNumerator (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val) :
    Int :=
  let km1 := GramSchmidt.prevRow k hk
  let B := adjacentSwapPivotCoeff b k hk
  ((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
      ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) + B ^ 2

/-- The integer quotient used as `d[k]'` in the adjacent-swap update formulas. -/
def adjacentSwapGramDetQuotient (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val) :
    Int :=
  adjacentSwapGramDetNumerator b k hk / adjacentSwapDenom b k

/-- Numerator of the adjacent-swap `nu[i][k-1]'` update for rows above `k`. -/
def adjacentSwapScaledCoeffAbovePrevNumerator (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (i : Fin n) : Int :=
  let km1 := GramSchmidt.prevRow k hk
  let B := adjacentSwapPivotCoeff b k hk
  ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) *
      GramSchmidt.entry (scaledCoeffs b) i k +
    B * GramSchmidt.entry (scaledCoeffs b) i km1

/-- Numerator of the adjacent-swap `nu[i][k]'` update for rows above `k`. -/
def adjacentSwapScaledCoeffAboveCurrNumerator (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (i : Fin n) : Int :=
  let km1 := GramSchmidt.prevRow k hk
  let B := adjacentSwapPivotCoeff b k hk
  ((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
      GramSchmidt.entry (scaledCoeffs b) i km1 -
    B * GramSchmidt.entry (scaledCoeffs b) i k

theorem basis_sizeReduce (b : Matrix Int n m) (j k : Fin n) (hjk : j.val < k.val)
    (r : Int) :
    basis (sizeReduce b j k r) = basis b := by
  sorry

theorem coeffs_sizeReduce_pivot (b : Matrix Int n m) (j k : Fin n) (hjk : j.val < k.val)
    (r : Int)
    (hnorm : Matrix.dot ((basis b).row j) ((basis b).row j) ≠ 0) :
    GramSchmidt.entry (coeffs (sizeReduce b j k r)) k j =
      GramSchmidt.entry (coeffs b) k j - (r : Rat) := by
  sorry

theorem coeffs_sizeReduce_lower (b : Matrix Int n m) (l j k : Fin n)
    (hlj : l.val < j.val) (hjk : j.val < k.val) (r : Int) :
    GramSchmidt.entry (coeffs (sizeReduce b j k r)) k l =
      GramSchmidt.entry (coeffs b) k l -
        (r : Rat) * GramSchmidt.entry (coeffs b) j l := by
  sorry

theorem gramDet_sizeReduce (b : Matrix Int n m) (j k : Fin n) (hjk : j.val < k.val)
    (r : Int) (t : Nat) (ht : t ≤ n) :
    gramDet (sizeReduce b j k r) t ht = gramDet b t ht := by
  sorry

theorem scaledCoeffs_sizeReduce_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (r : Int) :
    GramSchmidt.entry (scaledCoeffs (sizeReduce b j k r)) k j =
      GramSchmidt.entry (scaledCoeffs b) k j -
        r * Int.ofNat (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
  sorry

theorem scaledCoeffs_sizeReduce_lower (b : Matrix Int n m) (l j k : Fin n)
    (hlj : l.val < j.val) (hjk : j.val < k.val) (r : Int) :
    GramSchmidt.entry (scaledCoeffs (sizeReduce b j k r)) k l =
      GramSchmidt.entry (scaledCoeffs b) k l -
        r * GramSchmidt.entry (scaledCoeffs b) j l := by
  sorry

theorem basis_adjacentSwap_of_lt (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (i : Fin n) (hi : i.val + 1 < k.val) :
    (basis (adjacentSwap b k hk)).row i = (basis b).row i := by
  sorry

theorem basis_adjacentSwap_of_gt (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (i : Fin n) (hi : k.val < i.val) :
    (basis (adjacentSwap b k hk)).row i = (basis b).row i := by
  sorry

theorem basis_adjacentSwap_prev (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    (basis (adjacentSwap b k hk)).row km1 =
      (basis b).row k +
        GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1 := by
  sorry

theorem basis_adjacentSwap_curr (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (hdenom :
      let km1 := GramSchmidt.prevRow k hk
      let swappedPrev :=
        (basis b).row k + GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1
      Matrix.dot swappedPrev swappedPrev ≠ 0) :
    let km1 := GramSchmidt.prevRow k hk
    let μ := GramSchmidt.entry (coeffs b) k km1
    let prev := (basis b).row km1
    let curr := (basis b).row k
    let swappedPrev := curr + μ • prev
    (basis (adjacentSwap b k hk)).row k =
      (Matrix.dot curr curr / Matrix.dot swappedPrev swappedPrev) • prev -
        (μ * Matrix.dot prev prev / Matrix.dot swappedPrev swappedPrev) • curr := by
  sorry

theorem coeffs_adjacentSwap_lower_prev (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (j : Fin n) (hj : j.val + 1 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (coeffs (adjacentSwap b k hk)) km1 j =
      GramSchmidt.entry (coeffs b) k j := by
  sorry

theorem coeffs_adjacentSwap_lower_curr (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (j : Fin n) (hj : j.val + 1 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (coeffs (adjacentSwap b k hk)) k j =
      GramSchmidt.entry (coeffs b) km1 j := by
  sorry

theorem coeffs_adjacentSwap_pivot (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (hdenom :
      let km1 := GramSchmidt.prevRow k hk
      let swappedPrev :=
        (basis b).row k + GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1
      Matrix.dot swappedPrev swappedPrev ≠ 0) :
    let km1 := GramSchmidt.prevRow k hk
    let μ := GramSchmidt.entry (coeffs b) k km1
    let prev := (basis b).row km1
    let curr := (basis b).row k
    let swappedPrev := curr + μ • prev
    GramSchmidt.entry (coeffs (adjacentSwap b k hk)) k km1 =
      μ * Matrix.dot prev prev / Matrix.dot swappedPrev swappedPrev := by
  sorry

theorem gramDet_adjacentSwap_of_ne (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (t : Nat) (ht : t ≤ n) (htk : t ≠ k.val) :
    gramDet (adjacentSwap b k hk) t ht = gramDet b t ht := by
  sorry

theorem gramDet_adjacentSwap_pivot (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    let km1 := GramSchmidt.prevRow k hk
    let B : Int := GramSchmidt.entry (scaledCoeffs b) k km1
    ((gramDet (adjacentSwap b k hk) k.val (Nat.le_of_lt k.isLt) : Nat) : Int) =
      (((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
          ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) + B ^ 2) /
        ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) := by
  sorry

theorem adjacentSwap_gramDetNumerator_dvd (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val)
    (hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    adjacentSwapDenom b k ∣ adjacentSwapGramDetNumerator b k hk := by
  sorry

theorem scaledCoeffs_adjacentSwap_lower_prev (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (j : Fin n) (hj : j.val + 1 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) km1 j =
      GramSchmidt.entry (scaledCoeffs b) k j := by
  sorry

theorem scaledCoeffs_adjacentSwap_lower_curr (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (j : Fin n) (hj : j.val + 1 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) k j =
      GramSchmidt.entry (scaledCoeffs b) km1 j := by
  sorry

theorem scaledCoeffs_adjacentSwap_pivot (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) k km1 =
      GramSchmidt.entry (scaledCoeffs b) k km1 := by
  sorry

theorem scaledCoeffs_adjacentSwap_above_prev (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (i : Fin n) (hik : k.val < i.val)
    (hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    let km1 := GramSchmidt.prevRow k hk
    let B : Int := GramSchmidt.entry (scaledCoeffs b) k km1
    let dk' : Int :=
      (((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
          ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) + B ^ 2) /
        ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int)
    ((GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) i km1 : Int) : Int) =
      (GramSchmidt.entry (scaledCoeffs b) i km1 * dk' +
          GramSchmidt.entry (scaledCoeffs b) i k * B) /
        ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) := by
  sorry

theorem adjacentSwap_scaledCoeffAbovePrevNumerator_dvd (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (i : Fin n) (hik : k.val < i.val)
    (hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    adjacentSwapDenom b k ∣ adjacentSwapScaledCoeffAbovePrevNumerator b k hk i := by
  sorry

theorem scaledCoeffs_adjacentSwap_above_curr (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (i : Fin n) (hik : k.val < i.val)
    (hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    let km1 := GramSchmidt.prevRow k hk
    let B : Int := GramSchmidt.entry (scaledCoeffs b) k km1
    ((GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) i k : Int) : Int) =
      (GramSchmidt.entry (scaledCoeffs b) i k *
          ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) -
        GramSchmidt.entry (scaledCoeffs b) i km1 * B) /
      ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) := by
  sorry

theorem adjacentSwap_scaledCoeffAboveCurrNumerator_dvd (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (i : Fin n) (hik : k.val < i.val)
    (hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    adjacentSwapDenom b k ∣ adjacentSwapScaledCoeffAboveCurrNumerator b k hk i := by
  sorry

end GramSchmidt.Int

end Hex
