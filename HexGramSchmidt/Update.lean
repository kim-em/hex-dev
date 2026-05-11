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
  simpa [sizeReduce] using basis_rowAdd (b := b) (src := j) (dst := k) (c := -r) hjk

theorem coeffs_sizeReduce_pivot (b : Matrix Int n m) (j k : Fin n) (hjk : j.val < k.val)
    (r : Int)
    (hnorm : Matrix.dot ((basis b).row j) ((basis b).row j) ≠ 0) :
    GramSchmidt.entry (coeffs (sizeReduce b j k r)) k j =
      GramSchmidt.entry (coeffs b) k j - (r : Rat) := by
  rw [sizeReduce]
  rw [coeffs_rowAdd_pivot (b := b) (src := j) (dst := k) hjk (c := -r) hnorm]
  grind

theorem coeffs_sizeReduce_lower (b : Matrix Int n m) (l j k : Fin n)
    (hlj : l.val < j.val) (hjk : j.val < k.val) (r : Int) :
    GramSchmidt.entry (coeffs (sizeReduce b j k r)) k l =
      GramSchmidt.entry (coeffs b) k l -
        (r : Rat) * GramSchmidt.entry (coeffs b) j l := by
  rw [sizeReduce]
  rw [coeffs_rowAdd_lower (b := b) (col := l) (src := j) (dst := k) hlj hjk (c := -r)]
  grind

theorem coeffs_sizeReduce_other_row (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (r : Int) (i : Fin n) (hik : i ≠ k) :
    (coeffs (sizeReduce b j k r)).row i = (coeffs b).row i := by
  simpa [sizeReduce] using
    coeffs_rowAdd_other_row (b := b) (src := j) (dst := k) (c := -r) hjk i hik

theorem coeffs_sizeReduce_above_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (r : Int) (l : Fin n)
    (hjl : j.val < l.val) (hlk : l.val < k.val) :
    GramSchmidt.entry (coeffs (sizeReduce b j k r)) k l =
      GramSchmidt.entry (coeffs b) k l := by
  have _ : j.val < k.val := hjk
  simpa [sizeReduce] using
    coeffs_rowAdd_above_pivot (b := b) (src := j) (col := l) (dst := k) hjl hlk
      (c := -r)

theorem gramDet_sizeReduce (b : Matrix Int n m) (j k : Fin n) (hjk : j.val < k.val)
    (r : Int) (t : Nat) (ht : t ≤ n) :
    gramDet (sizeReduce b j k r) t ht = gramDet b t ht := by
  unfold sizeReduce
  exact gramDet_rowAdd_earlier b j k (-r) t ht hjk

private theorem scaledCoeffs_eq_fin (b : Matrix Int n m) (i j : Fin n)
    (hji : j.val < i.val) :
    ((GramSchmidt.entry (scaledCoeffs b) i j : Int) : Rat) =
      (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt) : Rat) *
        GramSchmidt.entry (coeffs b) i j := by
  simpa using scaledCoeffs_eq (b := b) i.val j.val i.isLt hji

private theorem intCast_rat_injective {a b : Int} (h : (a : Rat) = (b : Rat)) :
    a = b := by
  have hz : ((a - b : Int) : Rat) = 0 := by
    simp [h]
    grind
  have hsub : a - b = 0 := Rat.intCast_eq_zero_iff.mp hz
  omega

theorem scaledCoeffs_sizeReduce_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (r : Int) :
    GramSchmidt.entry (scaledCoeffs (sizeReduce b j k r)) k j =
      GramSchmidt.entry (scaledCoeffs b) k j -
        r * Int.ofNat (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
  have hnew := scaledCoeffs_eq_scaledCoeffMatrix_det
    (b := sizeReduce b j k r) (i := k) (j := j) hjk
  have hold := scaledCoeffs_eq_scaledCoeffMatrix_det (b := b) (i := k) (j := j) hjk
  have hbridge := scaledCoeffMatrix_rowAdd_pivot_det (b := b) (j := j) (k := k) hjk (-r)
  have hlead := leadingGramMatrixInt_det_eq_gramDet_int
    (b := b) (t := j.val + 1) (ht := Nat.succ_le_of_lt j.isLt)
  calc
    GramSchmidt.entry (scaledCoeffs (sizeReduce b j k r)) k j =
        Matrix.det (GramSchmidt.scaledCoeffMatrix (sizeReduce b j k r) k j hjk) := hnew
    _ =
        Matrix.det (GramSchmidt.scaledCoeffMatrix b k j hjk) +
          (-r) * Matrix.det
            (GramSchmidt.leadingGramMatrixInt b (j.val + 1)
              (Nat.succ_le_of_lt j.isLt)) := by
      simpa [sizeReduce] using hbridge
    _ =
        GramSchmidt.entry (scaledCoeffs b) k j +
          (-r) * Int.ofNat (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
      rw [← hold, hlead]
    _ =
        GramSchmidt.entry (scaledCoeffs b) k j -
          r * Int.ofNat (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
      rw [Int.neg_mul, Lean.Grind.Ring.sub_eq_add_neg]

theorem scaledCoeffs_sizeReduce_lower (b : Matrix Int n m) (l j k : Fin n)
    (hlj : l.val < j.val) (hjk : j.val < k.val) (r : Int) :
    GramSchmidt.entry (scaledCoeffs (sizeReduce b j k r)) k l =
      GramSchmidt.entry (scaledCoeffs b) k l -
        r * GramSchmidt.entry (scaledCoeffs b) j l := by
  apply intCast_rat_injective
  have hnew := scaledCoeffs_eq_fin (b := sizeReduce b j k r) k l
      (Nat.lt_trans hlj hjk)
  have holdk := scaledCoeffs_eq_fin (b := b) k l (Nat.lt_trans hlj hjk)
  have holdj := scaledCoeffs_eq_fin (b := b) j l hlj
  have hdet :
      gramDet (sizeReduce b j k r) (l.val + 1) (Nat.succ_le_of_lt l.isLt) =
        gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) :=
    gramDet_sizeReduce (b := b) (j := j) (k := k) hjk r (l.val + 1)
      (Nat.succ_le_of_lt l.isLt)
  have hcoeff := coeffs_sizeReduce_lower (b := b) (l := l) (j := j) (k := k) hlj hjk r
  calc
    ((GramSchmidt.entry (scaledCoeffs (sizeReduce b j k r)) k l : Int) : Rat)
        =
          (gramDet (sizeReduce b j k r) (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
            GramSchmidt.entry (coeffs (sizeReduce b j k r)) k l := hnew
    _ =
          (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
            (GramSchmidt.entry (coeffs b) k l -
              (r : Rat) * GramSchmidt.entry (coeffs b) j l) := by
          rw [hdet, hcoeff]
    _ =
          ((GramSchmidt.entry (scaledCoeffs b) k l -
            r * GramSchmidt.entry (scaledCoeffs b) j l : Int) : Rat) := by
          calc
            (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
                (GramSchmidt.entry (coeffs b) k l -
                  (r : Rat) * GramSchmidt.entry (coeffs b) j l)
                =
                  (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
                    GramSchmidt.entry (coeffs b) k l -
                    (r : Rat) *
                      ((gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
                        GramSchmidt.entry (coeffs b) j l) := by
                  grind
            _ =
                  ((GramSchmidt.entry (scaledCoeffs b) k l : Int) : Rat) -
                    (r : Rat) * ((GramSchmidt.entry (scaledCoeffs b) j l : Int) : Rat) := by
                  rw [← holdk, ← holdj]
            _ =
                  ((GramSchmidt.entry (scaledCoeffs b) k l -
                    r * GramSchmidt.entry (scaledCoeffs b) j l : Int) : Rat) := by
                  grind

theorem scaledCoeffs_sizeReduce_other_row (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (r : Int) (i : Fin n) (hik : i ≠ k) :
    (scaledCoeffs (sizeReduce b j k r)).row i = (scaledCoeffs b).row i := by
  apply Vector.ext
  intro col hcol
  let l : Fin n := ⟨col, hcol⟩
  change GramSchmidt.entry (scaledCoeffs (sizeReduce b j k r)) i l =
    GramSchmidt.entry (scaledCoeffs b) i l
  by_cases hli : l.val < i.val
  · apply intCast_rat_injective
    have hnew := scaledCoeffs_eq_fin (b := sizeReduce b j k r) i l hli
    have hold := scaledCoeffs_eq_fin (b := b) i l hli
    have hdet :
        gramDet (sizeReduce b j k r) (l.val + 1) (Nat.succ_le_of_lt l.isLt) =
          gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) :=
      gramDet_sizeReduce (b := b) (j := j) (k := k) hjk r (l.val + 1)
        (Nat.succ_le_of_lt l.isLt)
    have hrow := coeffs_sizeReduce_other_row (b := b) (j := j) (k := k) hjk r i hik
    have hcoeff :
        GramSchmidt.entry (coeffs (sizeReduce b j k r)) i l =
          GramSchmidt.entry (coeffs b) i l := by
      have hget := congrArg (fun row => row[l]) hrow
      simpa [GramSchmidt.entry] using hget
    calc
      ((GramSchmidt.entry (scaledCoeffs (sizeReduce b j k r)) i l : Int) : Rat)
          =
            (gramDet (sizeReduce b j k r) (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
              GramSchmidt.entry (coeffs (sizeReduce b j k r)) i l := hnew
      _ =
            (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
              GramSchmidt.entry (coeffs b) i l := by
            rw [hdet, hcoeff]
      _ = ((GramSchmidt.entry (scaledCoeffs b) i l : Int) : Rat) := hold.symm
  · by_cases hil : i = l
    · subst l
      rw [← hil]
      rw [scaledCoeffs_diag, scaledCoeffs_diag]
      exact congrArg Int.ofNat
        (gramDet_sizeReduce (b := b) (j := j) (k := k) hjk r (i.val + 1)
          (Nat.succ_le_of_lt i.isLt))
    · have hilv : i.val < l.val := by
        have hle : i.val ≤ l.val := Nat.le_of_not_lt hli
        exact Nat.lt_of_le_of_ne hle (fun h => hil (Fin.ext h))
      rw [scaledCoeffs_upper (sizeReduce b j k r) i.val l.val i.isLt l.isLt hilv,
        scaledCoeffs_upper b i.val l.val i.isLt l.isLt hilv]

theorem scaledCoeffs_sizeReduce_above_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (r : Int) (l : Fin n)
    (hjl : j.val < l.val) (hlk : l.val < k.val) :
    GramSchmidt.entry (scaledCoeffs (sizeReduce b j k r)) k l =
      GramSchmidt.entry (scaledCoeffs b) k l := by
  apply intCast_rat_injective
  have hnew := scaledCoeffs_eq_fin (b := sizeReduce b j k r) k l hlk
  have hold := scaledCoeffs_eq_fin (b := b) k l hlk
  have hdet :
      gramDet (sizeReduce b j k r) (l.val + 1) (Nat.succ_le_of_lt l.isLt) =
        gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) :=
    gramDet_sizeReduce (b := b) (j := j) (k := k) hjk r (l.val + 1)
      (Nat.succ_le_of_lt l.isLt)
  have hcoeff := coeffs_sizeReduce_above_pivot (b := b) (j := j) (k := k) hjk r
    l hjl hlk
  calc
    ((GramSchmidt.entry (scaledCoeffs (sizeReduce b j k r)) k l : Int) : Rat)
        =
          (gramDet (sizeReduce b j k r) (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
            GramSchmidt.entry (coeffs (sizeReduce b j k r)) k l := hnew
    _ =
          (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
            GramSchmidt.entry (coeffs b) k l := by
          rw [hdet, hcoeff]
    _ = ((GramSchmidt.entry (scaledCoeffs b) k l : Int) : Rat) := hold.symm

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
