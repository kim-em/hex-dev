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
  rw [sizeReduce]
  rw [scaledCoeffs_rowAdd_pivot (b := b) (j := j) (k := k) hjk (-r)]
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
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  simpa [adjacentSwap, km1] using
    GramSchmidt.Int.basis_rowSwap_adjacent_curr
      (b := b) (km1 := km1) (k := k) hkm1 hdenom

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
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  simpa [adjacentSwap, km1] using
    GramSchmidt.Int.coeffs_rowSwap_adjacent_pivot
      (b := b) (km1 := km1) (k := k) hkm1 hdenom

private theorem rowSwap_row_eq_of_ne_int {n' m' : Nat}
    (b : Matrix Int n' m') (i j r : Fin n') (hri : r ≠ i) (hrj : r ≠ j) :
    (Matrix.rowSwap b i j)[r] = b[r] := by
  apply Vector.ext
  intro idx hidx
  let c : Fin m' := ⟨idx, hidx⟩
  change (Matrix.rowSwap b i j)[r][c] = b[r][c]
  rw [Matrix.rowSwap_getElem]
  by_cases hrj' : r = j
  · exact absurd hrj' hrj
  · by_cases hri' : r = i
    · exact absurd hri' hri
    · simp [hri', hrj']

private theorem rowSwap_row_left_int {n' m' : Nat}
    (b : Matrix Int n' m') (i j : Fin n') :
    (Matrix.rowSwap b i j)[i] = b[j] := by
  apply Vector.ext
  intro idx hidx
  let c : Fin m' := ⟨idx, hidx⟩
  change (Matrix.rowSwap b i j)[i][c] = b[j][c]
  rw [Matrix.rowSwap_getElem]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

private theorem rowSwap_row_right_int {n' m' : Nat}
    (b : Matrix Int n' m') (i j : Fin n') :
    (Matrix.rowSwap b i j)[j] = b[i] := by
  apply Vector.ext
  intro idx hidx
  let c : Fin m' := ⟨idx, hidx⟩
  change (Matrix.rowSwap b i j)[j][c] = b[i][c]
  rw [Matrix.rowSwap_getElem]
  simp

/-- When the swap indices `km1, k` both lie outside the leading `t`-prefix
(`t ≤ km1.val`), the leading Gram matrix is unchanged by the row swap. -/
private theorem leadingGramMatrixInt_rowSwap_outside
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1k : km1.val < k.val)
    (t : Nat) (ht : t ≤ n) (htkm1 : t ≤ km1.val) :
    GramSchmidt.leadingGramMatrixInt (Matrix.rowSwap b km1 k) t ht =
      GramSchmidt.leadingGramMatrixInt b t ht := by
  rw [GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram,
      GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram]
  apply Vector.ext
  intro p hp
  apply Vector.ext
  intro q hq
  let pp : Fin t := ⟨p, hp⟩
  let qq : Fin t := ⟨q, hq⟩
  let pn : Fin n := ⟨p, Nat.lt_of_lt_of_le hp ht⟩
  let qn : Fin n := ⟨q, Nat.lt_of_lt_of_le hq ht⟩
  have hp_ne_km1 : pn ≠ km1 := by
    intro h
    have hv : p = km1.val := by simpa [pn] using congrArg Fin.val h
    omega
  have hp_ne_k : pn ≠ k := by
    intro h
    have hv : p = k.val := by simpa [pn] using congrArg Fin.val h
    omega
  have hq_ne_km1 : qn ≠ km1 := by
    intro h
    have hv : q = km1.val := by simpa [qn] using congrArg Fin.val h
    omega
  have hq_ne_k : qn ≠ k := by
    intro h
    have hv : q = k.val := by simpa [qn] using congrArg Fin.val h
    omega
  have hp_eq : (Matrix.rowSwap b km1 k)[pn] = b[pn] :=
    rowSwap_row_eq_of_ne_int b km1 k pn hp_ne_km1 hp_ne_k
  have hq_eq : (Matrix.rowSwap b km1 k)[qn] = b[qn] :=
    rowSwap_row_eq_of_ne_int b km1 k qn hq_ne_km1 hq_ne_k
  show (Matrix.leadingPrefix (Matrix.gramMatrix (Matrix.rowSwap b km1 k)) t ht)[pp][qq] =
       (Matrix.leadingPrefix (Matrix.gramMatrix b) t ht)[pp][qq]
  simp only [Matrix.leadingPrefix_entry]
  show (Matrix.gramMatrix (Matrix.rowSwap b km1 k))[pn][qn] =
       (Matrix.gramMatrix b)[pn][qn]
  have hentry_swap :
      (Matrix.gramMatrix (Matrix.rowSwap b km1 k))[pn][qn] =
        Hex.Vector.dotProduct ((Matrix.rowSwap b km1 k)[pn]) ((Matrix.rowSwap b km1 k)[qn]) := by
    simp [Matrix.gramMatrix, Matrix.row, Matrix.ofFn]
  have hentry_b :
      (Matrix.gramMatrix b)[pn][qn] =
        Hex.Vector.dotProduct (b[pn]) (b[qn]) := by
    simp [Matrix.gramMatrix, Matrix.row, Matrix.ofFn]
  rw [hentry_swap, hentry_b, hp_eq, hq_eq]

/-- When the swap indices `km1, k` both lie inside the leading `t`-prefix
(`k.val < t`), the leading Gram matrix of the row-swapped basis equals the
"row-and-column swap" of the original leading Gram matrix at the lifted
indices `km1', k'`. The row-and-column swap is expressed via two transposes:
swap rows, transpose, swap rows again, transpose back. -/
private theorem leadingGramMatrixInt_rowSwap_inside
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1k : km1.val < k.val)
    (t : Nat) (ht : t ≤ n) (hkt : k.val < t) :
    let km1' : Fin t := ⟨km1.val, Nat.lt_trans hkm1k hkt⟩
    let k' : Fin t := ⟨k.val, hkt⟩
    GramSchmidt.leadingGramMatrixInt (Matrix.rowSwap b km1 k) t ht =
      (Matrix.rowSwap
        ((Matrix.rowSwap (GramSchmidt.leadingGramMatrixInt b t ht) km1' k').transpose)
        km1' k').transpose := by
  intro km1' k'
  -- Convert both `leadingGramMatrixInt` references to `leadingPrefix (gramMatrix _) t ht`
  -- to avoid the private `liftFinLE` from `HexGramSchmidt/Int.lean`.
  rw [GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram
        (b := Matrix.rowSwap b km1 k) (k := t) (hk := ht),
      GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram
        (b := b) (k := t) (hk := ht)]
  let M : Matrix Int t t := Matrix.leadingPrefix (Matrix.gramMatrix b) t ht
  show Matrix.leadingPrefix (Matrix.gramMatrix (Matrix.rowSwap b km1 k)) t ht =
       (Matrix.rowSwap ((Matrix.rowSwap M km1' k').transpose) km1' k').transpose
  apply Vector.ext
  intro p hp
  apply Vector.ext
  intro q hq
  let pp : Fin t := ⟨p, hp⟩
  let qq : Fin t := ⟨q, hq⟩
  let pn : Fin n := ⟨p, Nat.lt_of_lt_of_le hp ht⟩
  let qn : Fin n := ⟨q, Nat.lt_of_lt_of_le hq ht⟩
  change (Matrix.leadingPrefix (Matrix.gramMatrix (Matrix.rowSwap b km1 k)) t ht)[pp][qq] =
         ((Matrix.rowSwap ((Matrix.rowSwap M km1' k').transpose) km1' k').transpose)[pp][qq]
  -- LHS: entry of leadingPrefix is gramMatrix entry at lifted indices.
  have hLHS :
      (Matrix.leadingPrefix (Matrix.gramMatrix (Matrix.rowSwap b km1 k)) t ht)[pp][qq] =
        Hex.Vector.dotProduct ((Matrix.rowSwap b km1 k)[pn]) ((Matrix.rowSwap b km1 k)[qn]) := by
    simp [Matrix.leadingPrefix, Matrix.gramMatrix, Matrix.row, Matrix.ofFn,
      pp, qq, pn, qn]
  -- Entry helper for M = leadingPrefix (gramMatrix b) t ht.
  have hM_entry : ∀ (a b' : Fin t),
      M[a][b'] =
        Hex.Vector.dotProduct (b[(⟨a.val, Nat.lt_of_lt_of_le a.isLt ht⟩ : Fin n)])
          (b[(⟨b'.val, Nat.lt_of_lt_of_le b'.isLt ht⟩ : Fin n)]) := by
    intro a b'
    simp [M, Matrix.leadingPrefix, Matrix.gramMatrix, Matrix.row, Matrix.ofFn]
  -- RHS: double-swap entry expressed via two transposes and two row swaps.
  have hRHS_T :
      ((Matrix.rowSwap ((Matrix.rowSwap M km1' k').transpose) km1' k').transpose)[pp][qq] =
        (Matrix.rowSwap ((Matrix.rowSwap M km1' k').transpose) km1' k')[qq][pp] := by
    simp [Matrix.transpose, Matrix.col]
  rw [hLHS, hRHS_T]
  rw [Matrix.rowSwap_getElem (M := (Matrix.rowSwap M km1' k').transpose)
    (i := km1') (j := k') (r := qq) (k := pp)]
  have hkm1'_ne_k' : (km1' : Fin t) ≠ k' := by
    intro h
    have : km1'.val = k'.val := congrArg Fin.val h
    change km1.val = k.val at this
    omega
  -- Reduce the `if-then-else` chain on qq to a single index σ(qq) and similarly for pp.
  have entry_after_outer_swap :
      ∀ (idx : Fin t),
        (Matrix.rowSwap M km1' k').transpose[idx][pp] =
          M[if pp = k' then km1' else if pp = km1' then k' else pp][idx] := by
    intro idx
    -- transpose, then rowSwap on M.
    have hT : (Matrix.rowSwap M km1' k').transpose[idx][pp] =
        (Matrix.rowSwap M km1' k')[pp][idx] := by
      simp [Matrix.transpose, Matrix.col]
    rw [hT]
    rw [Matrix.rowSwap_getElem (M := M) (i := km1') (j := k') (r := pp) (k := idx)]
    by_cases hpk : pp = k'
    · simp [hpk]
    · by_cases hpkm1 : pp = km1'
      · simp [hpkm1, hkm1'_ne_k']
      · simp [hpk, hpkm1]
  -- Helper: build the equality (rowSwap b km1 k)[r] = (rowSwap b km1 k)[r']
  -- from r = r' (avoiding `rw` motive issues with dependent indices).
  have heq_get_swap : ∀ (r r' : Fin n), r = r' →
      (Matrix.rowSwap b km1 k)[r] = (Matrix.rowSwap b km1 k)[r'] := by
    intros r r' h; exact congrArg (Matrix.rowSwap b km1 k).get h
  -- Apply the outer ite resolution at qq.
  by_cases hqk : qq = k'
  · -- qq = k': RHS specializes to M[σ(pp)][km1'].
    simp only [if_pos hqk]
    rw [entry_after_outer_swap km1']
    have hqn_k : qn = k := by
      apply Fin.ext
      have hv : qq.val = k'.val := congrArg Fin.val hqk
      change q = k.val
      exact hv
    have hqn_eq : (Matrix.rowSwap b km1 k)[qn] = b[km1] :=
      (heq_get_swap qn k hqn_k).trans (rowSwap_row_right_int b km1 k)
    rw [hqn_eq]
    by_cases hpk : pp = k'
    · simp only [if_pos hpk]
      have hpn_k : pn = k := by
        apply Fin.ext
        have hv : pp.val = k'.val := congrArg Fin.val hpk
        change p = k.val
        exact hv
      have hpn_eq : (Matrix.rowSwap b km1 k)[pn] = b[km1] :=
        (heq_get_swap pn k hpn_k).trans (rowSwap_row_right_int b km1 k)
      rw [hpn_eq, hM_entry]
    · by_cases hpkm1 : pp = km1'
      · simp only [if_neg hpk, if_pos hpkm1]
        have hpn_km1 : pn = km1 := by
          apply Fin.ext
          have hv : pp.val = km1'.val := congrArg Fin.val hpkm1
          change p = km1.val
          exact hv
        have hpn_eq : (Matrix.rowSwap b km1 k)[pn] = b[k] :=
          (heq_get_swap pn km1 hpn_km1).trans (rowSwap_row_left_int b km1 k)
        rw [hpn_eq, hM_entry]
      · simp only [if_neg hpk, if_neg hpkm1]
        have hpn_ne_km1 : pn ≠ km1 := by
          intro h
          apply hpkm1
          apply Fin.ext
          have hv : pn.val = km1.val := congrArg Fin.val h
          change p = km1.val
          exact hv
        have hpn_ne_k : pn ≠ k := by
          intro h
          apply hpk
          apply Fin.ext
          have hv : pn.val = k.val := congrArg Fin.val h
          change p = k.val
          exact hv
        have hp_swap : (Matrix.rowSwap b km1 k)[pn] = b[pn] :=
          rowSwap_row_eq_of_ne_int b km1 k pn hpn_ne_km1 hpn_ne_k
        rw [hp_swap, hM_entry]
  · by_cases hqkm1 : qq = km1'
    · simp only [if_neg hqk, if_pos hqkm1]
      rw [entry_after_outer_swap k']
      have hqn_km1 : qn = km1 := by
        apply Fin.ext
        have hv : qq.val = km1'.val := congrArg Fin.val hqkm1
        change q = km1.val
        exact hv
      have hqn_eq : (Matrix.rowSwap b km1 k)[qn] = b[k] :=
        (heq_get_swap qn km1 hqn_km1).trans (rowSwap_row_left_int b km1 k)
      rw [hqn_eq]
      by_cases hpk : pp = k'
      · simp only [if_pos hpk]
        have hpn_k : pn = k := by
          apply Fin.ext
          have hv : pp.val = k'.val := congrArg Fin.val hpk
          change p = k.val
          exact hv
        have hpn_eq : (Matrix.rowSwap b km1 k)[pn] = b[km1] :=
          (heq_get_swap pn k hpn_k).trans (rowSwap_row_right_int b km1 k)
        rw [hpn_eq, hM_entry]
      · by_cases hpkm1 : pp = km1'
        · simp only [if_neg hpk, if_pos hpkm1]
          have hpn_km1 : pn = km1 := by
            apply Fin.ext
            have hv : pp.val = km1'.val := congrArg Fin.val hpkm1
            change p = km1.val
            exact hv
          have hpn_eq : (Matrix.rowSwap b km1 k)[pn] = b[k] :=
            (heq_get_swap pn km1 hpn_km1).trans (rowSwap_row_left_int b km1 k)
          rw [hpn_eq, hM_entry]
        · simp only [if_neg hpk, if_neg hpkm1]
          have hpn_ne_km1 : pn ≠ km1 := by
            intro h
            apply hpkm1
            apply Fin.ext
            have hv : pn.val = km1.val := congrArg Fin.val h
            change p = km1.val
            exact hv
          have hpn_ne_k : pn ≠ k := by
            intro h
            apply hpk
            apply Fin.ext
            have hv : pn.val = k.val := congrArg Fin.val h
            change p = k.val
            exact hv
          have hp_swap : (Matrix.rowSwap b km1 k)[pn] = b[pn] :=
            rowSwap_row_eq_of_ne_int b km1 k pn hpn_ne_km1 hpn_ne_k
          rw [hp_swap, hM_entry]
    · -- qq ∉ {km1', k'}
      simp only [if_neg hqk, if_neg hqkm1]
      rw [entry_after_outer_swap qq]
      have hqn_ne_km1 : qn ≠ km1 := by
        intro h
        apply hqkm1
        apply Fin.ext
        have hv : qn.val = km1.val := congrArg Fin.val h
        change q = km1.val
        exact hv
      have hqn_ne_k : qn ≠ k := by
        intro h
        apply hqk
        apply Fin.ext
        have hv : qn.val = k.val := congrArg Fin.val h
        change q = k.val
        exact hv
      have hq_swap : (Matrix.rowSwap b km1 k)[qn] = b[qn] :=
        rowSwap_row_eq_of_ne_int b km1 k qn hqn_ne_km1 hqn_ne_k
      rw [hq_swap]
      by_cases hpk : pp = k'
      · simp only [if_pos hpk]
        have hpn_k : pn = k := by
          apply Fin.ext
          have hv : pp.val = k'.val := congrArg Fin.val hpk
          change p = k.val
          exact hv
        have hpn_eq : (Matrix.rowSwap b km1 k)[pn] = b[km1] :=
          (heq_get_swap pn k hpn_k).trans (rowSwap_row_right_int b km1 k)
        rw [hpn_eq, hM_entry]
      · by_cases hpkm1 : pp = km1'
        · simp only [if_neg hpk, if_pos hpkm1]
          have hpn_km1 : pn = km1 := by
            apply Fin.ext
            have hv : pp.val = km1'.val := congrArg Fin.val hpkm1
            change p = km1.val
            exact hv
          have hpn_eq : (Matrix.rowSwap b km1 k)[pn] = b[k] :=
            (heq_get_swap pn km1 hpn_km1).trans (rowSwap_row_left_int b km1 k)
          rw [hpn_eq, hM_entry]
        · simp only [if_neg hpk, if_neg hpkm1]
          have hpn_ne_km1 : pn ≠ km1 := by
            intro h
            apply hpkm1
            apply Fin.ext
            have hv : pn.val = km1.val := congrArg Fin.val h
            change p = km1.val
            exact hv
          have hpn_ne_k : pn ≠ k := by
            intro h
            apply hpk
            apply Fin.ext
            have hv : pn.val = k.val := congrArg Fin.val h
            change p = k.val
            exact hv
          have hp_swap : (Matrix.rowSwap b km1 k)[pn] = b[pn] :=
            rowSwap_row_eq_of_ne_int b km1 k pn hpn_ne_km1 hpn_ne_k
          rw [hp_swap, hM_entry]

/-- A "row-and-column swap" of a square matrix has the same determinant as the
original: the two row swaps each contribute a factor of -1, multiplying to 1. -/
private theorem det_rowSwap_transpose_rowSwap_transpose
    {R : Type u} [Lean.Grind.CommRing R] {n' : Nat}
    (M : Matrix R n' n') (i j : Fin n') (h : i ≠ j) :
    Matrix.det
        ((Matrix.rowSwap ((Matrix.rowSwap M i j).transpose) i j).transpose) =
      Matrix.det M := by
  rw [Matrix.det_transpose, Matrix.det_rowSwap _ _ _ h,
      Matrix.det_transpose, Matrix.det_rowSwap _ _ _ h]
  grind

theorem gramDet_adjacentSwap_of_ne (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (t : Nat) (ht : t ≤ n) (htk : t ≠ k.val) :
    gramDet (adjacentSwap b k hk) t ht = gramDet b t ht := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1k : km1.val < k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  unfold adjacentSwap gramDet
  congr 1
  by_cases hkt : k.val < t
  · -- Inside case: rows km1, k both inside the leading prefix.
    rw [leadingGramMatrixInt_rowSwap_inside (b := b) (km1 := km1) (k := k) hkm1k t ht hkt]
    rw [Matrix.bareiss_eq_det, Matrix.bareiss_eq_det]
    apply det_rowSwap_transpose_rowSwap_transpose
    intro h
    have : km1.val = k.val := by
      have := congrArg Fin.val h
      simpa using this
    omega
  · -- Outside case: t ≤ km1.val, leading Gram matrix unchanged.
    have htlt : t ≤ km1.val := by
      have ht_le : t ≤ k.val := Nat.le_of_not_lt hkt
      have htlt_k : t < k.val := Nat.lt_of_le_of_ne ht_le htk
      dsimp [km1, GramSchmidt.prevRow]
      omega
    rw [leadingGramMatrixInt_rowSwap_outside (b := b) (km1 := km1) (k := k) hkm1k t ht htlt]

theorem gramDet_adjacentSwap_pivot (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    let km1 := GramSchmidt.prevRow k hk
    let B : Int := GramSchmidt.entry (scaledCoeffs b) k km1
    ((gramDet (adjacentSwap b k hk) k.val (Nat.le_of_lt k.isLt) : Nat) : Int) =
      (((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
          ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) + B ^ 2) /
        ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) := by
  let km1 := GramSchmidt.prevRow k hk
  let B : Int := GramSchmidt.entry (scaledCoeffs b) k km1
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]; omega
  have hprod :=
    GramSchmidt.Int.gramDet_rowSwap_adjacent_pivot_product
      (b := b) (km1 := km1) (k := k) hkm1
  -- `hprod` is in terms of `Matrix.rowSwap`; `adjacentSwap` is exactly that.
  have hdk_pos :
      ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) ≠ 0 := by
    intro h
    apply hdet
    exact Int.ofNat.inj h
  -- From dprime_int * dk_int = (rhs) and dk_int ≠ 0, deduce dprime_int = rhs / dk_int.
  -- Goal: ((gramDet (adjacentSwap b k hk) k.val ...) : Int) = (rhs) / dk_int.
  show ((gramDet (Matrix.rowSwap b km1 k) k.val (Nat.le_of_lt k.isLt) : Nat) : Int) =
      (((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
          ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) + B ^ 2) /
        ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int)
  rw [← hprod]
  exact (Int.mul_ediv_cancel _ hdk_pos).symm

theorem adjacentSwap_gramDetNumerator_dvd (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val)
    (hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    adjacentSwapDenom b k ∣ adjacentSwapGramDetNumerator b k hk := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]; omega
  have hprod :=
    GramSchmidt.Int.gramDet_rowSwap_adjacent_pivot_product
      (b := b) (km1 := km1) (k := k) hkm1
  -- The numerator equals dprime_int * dk_int, hence dk_int divides it.
  show ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) ∣
      adjacentSwapGramDetNumerator b k hk
  show ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) ∣
      ((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
          ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) +
        (GramSchmidt.entry (scaledCoeffs b) k km1) ^ 2
  rw [← hprod]
  exact ⟨((gramDet (Matrix.rowSwap b km1 k) k.val (Nat.le_of_lt k.isLt) : Nat) : Int),
    Int.mul_comm _ _⟩

private theorem intCast_rat_injective_local {a b : Int} (h : (a : Rat) = (b : Rat)) :
    a = b := by
  have hz : ((a - b : Int) : Rat) = 0 := by
    simp [h]
    grind
  have hsub : a - b = 0 := Rat.intCast_eq_zero_iff.mp hz
  omega

theorem scaledCoeffs_adjacentSwap_lower_prev (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (j : Fin n) (hj : j.val + 1 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) km1 j =
      GramSchmidt.entry (scaledCoeffs b) k j := by
  intro km1
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hjkm1 : j.val < km1.val := by omega
  have hjk : j.val < k.val := by omega
  have hjsucc_ne : j.val + 1 ≠ k.val := by omega
  apply intCast_rat_injective_local
  have hLHS := scaledCoeffs_eq (b := adjacentSwap b k hk) km1.val j.val km1.isLt hjkm1
  have hRHS := scaledCoeffs_eq (b := b) k.val j.val k.isLt hjk
  have hdet :
      gramDet (adjacentSwap b k hk) (j.val + 1)
          (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) =
        gramDet b (j.val + 1) (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) := by
    apply gramDet_adjacentSwap_of_ne
    exact hjsucc_ne
  have hcoeff : GramSchmidt.entry (coeffs (adjacentSwap b k hk)) km1 j =
      GramSchmidt.entry (coeffs b) k j :=
    coeffs_adjacentSwap_lower_prev (b := b) k hk j hj
  calc ((GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) km1 j : Int) : Rat)
      = (gramDet (adjacentSwap b k hk) (j.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) : Rat) *
          GramSchmidt.entry (coeffs (adjacentSwap b k hk)) km1 j := hLHS
    _ = (gramDet b (j.val + 1) (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) : Rat) *
          GramSchmidt.entry (coeffs b) k j := by
          rw [hdet, hcoeff]
    _ = ((GramSchmidt.entry (scaledCoeffs b) k j : Int) : Rat) := hRHS.symm

theorem scaledCoeffs_adjacentSwap_lower_curr (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (j : Fin n) (hj : j.val + 1 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) k j =
      GramSchmidt.entry (scaledCoeffs b) km1 j := by
  intro km1
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hjkm1 : j.val < km1.val := by omega
  have hjk : j.val < k.val := by omega
  have hjsucc_ne : j.val + 1 ≠ k.val := by omega
  apply intCast_rat_injective_local
  have hLHS := scaledCoeffs_eq (b := adjacentSwap b k hk) k.val j.val k.isLt hjk
  have hRHS := scaledCoeffs_eq (b := b) km1.val j.val km1.isLt hjkm1
  have hdet :
      gramDet (adjacentSwap b k hk) (j.val + 1)
          (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) =
        gramDet b (j.val + 1) (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) := by
    apply gramDet_adjacentSwap_of_ne
    exact hjsucc_ne
  have hcoeff : GramSchmidt.entry (coeffs (adjacentSwap b k hk)) k j =
      GramSchmidt.entry (coeffs b) km1 j :=
    coeffs_adjacentSwap_lower_curr (b := b) k hk j hj
  calc ((GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) k j : Int) : Rat)
      = (gramDet (adjacentSwap b k hk) (j.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) : Rat) *
          GramSchmidt.entry (coeffs (adjacentSwap b k hk)) k j := hLHS
    _ = (gramDet b (j.val + 1) (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) : Rat) *
          GramSchmidt.entry (coeffs b) km1 j := by
          rw [hdet, hcoeff]
    _ = ((GramSchmidt.entry (scaledCoeffs b) km1 j : Int) : Rat) := hRHS.symm

theorem scaledCoeffs_adjacentSwap_pivot (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) k km1 =
      GramSchmidt.entry (scaledCoeffs b) k km1 := by
  intro km1
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hkm1k : km1.val < k.val := by omega
  calc
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) k km1
        = Matrix.det
            (GramSchmidt.scaledCoeffMatrix (Matrix.rowSwap b km1 k) k km1 hkm1k) := by
          rw [scaledCoeffs_eq_scaledCoeffMatrix_det]
          rfl
    _ = Matrix.det ((GramSchmidt.scaledCoeffMatrix b k km1 hkm1k).transpose) := by
          rw [GramSchmidt.Int.scaledCoeffMatrix_rowSwap_adjacent_pivot_transpose
            (b := b) (km1 := km1) (k := k) hkm1 hkm1k]
    _ = Matrix.det (GramSchmidt.scaledCoeffMatrix b k km1 hkm1k) := by
          rw [Matrix.det_transpose]
    _ = GramSchmidt.entry (scaledCoeffs b) k km1 := by
          rw [← scaledCoeffs_eq_scaledCoeffMatrix_det]

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
