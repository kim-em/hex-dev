import HexGramSchmidt.Int
import HexMatrixMathlib.Determinant

/-!
Mathlib bridge lemma for the executable Cramer-style scaled coefficient
matrix and the public Bareiss surface.

The Mathlib-free file `HexGramSchmidt/Int.lean` packages the executable
scaled-coefficient array entry as the no-pivot Bareiss trailing value on
`GramSchmidt.scaledCoeffMatrix` (via `scaledCoeffRows_lower_eq_…`). The
public Bareiss algorithm `Matrix.bareiss`, however, may insert a row swap
when a diagonal pivot is zero, so the executable array entry need not
match the public Bareiss value on the Cramer minor without crossing the
Bareiss/Leibniz determinant identity: the geometric vanishing in the
singular branch is visible only through the Leibniz determinant.

Per `SPEC/Libraries/hex-gram-schmidt.md` ("Proof path governs placement,
not just statement"), this bridge therefore lives in
`HexGramSchmidtMathlib`. The proof consumes the bridge-side identity
`HexMatrixMathlib.bareiss_eq_det`, which is owned by
`hex-matrix-mathlib`.
-/

namespace Hex
namespace GramSchmidt
namespace Int

/-- Non-singular branch of the Cramer/Bareiss bridge: when the no-pivot
Bareiss pass over the Gram matrix reaches column `j` without recording a
singular step, the executable scaled coefficient agrees with the public
row-pivoted Bareiss determinant of the Cramer minor. -/
theorem scaledCoeffs_eq_scaledCoeffMatrix_bareiss_of_no_singular
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val)
    (h_nonsing :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.bareiss (GramSchmidt.scaledCoeffMatrix b i j hji) := by
  have h_rows :=
    scaledCoeffRows_lower_eq_noPivotLoop_scaledCoeffMatrix b i j hji h_nonsing
  have h_scaled_nonsing :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState
            (GramSchmidt.scaledCoeffMatrix b i j hji))).singularStep = none := by
    rw [scaledCoeffMatrix_eq_borderedMinor b i j hji]
    have h_sync :=
      (noPivotLoop_full_eq_borderedMinor_at_trailing (Matrix.gramMatrix b) j.val
        (Nat.lt_trans hji i.isLt)
        (⟨j.val, Nat.lt_trans hji i.isLt⟩ : Fin n) i
        (Nat.le_refl _) (Nat.le_of_lt hji)).2
    exact h_sync ▸ h_nonsing
  have h_bareiss :=
    Matrix.bareiss_eq_noPivotLoop_last_of_no_singular
      (GramSchmidt.scaledCoeffMatrix b i j hji) h_scaled_nonsing
  have h_entry :
      GramSchmidt.entry (scaledCoeffs b) i j =
        (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState
            (GramSchmidt.scaledCoeffMatrix b i j hji))).matrix[
          Fin.last j.val][Fin.last j.val] := by
    rw [scaledCoeffs_entry_eq_getArrayEntry]
    exact h_rows
  exact h_entry.trans h_bareiss.symm

/-- Cramer/Bareiss bridge: below the diagonal, the integral scaled
Gram-Schmidt coefficient is exactly the public Bareiss determinant of the
Cramer minor `scaledCoeffMatrix`. The proof splits on whether the no-pivot
Bareiss pass over `gramMatrix b` reaches column `j` without recording a
singular step:

- Non-singular branch: defer to
  `scaledCoeffs_eq_scaledCoeffMatrix_bareiss_of_no_singular`.
- Singular branch: both sides vanish — the executable scaled coefficient is
  zero by `scaledCoeffs_eq_zero_of_singularStep_lt` (the lifted lower-column
  singular lemma from #4166), and the public Bareiss determinant of the
  Cramer minor is zero by `HexMatrixMathlib.bareiss_eq_det` composed with
  `scaledCoeffMatrix_det_eq_zero_of_singularStep_lt`. The latter Mathlib-free
  helper internally lifts partial-pass singularity to the full
  `bareissNoPivotData` pass and applies the Cramer determinant identity.

This case-split avoids the transitive dependency on the private sorry
`scaledCoeffRows_lower_eq_scaledCoeffMatrix_bareiss` that the older chain
proof carried via `scaledCoeffs_eq_scaledCoeffMatrix_det`. -/
theorem scaledCoeffs_eq_scaledCoeffMatrix_bareiss
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.bareiss (GramSchmidt.scaledCoeffMatrix b i j hji) := by
  cases h_sing : (Matrix.noPivotLoop j.val
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep with
  | none =>
      exact scaledCoeffs_eq_scaledCoeffMatrix_bareiss_of_no_singular b i j hji h_sing
  | some s =>
      have hsj : s < j.val := by
        have h := noPivotLoop_singularStep_lt j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl s h_sing
        change s < 0 + j.val at h
        omega
      have h_lhs : GramSchmidt.entry (scaledCoeffs b) i j = 0 :=
        scaledCoeffs_eq_zero_of_singularStep_lt b i j hji s h_sing hsj
      have h_det := scaledCoeffMatrix_det_eq_zero_of_singularStep_lt
        b i j hji s h_sing
      rw [h_lhs, HexMatrixMathlib.bareiss_eq_det, h_det]


/-- Below the diagonal, the executable integral scaled coefficient is exactly
the Cramer determinant encoded by `scaledCoeffMatrix`. -/
theorem scaledCoeffs_eq_scaledCoeffMatrix_det
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) := by
  rw [scaledCoeffs_eq_scaledCoeffMatrix_bareiss]
  exact HexMatrixMathlib.bareiss_eq_det (GramSchmidt.scaledCoeffMatrix b i j hji)


/-- Conditional form of the leading Gram determinant bridge. The remaining
unconditional bridge is exactly the nonnegativity of leading Gram determinants:
once `0 ≤ det` is available, the public `Nat`-valued `gramDet` casts back to
the signed determinant. -/
theorem leadingGramMatrixInt_det_eq_gramDet_int_of_nonneg
    (b : Matrix Int n m) (t : Nat) (ht : t ≤ n)
    (hdet : 0 ≤ Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht)) :
    Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht) =
      Int.ofNat (gramDet b t ht) := by
  rw [gramDet, HexMatrixMathlib.bareiss_eq_det]
  exact (Int.toNat_of_nonneg hdet).symm

/-- The public `Nat` Gram determinant casts back to the signed determinant of
the leading integer Gram matrix. -/
theorem leadingGramMatrixInt_det_eq_gramDet_int
    (b : Matrix Int n m) (t : Nat) (ht : t ≤ n) :
    Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht) =
      Int.ofNat (gramDet b t ht) :=
  leadingGramMatrixInt_det_eq_gramDet_int_of_nonneg b t ht
    (leadingGramMatrixInt_det_nonneg b t ht)

/-- The leading executable Gram determinants of a square upper-triangular
integer matrix with strictly positive diagonal are positive.

This theorem is bridge-only: its proof identifies the executable `gramDet`
with the Leibniz determinant of the leading Gram matrix via
`HexMatrixMathlib.bareiss_eq_det`. -/
theorem gramDet_pos_of_upperTriangular_pos_diag
    {n : Nat} (M : Matrix Int n n)
    (hzero : ∀ i j : Fin n, j.val < i.val -> M[i][j] = 0)
    (hdiag : ∀ i : Fin n, 0 < M[i][i])
    (k : Nat) (hk : k ≤ n) (hk' : 0 < k) :
    0 < gramDet M k hk := by
  cases k with
  | zero =>
      omega
  | succ r =>
      have hrn : r < n := Nat.lt_of_succ_le hk
      have hlead :
          Matrix.gramMatrix (Matrix.leadingRows M (r + 1) hk) =
            Matrix.leadingPrefix (Matrix.gramMatrix M) (r + 1) hk := by
        apply Vector.ext
        intro i hi
        apply Vector.ext
        intro j hj
        let iFin : Fin (r + 1) := ⟨i, hi⟩
        let jFin : Fin (r + 1) := ⟨j, hj⟩
        let ii : Fin n := ⟨i, Nat.lt_of_lt_of_le hi hk⟩
        let jj : Fin n := ⟨j, Nat.lt_of_lt_of_le hj hk⟩
        have hrow_i :
            Matrix.row (Matrix.leadingRows M (r + 1) hk) iFin =
              Matrix.row M ii := by
          apply Vector.ext
          intro c hc
          simp [Matrix.row, Matrix.leadingRows, Matrix.ofFn, iFin, ii]
        have hrow_j :
            Matrix.row (Matrix.leadingRows M (r + 1) hk) jFin =
              Matrix.row M jj := by
          apply Vector.ext
          intro c hc
          simp [Matrix.row, Matrix.leadingRows, Matrix.ofFn, jFin, jj]
        have hdot :
            Matrix.dot (Matrix.row (Matrix.leadingRows M (r + 1) hk) iFin)
                (Matrix.row (Matrix.leadingRows M (r + 1) hk) jFin) =
              Matrix.dot (Matrix.row M ii) (Matrix.row M jj) := by
          rw [hrow_i, hrow_j]
        simpa [Matrix.gramMatrix, Matrix.leadingPrefix, Matrix.ofFn, iFin, jFin, ii, jj]
          using hdot
      have hdet_pos :
          0 < Matrix.det (GramSchmidt.leadingGramMatrixInt M (r + 1) hk) := by
        have hpos :=
          Matrix.det_gramMatrix_leadingRows_pos_of_upperTriangular_pos_diag M hzero hdiag
            (r + 1) hk
        rwa [hlead, ← GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram] at hpos
      have hdet_nat :
          Matrix.det (GramSchmidt.leadingGramMatrixInt M (r + 1) hk) =
            Int.ofNat (gramDet M (r + 1) hk) :=
        leadingGramMatrixInt_det_eq_gramDet_int M (r + 1) hk
      have hnat_int : 0 < Int.ofNat (gramDet M (r + 1) hk) := by
        simpa [hdet_nat] using hdet_pos
      exact Int.ofNat_lt.mp hnat_int


/-- The executable scaled-coefficient pivot entry changes predictably under
an earlier-row addition. This packages the Cramer/Bareiss pivot identity at
the public `scaledCoeffs` level so update consumers need not unfold the
determinant bridge directly. -/
theorem scaledCoeffs_rowAdd_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (c : Int) :
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k j =
      GramSchmidt.entry (scaledCoeffs b) k j +
        c * Int.ofNat (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
  have hnew := scaledCoeffs_eq_scaledCoeffMatrix_det
    (b := Matrix.rowAdd b j k c) (i := k) (j := j) hjk
  have hold := scaledCoeffs_eq_scaledCoeffMatrix_det (b := b) (i := k) (j := j) hjk
  have hbridge := scaledCoeffMatrix_rowAdd_pivot_det (b := b) (j := j) (k := k) hjk c
  have hlead := leadingGramMatrixInt_det_eq_gramDet_int
    (b := b) (t := j.val + 1) (ht := Nat.succ_le_of_lt j.isLt)
  calc
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k j =
        Matrix.det (GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk) := hnew
    _ =
        Matrix.det (GramSchmidt.scaledCoeffMatrix b k j hjk) +
          c * Matrix.det
            (GramSchmidt.leadingGramMatrixInt b (j.val + 1)
              (Nat.succ_le_of_lt j.isLt)) := hbridge
    _ =
        GramSchmidt.entry (scaledCoeffs b) k j +
          c * Int.ofNat (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
      rw [← hold, hlead]


/-- Adding a multiple of an earlier row to a later row leaves the leading
Gram determinant unchanged. The hypothesis `j.val < k.val` makes the source
row earlier than the destination row in the basis. -/
theorem gramDet_rowAdd_earlier
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hjk : j.val < k.val) :
    gramDet (Matrix.rowAdd b j k c) t ht = gramDet b t ht := by
  unfold gramDet
  -- Reduce to the underlying Bareiss-determinant equality on `Int`.
  congr 1
  by_cases hkt : k.val < t
  · -- Inside case: bareiss = det, then det_rowAdd / det_colAdd preserve.
    rw [leadingGramMatrixInt_rowAdd_inside b j k c t ht hjk hkt]
    rw [HexMatrixMathlib.bareiss_eq_det, HexMatrixMathlib.bareiss_eq_det]
    -- Indices and inequality between `jt` and `kt` in `Fin t`.
    have hjt_ne_kt : (⟨j.val, Nat.lt_trans hjk hkt⟩ : Fin t) ≠ ⟨k.val, hkt⟩ := by
      intro h
      have hval : (⟨j.val, Nat.lt_trans hjk hkt⟩ : Fin t).val =
          (⟨k.val, hkt⟩ : Fin t).val :=
        congrArg Fin.val h
      exact Nat.ne_of_lt hjk hval
    rw [Matrix.det_colAdd _ _ _ _ hjt_ne_kt]
    rw [Matrix.det_rowAdd _ _ _ _ hjt_ne_kt]
  · -- Outside case: leading prefix unchanged.
    have hkt' : t ≤ k.val := Nat.le_of_not_lt hkt
    rw [leadingGramMatrixInt_rowAdd_outside b j k c t ht hkt']


/-! ### `scaledCoeffs` row-by-row updates under earlier-row addition

The three theorems below package the scaled-coefficient update under
`Matrix.rowAdd b j k c` with `j.val < k.val` at each below-diagonal column
position (left of the pivot, the row that is unchanged when not the
destination, and strictly between the source and the pivot column). They
mirror the pattern of `scaledCoeffs_rowAdd_pivot` and let the
`LLLState.sizeReduceColumn` proof-field discharges in `HexLLL/Basic.lean`
work against `rowAdd` directly, without reaching for the bridge-bound
`scaledCoeffs_sizeReduce_*` wrappers in `HexGramSchmidt/Update.lean`. -/

private theorem intCast_rat_injective_for_rowAdd {a b : Int}
    (h : (a : Rat) = (b : Rat)) : a = b := by
  have hz : ((a - b : Int) : Rat) = 0 := by
    push_cast
    grind
  have hsub : a - b = 0 := Rat.intCast_eq_zero_iff.mp hz
  omega

private theorem scaledCoeffs_eq_fin_of_lt (b : Matrix Int n m) (i j : Fin n)
    (hji : j.val < i.val) :
    ((GramSchmidt.entry (scaledCoeffs b) i j : Int) : Rat) =
      (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt) : Rat) *
        GramSchmidt.entry (coeffs b) i j := by
  simpa using scaledCoeffs_eq (b := b) i.val j.val i.isLt hji

/-- Under `Matrix.rowAdd b j k c` with `l.val < j.val < k.val`, the
destination-row scaled coefficient at column `l` updates by the linear
combination `(scaledCoeffs b)[k][l] + c * (scaledCoeffs b)[j][l]`. -/
theorem scaledCoeffs_rowAdd_lower (b : Matrix Int n m) (l j k : Fin n)
    (hlj : l.val < j.val) (hjk : j.val < k.val) (c : Int) :
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k l =
      GramSchmidt.entry (scaledCoeffs b) k l +
        c * GramSchmidt.entry (scaledCoeffs b) j l := by
  apply intCast_rat_injective_for_rowAdd
  have hlk : l.val < k.val := Nat.lt_trans hlj hjk
  have hnew := scaledCoeffs_eq_fin_of_lt (b := Matrix.rowAdd b j k c) k l hlk
  have holdk := scaledCoeffs_eq_fin_of_lt (b := b) k l hlk
  have holdj := scaledCoeffs_eq_fin_of_lt (b := b) j l hlj
  have hdet :
      gramDet (Matrix.rowAdd b j k c) (l.val + 1) (Nat.succ_le_of_lt l.isLt) =
        gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) :=
    gramDet_rowAdd_earlier b j k c (l.val + 1)
      (Nat.succ_le_of_lt l.isLt) hjk
  have hcoeff := coeffs_rowAdd_lower (b := b) l j k hlj hjk c
  calc
    ((GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k l : Int) : Rat)
        =
          (gramDet (Matrix.rowAdd b j k c) (l.val + 1)
              (Nat.succ_le_of_lt l.isLt) : Rat) *
            GramSchmidt.entry (coeffs (Matrix.rowAdd b j k c)) k l := hnew
    _ =
          (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
            (GramSchmidt.entry (coeffs b) k l +
              (c : Rat) * GramSchmidt.entry (coeffs b) j l) := by
          rw [hdet, hcoeff]
    _ =
          ((GramSchmidt.entry (scaledCoeffs b) k l +
            c * GramSchmidt.entry (scaledCoeffs b) j l : Int) : Rat) := by
          calc
            (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
                (GramSchmidt.entry (coeffs b) k l +
                  (c : Rat) * GramSchmidt.entry (coeffs b) j l)
                =
                  (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
                    GramSchmidt.entry (coeffs b) k l +
                    (c : Rat) *
                      ((gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
                        GramSchmidt.entry (coeffs b) j l) := by
                  grind
            _ =
                  ((GramSchmidt.entry (scaledCoeffs b) k l : Int) : Rat) +
                    (c : Rat) *
                      ((GramSchmidt.entry (scaledCoeffs b) j l : Int) : Rat) := by
                  rw [← holdk, ← holdj]
            _ =
                  ((GramSchmidt.entry (scaledCoeffs b) k l +
                    c * GramSchmidt.entry (scaledCoeffs b) j l : Int) : Rat) := by
                  grind

/-- Under `Matrix.rowAdd b j k c` with `j.val < k.val`, every row of
`scaledCoeffs` other than the destination row `k` is preserved. -/
theorem scaledCoeffs_rowAdd_other_row (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (c : Int) (i : Fin n) (hik : i ≠ k) :
    (scaledCoeffs (Matrix.rowAdd b j k c)).row i = (scaledCoeffs b).row i := by
  apply Vector.ext
  intro col hcol
  let l : Fin n := ⟨col, hcol⟩
  change GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) i l =
    GramSchmidt.entry (scaledCoeffs b) i l
  by_cases hli : l.val < i.val
  · apply intCast_rat_injective_for_rowAdd
    have hnew := scaledCoeffs_eq_fin_of_lt (b := Matrix.rowAdd b j k c) i l hli
    have hold := scaledCoeffs_eq_fin_of_lt (b := b) i l hli
    have hdet :
        gramDet (Matrix.rowAdd b j k c) (l.val + 1) (Nat.succ_le_of_lt l.isLt) =
          gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) :=
      gramDet_rowAdd_earlier b j k c (l.val + 1)
        (Nat.succ_le_of_lt l.isLt) hjk
    have hrow := coeffs_rowAdd_other_row (b := b) j k c hjk i hik
    have hcoeff :
        GramSchmidt.entry (coeffs (Matrix.rowAdd b j k c)) i l =
          GramSchmidt.entry (coeffs b) i l := by
      have hget := congrArg (fun row => row[l]) hrow
      simpa [GramSchmidt.entry] using hget
    calc
      ((GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) i l : Int) : Rat)
          =
            (gramDet (Matrix.rowAdd b j k c) (l.val + 1)
                (Nat.succ_le_of_lt l.isLt) : Rat) *
              GramSchmidt.entry (coeffs (Matrix.rowAdd b j k c)) i l := hnew
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
        (gramDet_rowAdd_earlier b j k c (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) hjk)
    · have hilv : i.val < l.val := by
        have hle : i.val ≤ l.val := Nat.le_of_not_lt hli
        exact Nat.lt_of_le_of_ne hle (fun h => hil (Fin.ext h))
      rw [scaledCoeffs_upper (Matrix.rowAdd b j k c) i.val l.val i.isLt l.isLt hilv,
        scaledCoeffs_upper b i.val l.val i.isLt l.isLt hilv]

/-- Under `Matrix.rowAdd b j k c` with `j.val < l.val < k.val`, the
destination-row scaled coefficient at column `l` between the source column
and the pivot is preserved. -/
theorem scaledCoeffs_rowAdd_above_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (c : Int) (l : Fin n)
    (hjl : j.val < l.val) (hlk : l.val < k.val) :
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k l =
      GramSchmidt.entry (scaledCoeffs b) k l := by
  apply intCast_rat_injective_for_rowAdd
  have hnew := scaledCoeffs_eq_fin_of_lt (b := Matrix.rowAdd b j k c) k l hlk
  have hold := scaledCoeffs_eq_fin_of_lt (b := b) k l hlk
  have hdet :
      gramDet (Matrix.rowAdd b j k c) (l.val + 1) (Nat.succ_le_of_lt l.isLt) =
        gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) :=
    gramDet_rowAdd_earlier b j k c (l.val + 1)
      (Nat.succ_le_of_lt l.isLt) hjk
  have hcoeff := coeffs_rowAdd_above_pivot (b := b) j l k hjl hlk c
  calc
    ((GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k l : Int) : Rat)
        =
          (gramDet (Matrix.rowAdd b j k c) (l.val + 1)
              (Nat.succ_le_of_lt l.isLt) : Rat) *
            GramSchmidt.entry (coeffs (Matrix.rowAdd b j k c)) k l := hnew
    _ =
          (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
            GramSchmidt.entry (coeffs b) k l := by
          rw [hdet, hcoeff]
    _ = ((GramSchmidt.entry (scaledCoeffs b) k l : Int) : Rat) := hold.symm


end Int
end GramSchmidt
end Hex
