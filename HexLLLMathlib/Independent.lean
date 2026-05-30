import HexLLL.Basic
import HexGramSchmidtMathlib.Int

/-!
Mathlib-side independence theorems for `HexLLL`.

This module hosts the determinant-backed independence helpers whose proofs
factor through `GramSchmidt.Int.independent_of_det_positive` and therefore
ultimately depend on the Bareiss/`Matrix.det` correspondence. They are kept
out of the Mathlib-free `HexLLL/Basic.lean` so that the executable LLL core
does not expose a proof-only surface tied to the Mathlib-side layer.
-/

namespace Hex

namespace Matrix

/-- The identity matrix is independent: every executable leading Gram
determinant is positive. Used by Phase 4 benchmarks of
`lll.firstShortVector`, where the identity basis is the degenerate BZ-style
recombination input with all-zero lift coefficients. -/
theorem identity_independent {n : Nat} : (1 : Matrix Int n n).independent := by
  exact GramSchmidt.Int.independent_one

theorem gramMatrix_leadingRows_eq_submatrix {n : Nat} (M : Matrix Int n n) (k : Fin n) :
    gramMatrix (leadingRows M (k.val + 1) (Nat.succ_le_of_lt k.isLt)) =
      submatrix (gramMatrix M) k := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let iFin : Fin (k.val + 1) := ⟨i, hi⟩
  let jFin : Fin (k.val + 1) := ⟨j, hj⟩
  let ii : Fin n := ⟨i, Nat.lt_of_lt_of_le hi (Nat.succ_le_of_lt k.isLt)⟩
  let jj : Fin n := ⟨j, Nat.lt_of_lt_of_le hj (Nat.succ_le_of_lt k.isLt)⟩
  have hrow_i :
      row (leadingRows M (k.val + 1) (Nat.succ_le_of_lt k.isLt)) iFin = row M ii := by
    apply Vector.ext
    intro c hc
    simp [row, leadingRows, ofFn, iFin, ii]
  have hrow_j :
      row (leadingRows M (k.val + 1) (Nat.succ_le_of_lt k.isLt)) jFin = row M jj := by
    apply Vector.ext
    intro c hc
    simp [row, leadingRows, ofFn, jFin, jj]
  have hdot :
      Hex.Vector.dotProduct
          (row (leadingRows M (k.val + 1) (Nat.succ_le_of_lt k.isLt)) iFin)
          (row (leadingRows M (k.val + 1) (Nat.succ_le_of_lt k.isLt)) jFin) =
        Hex.Vector.dotProduct (row M ii) (row M jj) := by
    rw [hrow_i, hrow_j]
  simpa [gramMatrix, submatrix, ofFn, iFin, jFin, ii, jj] using
    hdot

theorem independent_of_upperTriangular_pos_diag {n : Nat}
    (M : Matrix Int n n)
    (hzero : ∀ i j : Fin n, j.val < i.val -> M[i][j] = 0)
    (hdiag : ∀ i : Fin n, 0 < M[i][i]) : M.independent := by
  exact GramSchmidt.Int.independent_of_det_positive M (by
    intro k
    have hpos :=
      det_gramMatrix_leadingRows_pos_of_upperTriangular_pos_diag M hzero hdiag
        (k.val + 1) (Nat.succ_le_of_lt k.isLt)
    rwa [gramMatrix_leadingRows_eq_submatrix M k] at hpos)

end Matrix

namespace LLLState

/-- Size reduction preserves the executable Gram-determinant independence
predicate.  This public theorem lives in the Mathlib-side library so the
Mathlib-free LLL core does not expose determinant-bound preservation surfaces. -/
theorem sizeReduce_independent (s : LLLState n m) (k : Nat)
    (hind : s.b.independent) (hvalid : s.Valid) (hvalid' : (s.sizeReduce k).Valid) :
    (s.sizeReduce k).b.independent := by
  intro i
  have hd_vec :
      (s.sizeReduce k).d.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ =
        s.d.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
    simpa using congrArg
      (fun d : Vector Nat (n + 1) => d.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (sizeReduce_d s k)
  have hgram :
      GramSchmidt.Int.gramDet (s.sizeReduce k).b (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) =
        GramSchmidt.Int.gramDet s.b (i.val + 1) (Nat.succ_le_of_lt i.isLt) := by
    rw [← hvalid'.d_eq (i.val + 1) (Nat.succ_lt_succ i.isLt)]
    rw [hd_vec]
    rw [hvalid.d_eq (i.val + 1) (Nat.succ_lt_succ i.isLt)]
  rw [hgram]
  exact hind i

end LLLState

end Hex
