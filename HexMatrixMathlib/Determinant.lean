import HexMatrixMathlib.Basic
import HexMatrixMathlib.Determinant.DesnanotJacobi
import HexMatrix.Bareiss
import HexMatrix.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
Determinant bridge theorems for `hex-matrix-mathlib`.

This module relates the executable Leibniz-formula determinant on `Hex.Matrix`
to Mathlib's determinant on function-based matrices. The supporting lemmas keep
the permutation-indexed product surface in a form that downstream proofs can
rewrite through `matrixEquiv` directly.
-/

namespace HexMatrixMathlib

universe u

variable {R : Type u} {n : Nat}

namespace PermutationVector

private theorem get_injective_of_nodup
    {perm : Vector (Fin n) n} (hnodup : perm.toList.Nodup) :
    Function.Injective fun i : Fin n => perm[i] := by
  intro i j hij
  have hi : i.val < perm.toList.length := by
    simp [Vector.length_toList]
  have hj : j.val < perm.toList.length := by
    simp [Vector.length_toList]
  have hget :
      perm.toList[i.val]'hi = perm.toList[j.val]'hj := by
    simpa [Vector.getElem_toList] using hij
  exact Fin.ext ((hnodup.getElem_inj_iff).mp hget)

/-- Convert a Hex permutation vector into the corresponding Mathlib permutation. -/
noncomputable def toPerm (perm : Vector (Fin n) n)
    (hnodup : perm.toList.Nodup) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i : Fin n => perm[i])
    ⟨get_injective_of_nodup hnodup,
      Finite.surjective_of_injective (get_injective_of_nodup hnodup)⟩

@[simp]
theorem toPerm_apply (perm : Vector (Fin n) n)
    (hnodup : perm.toList.Nodup) (i : Fin n) :
    toPerm perm hnodup i = perm[i] := by
  rfl

theorem toPerm_injective :
    Function.Injective
      (fun p : {perm : Vector (Fin n) n // perm.toList.Nodup} =>
        toPerm p.1 p.2) := by
  intro p q hpq
  apply Subtype.ext
  apply Vector.ext
  intro i hi
  exact congrFun (congrArg Equiv.toFun hpq) ⟨i, hi⟩

private theorem vectorOfPerm_toList (σ : Equiv.Perm (Fin n)) :
    (Vector.ofFn fun i : Fin n => σ i).toList =
      (List.finRange n).map fun i : Fin n => σ i := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro i hi₁ hi₂
    simp [Vector.getElem_toList]

private theorem vectorOfPerm_nodup (σ : Equiv.Perm (Fin n)) :
    (Vector.ofFn fun i : Fin n => σ i).toList.Nodup := by
  rw [vectorOfPerm_toList]
  exact List.Nodup.map σ.injective (List.nodup_finRange n)

theorem toPerm_vectorOfPerm (σ : Equiv.Perm (Fin n)) :
    toPerm (Vector.ofFn fun i : Fin n => σ i) (vectorOfPerm_nodup σ) = σ := by
  ext i
  simp [toPerm]

/-- Hex permutation vectors converted to Mathlib permutations, with proofs attached. -/
noncomputable def equivs (n : Nat) : List (Equiv.Perm (Fin n)) :=
  (Hex.Matrix.permutationVectors n).attach.map fun perm =>
    toPerm perm.1 (Hex.Matrix.permutationVectors_nodup perm.2)

theorem equivs_complete (σ : Equiv.Perm (Fin n)) :
    σ ∈ equivs n := by
  let perm : Vector (Fin n) n := Vector.ofFn fun i : Fin n => σ i
  have hnodup : perm.toList.Nodup := vectorOfPerm_nodup σ
  have hmem : perm ∈ Hex.Matrix.permutationVectors n :=
    Hex.Matrix.permutationVectors_complete hnodup
  rw [equivs, List.mem_map]
  refine ⟨⟨perm, hmem⟩, List.mem_attach _ _, ?_⟩
  exact toPerm_vectorOfPerm σ

theorem equivs_nodup (n : Nat) :
    (equivs n).Nodup := by
  unfold equivs
  refine List.Nodup.map ?_ (List.Nodup.attach Hex.Matrix.permutationVectors_nodup_list)
  intro p q hpq
  apply Subtype.ext
  have hpq' :
      (⟨p.1, Hex.Matrix.permutationVectors_nodup p.2⟩ :
        {perm : Vector (Fin n) n // perm.toList.Nodup}) =
        ⟨q.1, Hex.Matrix.permutationVectors_nodup q.2⟩ := by
    exact toPerm_injective hpq
  exact congrArg (fun x : {perm : Vector (Fin n) n // perm.toList.Nodup} => x.1) hpq'

private theorem vectorOfPerm_swap_mul (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (Vector.ofFn fun r : Fin n => (Equiv.swap i j * σ) r) =
      Hex.Matrix.swapPermutationValues (Vector.ofFn fun r : Fin n => σ r) i j := by
  apply Vector.ext
  intro r hr
  show (Vector.ofFn fun r : Fin n => (Equiv.swap i j * σ) r)[(⟨r, hr⟩ : Fin n)] =
    (Hex.Matrix.swapPermutationValues (Vector.ofFn fun r : Fin n => σ r) i j)[(⟨r, hr⟩ : Fin n)]
  rw [Hex.Matrix.swapPermutationValues_get_if]
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def]

/-- Hex's inversion-count determinant sign agrees with Mathlib's permutation sign. -/
theorem detSign_vectorOfPerm_eq_permSign [CommRing R] (σ : Equiv.Perm (Fin n)) :
    Hex.Matrix.detSign (R := R) (Vector.ofFn fun i : Fin n => σ i) =
      ((Equiv.Perm.sign σ : Int) : R) := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
      simp [Hex.Matrix.detSign_identity]
  | swap_mul σ i j hne ih =>
      rw [vectorOfPerm_swap_mul σ i j]
      have hflip := Hex.Matrix.detSign_swapPermutationValues (R := R)
        (perm := (Vector.ofFn fun r : Fin n => σ r)) (i := i) (j := j)
        (hnodup := vectorOfPerm_nodup σ) hne
      have hswapped :
          Hex.Matrix.detSign (R := R)
              (Hex.Matrix.swapPermutationValues (Vector.ofFn fun r : Fin n => σ r) i j) =
            -Hex.Matrix.detSign (R := R) (Vector.ofFn fun r : Fin n => σ r) := by
        rw [hflip]
        simp
      rw [hswapped]
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]
      rw [ih]
      norm_num

/-- Hex's inversion-count determinant sign agrees with Mathlib's permutation sign. -/
theorem detSign_eq_permSign [CommRing R]
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    Hex.Matrix.detSign (R := R) perm =
      ((Equiv.Perm.sign (toPerm perm hnodup) : Int) : R) := by
  have hperm :
      (Vector.ofFn fun i : Fin n => toPerm perm hnodup i) = perm := by
    apply Vector.ext
    intro i hi
    simp [toPerm]
  calc
    Hex.Matrix.detSign (R := R) perm =
        Hex.Matrix.detSign (R := R) (Vector.ofFn fun i : Fin n => toPerm perm hnodup i) := by
          rw [hperm]
    _ = ((Equiv.Perm.sign (toPerm perm hnodup) : Int) : R) := by
          exact detSign_vectorOfPerm_eq_permSign (R := R) (toPerm perm hnodup)

end PermutationVector

@[simp]
theorem detProduct_eq_matrixEquiv
    [Lean.Grind.Ring R] (M : Hex.Matrix R n n) (perm : Vector (Fin n) n) :
    Hex.Matrix.detProduct M perm =
      (List.finRange n).foldl (fun acc i => acc * matrixEquiv M i (perm[i])) 1 := by
  rfl

@[simp]
theorem detTerm_eq_matrixEquiv
    [Lean.Grind.Ring R] (M : Hex.Matrix R n n) (perm : Vector (Fin n) n) :
    Hex.Matrix.detTerm M perm =
      Hex.Matrix.detSign perm *
        (List.finRange n).foldl (fun acc i => acc * matrixEquiv M i (perm[i])) 1 := by
  rfl

private theorem foldl_sum_map_start {α : Type u} {S : Type v} [AddCommMonoid S]
    (xs : List α) (f : α → S) (z : S) :
    xs.foldl (fun acc x => acc + f x) z = z + (xs.map f).sum := by
  induction xs generalizing z with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih (z + f x)]
      simp [add_assoc]

private theorem foldl_sum_map {α : Type u} {S : Type v} [AddCommMonoid S]
    (xs : List α) (f : α → S) :
    xs.foldl (fun acc x => acc + f x) 0 = (xs.map f).sum := by
  simpa using foldl_sum_map_start xs f (0 : S)

private theorem foldl_prod_map_start {α : Type u} {S : Type v} [CommMonoid S]
    (xs : List α) (f : α → S) (z : S) :
    xs.foldl (fun acc x => acc * f x) z = z * (xs.map f).prod := by
  induction xs generalizing z with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih (z * f x)]
      simp [mul_assoc]

private theorem foldl_prod_finRange {S : Type u} [CommMonoid S] {n : Nat}
    (f : Fin n → S) :
    (List.finRange n).foldl (fun acc i => acc * f i) 1 = ∏ i, f i := by
  rw [foldl_prod_map_start]
  simp only [one_mul]
  rw [← List.prod_toFinset f (List.nodup_finRange n)]
  rw [List.toFinset_finRange]

private theorem prod_perm_inv [CommRing R] (A : Matrix (Fin n) (Fin n) R)
    (σ : Equiv.Perm (Fin n)) :
    (∏ i, A (σ i) i) = ∏ i, A i (σ⁻¹ i) := by
  refine Finset.prod_bij (fun i _ => σ i) ?_ ?_ ?_ ?_
  · intro i hi
    simp
  · intro i hi j hj hij
    exact σ.injective hij
  · intro j hj
    refine ⟨σ⁻¹ j, by simp, ?_⟩
    simp
  · intro i hi
    simp

private theorem det_apply_row [CommRing R] (A : Matrix (Fin n) (Fin n) R) :
    A.det = ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : Int) : R) * ∏ i, A i (σ i) := by
  rw [Matrix.det_apply']
  refine Finset.sum_bij (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp
  · intro σ hσ τ hτ h
    exact inv_injective h
  · intro τ hτ
    refine ⟨τ⁻¹, by simp, ?_⟩
    simp
  · intro σ hσ
    rw [Equiv.Perm.sign_inv]
    simp [prod_perm_inv]

private theorem equivs_toFinset (n : Nat) :
    (PermutationVector.equivs n).toFinset =
      (Finset.univ : Finset (Equiv.Perm (Fin n))) := by
  ext σ
  simp [PermutationVector.equivs_complete]

theorem det_eq [CommRing R] (M : Hex.Matrix R n n) :
    Hex.Matrix.det M = Matrix.det (matrixEquiv M) := by
  let term : Equiv.Perm (Fin n) → R := fun σ =>
    ((Equiv.Perm.sign σ : Int) : R) * ∏ i, matrixEquiv M i (σ i)
  have hhex : Hex.Matrix.det M = (PermutationVector.equivs n).toFinset.sum term := by
    unfold Hex.Matrix.det
    rw [foldl_sum_map]
    calc
      ((Hex.Matrix.permutationVectors n).map (Hex.Matrix.detTerm M)).sum =
          ((Hex.Matrix.permutationVectors n).attach.map fun p =>
            Hex.Matrix.detTerm M p.1).sum := by
            rw [List.attach_map_val]
      _ = ((Hex.Matrix.permutationVectors n).attach.map fun p =>
            term (PermutationVector.toPerm p.1
              (Hex.Matrix.permutationVectors_nodup p.2))).sum := by
            congr 1
            apply List.map_congr_left
            intro p hp
            dsimp [term]
            rw [detTerm_eq_matrixEquiv]
            rw [PermutationVector.detSign_eq_permSign
              (hnodup := Hex.Matrix.permutationVectors_nodup p.2)]
            rw [foldl_prod_finRange]
            simp [PermutationVector.toPerm_apply]
      _ = ((PermutationVector.equivs n).map term).sum := by
            rw [PermutationVector.equivs]
            rw [List.map_map]
            apply congrArg List.sum
            apply List.map_congr_left
            intro p hp
            rfl
      _ = (PermutationVector.equivs n).toFinset.sum term := by
            exact (List.sum_toFinset term (PermutationVector.equivs_nodup n)).symm
  rw [hhex, det_apply_row]
  rw [equivs_toFinset]

/-- `matrixEquiv` sends Hex leading prefixes to Mathlib submatrices. -/
theorem matrixEquiv_leadingPrefix
    (M : Hex.Matrix R n n) (k : Nat) (hk : k ≤ n) :
    matrixEquiv (Hex.Matrix.leadingPrefix M k hk) =
      (matrixEquiv M).submatrix
        (fun r : Fin k => ⟨r.val, Nat.lt_of_lt_of_le r.isLt hk⟩)
        (fun c : Fin k => ⟨c.val, Nat.lt_of_lt_of_le c.isLt hk⟩) := by
  ext r c
  simp [Hex.Matrix.leadingPrefix, Hex.Matrix.ofFn]

/-- `matrixEquiv` sends Hex bordered Bareiss minors to Mathlib submatrices. -/
theorem matrixEquiv_borderedMinor
    (M : Hex.Matrix R n n) (k : Nat) (hk : k < n) (i j : Fin n) :
    matrixEquiv (Hex.Matrix.borderedMinor M k hk i j) =
      (matrixEquiv M).submatrix
        (fun r : Fin (k + 1) =>
          if hr : r.val < k then ⟨r.val, Nat.lt_trans hr hk⟩ else i)
        (fun c : Fin (k + 1) =>
          if hc : c.val < k then ⟨c.val, Nat.lt_trans hc hk⟩ else j) := by
  ext r c
  simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn]

/-- Determinant form of `matrixEquiv_leadingPrefix`. -/
theorem det_leadingPrefix_eq_submatrix_det [CommRing R]
    (M : Hex.Matrix R n n) (k : Nat) (hk : k ≤ n) :
    Hex.Matrix.det (Hex.Matrix.leadingPrefix M k hk) =
      Matrix.det
        ((matrixEquiv M).submatrix
          (fun r : Fin k => ⟨r.val, Nat.lt_of_lt_of_le r.isLt hk⟩)
          (fun c : Fin k => ⟨c.val, Nat.lt_of_lt_of_le c.isLt hk⟩)) := by
  rw [det_eq, matrixEquiv_leadingPrefix]

/-- Determinant form of `matrixEquiv_borderedMinor`. -/
theorem det_borderedMinor_eq_submatrix_det [CommRing R]
    (M : Hex.Matrix R n n) (k : Nat) (hk : k < n) (i j : Fin n) :
    Hex.Matrix.det (Hex.Matrix.borderedMinor M k hk i j) =
      Matrix.det
        ((matrixEquiv M).submatrix
          (fun r : Fin (k + 1) =>
            if hr : r.val < k then ⟨r.val, Nat.lt_trans hr hk⟩ else i)
          (fun c : Fin (k + 1) =>
            if hc : c.val < k then ⟨c.val, Nat.lt_trans hc hk⟩ else j)) := by
  rw [det_eq, matrixEquiv_borderedMinor]

/-- Reindex the `(k+2) × (k+2)` bordered minor so Desnanot-Jacobi deletes the
Bareiss pivot row/column first and the trailing row/column last.

The order is `[k, 0, 1, ..., k-1, k+1]` in the original bordered-minor
coordinates. Applying the same permutation to rows and columns preserves the
determinant and makes the Desnanot interior the previous leading pivot. -/
def bareissDesnanotIndex (k : Nat) : Fin (k + 2) ≃ Fin (k + 2) where
  toFun r :=
    if hzero : r.val = 0 then
      ⟨k, by omega⟩
    else if hlast : r.val = k + 1 then
      Fin.last (k + 1)
    else
      ⟨r.val - 1, by omega⟩
  invFun r :=
    if hk : r.val = k then
      0
    else if hlt : r.val < k then
      ⟨r.val + 1, by omega⟩
    else
      Fin.last (k + 1)
  left_inv r := by
    ext
    dsimp
    by_cases hzero : r.val = 0
    · simp [hzero]
    · by_cases hlast : r.val = k + 1
      · simp [hlast]
      · have hlt : r.val - 1 < k := by omega
        have hne : r.val - 1 ≠ k := by omega
        simp [hzero, hlast, hlt, hne]
        omega
  right_inv r := by
    ext
    dsimp
    by_cases hk : r.val = k
    · simp [hk]
    · by_cases hlt : r.val < k
      · have hsucc_ne_last : r.val + 1 ≠ k + 1 := by omega
        simp [hk, hlt]
      · have hlast : r.val = k + 1 := by omega
        simp [hlast]

@[simp]
theorem bareissDesnanotIndex_zero (k : Nat) :
    bareissDesnanotIndex k 0 = (⟨k, by omega⟩ : Fin (k + 2)) := by
  rfl

@[simp]
theorem bareissDesnanotIndex_last (k : Nat) :
    bareissDesnanotIndex k (Fin.last (k + 1)) = Fin.last (k + 1) := by
  simp [bareissDesnanotIndex]

/-- Reindexing a bordered minor by `bareissDesnanotIndex` on both axes does not
change its determinant. -/
theorem det_borderedMinor_bareissDesnanotIndex [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n)
    (i j : Fin n) :
    ((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).det =
      Hex.Matrix.det (Hex.Matrix.borderedMinor source (k + 1) hnext i j) := by
  rw [Matrix.det_submatrix_equiv_self, ← det_eq]

/-- Desnanot-Jacobi specialized to a Bareiss bordered minor after the row/column
reindexing used by `bareissDesnanotIndex`.

This is the Mathlib determinant identity that later proofs rewrite through
`matrixEquiv_borderedMinor`/`det_borderedMinor_eq_submatrix_det` to obtain the
`hdesnanot` hypothesis for `bareissExactDiv_borderedMinor_of_mul_eq`. -/
theorem desnanot_jacobi_borderedMinor_reindex [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n)
    (i j : Fin n) :
    let M : Matrix (Fin (k + 2)) (Fin (k + 2)) R :=
      (matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)
    M.det *
        (M.submatrix (Fin.succAbove 0 ∘ (Fin.last k).succAbove)
          (Fin.succAbove 0 ∘ (Fin.last k).succAbove)).det =
      (M.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det *
        (M.submatrix (Fin.last (k + 1)).succAbove
          (Fin.last (k + 1)).succAbove).det -
      (M.submatrix (Fin.succAbove 0) (Fin.last (k + 1)).succAbove).det *
        (M.submatrix (Fin.last (k + 1)).succAbove (Fin.succAbove 0)).det := by
  intro M
  exact desnanot_jacobi M

/-- Exact-division bridge for one Bareiss bordered-minor update.

The remaining Mathlib-side recurrence proof can supply `hdesnanot` from the
Desnanot-Jacobi identity; this lemma packages the resulting product identity
as the `hexact` premise expected by `Hex.Matrix.stepMatrix_borderedMinor_update`.
-/
theorem bareissExactDiv_borderedMinor_of_mul_eq
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val) (prevPivot : Int)
    (hprev_ne : prevPivot ≠ 0)
    (hdesnanot :
      Hex.Matrix.det (Hex.Matrix.borderedMinor source (k + 1) hnext i j) * prevPivot =
        Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk i j) -
          Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
            i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j)) :
    Hex.Matrix.exactDiv
        (Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk i j) -
          Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
            i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
        prevPivot =
      Hex.Matrix.det (Hex.Matrix.borderedMinor source (k + 1) hnext i j) := by
  let nextMinor := Hex.Matrix.det (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
  let numerator :=
    Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
        (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
        (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
      Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk i j) -
      Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
        i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
      Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
        (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j)
  have hnum : numerator = prevPivot * nextMinor := by
    dsimp [numerator, nextMinor]
    rw [← hdesnanot, mul_comm]
  have hdvd : prevPivot ∣ numerator := ⟨nextMinor, hnum⟩
  rw [Hex.Matrix.exactDiv_eq_divExact hdvd]
  change numerator / prevPivot = nextMinor
  exact Int.ediv_eq_of_eq_mul_right hprev_ne hnum

/-- Cyclic shift on `Fin (k + 1)` mapping `0 ↦ k`, `r ↦ r - 1` for `r ≥ 1`.

This is the row/column rearrangement induced by `bareissDesnanotIndex k` on the
sub-positions selected by `(Fin.last (k + 1)).succAbove`: it carries the Bareiss
pivot row (originally position `k`) from sub-position `0` back to the trailing
sub-position `k`. The same shift compares `bareissDesnanotIndex k` columns with
the natural bordered-minor column order. Defined as the inverse of Mathlib's
`finRotate (k + 1)` so the sign is available immediately. -/
private def bareissCyclicShift (k : Nat) : Fin (k + 1) ≃ Fin (k + 1) :=
  (finRotate (k + 1)).symm

@[simp]
private theorem bareissCyclicShift_apply_zero (k : Nat) :
    bareissCyclicShift k 0 = (Fin.last k : Fin (k + 1)) := by
  show (finRotate (k + 1)).symm 0 = Fin.last k
  rw [Equiv.symm_apply_eq]
  exact finRotate_last.symm

private theorem bareissCyclicShift_apply_of_pos (k : Nat) (r : Fin (k + 1))
    (h : 0 < r.val) :
    bareissCyclicShift k r = (⟨r.val - 1, by omega⟩ : Fin (k + 1)) := by
  have hne : r ≠ 0 := by
    intro h_eq
    rw [h_eq] at h
    exact absurd h (Nat.lt_irrefl _)
  have : NeZero (k + 1) := ⟨Nat.succ_ne_zero _⟩
  ext
  show ((finRotate (k + 1)).symm r : ℕ) = r.val - 1
  exact coe_finRotate_symm_of_ne_zero hne

/-- Sign of the cyclic shift: `(-1)^k`. -/
private theorem sign_bareissCyclicShift (k : Nat) :
    Equiv.Perm.sign (bareissCyclicShift k) = (-1) ^ k := by
  show Equiv.Perm.sign (finRotate (k + 1)).symm = _
  rw [Equiv.Perm.sign_symm]
  exact sign_finRotate k

/-- The entry formula for a Bareiss-reindexed bordered minor: the position
returned by `bareissDesnanotIndex k s.succ` is either an interior source row
(when `s.val < k`) or the trailing row `i` (when `s.val = k`). -/
private theorem bareissDesnanotIndex_succ_lt (k : Nat) (s : Fin (k + 1))
    (hs : s.val < k) :
    bareissDesnanotIndex k s.succ = (⟨s.val, by omega⟩ : Fin (k + 2)) := by
  show (if hzero : s.succ.val = 0 then (⟨k, by omega⟩ : Fin (k + 2))
        else if hlast : s.succ.val = k + 1 then Fin.last (k + 1)
        else ⟨s.succ.val - 1, by omega⟩) = _
  have hzero : s.succ.val ≠ 0 := Nat.succ_ne_zero _
  have hne_last : s.succ.val ≠ k + 1 := by
    show s.val + 1 ≠ k + 1; omega
  rw [dif_neg hzero, dif_neg hne_last]
  ext
  show s.succ.val - 1 = s.val
  simp

private theorem bareissDesnanotIndex_succ_top (k : Nat) (s : Fin (k + 1))
    (hs : s.val = k) :
    bareissDesnanotIndex k s.succ = Fin.last (k + 1) := by
  show (if hzero : s.succ.val = 0 then (⟨k, by omega⟩ : Fin (k + 2))
        else if hlast : s.succ.val = k + 1 then Fin.last (k + 1)
        else ⟨s.succ.val - 1, by omega⟩) = _
  have hzero : s.succ.val ≠ 0 := Nat.succ_ne_zero _
  have hlast : s.succ.val = k + 1 := by
    show s.val + 1 = k + 1; omega
  rw [dif_neg hzero, dif_pos hlast]

private theorem bareissDesnanotIndex_castSucc_zero (k : Nat) (s : Fin (k + 1))
    (hs : s.val = 0) :
    bareissDesnanotIndex k s.castSucc = (⟨k, by omega⟩ : Fin (k + 2)) := by
  show (if hzero : s.castSucc.val = 0 then (⟨k, by omega⟩ : Fin (k + 2))
        else if hlast : s.castSucc.val = k + 1 then Fin.last (k + 1)
        else ⟨s.castSucc.val - 1, by omega⟩) = _
  have hzero' : s.castSucc.val = 0 := hs
  rw [dif_pos hzero']

private theorem bareissDesnanotIndex_castSucc_pos (k : Nat) (s : Fin (k + 1))
    (hs : 0 < s.val) :
    bareissDesnanotIndex k s.castSucc = (⟨s.val - 1, by omega⟩ : Fin (k + 2)) := by
  have hcv : s.castSucc.val = s.val := rfl
  show (if hzero : s.castSucc.val = 0 then (⟨k, by omega⟩ : Fin (k + 2))
        else if hlast : s.castSucc.val = k + 1 then Fin.last (k + 1)
        else ⟨s.castSucc.val - 1, by omega⟩) = _
  have hne_zero : s.castSucc.val ≠ 0 := by rw [hcv]; exact Nat.ne_of_gt hs
  have hne_last : s.castSucc.val ≠ k + 1 := by
    rw [hcv]; exact Nat.ne_of_lt (by have := s.isLt; omega)
  rw [dif_neg hne_zero, dif_neg hne_last]
  ext
  show s.castSucc.val - 1 = s.val - 1
  rw [hcv]

/-- Source-row index returned by `bareissDesnanotIndex k r.succ` from `r : Fin (k+1)`:
`r.val` for interior `r.val < k`, `i` when `r.val = k`. -/
private theorem source_row_of_succ [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n) (i j : Fin n)
    (r : Fin (k + 1)) :
    ∀ (c : Fin (k + 1)),
      matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k r.succ) (bareissDesnanotIndex k c.succ) =
      (let rr : Fin n := if hr : r.val < k then ⟨r.val, by omega⟩ else i
       let cc : Fin n := if hc : c.val < k then ⟨c.val, by omega⟩ else j
       source[rr][cc]) := by
  intro c
  have hkn : k < n := Nat.lt_of_succ_lt hnext
  by_cases hr : r.val < k <;> by_cases hc : c.val < k
  · rw [bareissDesnanotIndex_succ_lt k r hr, bareissDesnanotIndex_succ_lt k c hc]
    have hri : (⟨r.val, by omega⟩ : Fin (k + 2)).val < k + 1 := by show r.val < k + 1; omega
    have hci : (⟨c.val, by omega⟩ : Fin (k + 2)).val < k + 1 := by show c.val < k + 1; omega
    rw [show (matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
            (⟨r.val, by omega⟩ : Fin (k + 2)) (⟨c.val, by omega⟩ : Fin (k + 2)) : R) =
          (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
            (⟨r.val, by omega⟩ : Fin (k + 2))][(⟨c.val, by omega⟩ : Fin (k + 2))] from rfl]
    rw [Hex.Matrix.borderedMinor_entry_lt_lt source (k + 1) hnext i j _ _ hri hci]
    simp [hr, hc]
  · have hc_eq : c.val = k := by have := c.isLt; omega
    rw [bareissDesnanotIndex_succ_lt k r hr, bareissDesnanotIndex_succ_top k c hc_eq]
    have hri : (⟨r.val, by omega⟩ : Fin (k + 2)).val < k + 1 := by show r.val < k + 1; omega
    rw [show (matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
            (⟨r.val, by omega⟩ : Fin (k + 2)) (Fin.last (k + 1)) : R) =
          (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
            (⟨r.val, by omega⟩ : Fin (k + 2))][Fin.last (k + 1)] from rfl]
    rw [Hex.Matrix.borderedMinor_entry_lt_last source (k + 1) hnext i j _ hri]
    simp [hr, hc]
  · have hr_eq : r.val = k := by have := r.isLt; omega
    rw [bareissDesnanotIndex_succ_top k r hr_eq, bareissDesnanotIndex_succ_lt k c hc]
    have hci : (⟨c.val, by omega⟩ : Fin (k + 2)).val < k + 1 := by show c.val < k + 1; omega
    rw [show (matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
            (Fin.last (k + 1)) (⟨c.val, by omega⟩ : Fin (k + 2)) : R) =
          (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
            Fin.last (k + 1)][(⟨c.val, by omega⟩ : Fin (k + 2))] from rfl]
    rw [Hex.Matrix.borderedMinor_entry_last_lt source (k + 1) hnext i j _ hci]
    simp [hr, hc]
  · have hr_eq : r.val = k := by have := r.isLt; omega
    have hc_eq : c.val = k := by have := c.isLt; omega
    rw [bareissDesnanotIndex_succ_top k r hr_eq, bareissDesnanotIndex_succ_top k c hc_eq]
    rw [show (matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
            (Fin.last (k + 1)) (Fin.last (k + 1)) : R) =
          (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
            Fin.last (k + 1)][Fin.last (k + 1)] from rfl]
    rw [Hex.Matrix.borderedMinor_entry_last_last]
    simp [hr, hc]

private theorem source_row_of_borderedMinor [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (i j : Fin n)
    (r c : Fin (k + 1)) :
    matrixEquiv (Hex.Matrix.borderedMinor source k hk i j) r c =
      (let rr : Fin n := if hr : r.val < k then ⟨r.val, by omega⟩ else i
       let cc : Fin n := if hc : c.val < k then ⟨c.val, by omega⟩ else j
       source[rr][cc]) := by
  show (Hex.Matrix.borderedMinor source k hk i j)[r][c] = _
  simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn]

/-- For row positions `r.castSucc` (i.e. column `(Fin.last (k + 1)).succAbove r`),
the entry at `bareissDesnanotIndex k r.castSucc` lands in the interior of the
`(k+2)` bordered minor: source row `k` for `r = 0`, source row `r.val - 1` for
`r.val ≥ 1`. Same for columns. -/
private theorem source_row_of_castSucc [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n) (i j : Fin n)
    (r c : Fin (k + 1)) :
    matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k r.castSucc) (bareissDesnanotIndex k c.castSucc) =
      (let rr : Fin n := if r.val = 0 then ⟨k, by omega⟩ else ⟨r.val - 1, by omega⟩
       let cc : Fin n := if c.val = 0 then ⟨k, by omega⟩ else ⟨c.val - 1, by omega⟩
       source[rr][cc]) := by
  by_cases hr : r.val = 0 <;> by_cases hc : c.val = 0
  · rw [bareissDesnanotIndex_castSucc_zero k r hr,
        bareissDesnanotIndex_castSucc_zero k c hc]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨k, by omega⟩ : Fin (k + 2))][(⟨k, by omega⟩ : Fin (k + 2))] = _
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc]
  · have hcpos : 0 < c.val := Nat.pos_of_ne_zero hc
    rw [bareissDesnanotIndex_castSucc_zero k r hr,
        bareissDesnanotIndex_castSucc_pos k c hcpos]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨k, by omega⟩ : Fin (k + 2))][(⟨c.val - 1, by omega⟩ : Fin (k + 2))] = _
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc]
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
    rw [bareissDesnanotIndex_castSucc_pos k r hrpos,
        bareissDesnanotIndex_castSucc_zero k c hc]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val - 1, by omega⟩ : Fin (k + 2))][(⟨k, by omega⟩ : Fin (k + 2))] = _
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc]
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
    have hcpos : 0 < c.val := Nat.pos_of_ne_zero hc
    rw [bareissDesnanotIndex_castSucc_pos k r hrpos,
        bareissDesnanotIndex_castSucc_pos k c hcpos]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val - 1, by omega⟩ : Fin (k + 2))][(⟨c.val - 1, by omega⟩ : Fin (k + 2))] = _
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc]

/-- Mixed `succ`/`castSucc` source-row helper used for `M_1k`. -/
private theorem source_row_of_succ_castSucc [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n) (i j : Fin n)
    (r c : Fin (k + 1)) :
    matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k r.succ) (bareissDesnanotIndex k c.castSucc) =
      (let rr : Fin n := if hr : r.val < k then ⟨r.val, by omega⟩ else i
       let cc : Fin n := if c.val = 0 then ⟨k, by omega⟩ else ⟨c.val - 1, by omega⟩
       source[rr][cc]) := by
  by_cases hr : r.val < k <;> by_cases hc : c.val = 0
  · rw [bareissDesnanotIndex_succ_lt k r hr, bareissDesnanotIndex_castSucc_zero k c hc]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val, by omega⟩ : Fin (k + 2))][(⟨k, by omega⟩ : Fin (k + 2))] = _
    have hrle : r.val ≤ k := hr.le
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc, hrle]
  · have hcpos : 0 < c.val := Nat.pos_of_ne_zero hc
    rw [bareissDesnanotIndex_succ_lt k r hr, bareissDesnanotIndex_castSucc_pos k c hcpos]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val, by omega⟩ : Fin (k + 2))][(⟨c.val - 1, by omega⟩ : Fin (k + 2))] = _
    have hrle : r.val ≤ k := hr.le
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc, hrle]
  · have hr_eq : r.val = k := by have := r.isLt; omega
    rw [bareissDesnanotIndex_succ_top k r hr_eq, bareissDesnanotIndex_castSucc_zero k c hc]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        Fin.last (k + 1)][(⟨k, by omega⟩ : Fin (k + 2))] = _
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc]
  · have hr_eq : r.val = k := by have := r.isLt; omega
    have hcpos : 0 < c.val := Nat.pos_of_ne_zero hc
    rw [bareissDesnanotIndex_succ_top k r hr_eq, bareissDesnanotIndex_castSucc_pos k c hcpos]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        Fin.last (k + 1)][(⟨c.val - 1, by omega⟩ : Fin (k + 2))] = _
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc]

/-- Mixed `castSucc`/`succ` source-row helper used for `M_k1`. -/
private theorem source_row_of_castSucc_succ [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n) (i j : Fin n)
    (r c : Fin (k + 1)) :
    matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k r.castSucc) (bareissDesnanotIndex k c.succ) =
      (let rr : Fin n := if r.val = 0 then ⟨k, by omega⟩ else ⟨r.val - 1, by omega⟩
       let cc : Fin n := if hc : c.val < k then ⟨c.val, by omega⟩ else j
       source[rr][cc]) := by
  by_cases hr : r.val = 0 <;> by_cases hc : c.val < k
  · rw [bareissDesnanotIndex_castSucc_zero k r hr, bareissDesnanotIndex_succ_lt k c hc]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨k, by omega⟩ : Fin (k + 2))][(⟨c.val, by omega⟩ : Fin (k + 2))] = _
    have hcle : c.val ≤ k := hc.le
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc, hcle]
  · have hc_eq : c.val = k := by have := c.isLt; omega
    rw [bareissDesnanotIndex_castSucc_zero k r hr, bareissDesnanotIndex_succ_top k c hc_eq]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨k, by omega⟩ : Fin (k + 2))][Fin.last (k + 1)] = _
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc]
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
    rw [bareissDesnanotIndex_castSucc_pos k r hrpos, bareissDesnanotIndex_succ_lt k c hc]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val - 1, by omega⟩ : Fin (k + 2))][(⟨c.val, by omega⟩ : Fin (k + 2))] = _
    have hcle : c.val ≤ k := hc.le
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc, hcle]
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
    have hc_eq : c.val = k := by have := c.isLt; omega
    rw [bareissDesnanotIndex_castSucc_pos k r hrpos, bareissDesnanotIndex_succ_top k c hc_eq]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val - 1, by omega⟩ : Fin (k + 2))][Fin.last (k + 1)] = _
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc]

/-- The Fin-valued cyclic shift on `Fin (k+1)` agrees with the
position-indexing-by-cases used in `source_row_of_castSucc`. -/
private theorem fin_n_cyclicShift_eq_castSucc_index (k : Nat) (hk : k < n)
    (r : Fin (k + 1)) :
    (if r.val = 0 then (⟨k, hk⟩ : Fin n) else ⟨r.val - 1, by omega⟩) =
    (if h : (bareissCyclicShift k r).val < k then (⟨(bareissCyclicShift k r).val, by omega⟩ : Fin n)
     else ⟨k, hk⟩) := by
  by_cases hr : r.val = 0
  · have hr0 : r = 0 := Fin.ext hr
    have hbs : bareissCyclicShift k r = (Fin.last k : Fin (k + 1)) := by
      rw [hr0]; exact bareissCyclicShift_apply_zero k
    have hge : ¬ (bareissCyclicShift k r).val < k := by
      rw [hbs]; show ¬ k < k; exact Nat.lt_irrefl _
    rw [if_pos hr, dif_neg hge]
  · have hpos : 0 < r.val := Nat.pos_of_ne_zero hr
    have hbs : bareissCyclicShift k r = (⟨r.val - 1, by omega⟩ : Fin (k + 1)) :=
      bareissCyclicShift_apply_of_pos k r hpos
    have hbs_val : (bareissCyclicShift k r).val = r.val - 1 := by rw [hbs]
    have hlt : (bareissCyclicShift k r).val < k := by
      rw [hbs_val]; have := r.isLt; omega
    rw [if_neg hr, dif_pos hlt]
    apply Fin.ext
    show r.val - 1 = (bareissCyclicShift k r).val
    rw [hbs_val]

/-- After reindexing by `bareissDesnanotIndex k`, deleting the last row and
column yields the natural `(k+1)` bordered minor of `source` with the original
pivot row/column position `⟨k, _⟩` (i.e. the leading prefix of `source` of size
`k+1`), reindexed by the cyclic shift `bareissCyclicShift k`. -/
private theorem M_kk_eq_matrixEquiv_borderedMinor_submatrix [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) :
    (((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).submatrix
        (Fin.succAbove (Fin.last (k + 1))) (Fin.succAbove (Fin.last (k + 1)))) =
      (matrixEquiv (Hex.Matrix.borderedMinor source k hk
        (⟨k, hk⟩ : Fin n) (⟨k, hk⟩ : Fin n))).submatrix
        (bareissCyclicShift k) (bareissCyclicShift k) := by
  ext r c
  show matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k (Fin.succAbove (Fin.last (k + 1)) r))
        (bareissDesnanotIndex k (Fin.succAbove (Fin.last (k + 1)) c)) =
      matrixEquiv (Hex.Matrix.borderedMinor source k hk ⟨k, hk⟩ ⟨k, hk⟩)
        (bareissCyclicShift k r) (bareissCyclicShift k c)
  simp only [Fin.succAbove_last]
  rw [source_row_of_castSucc source k hnext i j r c,
      source_row_of_borderedMinor source k hk ⟨k, hk⟩ ⟨k, hk⟩
        (bareissCyclicShift k r) (bareissCyclicShift k c)]
  dsimp only
  simp only [fin_n_cyclicShift_eq_castSucc_index k hk r,
             fin_n_cyclicShift_eq_castSucc_index k hk c]

/-- After reindexing by `bareissDesnanotIndex k`, deleting row 0 and the last
column yields the natural `(k+1)` bordered minor with trailing row `i` and
trailing column position `⟨k, _⟩`, with columns reindexed by
`bareissCyclicShift k`. -/
private theorem M_1k_eq_matrixEquiv_borderedMinor_submatrix [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) :
    (((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).submatrix
        (Fin.succAbove (0 : Fin (k + 2))) (Fin.succAbove (Fin.last (k + 1)))) =
      (matrixEquiv (Hex.Matrix.borderedMinor source k hk i (⟨k, hk⟩ : Fin n))).submatrix
        id (bareissCyclicShift k) := by
  ext r c
  show matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k (Fin.succAbove (0 : Fin (k + 2)) r))
        (bareissDesnanotIndex k (Fin.succAbove (Fin.last (k + 1)) c)) =
      matrixEquiv (Hex.Matrix.borderedMinor source k hk i ⟨k, hk⟩)
        r (bareissCyclicShift k c)
  rw [show Fin.succAbove (0 : Fin (k + 2)) r = r.succ from rfl]
  simp only [Fin.succAbove_last]
  rw [source_row_of_succ_castSucc source k hnext i j r c,
      source_row_of_borderedMinor source k hk i ⟨k, hk⟩ r (bareissCyclicShift k c)]
  dsimp only
  simp only [fin_n_cyclicShift_eq_castSucc_index k hk c]

/-- After reindexing by `bareissDesnanotIndex k`, deleting the last row and
column 0 yields the natural `(k+1)` bordered minor with trailing row position
`⟨k, _⟩` and trailing column `j`, with rows reindexed by
`bareissCyclicShift k`. -/
private theorem M_k1_eq_matrixEquiv_borderedMinor_submatrix [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) :
    (((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).submatrix
        (Fin.succAbove (Fin.last (k + 1))) (Fin.succAbove (0 : Fin (k + 2)))) =
      (matrixEquiv (Hex.Matrix.borderedMinor source k hk (⟨k, hk⟩ : Fin n) j)).submatrix
        (bareissCyclicShift k) id := by
  ext r c
  show matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k (Fin.succAbove (Fin.last (k + 1)) r))
        (bareissDesnanotIndex k (Fin.succAbove (0 : Fin (k + 2)) c)) =
      matrixEquiv (Hex.Matrix.borderedMinor source k hk ⟨k, hk⟩ j)
        (bareissCyclicShift k r) c
  rw [show Fin.succAbove (0 : Fin (k + 2)) c = c.succ from rfl]
  simp only [Fin.succAbove_last]
  rw [source_row_of_castSucc_succ source k hnext i j r c,
      source_row_of_borderedMinor source k hk ⟨k, hk⟩ j (bareissCyclicShift k r) c]
  dsimp only
  simp only [fin_n_cyclicShift_eq_castSucc_index k hk r]

/-- After reindexing the `(k+2)` bordered minor by `bareissDesnanotIndex k`,
deleting row 0 and column 0 yields exactly `matrixEquiv` of the natural
`(k+1)` bordered minor with the same trailing row `i` and column `j`. -/
private theorem M11_eq_matrixEquiv_borderedMinor [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) :
    (((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).submatrix
        (Fin.succAbove (0 : Fin (k + 2))) (Fin.succAbove (0 : Fin (k + 2)))) =
      matrixEquiv (Hex.Matrix.borderedMinor source k hk i j) := by
  ext r c
  show matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k (Fin.succAbove (0 : Fin (k + 2)) r))
        (bareissDesnanotIndex k (Fin.succAbove (0 : Fin (k + 2)) c)) =
      matrixEquiv (Hex.Matrix.borderedMinor source k hk i j) r c
  rw [show Fin.succAbove (0 : Fin (k + 2)) r = r.succ from rfl,
      show Fin.succAbove (0 : Fin (k + 2)) c = c.succ from rfl,
      source_row_of_succ source k hnext i j r c,
      source_row_of_borderedMinor source k hk i j r c]

end HexMatrixMathlib
