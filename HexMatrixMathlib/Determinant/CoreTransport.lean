module

public import HexMatrixMathlib.Basic
public import HexMatrixMathlib.Determinant.DesnanotJacobi
public import HexMatrix.Bareiss
public import HexMatrix.Determinant
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace HexMatrixMathlib
universe u v
variable {R : Type u} {n : Nat}

namespace PermutationVector

theorem get_injective_of_nodup
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
@[expose]
noncomputable def toPerm (perm : Vector (Fin n) n)
    (hnodup : perm.toList.Nodup) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i : Fin n => perm[i])
    ⟨get_injective_of_nodup hnodup,
      Finite.surjective_of_injective (get_injective_of_nodup hnodup)⟩

@[simp, grind =]
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

theorem vectorOfPerm_nodup (σ : Equiv.Perm (Fin n)) :
    (Vector.ofFn fun i : Fin n => σ i).toList.Nodup := by
  rw [vectorOfPerm_toList]
  exact List.Nodup.map σ.injective (List.nodup_finRange n)

theorem toPerm_vectorOfPerm (σ : Equiv.Perm (Fin n)) :
    toPerm (Vector.ofFn fun i : Fin n => σ i) (vectorOfPerm_nodup σ) = σ := by
  ext i
  simp [toPerm]

/-- Hex permutation vectors converted to Mathlib permutations, with proofs attached. -/
@[expose]
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

@[simp, grind =]
theorem detProduct_eq_matrixEquiv
    [Lean.Grind.Ring R] (M : Hex.Matrix R n n) (perm : Vector (Fin n) n) :
    Hex.Matrix.detProduct M perm =
      (List.finRange n).foldl (fun acc i => acc * matrixEquiv M i (perm[i])) 1 := by
  rfl

@[simp, grind =]
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

/-- Deleting a row and column in the Hex matrix representation is the same as
submatrixing the Mathlib representation by the corresponding skip maps. -/
theorem matrixEquiv_deleteRowCol
    (M : Hex.Matrix R (n + 1) (n + 1)) (row col : Fin (n + 1)) :
    matrixEquiv (Hex.Matrix.deleteRowCol M row col) =
      (matrixEquiv M).submatrix (Hex.Matrix.skipIndex row) (Hex.Matrix.skipIndex col) := by
  ext i j
  change (Hex.Matrix.deleteRowCol M row col)[i][j] =
    M[Hex.Matrix.skipIndex row i][Hex.Matrix.skipIndex col j]
  rw [Hex.Matrix.deleteRowCol_entry]

private theorem matrixEquiv_deleteRowCol_zero_zero
    (M : Hex.Matrix R (n + 2) (n + 2)) :
    matrixEquiv (Hex.Matrix.deleteRowCol M 0 0) =
      (matrixEquiv M).submatrix (Fin.succAbove 0) (Fin.succAbove 0) := by
  rw [matrixEquiv_deleteRowCol]
  ext i j
  rfl

private theorem matrixEquiv_deleteRowCol_last_last
    (M : Hex.Matrix R (n + 2) (n + 2)) :
    matrixEquiv (Hex.Matrix.deleteRowCol M (Fin.last (n + 1)) (Fin.last (n + 1))) =
      (matrixEquiv M).submatrix
        (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove := by
  rw [matrixEquiv_deleteRowCol]
  ext i j
  rfl

private theorem matrixEquiv_deleteRowCol_zero_last
    (M : Hex.Matrix R (n + 2) (n + 2)) :
    matrixEquiv (Hex.Matrix.deleteRowCol M 0 (Fin.last (n + 1))) =
      (matrixEquiv M).submatrix (Fin.succAbove 0) (Fin.last (n + 1)).succAbove := by
  rw [matrixEquiv_deleteRowCol]
  ext i j
  rfl

private theorem matrixEquiv_deleteRowCol_last_zero
    (M : Hex.Matrix R (n + 2) (n + 2)) :
    matrixEquiv (Hex.Matrix.deleteRowCol M (Fin.last (n + 1)) 0) =
      (matrixEquiv M).submatrix (Fin.last (n + 1)).succAbove (Fin.succAbove 0) := by
  rw [matrixEquiv_deleteRowCol]
  ext i j
  rfl

private theorem matrixEquiv_deleteRowCol_zero_zero_last_last
    (M : Hex.Matrix R (n + 2) (n + 2)) :
    matrixEquiv
        (Hex.Matrix.deleteRowCol (Hex.Matrix.deleteRowCol M 0 0)
          (Fin.last n) (Fin.last n)) =
      (matrixEquiv M).submatrix
        (Fin.succAbove 0 ∘ (Fin.last n).succAbove)
        (Fin.succAbove 0 ∘ (Fin.last n).succAbove) := by
  rw [matrixEquiv_deleteRowCol]
  rw [matrixEquiv_deleteRowCol_zero_zero]
  ext i j
  rfl

/-- Endpoint Hex-minor form of Desnanot-Jacobi. Reindex rows and columns first
to use it for an arbitrary two-row/two-column choice. -/
theorem desnanot_jacobi_deleteRowCol_endpoints [CommRing R]
    (M : Hex.Matrix R (n + 2) (n + 2)) :
    Hex.Matrix.det M *
        Hex.Matrix.det
          (Hex.Matrix.deleteRowCol (Hex.Matrix.deleteRowCol M 0 0)
            (Fin.last n) (Fin.last n)) =
      Hex.Matrix.det (Hex.Matrix.deleteRowCol M 0 0) *
        Hex.Matrix.det
          (Hex.Matrix.deleteRowCol M (Fin.last (n + 1)) (Fin.last (n + 1))) -
      Hex.Matrix.det (Hex.Matrix.deleteRowCol M 0 (Fin.last (n + 1))) *
        Hex.Matrix.det (Hex.Matrix.deleteRowCol M (Fin.last (n + 1)) 0) := by
  have hdj := desnanot_jacobi (matrixEquiv M)
  rw [← det_eq M] at hdj
  have hInterior :
      ((matrixEquiv M).submatrix
          (Fin.succAbove 0 ∘ (Fin.last n).succAbove)
          (Fin.succAbove 0 ∘ (Fin.last n).succAbove)).det =
        Hex.Matrix.det
          (Hex.Matrix.deleteRowCol (Hex.Matrix.deleteRowCol M 0 0)
            (Fin.last n) (Fin.last n)) := by
    rw [← matrixEquiv_deleteRowCol_zero_zero_last_last M, ← det_eq]
  have h00 :
      ((matrixEquiv M).submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det =
        Hex.Matrix.det (Hex.Matrix.deleteRowCol M 0 0) := by
    rw [← matrixEquiv_deleteRowCol_zero_zero M, ← det_eq]
  have hLL :
      ((matrixEquiv M).submatrix
          (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove).det =
        Hex.Matrix.det
          (Hex.Matrix.deleteRowCol M (Fin.last (n + 1)) (Fin.last (n + 1))) := by
    rw [← matrixEquiv_deleteRowCol_last_last M, ← det_eq]
  have h0L :
      ((matrixEquiv M).submatrix (Fin.succAbove 0) (Fin.last (n + 1)).succAbove).det =
        Hex.Matrix.det (Hex.Matrix.deleteRowCol M 0 (Fin.last (n + 1))) := by
    rw [← matrixEquiv_deleteRowCol_zero_last M, ← det_eq]
  have hL0 :
      ((matrixEquiv M).submatrix (Fin.last (n + 1)).succAbove (Fin.succAbove 0)).det =
        Hex.Matrix.det (Hex.Matrix.deleteRowCol M (Fin.last (n + 1)) 0) := by
    rw [← matrixEquiv_deleteRowCol_last_zero M, ← det_eq]
  rw [hInterior, h00, hLL, h0L, hL0] at hdj
  exact hdj

/-- Desnanot-Jacobi for an arbitrary pair of rows and columns, expressed as a
row/column reindexing of a Hex matrix and proved in the Mathlib bridge layer.

Consumers choose `row` and `col` so that their two distinguished rows and
columns are sent to `0` and `Fin.last`; the four one-row minors and the
two-row/two-column interior minor are then the displayed submatrices of the
reindexed matrix. -/
theorem desnanot_jacobi_matrixEquiv_reindex [CommRing R]
    (M : Hex.Matrix R (n + 2) (n + 2))
    (row col : Fin (n + 2) ≃ Fin (n + 2)) :
    let A : Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
      (matrixEquiv M).submatrix row col
    A.det *
        (A.submatrix (Fin.succAbove 0 ∘ (Fin.last n).succAbove)
          (Fin.succAbove 0 ∘ (Fin.last n).succAbove)).det =
      (A.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det *
        (A.submatrix (Fin.last (n + 1)).succAbove
          (Fin.last (n + 1)).succAbove).det -
      (A.submatrix (Fin.succAbove 0) (Fin.last (n + 1)).succAbove).det *
        (A.submatrix (Fin.last (n + 1)).succAbove (Fin.succAbove 0)).det := by
  intro A
  exact desnanot_jacobi A

private theorem matrixEquiv_setRow
    (M : Hex.Matrix R (n + 1) (n + 1)) (row : Fin (n + 1))
    (v : Vector R (n + 1)) :
    matrixEquiv (Hex.Matrix.setRow M row v) =
      (matrixEquiv M).updateRow row (fun col => v[col]) := by
  ext i j
  by_cases hi : i = row
  · subst i
    rw [Matrix.updateRow_self]
    exact congrArg (fun rowv => rowv[j])
      (Hex.Matrix.setRow_get_self M row v)
  · rw [Matrix.updateRow_ne hi]
    exact congrArg (fun rowv => rowv[j])
      (Hex.Matrix.setRow_row_ne M row i v hi)

private theorem cofactorSign_eq_neg_one_pow
    [CommRing R] {n : Nat} (row col : Fin (n + 1)) :
    Hex.Matrix.cofactorSign (R := R) row col =
      (-1 : R) ^ (row.val + col.val) := by
  unfold Hex.Matrix.cofactorSign
  by_cases h : (row.val + col.val) % 2 = 0
  · rw [if_pos h]
    exact (Even.neg_one_pow (Nat.even_iff.mpr h)).symm
  · rw [if_neg h]
    have hmod : (row.val + col.val) % 2 = 1 := by omega
    have hodd : Odd (row.val + col.val) := Nat.odd_iff.mpr hmod
    exact (Odd.neg_one_pow hodd).symm

private theorem cofactorSign_consecutive_last_neg
    [CommRing R] {n : Nat} (a : Nat) (ha : a + 1 < n + 1) :
    Hex.Matrix.cofactorSign (R := R)
        (⟨a + 1, ha⟩ : Fin (n + 1)) (Fin.last n) =
      -Hex.Matrix.cofactorSign (R := R)
        (⟨a, by omega⟩ : Fin (n + 1)) (Fin.last n) := by
  rw [cofactorSign_eq_neg_one_pow (R := R)
      (⟨a + 1, ha⟩ : Fin (n + 1)) (Fin.last n)]
  rw [cofactorSign_eq_neg_one_pow (R := R)
      (⟨a, by omega⟩ : Fin (n + 1)) (Fin.last n)]
  show (-1 : R) ^ (a + 1 + n) = -((-1 : R) ^ (a + n))
  rw [show a + 1 + n = (a + n) + 1 by omega, pow_succ]
  ring

private theorem matrixEquiv_adjugate_apply_eq_cofactor
    [CommRing R] (M : Hex.Matrix R (n + 1) (n + 1))
    (row col : Fin (n + 1)) :
    (Matrix.adjugate (matrixEquiv M)) col row = Hex.Matrix.cofactor M row col := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  unfold Hex.Matrix.cofactor
  rw [cofactorSign_eq_neg_one_pow (R := R) row col]
  rw [show Hex.Matrix.det (Hex.Matrix.deleteRowCol M row col) =
      Matrix.det (matrixEquiv (Hex.Matrix.deleteRowCol M row col)) by
        exact det_eq (Hex.Matrix.deleteRowCol M row col)]
  rw [matrixEquiv_deleteRowCol M row col]
  congr 2

private theorem mathlib_det_mul_adjugate_updateRow_of_ne
    [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (r s c : ι) (rowv : ι → R) (hrs : s ≠ r) :
    A.det * Matrix.adjugate (A.updateRow r rowv) c s =
      (A.updateRow r rowv).det * Matrix.adjugate A c s -
        (A.updateRow s rowv).det * Matrix.adjugate A c r := by
  let N : Matrix ι ι R := A.updateRow r rowv
  let adjA : Matrix ι ι R := Matrix.adjugate A
  let adjN : Matrix ι ι R := Matrix.adjugate N
  have hAdj_r : adjN c r = adjA c r := by
    simp [adjN, adjA, N, Matrix.adjugate_apply]
  have hNr :
      (N * adjA) r s = (A.updateRow s rowv).det := by
    rw [Matrix.mul_apply]
    rw [Matrix.det_eq_sum_mul_adjugate_row (A.updateRow s rowv) s]
    apply Finset.sum_congr rfl
    intro k _hk
    simp [N, adjA, Matrix.adjugate_apply]
  have hNs : (N * adjA) s s = A.det := by
    calc
      (N * adjA) s s = (A * adjA) s s := by
        rw [Matrix.mul_apply, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro k _hk
        simp [N, adjA, Matrix.updateRow_ne hrs]
      _ = A.det := by
        have h := congrFun (congrFun (Matrix.mul_adjugate A) s) s
        simpa [adjA] using h
  have hNzero : ∀ i : ι, i ≠ r → i ≠ s → (N * adjA) i s = 0 := by
    intro i hir his
    calc
      (N * adjA) i s = (A * adjA) i s := by
        rw [Matrix.mul_apply, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro k _hk
        simp [N, adjA, Matrix.updateRow_ne hir]
      _ = 0 := by
        have h := congrFun (congrFun (Matrix.mul_adjugate A) i) s
        simpa [adjA, his] using h
  let f : ι → R := fun i => adjN c i * (N * adjA) i s
  have hsum_tail :
      (∑ i ∈ (Finset.univ.erase r).erase s, f i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hir : i ≠ r := by
      intro h
      subst h
      simp at hi
    have his : i ≠ s := by
      intro h
      subst h
      simp at hi
    simp [f, hNzero i hir his]
  have hs_mem : s ∈ Finset.univ.erase r := by
    simp [hrs]
  have hsum :
      (∑ i, f i) = f r + f s := by
    calc
      (∑ i, f i) = f r + ∑ i ∈ Finset.univ.erase r, f i := by
        exact (Finset.univ.add_sum_erase f (Finset.mem_univ r)).symm
      _ = f r + (f s + ∑ i ∈ (Finset.univ.erase r).erase s, f i) := by
        rw [(Finset.univ.erase r).add_sum_erase f hs_mem]
      _ = f r + f s := by
        rw [hsum_tail]
        ring
  have hmain :
      (∑ i, f i) = (A.updateRow r rowv).det * adjA c s := by
    have hmat :
        adjN * (N * adjA) = (N.det • (1 : Matrix ι ι R)) * adjA := by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul]
    have hentry := congrFun (congrFun hmat c) s
    rw [Matrix.mul_apply] at hentry
    change (∑ x, f x) =
      ((N.det • (1 : Matrix ι ι R)) * adjA) c s at hentry
    rw [Matrix.mul_apply] at hentry
    have hright :
        (∑ x, (A.updateRow r rowv).det * (1 : Matrix ι ι R) c x * adjA x s) =
          (A.updateRow r rowv).det * adjA c s := by
      rw [Finset.sum_eq_single c]
      · simp
      · intro b _hb hbc
        have hcb : c ≠ b := hbc.symm
        simp [hcb]
      · intro hc
        exact False.elim (hc (Finset.mem_univ c))
    exact hentry.trans (by simpa [N] using hright)
  rw [hsum] at hmain
  simp [f, hNr, hNs, hAdj_r] at hmain
  have hgoal : A.det * adjN c s =
      -((A.updateRow s rowv).det * adjA c r) + (A.updateRow r rowv).det * adjA c s := by
    rw [← hmain]
    ring
  simpa [N, adjN, adjA, sub_eq_add_neg, add_comm] using hgoal

/-- One-row replacement cofactor identity in the Hex matrix API.

Replacing row `r` by `u` and then taking a cofactor along a distinct row `s`
is controlled by the two cofactor-row pairings of `u` against the original
matrix. This bridge-layer theorem is the row-replacement form of the
Desnanot-Jacobi/adjugate relation needed by the two-row replacement Plucker
transport. -/
theorem det_mul_cofactor_setRow_eq_cofactorRowPairing_mul_sub
    [CommRing R] (M : Hex.Matrix R (n + 1) (n + 1))
    (r s c : Fin (n + 1)) (rowVec : Vector R (n + 1)) (hrs : s ≠ r) :
    Hex.Matrix.det M * Hex.Matrix.cofactor (Hex.Matrix.setRow M r rowVec) s c =
      Hex.Matrix.cofactorRowPairing M r rowVec * Hex.Matrix.cofactor M s c -
        Hex.Matrix.cofactorRowPairing M s rowVec * Hex.Matrix.cofactor M r c := by
  have h := mathlib_det_mul_adjugate_updateRow_of_ne
    (A := matrixEquiv M) (r := r) (s := s) (c := c)
    (rowv := fun col : Fin (n + 1) => rowVec[col]) hrs
  rw [← det_eq M] at h
  rw [← matrixEquiv_setRow M r rowVec] at h
  rw [← matrixEquiv_setRow M s rowVec] at h
  rw [← det_eq (Hex.Matrix.setRow M r rowVec)] at h
  rw [← det_eq (Hex.Matrix.setRow M s rowVec)] at h
  rw [matrixEquiv_adjugate_apply_eq_cofactor] at h
  rw [matrixEquiv_adjugate_apply_eq_cofactor] at h
  rw [matrixEquiv_adjugate_apply_eq_cofactor] at h
  rw [Hex.Matrix.det_setRow_eq_cofactorRowPairing] at h
  rw [Hex.Matrix.det_setRow_eq_cofactorRowPairing] at h
  exact h

private theorem foldl_pairing_mul_sub
    [CommRing R] {β : Type v} (xs : List β)
    (det a b accF accG accH : R) (row f g h : β → R)
    (hacc : det * accF = a * accG - b * accH)
    (hpoint : ∀ x, det * f x = a * g x - b * h x) :
    det * xs.foldl (fun acc x => acc + row x * f x) accF =
      a * xs.foldl (fun acc x => acc + row x * g x) accG -
        b * xs.foldl (fun acc x => acc + row x * h x) accH := by
  induction xs generalizing accF accG accH with
  | nil =>
      simpa using hacc
  | cons x xs ih =>
      apply ih
      have hx := hpoint x
      dsimp
      calc
        det * (accF + row x * f x) =
            det * accF + row x * (det * f x) := by ring
        _ = a * (accG + row x * g x) - b * (accH + row x * h x) := by
            rw [hacc, hx]
            ring

/-- Two-row replacement determinant identity in the Hex matrix API.

Replacing distinct rows `r` and `s` by `u` and `v` satisfies the adjugate
two-row determinant relation, stated entirely in terms of Hex determinants
and cofactor-row pairings. -/
theorem det_mul_det_setRow_setRow_eq_cofactorRowPairing_mul_sub
    [CommRing R] (M : Hex.Matrix R (n + 1) (n + 1))
    (r s : Fin (n + 1)) (u v : Vector R (n + 1)) (hrs : s ≠ r) :
    Hex.Matrix.det M * Hex.Matrix.det (Hex.Matrix.setRow (Hex.Matrix.setRow M r u) s v) =
      Hex.Matrix.cofactorRowPairing M r u * Hex.Matrix.cofactorRowPairing M s v -
        Hex.Matrix.cofactorRowPairing M s u * Hex.Matrix.cofactorRowPairing M r v := by
  rw [Hex.Matrix.det_setRow_eq_cofactorRowPairing]
  unfold Hex.Matrix.cofactorRowPairing
  apply foldl_pairing_mul_sub
  · ring
  · intro col
    exact det_mul_cofactor_setRow_eq_cofactorRowPairing_mul_sub M r s col u hrs

/-! ### Ordered `nMatrix` row transport helpers -/

theorem skipIndex2_ordered_four_row_p2 {n : Nat}
    (p1 p2 p3 q : Fin (n + 2))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    Hex.Matrix.skipIndex2 p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q))
        (⟨p2.val - 1, by have := q.isLt; omega⟩ : Fin n) = p2 := by
  apply Fin.ext
  have hnot_lt : ¬ (p2.val - 1) < p1.val := by omega
  have hbetween : (p2.val - 1) + 1 < q.val := by omega
  rw [Hex.Matrix.skipIndex2_val_of_between p1 q
    (Nat.lt_trans h12 (Nat.lt_trans h23 h3q))
    (⟨p2.val - 1, by have := q.isLt; omega⟩ : Fin n) hnot_lt hbetween]
  simp
  omega

theorem skipIndex2_ordered_four_row_p3 {n : Nat}
    (p1 p2 p3 q : Fin (n + 2))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    Hex.Matrix.skipIndex2 p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q))
        (⟨p3.val - 1, by have := q.isLt; omega⟩ : Fin n) = p3 := by
  apply Fin.ext
  have hnot_lt : ¬ (p3.val - 1) < p1.val := by omega
  have hbetween : (p3.val - 1) + 1 < q.val := by omega
  rw [Hex.Matrix.skipIndex2_val_of_between p1 q
    (Nat.lt_trans h12 (Nat.lt_trans h23 h3q))
    (⟨p3.val - 1, by have := q.isLt; omega⟩ : Fin n) hnot_lt hbetween]
  simp
  omega

theorem nMatrix_ordered_four_row_p2 {R : Type u} {n : Nat}
    (B : Hex.Matrix R (n + 2) n) (p1 p2 p3 q : Fin (n + 2))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    (Hex.Matrix.nMatrix B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q)))[
        (⟨p2.val - 1, by have := q.isLt; omega⟩ : Fin n)] = B[p2] := by
  apply Vector.ext
  intro j hj
  let jj : Fin n := ⟨j, hj⟩
  change (Hex.Matrix.nMatrix B p1 q
      (Nat.lt_trans h12 (Nat.lt_trans h23 h3q)))[
        (⟨p2.val - 1, by have := q.isLt; omega⟩ : Fin n)][jj] = B[p2][jj]
  rw [Hex.Matrix.nMatrix_entry]
  have hrow := skipIndex2_ordered_four_row_p2 p1 p2 p3 q h12 h23 h3q
  simp [hrow]

theorem nMatrix_ordered_four_row_p3 {R : Type u} {n : Nat}
    (B : Hex.Matrix R (n + 2) n) (p1 p2 p3 q : Fin (n + 2))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    (Hex.Matrix.nMatrix B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q)))[
        (⟨p3.val - 1, by have := q.isLt; omega⟩ : Fin n)] = B[p3] := by
  apply Vector.ext
  intro j hj
  let jj : Fin n := ⟨j, hj⟩
  change (Hex.Matrix.nMatrix B p1 q
      (Nat.lt_trans h12 (Nat.lt_trans h23 h3q)))[
        (⟨p3.val - 1, by have := q.isLt; omega⟩ : Fin n)][jj] = B[p3][jj]
  rw [Hex.Matrix.nMatrix_entry]
  have hrow := skipIndex2_ordered_four_row_p3 p1 p2 p3 q h12 h23 h3q
  simp [hrow]

theorem skipIndex2_ordered_four_p1_p2_row_q {n : Nat}
    (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    Hex.Matrix.skipIndex2 p1 p2 h12
        (⟨q.val - 2, by have := q.isLt; omega⟩ : Fin (n + 1)) = q := by
  apply Fin.ext
  have hnot_lt : ¬ q.val - 2 < p1.val := by omega
  have hnot_between : ¬ (q.val - 2) + 1 < p2.val := by omega
  rw [Hex.Matrix.skipIndex2_val_of_ge_q p1 p2 h12
    (⟨q.val - 2, by have := q.isLt; omega⟩ : Fin (n + 1)) hnot_lt hnot_between]
  simp
  omega

theorem skipIndex2_ordered_four_p1_p3_row_q {n : Nat}
    (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    Hex.Matrix.skipIndex2 p1 p3 (Nat.lt_trans h12 h23)
        (⟨q.val - 2, by have := q.isLt; omega⟩ : Fin (n + 1)) = q := by
  apply Fin.ext
  have hnot_lt : ¬ q.val - 2 < p1.val := by omega
  have hnot_between : ¬ (q.val - 2) + 1 < p3.val := by omega
  rw [Hex.Matrix.skipIndex2_val_of_ge_q p1 p3 (Nat.lt_trans h12 h23)
    (⟨q.val - 2, by have := q.isLt; omega⟩ : Fin (n + 1)) hnot_lt hnot_between]
  simp
  omega

theorem nMatrix_ordered_four_p1_p2_row_q {R : Type u} {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    (Hex.Matrix.nMatrix B p1 p2 h12)[
        (⟨q.val - 2, by have := q.isLt; omega⟩ : Fin (n + 1))] = B[q] := by
  apply Vector.ext
  intro j hj
  let jj : Fin (n + 1) := ⟨j, hj⟩
  change (Hex.Matrix.nMatrix B p1 p2 h12)[
        (⟨q.val - 2, by have := q.isLt; omega⟩ : Fin (n + 1))][jj] = B[q][jj]
  rw [Hex.Matrix.nMatrix_entry]
  have hrow := skipIndex2_ordered_four_p1_p2_row_q p1 p2 p3 q h12 h23 h3q
  simp [hrow]

theorem nMatrix_ordered_four_p1_p3_row_q {R : Type u} {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    (Hex.Matrix.nMatrix B p1 p3 (Nat.lt_trans h12 h23))[
        (⟨q.val - 2, by have := q.isLt; omega⟩ : Fin (n + 1))] = B[q] := by
  apply Vector.ext
  intro j hj
  let jj : Fin (n + 1) := ⟨j, hj⟩
  change (Hex.Matrix.nMatrix B p1 p3 (Nat.lt_trans h12 h23))[
        (⟨q.val - 2, by have := q.isLt; omega⟩ : Fin (n + 1))][jj] = B[q][jj]
  rw [Hex.Matrix.nMatrix_entry]
  have hrow := skipIndex2_ordered_four_p1_p3_row_q p1 p2 p3 q h12 h23 h3q
  simp [hrow]

theorem ordered_four_row_p2_ne_p3 {n : Nat}
    (p1 p2 p3 q : Fin (n + 2)) (h12 : p1.val < p2.val)
    (h23 : p2.val < p3.val) (h3q : p3.val < q.val) :
    (⟨p3.val - 1, by have := q.isLt; omega⟩ : Fin n) ≠
      (⟨p2.val - 1, by have := q.isLt; omega⟩ : Fin n) := by
  intro h
  have hval := congrArg Fin.val h
  simp at hval
  omega

theorem nMatrix_ordered_four_setRow_p2_row_p3 {R : Type u} {n : Nat}
    (B : Hex.Matrix R (n + 2) n) (p1 p2 p3 q : Fin (n + 2))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) (u : Vector R n) :
    (Hex.Matrix.setRow
        (Hex.Matrix.nMatrix B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q)))
        (⟨p2.val - 1, by have := q.isLt; omega⟩ : Fin n) u)[
        (⟨p3.val - 1, by have := q.isLt; omega⟩ : Fin n)] = B[p3] := by
  rw [Hex.Matrix.setRow_row_ne]
  · exact nMatrix_ordered_four_row_p3 B p1 p2 p3 q h12 h23 h3q
  · exact ordered_four_row_p2_ne_p3 p1 p2 p3 q h12 h23 h3q

theorem nMatrix_ordered_four_setRow_p3_row_p2 {R : Type u} {n : Nat}
    (B : Hex.Matrix R (n + 2) n) (p1 p2 p3 q : Fin (n + 2))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) (v : Vector R n) :
    (Hex.Matrix.setRow
        (Hex.Matrix.nMatrix B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q)))
        (⟨p3.val - 1, by have := q.isLt; omega⟩ : Fin n) v)[
        (⟨p2.val - 1, by have := q.isLt; omega⟩ : Fin n)] = B[p2] := by
  rw [Hex.Matrix.setRow_row_ne]
  · exact nMatrix_ordered_four_row_p2 B p1 p2 p3 q h12 h23 h3q
  · exact (ordered_four_row_p2_ne_p3 p1 p2 p3 q h12 h23 h3q).symm

theorem ordered_four_cofactorRowPairing_p2_p1_eq_det_setRow
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    let M := Hex.Matrix.nMatrix B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q))
    let r2 : Fin (n + 1) := ⟨p2.val - 1, by have := q.isLt; omega⟩
    Hex.Matrix.cofactorRowPairing M r2 B[p1] =
      Hex.Matrix.det (Hex.Matrix.setRow M r2 B[p1]) := by
  intro M r2
  exact (Hex.Matrix.det_setRow_eq_cofactorRowPairing M r2 B[p1]).symm

theorem ordered_four_cofactorRowPairing_p3_p1_eq_det_setRow
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    let M := Hex.Matrix.nMatrix B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q))
    let r3 : Fin (n + 1) := ⟨p3.val - 1, by have := q.isLt; omega⟩
    Hex.Matrix.cofactorRowPairing M r3 B[p1] =
      Hex.Matrix.det (Hex.Matrix.setRow M r3 B[p1]) := by
  intro M r3
  exact (Hex.Matrix.det_setRow_eq_cofactorRowPairing M r3 B[p1]).symm

theorem ordered_four_cofactorRowPairing_p2_q_eq_det_setRow
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    let M := Hex.Matrix.nMatrix B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q))
    let r2 : Fin (n + 1) := ⟨p2.val - 1, by have := q.isLt; omega⟩
    Hex.Matrix.cofactorRowPairing M r2 B[q] =
      Hex.Matrix.det (Hex.Matrix.setRow M r2 B[q]) := by
  intro M r2
  exact (Hex.Matrix.det_setRow_eq_cofactorRowPairing M r2 B[q]).symm

theorem ordered_four_cofactorRowPairing_p3_q_eq_det_setRow
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    let M := Hex.Matrix.nMatrix B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q))
    let r3 : Fin (n + 1) := ⟨p3.val - 1, by have := q.isLt; omega⟩
    Hex.Matrix.cofactorRowPairing M r3 B[q] =
      Hex.Matrix.det (Hex.Matrix.setRow M r3 B[q]) := by
  intro M r3
  exact (Hex.Matrix.det_setRow_eq_cofactorRowPairing M r3 B[q]).symm

/-! ### Cyclic shift permutation for ordered four-row `B[p1]` transports

These helpers package the row permutation that moves `B[p1]` from position
`p1.val` past the intermediate rows up to position `p_t.val - 1`. Together
with `Matrix.det_permute`, they give signed `nDet` transports for the
`cofactorRowPairing M r? B[p1]` pairings used by the ordered four-row
Plucker assembly.
-/

namespace OrderedFourShift

variable {n : Nat}

/-- The cycle `(a, a+1, …, a+m)` on `Fin (n + 1)`: position `a + k` is sent
to `a + k + 1` for `k < m`, position `a + m` is sent back to `a`, and other
positions are fixed. Defined recursively as a product of adjacent
transpositions so the sign is `(-1)^m`. -/
private def cycleAhead : (a m : Nat) → a + m < n + 1 → Equiv.Perm (Fin (n + 1))
  | _, 0, _ => 1
  | a, k + 1, hm =>
      Equiv.swap (⟨a, by omega⟩ : Fin (n + 1)) (⟨a + 1, by omega⟩ : Fin (n + 1)) *
        cycleAhead (a + 1) k (by omega)

private theorem cycleAhead_zero (a : Nat) (hm : a + 0 < n + 1) :
    cycleAhead (n := n) a 0 hm = 1 := rfl

private theorem cycleAhead_succ (a k : Nat) (hm : a + (k + 1) < n + 1) :
    cycleAhead (n := n) a (k + 1) hm =
      Equiv.swap (⟨a, by omega⟩ : Fin (n + 1)) (⟨a + 1, by omega⟩ : Fin (n + 1)) *
        cycleAhead (a + 1) k (by omega) := rfl

private theorem sign_cycleAhead (a m : Nat) (hm : a + m < n + 1) :
    Equiv.Perm.sign (cycleAhead (n := n) a m hm) = (-1) ^ m := by
  induction m generalizing a with
  | zero => simp [cycleAhead]
  | succ k ih =>
      rw [cycleAhead_succ, map_mul, ih (a + 1) (by omega)]
      have h_ne : (⟨a, by omega⟩ : Fin (n + 1)) ≠ ⟨a + 1, by omega⟩ := by
        intro he
        have := congrArg Fin.val he
        simp at this
      rw [Equiv.Perm.sign_swap h_ne]
      exact (pow_succ' _ _).symm

/-- Below the cycle range: `cycleAhead a m` fixes `i` when `i.val < a`. -/
private theorem cycleAhead_val_below (a m : Nat) (hm : a + m < n + 1)
    (i : Fin (n + 1)) (h : i.val < a) :
    (cycleAhead (n := n) a m hm i).val = i.val := by
  induction m generalizing a with
  | zero => simp [cycleAhead]
  | succ k ih =>
      rw [cycleAhead_succ, Equiv.Perm.mul_apply]
      have h_inner_val :
          ((cycleAhead (n := n) (a + 1) k (by omega) i)).val = i.val :=
        ih (a + 1) (by omega) (by omega)
      have h_inner_ne_a :
          cycleAhead (n := n) (a + 1) k (by omega) i ≠ ⟨a, by omega⟩ := by
        intro he
        have hv : (cycleAhead (n := n) (a + 1) k (by omega) i).val = a := congrArg Fin.val he
        omega
      have h_inner_ne_a1 :
          cycleAhead (n := n) (a + 1) k (by omega) i ≠ ⟨a + 1, by omega⟩ := by
        intro he
        have hv : (cycleAhead (n := n) (a + 1) k (by omega) i).val = a + 1 :=
          congrArg Fin.val he
        omega
      rw [Equiv.swap_apply_of_ne_of_ne h_inner_ne_a h_inner_ne_a1]
      exact h_inner_val

/-- Above the cycle range: `cycleAhead a m` fixes `i` when `a + m < i.val`. -/
private theorem cycleAhead_val_above (a m : Nat) (hm : a + m < n + 1)
    (i : Fin (n + 1)) (h : a + m < i.val) :
    (cycleAhead (n := n) a m hm i).val = i.val := by
  induction m generalizing a with
  | zero => simp [cycleAhead]
  | succ k ih =>
      rw [cycleAhead_succ, Equiv.Perm.mul_apply]
      have h_inner_val :
          (cycleAhead (n := n) (a + 1) k (by omega) i).val = i.val :=
        ih (a + 1) (by omega) (by omega)
      have h_inner_ne_a :
          cycleAhead (n := n) (a + 1) k (by omega) i ≠ ⟨a, by omega⟩ := by
        intro he
        have hv : (cycleAhead (n := n) (a + 1) k (by omega) i).val = a := congrArg Fin.val he
        omega
      have h_inner_ne_a1 :
          cycleAhead (n := n) (a + 1) k (by omega) i ≠ ⟨a + 1, by omega⟩ := by
        intro he
        have hv : (cycleAhead (n := n) (a + 1) k (by omega) i).val = a + 1 :=
          congrArg Fin.val he
        omega
      rw [Equiv.swap_apply_of_ne_of_ne h_inner_ne_a h_inner_ne_a1]
      exact h_inner_val

/-- At the top of the cycle range: `cycleAhead a m` sends `i.val = a + m` to `a`. -/
private theorem cycleAhead_val_top (a m : Nat) (hm : a + m < n + 1)
    (i : Fin (n + 1)) (h : i.val = a + m) :
    (cycleAhead (n := n) a m hm i).val = a := by
  induction m generalizing a with
  | zero =>
      simp [cycleAhead]
      exact h
  | succ k ih =>
      rw [cycleAhead_succ, Equiv.Perm.mul_apply]
      have h_inner_val :
          (cycleAhead (n := n) (a + 1) k (by omega) i).val = a + 1 :=
        ih (a + 1) (by omega) (by omega)
      have h_inner_eq :
          cycleAhead (n := n) (a + 1) k (by omega) i = ⟨a + 1, by omega⟩ :=
        Fin.ext h_inner_val
      rw [h_inner_eq, Equiv.swap_apply_right]

/-- Strictly inside the cycle range: `cycleAhead a m` sends `i.val` to `i.val + 1`
when `a ≤ i.val < a + m`. -/
private theorem cycleAhead_val_in (a m : Nat) (hm : a + m < n + 1)
    (i : Fin (n + 1)) (h1 : a ≤ i.val) (h2 : i.val < a + m) :
    (cycleAhead (n := n) a m hm i).val = i.val + 1 := by
  induction m generalizing a with
  | zero => omega
  | succ k ih =>
      rw [cycleAhead_succ, Equiv.Perm.mul_apply]
      by_cases hi_eq_a : i.val = a
      · -- i.val = a: inner via below, then swap sends to a + 1
        have h_inner_val :
            (cycleAhead (n := n) (a + 1) k (by omega) i).val = a :=
          (cycleAhead_val_below (a + 1) k (by omega) i (by omega)).trans hi_eq_a
        have h_inner_eq :
            cycleAhead (n := n) (a + 1) k (by omega) i = ⟨a, by omega⟩ :=
          Fin.ext h_inner_val
        rw [h_inner_eq, Equiv.swap_apply_left]
        show a + 1 = i.val + 1
        omega
      · -- a + 1 ≤ i.val < a + 1 + k: inner via IH at i, then swap leaves alone
        have ha1 : a + 1 ≤ i.val := by omega
        have hub : i.val < a + 1 + k := by omega
        have h_inner_val :
            (cycleAhead (n := n) (a + 1) k (by omega) i).val = i.val + 1 :=
          ih (a + 1) (by omega) ha1 hub
        have h_inner_ne_a :
            cycleAhead (n := n) (a + 1) k (by omega) i ≠ ⟨a, by omega⟩ := by
          intro he
          have hv : i.val + 1 = a := h_inner_val ▸ congrArg Fin.val he
          omega
        have h_inner_ne_a1 :
            cycleAhead (n := n) (a + 1) k (by omega) i ≠ ⟨a + 1, by omega⟩ := by
          intro he
          have hv : i.val + 1 = a + 1 := h_inner_val ▸ congrArg Fin.val he
          omega
        rw [Equiv.swap_apply_of_ne_of_ne h_inner_ne_a h_inner_ne_a1]
        exact h_inner_val

/-- The inverse cycle of `cycleAhead`: sends `a` to `a + m`, `a + k` to `a + k - 1`
for `1 ≤ k ≤ m`, and fixes positions outside `[a, a + m]`. Defined as
`(cycleAhead a m hm).symm` so the sign is `(-1) ^ m`. -/
private def cycleBehind (a m : Nat) (hm : a + m < n + 1) :
    Equiv.Perm (Fin (n + 1)) :=
  (cycleAhead (n := n) a m hm).symm

private theorem sign_cycleBehind (a m : Nat) (hm : a + m < n + 1) :
    Equiv.Perm.sign (cycleBehind (n := n) a m hm) = (-1) ^ m := by
  show Equiv.Perm.sign (cycleAhead a m hm).symm = (-1) ^ m
  rw [Equiv.Perm.sign_symm]
  exact sign_cycleAhead a m hm

/-- Below the cycle range: `cycleBehind a m` fixes `i` when `i.val < a`. -/
private theorem cycleBehind_val_below (a m : Nat) (hm : a + m < n + 1)
    (i : Fin (n + 1)) (h : i.val < a) :
    (cycleBehind (n := n) a m hm i).val = i.val := by
  show ((cycleAhead a m hm).symm i).val = i.val
  have h_fwd : cycleAhead (n := n) a m hm i = i :=
    Fin.ext (cycleAhead_val_below a m hm i h)
  conv_lhs => rw [← h_fwd, Equiv.symm_apply_apply]

/-- Above the cycle range: `cycleBehind a m` fixes `i` when `a + m < i.val`. -/
private theorem cycleBehind_val_above (a m : Nat) (hm : a + m < n + 1)
    (i : Fin (n + 1)) (h : a + m < i.val) :
    (cycleBehind (n := n) a m hm i).val = i.val := by
  show ((cycleAhead a m hm).symm i).val = i.val
  have h_fwd : cycleAhead (n := n) a m hm i = i :=
    Fin.ext (cycleAhead_val_above a m hm i h)
  conv_lhs => rw [← h_fwd, Equiv.symm_apply_apply]

/-- At the base of the cycle: `cycleBehind a m` sends `i.val = a` to `a + m`. -/
private theorem cycleBehind_val_base (a m : Nat) (hm : a + m < n + 1)
    (i : Fin (n + 1)) (h : i.val = a) :
    (cycleBehind (n := n) a m hm i).val = a + m := by
  show ((cycleAhead a m hm).symm i).val = a + m
  have h_fwd : cycleAhead (n := n) a m hm ⟨a + m, by omega⟩ = i := by
    apply Fin.ext
    rw [cycleAhead_val_top a m hm ⟨a + m, by omega⟩ rfl]
    exact h.symm
  conv_lhs => rw [← h_fwd, Equiv.symm_apply_apply]

/-- Strictly inside the cycle range: `cycleBehind a m` sends `i.val` to `i.val - 1`
when `a < i.val ≤ a + m`. -/
private theorem cycleBehind_val_in (a m : Nat) (hm : a + m < n + 1)
    (i : Fin (n + 1)) (h1 : a < i.val) (h2 : i.val ≤ a + m) :
    (cycleBehind (n := n) a m hm i).val = i.val - 1 := by
  show ((cycleAhead a m hm).symm i).val = i.val - 1
  have hi_lt : i.val - 1 < n + 1 := by have := i.isLt; omega
  have h_le_am : i.val - 1 < a + m := by omega
  have h_ge_a : a ≤ i.val - 1 := by omega
  have h_fwd : cycleAhead (n := n) a m hm ⟨i.val - 1, hi_lt⟩ = i := by
    apply Fin.ext
    rw [cycleAhead_val_in a m hm ⟨i.val - 1, hi_lt⟩ h_ge_a h_le_am]
    show i.val - 1 + 1 = i.val
    omega
  conv_lhs => rw [← h_fwd, Equiv.symm_apply_apply]

end OrderedFourShift

private theorem matrixEquiv_setRow_p1_eq_submatrix_nMatrix
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p_t q : Fin (n + 3))
    (h1t : p1.val < p_t.val) (htq : p_t.val < q.val) :
    let h1q : p1.val < q.val := Nat.lt_trans h1t htq
    let M := Hex.Matrix.nMatrix B p1 q h1q
    let r : Fin (n + 1) := ⟨p_t.val - 1, by have := q.isLt; omega⟩
    let m : Nat := p_t.val - p1.val - 1
    let hm_bound : p1.val + m < n + 1 := by have := q.isLt; omega
    let σ : Equiv.Perm (Fin (n + 1)) :=
      OrderedFourShift.cycleAhead (n := n) p1.val m hm_bound
    matrixEquiv (Hex.Matrix.setRow M r B[p1]) =
      (matrixEquiv (Hex.Matrix.nMatrix B p_t q htq)).submatrix σ id := by
  intro h1q M r m hm_bound σ
  ext i j
  show (Hex.Matrix.setRow M r B[p1])[i][j] = (Hex.Matrix.nMatrix B p_t q htq)[σ i][j]
  -- Determine σ i in terms of i.val via the four cycleAhead val-lemmas.
  have hr_val : r.val = p_t.val - 1 := rfl
  have hm_val : m = p_t.val - p1.val - 1 := rfl
  -- Helper: B[k1][j] = B[k2][j] when k1 = k2 (avoids motive issues for indexing rewrites).
  have B_entry_congr :
      ∀ (k1 k2 : Fin (n + 3)), k1 = k2 → B[k1][j] = B[k2][j] := fun k1 k2 h => by
    exact congrArg (fun (x : Fin (n + 3)) => B[x][j]) h
  by_cases h_below : i.val < p1.val
  · -- Below the cycle: σ i has val = i.val, both matrices give B[i.val]
    have hσ_val : (σ i).val = i.val :=
      OrderedFourShift.cycleAhead_val_below p1.val m hm_bound i h_below
    have hir : i ≠ r := by
      intro he
      have hv : i.val = r.val := congrArg Fin.val he
      rw [hr_val] at hv
      omega
    rw [Hex.Matrix.setRow_row_ne M r i B[p1] hir]
    show (Hex.Matrix.nMatrix B p1 q h1q)[i][j] =
      (Hex.Matrix.nMatrix B p_t q htq)[σ i][j]
    rw [Hex.Matrix.nMatrix_entry, Hex.Matrix.nMatrix_entry]
    apply B_entry_congr
    apply Fin.ext
    rw [Hex.Matrix.skipIndex2_val_of_lt_p p1 q h1q i h_below,
        Hex.Matrix.skipIndex2_val_of_lt_p p_t q htq (σ i)
          (by show (σ i).val < p_t.val; omega)]
    exact hσ_val.symm
  · by_cases h_above : p_t.val ≤ i.val
    · -- Above the cycle: σ i has val = i.val, both matrices agree
      have h_not_lt_p1 : ¬ i.val < p1.val := h_below
      have h_above_cycle : p1.val + m < i.val := by
        show p1.val + (p_t.val - p1.val - 1) < i.val
        omega
      have hσ_val : (σ i).val = i.val :=
        OrderedFourShift.cycleAhead_val_above p1.val m hm_bound i h_above_cycle
      have hir : i ≠ r := by
        intro he
        have hv : i.val = r.val := congrArg Fin.val he
        rw [hr_val] at hv
        omega
      rw [Hex.Matrix.setRow_row_ne M r i B[p1] hir]
      show (Hex.Matrix.nMatrix B p1 q h1q)[i][j] =
        (Hex.Matrix.nMatrix B p_t q htq)[σ i][j]
      rw [Hex.Matrix.nMatrix_entry, Hex.Matrix.nMatrix_entry]
      apply B_entry_congr
      apply Fin.ext
      have h_not_lt_pt_for_σi : ¬ (σ i).val < p_t.val := by
        show ¬ (σ i).val < p_t.val; omega
      have h_not_lt_p1_for_σi : ¬ (σ i).val < p1.val := by
        show ¬ (σ i).val < p1.val; omega
      by_cases hqub : i.val + 1 < q.val
      · rw [Hex.Matrix.skipIndex2_val_of_between p1 q h1q i h_not_lt_p1 hqub]
        have hqub_σ : (σ i).val + 1 < q.val := by
          show (σ i).val + 1 < q.val; omega
        rw [Hex.Matrix.skipIndex2_val_of_between p_t q htq (σ i)
              h_not_lt_pt_for_σi hqub_σ]
        omega
      · rw [Hex.Matrix.skipIndex2_val_of_ge_q p1 q h1q i h_not_lt_p1 hqub]
        have hqub_σ : ¬ (σ i).val + 1 < q.val := by
          show ¬ (σ i).val + 1 < q.val; omega
        rw [Hex.Matrix.skipIndex2_val_of_ge_q p_t q htq (σ i)
              h_not_lt_pt_for_σi hqub_σ]
        omega
    · -- Inside the cycle: p1.val ≤ i.val < p_t.val
      have h_ge_p1 : p1.val ≤ i.val := by
        by_contra hc; exact h_below (by omega)
      have h_lt_pt : i.val < p_t.val := by
        by_contra hc; exact h_above (by omega)
      by_cases h_at_r : i.val = p_t.val - 1
      · -- i = r: setRow gives B[p1]; σ i has val p1.val, giving B[p1]
        have hir : i = r := Fin.ext (by rw [hr_val, h_at_r])
        rw [hir, Hex.Matrix.setRow_get_self]
        show B[p1][j] = (Hex.Matrix.nMatrix B p_t q htq)[σ r][j]
        have h_r_at_top : r.val = p1.val + m := by
          rw [hr_val]
          show p_t.val - 1 = p1.val + (p_t.val - p1.val - 1)
          omega
        have hσ_val : (σ r).val = p1.val :=
          OrderedFourShift.cycleAhead_val_top p1.val m hm_bound r h_r_at_top
        rw [Hex.Matrix.nMatrix_entry]
        apply B_entry_congr
        apply Fin.ext
        show p1.val = (Hex.Matrix.skipIndex2 p_t q htq (σ r)).val
        have h_σr_lt_pt : (σ r).val < p_t.val := by omega
        rw [Hex.Matrix.skipIndex2_val_of_lt_p p_t q htq _ h_σr_lt_pt]
        exact hσ_val.symm
      · -- p1.val ≤ i.val < p_t.val - 1: σ i has val i.val + 1
        have h_lt_r : i.val < p_t.val - 1 := by omega
        have h_in_lt : i.val < p1.val + m := by
          show i.val < p1.val + (p_t.val - p1.val - 1)
          omega
        have hσ_val : (σ i).val = i.val + 1 :=
          OrderedFourShift.cycleAhead_val_in p1.val m hm_bound i h_ge_p1 h_in_lt
        have hir : i ≠ r := by
          intro he
          have hv : i.val = r.val := congrArg Fin.val he
          rw [hr_val] at hv
          omega
        rw [Hex.Matrix.setRow_row_ne M r i B[p1] hir]
        show (Hex.Matrix.nMatrix B p1 q h1q)[i][j] =
          (Hex.Matrix.nMatrix B p_t q htq)[σ i][j]
        rw [Hex.Matrix.nMatrix_entry, Hex.Matrix.nMatrix_entry]
        apply B_entry_congr
        apply Fin.ext
        have h_not_lt_p1 : ¬ i.val < p1.val := by
          show ¬ i.val < p1.val; omega
        have h_between : i.val + 1 < q.val := by
          have : p_t.val < q.val := htq
          omega
        rw [Hex.Matrix.skipIndex2_val_of_between p1 q h1q i h_not_lt_p1 h_between]
        have h_σi_lt_pt : (σ i).val < p_t.val := by omega
        rw [Hex.Matrix.skipIndex2_val_of_lt_p p_t q htq (σ i) h_σi_lt_pt]
        omega

/-- Determinant-level transport: for `p1.val < p_t.val < q.val`, replacing the
ordered row at `r := p_t.val - 1` in `nMatrix B p1 q` by `B[p1]` produces the
signed `nDet B p_t q` minor with sign `(-1)^(p_t.val - p1.val - 1)`. -/
private theorem det_setRow_p1
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p_t q : Fin (n + 3))
    (h1t : p1.val < p_t.val) (htq : p_t.val < q.val) :
    let h1q : p1.val < q.val := Nat.lt_trans h1t htq
    let M := Hex.Matrix.nMatrix B p1 q h1q
    let r : Fin (n + 1) := ⟨p_t.val - 1, by have := q.isLt; omega⟩
    Hex.Matrix.det (Hex.Matrix.setRow M r B[p1]) =
      (-1 : R) ^ (p_t.val - p1.val - 1) * Hex.Matrix.nDet B p_t q htq := by
  intro h1q M r
  have h_sub := matrixEquiv_setRow_p1_eq_submatrix_nMatrix B p1 p_t q h1t htq
  rw [det_eq, h_sub, Matrix.det_permute,
      OrderedFourShift.sign_cycleAhead p1.val (p_t.val - p1.val - 1), ← det_eq]
  show ((((-1 : ℤˣ) ^ (p_t.val - p1.val - 1) : ℤˣ) : ℤ) : R) *
      Hex.Matrix.det (Hex.Matrix.nMatrix B p_t q htq) =
    (-1 : R) ^ (p_t.val - p1.val - 1) * Hex.Matrix.nDet B p_t q htq
  have h_cast :
      ((((-1 : ℤˣ) ^ (p_t.val - p1.val - 1) : ℤˣ) : ℤ) : R) =
        (-1 : R) ^ (p_t.val - p1.val - 1) := by
    induction p_t.val - p1.val - 1 with
    | zero => simp
    | succ k ih =>
        have h_lhs : ((-1 : ℤˣ)) ^ (k + 1) = ((-1 : ℤˣ))^k * (-1 : ℤˣ) := pow_succ _ _
        rw [h_lhs, Units.val_mul, Int.cast_mul, ih, pow_succ]
        simp
  rw [h_cast]
  rfl

/-- Bridge-layer transport for the ordered four-row Plucker setup.

For `p1 < p2 < p3 < q`, the cofactor-row pairing
`cofactorRowPairing M r2 B[p1]` of the ordered base matrix
`M = nMatrix B p1 q` against `B[p1]` at row `r2 := p2.val - 1` equals the
signed `nDet B p2 q` minor with sign `(-1)^(p2.val - p1.val - 1)`. -/
theorem ordered_four_cofactorRowPairing_p2_p1_eq_pow_mul_nDet
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    let M := Hex.Matrix.nMatrix B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q))
    let r2 : Fin (n + 1) := ⟨p2.val - 1, by have := q.isLt; omega⟩
    let h2q : p2.val < q.val := Nat.lt_trans h23 h3q
    Hex.Matrix.cofactorRowPairing M r2 B[p1] =
      (-1 : R) ^ (p2.val - p1.val - 1) * Hex.Matrix.nDet B p2 q h2q := by
  intro M r2 h2q
  rw [show Hex.Matrix.cofactorRowPairing M r2 B[p1] =
      Hex.Matrix.det (Hex.Matrix.setRow M r2 B[p1]) from
    (Hex.Matrix.det_setRow_eq_cofactorRowPairing M r2 B[p1]).symm]
  exact det_setRow_p1 B p1 p2 q h12 h2q

/-- Bridge-layer transport for the ordered four-row Plucker setup.

For `p1 < p2 < p3 < q`, the cofactor-row pairing
`cofactorRowPairing M r3 B[p1]` of the ordered base matrix
`M = nMatrix B p1 q` against `B[p1]` at row `r3 := p3.val - 1` equals the
signed `nDet B p3 q` minor with sign `(-1)^(p3.val - p1.val - 1)`. -/
theorem ordered_four_cofactorRowPairing_p3_p1_eq_pow_mul_nDet
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    let M := Hex.Matrix.nMatrix B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q))
    let r3 : Fin (n + 1) := ⟨p3.val - 1, by have := q.isLt; omega⟩
    let h3qq : p3.val < q.val := h3q
    Hex.Matrix.cofactorRowPairing M r3 B[p1] =
      (-1 : R) ^ (p3.val - p1.val - 1) * Hex.Matrix.nDet B p3 q h3qq := by
  intro M r3 h3qq
  rw [show Hex.Matrix.cofactorRowPairing M r3 B[p1] =
      Hex.Matrix.det (Hex.Matrix.setRow M r3 B[p1]) from
    (Hex.Matrix.det_setRow_eq_cofactorRowPairing M r3 B[p1]).symm]
  exact det_setRow_p1 B p1 p3 q (Nat.lt_trans h12 h23) h3qq

private theorem matrixEquiv_nMatrix_p1_pt_eq_submatrix_setRow_q
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p_t q : Fin (n + 3))
    (h1t : p1.val < p_t.val) (htq : p_t.val < q.val) :
    let h1q : p1.val < q.val := Nat.lt_trans h1t htq
    let M := Hex.Matrix.nMatrix B p1 q h1q
    let r : Fin (n + 1) := ⟨p_t.val - 1, by have := q.isLt; omega⟩
    let m : Nat := q.val - p_t.val - 1
    let a : Nat := p_t.val - 1
    let hm_bound : a + m < n + 1 := by have := q.isLt; omega
    let σ : Equiv.Perm (Fin (n + 1)) :=
      OrderedFourShift.cycleAhead (n := n) a m hm_bound
    matrixEquiv (Hex.Matrix.nMatrix B p1 p_t h1t) =
      (matrixEquiv (Hex.Matrix.setRow M r B[q])).submatrix σ id := by
  intro h1q M r m a hm_bound σ
  ext i j
  show (Hex.Matrix.nMatrix B p1 p_t h1t)[i][j] =
    (Hex.Matrix.setRow M r B[q])[σ i][j]
  have hr_val : r.val = p_t.val - 1 := rfl
  have ha_val : a = p_t.val - 1 := rfl
  have hm_val : m = q.val - p_t.val - 1 := rfl
  have htop_val : a + m = q.val - 2 := by omega
  have B_entry_congr :
      ∀ (k1 k2 : Fin (n + 3)), k1 = k2 → B[k1][j] = B[k2][j] := fun k1 k2 h => by
    exact congrArg (fun (x : Fin (n + 3)) => B[x][j]) h
  by_cases h_below : i.val < a
  · have hσ_val : (σ i).val = i.val :=
      OrderedFourShift.cycleAhead_val_below a m hm_bound i h_below
    have hσ_ne_r : σ i ≠ r := by
      intro he
      have hv : (σ i).val = r.val := congrArg Fin.val he
      rw [hr_val, hσ_val] at hv
      omega
    rw [Hex.Matrix.setRow_row_ne M r (σ i) B[q] hσ_ne_r]
    rw [Hex.Matrix.nMatrix_entry, Hex.Matrix.nMatrix_entry]
    apply B_entry_congr
    apply Fin.ext
    by_cases hi1 : i.val < p1.val
    · have hσ1 : (σ i).val < p1.val := by omega
      rw [Hex.Matrix.skipIndex2_val_of_lt_p p1 p_t h1t i hi1,
          Hex.Matrix.skipIndex2_val_of_lt_p p1 q h1q (σ i) hσ1]
      exact hσ_val.symm
    · have hi_between : i.val + 1 < p_t.val := by omega
      have hσ_not_lt_p1 : ¬ (σ i).val < p1.val := by omega
      have hσ_between : (σ i).val + 1 < q.val := by omega
      rw [Hex.Matrix.skipIndex2_val_of_between p1 p_t h1t i hi1 hi_between,
          Hex.Matrix.skipIndex2_val_of_between p1 q h1q (σ i) hσ_not_lt_p1 hσ_between]
      omega
  · by_cases h_above : a + m < i.val
    · have hσ_val : (σ i).val = i.val :=
        OrderedFourShift.cycleAhead_val_above a m hm_bound i h_above
      have hσ_ne_r : σ i ≠ r := by
        intro he
        have hv : (σ i).val = r.val := congrArg Fin.val he
        rw [hr_val, hσ_val] at hv
        omega
      rw [Hex.Matrix.setRow_row_ne M r (σ i) B[q] hσ_ne_r]
      rw [Hex.Matrix.nMatrix_entry, Hex.Matrix.nMatrix_entry]
      apply B_entry_congr
      apply Fin.ext
      have hi_not_lt_p1 : ¬ i.val < p1.val := by omega
      have hi_not_between_pt : ¬ i.val + 1 < p_t.val := by omega
      have hσ_not_lt_p1 : ¬ (σ i).val < p1.val := by omega
      have hσ_not_between_q : ¬ (σ i).val + 1 < q.val := by omega
      rw [Hex.Matrix.skipIndex2_val_of_ge_q p1 p_t h1t i hi_not_lt_p1 hi_not_between_pt,
          Hex.Matrix.skipIndex2_val_of_ge_q p1 q h1q (σ i) hσ_not_lt_p1 hσ_not_between_q]
      omega
    · have h_ge_a : a ≤ i.val := by omega
      have h_le_top : i.val ≤ a + m := by omega
      by_cases h_at_top : i.val = a + m
      · have hσ_val : (σ i).val = a :=
          OrderedFourShift.cycleAhead_val_top a m hm_bound i h_at_top
        have hσ_eq_r : σ i = r := by
          apply Fin.ext
          rw [hσ_val, hr_val, ha_val]
        have hrow : (Hex.Matrix.setRow M r B[q])[σ i] = B[q] := by
          simpa [hσ_eq_r] using Hex.Matrix.setRow_get_self M r B[q]
        rw [hrow]
        rw [Hex.Matrix.nMatrix_entry]
        apply B_entry_congr
        apply Fin.ext
        have hi_not_lt_p1 : ¬ i.val < p1.val := by omega
        have hi_not_between : ¬ i.val + 1 < p_t.val := by omega
        rw [Hex.Matrix.skipIndex2_val_of_ge_q p1 p_t h1t i hi_not_lt_p1 hi_not_between]
        omega
      · have h_lt_top : i.val < a + m := by omega
        have hσ_val : (σ i).val = i.val + 1 :=
          OrderedFourShift.cycleAhead_val_in a m hm_bound i h_ge_a h_lt_top
        have hσ_ne_r : σ i ≠ r := by
          intro he
          have hv : (σ i).val = r.val := congrArg Fin.val he
          rw [hr_val, hσ_val] at hv
          omega
        rw [Hex.Matrix.setRow_row_ne M r (σ i) B[q] hσ_ne_r]
        rw [Hex.Matrix.nMatrix_entry, Hex.Matrix.nMatrix_entry]
        apply B_entry_congr
        apply Fin.ext
        have hi_not_lt_p1 : ¬ i.val < p1.val := by omega
        have hi_not_between_pt : ¬ i.val + 1 < p_t.val := by omega
        have hσ_not_lt_p1 : ¬ (σ i).val < p1.val := by omega
        have hσ_between_q : (σ i).val + 1 < q.val := by omega
        rw [Hex.Matrix.skipIndex2_val_of_ge_q p1 p_t h1t i hi_not_lt_p1 hi_not_between_pt,
            Hex.Matrix.skipIndex2_val_of_between p1 q h1q (σ i) hσ_not_lt_p1 hσ_between_q]
        omega

private theorem det_setRow_q
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p_t q : Fin (n + 3))
    (h1t : p1.val < p_t.val) (htq : p_t.val < q.val) :
    let h1q : p1.val < q.val := Nat.lt_trans h1t htq
    let M := Hex.Matrix.nMatrix B p1 q h1q
    let r : Fin (n + 1) := ⟨p_t.val - 1, by have := q.isLt; omega⟩
    Hex.Matrix.det (Hex.Matrix.setRow M r B[q]) =
      (-1 : R) ^ (q.val - p_t.val - 1) * Hex.Matrix.nDet B p1 p_t h1t := by
  intro h1q M r
  let m : Nat := q.val - p_t.val - 1
  let a : Nat := p_t.val - 1
  have hm_bound : a + m < n + 1 := by
    dsimp [a, m]
    have := q.isLt
    omega
  let σ : Equiv.Perm (Fin (n + 1)) := OrderedFourShift.cycleAhead (n := n) a m hm_bound
  have h_sub := matrixEquiv_nMatrix_p1_pt_eq_submatrix_setRow_q B p1 p_t q h1t htq
  have hdet :
      Hex.Matrix.nDet B p1 p_t h1t =
        (-1 : R) ^ m * Hex.Matrix.det (Hex.Matrix.setRow M r B[q]) := by
    change Hex.Matrix.det (Hex.Matrix.nMatrix B p1 p_t h1t) =
      (-1 : R) ^ m * Hex.Matrix.det (Hex.Matrix.setRow M r B[q])
    rw [det_eq, h_sub, Matrix.det_permute,
        OrderedFourShift.sign_cycleAhead a m hm_bound, ← det_eq]
    show ((((-1 : ℤˣ) ^ m : ℤˣ) : ℤ) : R) *
        Hex.Matrix.det (Hex.Matrix.setRow M r B[q]) =
      (-1 : R) ^ m * Hex.Matrix.det (Hex.Matrix.setRow M r B[q])
    have h_cast :
        ((((-1 : ℤˣ) ^ m : ℤˣ) : ℤ) : R) = (-1 : R) ^ m := by
      induction m with
      | zero => simp
      | succ k ih =>
          have h_lhs : ((-1 : ℤˣ)) ^ (k + 1) = ((-1 : ℤˣ))^k * (-1 : ℤˣ) :=
            pow_succ _ _
          rw [h_lhs, Units.val_mul, Int.cast_mul, ih, pow_succ]
          simp
    rw [h_cast]
  have hsign_sq : (-1 : R) ^ m * ((-1 : R) ^ m * Hex.Matrix.det (Hex.Matrix.setRow M r B[q])) =
      Hex.Matrix.det (Hex.Matrix.setRow M r B[q]) := by
    rw [← mul_assoc]
    rw [← pow_add]
    have h_even : m + m = 2 * m := by omega
    rw [h_even, pow_mul]
    simp
  calc
    Hex.Matrix.det (Hex.Matrix.setRow M r B[q])
        = (-1 : R) ^ m * Hex.Matrix.nDet B p1 p_t h1t := by
          rw [hdet, hsign_sq]
    _ = (-1 : R) ^ (q.val - p_t.val - 1) * Hex.Matrix.nDet B p1 p_t h1t := rfl

/-- Bridge-layer transport for the ordered four-row Plucker setup.

For `p1 < p2 < p3 < q`, the cofactor-row pairing
`cofactorRowPairing M r2 B[q]` of the ordered base matrix
`M = nMatrix B p1 q` against `B[q]` at row `r2 := p2.val - 1` equals the
signed `nDet B p1 p2` minor with sign `(-1)^(q.val - p2.val - 1)`. -/
theorem ordered_four_cofactorRowPairing_p2_q_eq_pow_mul_nDet
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    let M := Hex.Matrix.nMatrix B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q))
    let r2 : Fin (n + 1) := ⟨p2.val - 1, by have := q.isLt; omega⟩
    Hex.Matrix.cofactorRowPairing M r2 B[q] =
      (-1 : R) ^ (q.val - p2.val - 1) * Hex.Matrix.nDet B p1 p2 h12 := by
  intro M r2
  rw [show Hex.Matrix.cofactorRowPairing M r2 B[q] =
      Hex.Matrix.det (Hex.Matrix.setRow M r2 B[q]) from
    (Hex.Matrix.det_setRow_eq_cofactorRowPairing M r2 B[q]).symm]
  exact det_setRow_q B p1 p2 q h12 (Nat.lt_trans h23 h3q)

/-- Bridge-layer transport for the ordered four-row Plucker setup.

For `p1 < p2 < p3 < q`, the cofactor-row pairing
`cofactorRowPairing M r3 B[q]` of the ordered base matrix
`M = nMatrix B p1 q` against `B[q]` at row `r3 := p3.val - 1` equals the
signed `nDet B p1 p3` minor with sign `(-1)^(q.val - p3.val - 1)`. -/
theorem ordered_four_cofactorRowPairing_p3_q_eq_pow_mul_nDet
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    let M := Hex.Matrix.nMatrix B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q))
    let r3 : Fin (n + 1) := ⟨p3.val - 1, by have := q.isLt; omega⟩
    Hex.Matrix.cofactorRowPairing M r3 B[q] =
      (-1 : R) ^ (q.val - p3.val - 1) *
        Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23) := by
  intro M r3
  rw [show Hex.Matrix.cofactorRowPairing M r3 B[q] =
      Hex.Matrix.det (Hex.Matrix.setRow M r3 B[q]) from
    (Hex.Matrix.det_setRow_eq_cofactorRowPairing M r3 B[q]).symm]
  exact det_setRow_q B p1 p3 q (Nat.lt_trans h12 h23) h3q

end HexMatrixMathlib
