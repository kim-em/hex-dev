/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRankMathlib.Produce

public section

/-!
Producer correctness: the certificate `rankCertWith` emits checks.

The second pass runs over `[B | 1]` for the nonsingular pivot block `B` of the
first pass. Every column of `B` is a pivot column of that pass (a skipped
column would give `B` a nontrivial kernel vector), so its pivot columns are
exactly the columns of `B` in order, its pivot rows are a permutation `π` of
the rows of `B`, and its reported pivot rows restricted to the right block are
`adjugate (B.submatrix π id)` with the columns permuted back by `π`. The
three certificate identities then follow from `Matrix.mul_adjugate` and the
first pass's all-column identity.
-/

open Matrix

namespace HexMatrixMathlib

universe u

variable {R : Type u} [CommRing R] [DecidableEq R] {n m : Nat}

namespace RowReduce

omit [DecidableEq R] in
/-- Entry formula for the augmented block `[B | 1]`. -/
theorem matrixEquiv_augmentIdentity {r : Nat} (B : Hex.Matrix R r r) (i : Fin r)
    (j : Fin (r + r)) :
    matrixEquiv (Hex.Matrix.augmentIdentity B) i j =
      if h : j.val < r then matrixEquiv B i ⟨j.val, h⟩
      else if i.val + r = j.val then 1 else 0 := by
  simp only [Hex.Matrix.augmentIdentity, matrixEquiv_ofFn]
  rfl

omit [DecidableEq R] in
/-- The left block of `[B | 1]` is `B`. -/
theorem matrixEquiv_augmentIdentity_castAdd {r : Nat} (B : Hex.Matrix R r r) (i c : Fin r) :
    matrixEquiv (Hex.Matrix.augmentIdentity B) i (Fin.castAdd r c) = matrixEquiv B i c := by
  rw [matrixEquiv_augmentIdentity, dite_eq_left (by simp)]
  rfl

omit [DecidableEq R] in
/-- The right block of `[B | 1]` is the identity. -/
theorem matrixEquiv_augmentIdentity_natAdd {r : Nat} (B : Hex.Matrix R r r) (i c : Fin r) :
    matrixEquiv (Hex.Matrix.augmentIdentity B) i (Fin.natAdd r c) = if i = c then 1 else 0 := by
  rw [matrixEquiv_augmentIdentity, dite_eq_right (by simp)]
  simp only [Fin.val_natAdd]
  by_cases h : i = c
  · subst h
    simp [Nat.add_comm]
  · rw [ite_eq_right h, ite_eq_right]
    intro h'
    exact h (Fin.ext (by omega))

omit [DecidableEq R] in
/-- `[B | 1]` has rank `r`. -/
theorem rank_augmentIdentity [IsDomain R] {r : Nat} (B : Hex.Matrix R r r) :
    (matrixEquiv (Hex.Matrix.augmentIdentity B)).rank = r := by
  classical
  apply le_antisymm
  · exact (rank_le_card_height _).trans (Fintype.card_fin r).le
  · have h1 : (matrixEquiv (Hex.Matrix.augmentIdentity B)).submatrix id (Fin.natAdd r) =
        (1 : Matrix (Fin r) (Fin r) R) := by
      ext i c
      rw [Matrix.submatrix_apply, id_eq, matrixEquiv_augmentIdentity_natAdd, Matrix.one_apply]
    calc r = (1 : Matrix (Fin r) (Fin r) R).rank := by rw [rank_one, Fintype.card_fin]
      _ ≤ _ := by rw [← h1]; exact rank_submatrix_le _ _ _

/-- The pivot columns only grow along the pass. -/
theorem cols_subset_reduceStep {quot : R → R → R} (S : Hex.Matrix.ReducedForm R n m) (j : Fin m) :
    S.profile.cols.toList ⊆ (Hex.Matrix.reduceStep quot S j).profile.cols.toList := by
  cases hp : Hex.Matrix.findPivotRow? S.matrix S.profile.rows.toList j with
  | none =>
    rw [Hex.Matrix.reduceStep_skip hp]
    exact List.Subset.refl _
  | some p =>
    rw [Hex.Matrix.reduceStep_pivot_profile hp]
    simp only [Vector.toList_push]
    exact List.subset_append_left _ _

/-- The pivot columns only grow along a run of columns. -/
theorem cols_subset_foldl {quot : R → R → R} (l : List (Fin m)) (S : Hex.Matrix.ReducedForm R n m) :
    S.profile.cols.toList ⊆ (l.foldl (Hex.Matrix.reduceStep quot) S).profile.cols.toList := by
  induction l generalizing S with
  | nil => exact List.Subset.refl _
  | cons j l ih =>
    rw [List.foldl_cons]
    exact List.Subset.trans (cols_subset_reduceStep S j) (ih _)

/-- A pivot column is recorded. -/
theorem mem_cols_reduceStep {quot : R → R → R} {S : Hex.Matrix.ReducedForm R n m} {j : Fin m}
    {p : Fin n} (hp : Hex.Matrix.findPivotRow? S.matrix S.profile.rows.toList j = some p) :
    j ∈ (Hex.Matrix.reduceStep quot S j).profile.cols.toList := by
  rw [Hex.Matrix.reduceStep_pivot_profile hp]
  simp [Vector.toList_push]

/-- The pivot columns after `t` columns are pivot columns of the whole pass. -/
theorem reduceCols_cols_subset (quot : R → R → R) (A : Hex.Matrix R n m) (t : Nat) :
    (reduceCols quot A t).profile.cols.toList ⊆
      (Hex.Matrix.rowReduceWith quot A).profile.cols.toList := by
  rw [Hex.Matrix.rowReduceWith, ← List.take_append_drop t (List.finRange m), List.foldl_append]
  exact cols_subset_foldl _ _

/-- Every column of a nonsingular block `B` is a pivot column of the pass over
`[B | 1]`: a skipped column would be a combination of earlier columns of `B`. -/
theorem augment_col_mem_cols {quot : R → R → R} (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0) {r : Nat} (B : Hex.Matrix R r r) (hB : (matrixEquiv B).det ≠ 0)
    (c : Fin r) :
    Fin.castAdd r c ∈
      (Hex.Matrix.rowReduceWith quot (Hex.Matrix.augmentIdentity B)).profile.cols.toList := by
  have := isDomain_of_quot quot hquot h1
  have hS := inv_reduceCols hquot h1 (Hex.Matrix.augmentIdentity B) (t := c.val) (by omega)
  have hstep := reduceCols_succ quot (Hex.Matrix.augmentIdentity B) (t := c.val) (by omega)
  have hc : (⟨c.val, by omega⟩ : Fin (r + r)) = Fin.castAdd r c := rfl
  rw [hc] at hstep
  set S := reduceCols quot (Hex.Matrix.augmentIdentity B) c.val
  refine reduceCols_cols_subset quot _ (c.val + 1) ?_
  rw [hstep]
  cases hp : Hex.Matrix.findPivotRow? S.matrix S.profile.rows.toList (Fin.castAdd r c) with
  | some p => exact mem_cols_reduceStep hp
  | none =>
    exfalso
    have hdep := col_skipped_dependent hS hp
    have hcl : ∀ l, (S.profile.cols.get l).val < r := fun l => lt_of_lt_of_le (hS.cols_lt l) c.isLt.le
    let cl : Fin S.profile.rank → Fin r := fun l => ⟨(S.profile.cols.get l).val, hcl l⟩
    have hcols_eq : ∀ l, S.profile.cols.get l = Fin.castAdd r (cl l) := fun l => Fin.ext rfl
    let w : Fin S.profile.rank → R := fun l =>
      coeff (matrixEquiv (Hex.Matrix.augmentIdentity B)) S l (Fin.castAdd r c)
    have hdep' : ∀ i, S.denom * matrixEquiv B i c = ∑ l, matrixEquiv B i (cl l) * w l := by
      intro i
      have h := hdep i
      simp only [hcols_eq, matrixEquiv_augmentIdentity_castAdd] at h
      exact h
    have hcl_ne : ∀ l, cl l ≠ c := by
      intro l h
      have := hS.cols_lt l
      have h' := congrArg Fin.val h
      simp only [cl] at h'
      omega
    let v : Fin r → R := Pi.single c S.denom - fun x => ∑ l, if cl l = x then w l else 0
    have hv : (matrixEquiv B) *ᵥ v = 0 := by
      funext i
      simp only [Matrix.mulVec, dotProduct, v, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
        Pi.zero_apply, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [mul_comm, hdep' i, sub_self]
    have hv0 := Matrix.eq_zero_of_mulVec_eq_zero hB hv
    have hc0 := congrFun hv0 c
    simp only [v, Pi.sub_apply, Pi.single_eq_same, Pi.zero_apply] at hc0
    rw [Finset.sum_eq_zero (fun l _ => by rw [ite_eq_right (hcl_ne l)]), sub_zero] at hc0
    exact hS.denom_ne hc0

/-- A strictly increasing map `Fin r → Fin (r + r)` whose range contains the
first `r` indices is the embedding of the first `r` indices. -/
theorem strictMono_eq_castAdd {r : Nat} (f : Fin r → Fin (r + r)) (hf : StrictMono f)
    (hsurj : ∀ c : Fin r, ∃ l, f l = Fin.castAdd r c) : ∀ l, f l = Fin.castAdd r l := by
  have hle : ∀ (N : Nat) (l : Fin r), l.val = N → N ≤ (f l).val := by
    intro N
    induction N with
    | zero => intro l _; exact Nat.zero_le _
    | succ N ih =>
      intro l hl
      have hlt : N < r := by omega
      have h := ih ⟨N, hlt⟩ rfl
      have h' : f ⟨N, hlt⟩ < f l := hf (by rw [Fin.lt_def]; simp [hl])
      rw [Fin.lt_def] at h'
      omega
  have main : ∀ (N : Nat) (l : Fin r), l.val < N → f l = Fin.castAdd r l := by
    intro N
    induction N with
    | zero => intro l hl; exact absurd hl (Nat.not_lt_zero _)
    | succ N ih =>
      intro l hl
      by_cases hlN : l.val < N
      · exact ih l hlN
      · have hlN' : l.val = N := by omega
        obtain ⟨l', hl'⟩ := hsurj l
        by_cases hval : (f l).val = l.val
        · exact Fin.ext (by simpa using hval)
        · have hle' := hle l.val l rfl
          have hlt : (f l').val < (f l).val := by
            rw [hl', Fin.val_castAdd]; omega
          have hl'l : l' < l := hf.lt_iff_lt.mp (Fin.lt_def.mpr hlt)
          have := ih l' (by rw [Fin.lt_def] at hl'l; omega)
          rw [this] at hl'
          have := Fin.castAdd_injective r r hl'  -- l' = l
          exact absurd this (ne_of_lt hl'l)
  exact fun l => main (l.val + 1) l (Nat.lt_succ_self _)

omit [CommRing R] [DecidableEq R] in
/-- The pivot row read by the certificate is the recorded pivot row. -/
theorem pivotRowAt_eq {r : Nat} (rows₂ : Vector (Fin r) r) (cols₂ : Vector (Fin (r + r)) r)
    (d₂ : R) (M₂ : Hex.Matrix R r (r + r)) (k : Fin r) :
    Hex.Matrix.pivotRowAt (⟨⟨r, rows₂, cols₂⟩, d₂, M₂⟩ : Hex.Matrix.ReducedForm R r (r + r)) k =
      rows₂.get k := by
  simp [Hex.Matrix.pivotRowAt, Array.getD, Vector.get]

end RowReduce

open RowReduce

variable {quot : R → R → R}

/-- Producer correctness for any first pass satisfying the invariant. -/
theorem rankCertOf_check (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a) (h1 : (1 : R) ≠ 0)
    (A : Hex.Matrix R n m) {D : Hex.Matrix.ReducedForm R n m} (hS : Inv (matrixEquiv A) m D) :
    Hex.Matrix.checkRank A (Hex.Matrix.rankCertOf quot A D) = true := by
  have := isDomain_of_quot quot hquot h1
  obtain ⟨⟨r, rows, cols⟩, d, M⟩ := D
  set B := Hex.Matrix.selectedSubmatrix A rows cols with hBdef
  have hS₂ := inv_rowReduceWith hquot h1 (Hex.Matrix.augmentIdentity B)
  have hmem := fun c => augment_col_mem_cols hquot h1 B (by
    rw [hBdef, matrixEquiv_selectedSubmatrix]
    exact hS.denom_eq ▸ hS.denom_ne) c
  have hrank₂ :
      (Hex.Matrix.rowReduceWith quot (Hex.Matrix.augmentIdentity B)).profile.rank = r := by
    rw [← hS₂.rank_eq, rank_augmentIdentity]
  change Hex.Matrix.checkRank A ⟨r, rows, cols,
    (Hex.Matrix.rowReduceWith quot (Hex.Matrix.augmentIdentity B)).denom,
    Hex.Matrix.adjugateOf (Hex.Matrix.rowReduceWith quot (Hex.Matrix.augmentIdentity B))⟩ = true
  generalize hD₂ : Hex.Matrix.rowReduceWith quot (Hex.Matrix.augmentIdentity B) = D₂
    at hS₂ hmem hrank₂ ⊢
  obtain ⟨⟨r₂, rows₂, cols₂⟩, d₂, M₂⟩ := D₂
  simp only at hS₂ hmem hrank₂ ⊢
  subst r₂
  rw [checkRank_iff_matrixEquiv]
  simp only
  -- the pivot columns of the second pass are the columns of `B`, in order
  have hcols₂ : ∀ l, cols₂.get l = Fin.castAdd r l :=
    strictMono_eq_castAdd cols₂.get hS₂.cols_mono
      (fun c => (mem_toList_iff cols₂ _).mp (hmem c))
  -- the pivot rows of the second pass are a permutation of the rows of `B`
  have hinj : Function.Injective rows₂.get := hS₂.rows_injective
  let π : Fin r ≃ Fin r := Equiv.ofBijective rows₂.get (Finite.injective_iff_bijective.mp hinj)
  have hπ : ∀ k, π k = rows₂.get k := fun k => rfl
  -- notation
  set eA := matrixEquiv A with heA
  set eB : Matrix (Fin r) (Fin r) R := eA.submatrix rows.get cols.get with heB
  have heB' : matrixEquiv B = eB := by rw [hBdef, matrixEquiv_selectedSubmatrix]
  set B₂ : Matrix (Fin r) (Fin r) R := eB.submatrix π id with hB₂
  have hblock₂ : block (matrixEquiv (Hex.Matrix.augmentIdentity B))
      ⟨⟨r, rows₂, cols₂⟩, d₂, M₂⟩ = B₂ := by
    ext a b
    simp only [block, Matrix.submatrix_apply, hcols₂, matrixEquiv_augmentIdentity_castAdd, heB',
      hB₂, hπ, id_eq]
  have hd₂ : d₂ = B₂.det := by rw [← hblock₂]; exact hS₂.denom_eq
  have hd₂0 : d₂ ≠ 0 := hS₂.denom_ne
  -- the adjugate read off the second pass
  have hadj : matrixEquiv (Hex.Matrix.adjugateOf
      (⟨⟨r, rows₂, cols₂⟩, d₂, M₂⟩ : Hex.Matrix.ReducedForm R r (r + r))) =
      B₂.adjugate.submatrix id π.symm := by
    ext k l
    rw [Hex.Matrix.adjugateOf, matrixEquiv_ofFn, Matrix.submatrix_apply, id_eq, pivotRowAt_eq,
      Hex.Matrix.getElem_pair_eq_nested, ← matrixEquiv_apply]
    have h := congrFun (hS₂.pivot_row k) ⟨r + l.val, by omega⟩
    rw [h]
    simp only [coeff, hblock₂, Matrix.mul_apply, Matrix.submatrix_apply, id_eq]
    have hnat : (⟨r + l.val, by omega⟩ : Fin (r + r)) = Fin.natAdd r l := rfl
    simp only [hnat, matrixEquiv_augmentIdentity_natAdd, ← hπ, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (π.symm l)]
    · simp
    · intro b _ hb
      rw [ite_eq_right]
      intro h'
      exact hb (by rw [← h', Equiv.symm_apply_apply])
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  rw [hadj]
  -- identity 2
  have hid2 : eB * B₂.adjugate.submatrix id π.symm = d₂ • (1 : Matrix (Fin r) (Fin r) R) := by
    have h : (eB * B₂.adjugate).submatrix π id = d₂ • (1 : Matrix (Fin r) (Fin r) R) := by
      rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id, ← hB₂,
        hd₂]
      exact Matrix.mul_adjugate B₂
    ext a b
    rw [Matrix.mul_apply]
    have hab := congrFun (congrFun h (π.symm a)) (π.symm b)
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply, id_eq, Matrix.mul_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Equiv.symm_apply_eq,
      Equiv.apply_symm_apply] at hab
    simpa [Matrix.smul_apply, Matrix.one_apply] using hab
  refine ⟨hd₂0, hid2, ?_⟩
  -- identity 3, from the first pass
  have hid1 := hS.identity
  simp only [coeff, block] at hid1
  have hd : d = eB.det := hS.denom_eq
  have hd0 : d ≠ 0 := hS.denom_ne
  have hscale : d • B₂.adjugate.submatrix id π.symm = d₂ • eB.adjugate := by
    apply mul_left_cancel_of_det_ne_zero (hd ▸ hd0)
    rw [Matrix.mul_smul, hid2, Matrix.mul_smul, Matrix.mul_adjugate, ← hd, smul_smul, smul_smul,
      mul_comm]
  ext i j
  have h := congrFun (congrFun hid1 i) j
  apply mul_left_cancel₀ hd0
  calc d * (d₂ • eA) i j = d₂ * (d • eA) i j := by
        simp only [Matrix.smul_apply, smul_eq_mul]; ring
    _ = d₂ * (eA.submatrix id cols.get * (eB.adjugate * eA.submatrix rows.get id)) i j := by
        rw [h]
    _ = (eA.submatrix id cols.get * ((d₂ • eB.adjugate) * eA.submatrix rows.get id)) i j := by
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    _ = (eA.submatrix id cols.get * ((d • B₂.adjugate.submatrix id π.symm) *
          eA.submatrix rows.get id)) i j := by rw [hscale]
    _ = d * (eA.submatrix id cols.get * (B₂.adjugate.submatrix id π.symm *
          eA.submatrix rows.get id)) i j := by
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]

/-- Producer correctness: the certificate emitted by `rankCertWith` checks. -/
theorem rankCertWith_check (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a) (h1 : (1 : R) ≠ 0)
    (A : Hex.Matrix R n m) :
    Hex.Matrix.checkRank A (Hex.Matrix.rankCertWith quot A) = true :=
  rankCertOf_check hquot h1 A (inv_rowReduceWith hquot h1 A)

/-- Completeness with no quotient hypothesis: every matrix over a domain has a
certificate that checks, through the classical exact quotient. -/
theorem exists_rankCert [IsDomain R] (A : Hex.Matrix R n m) :
    ∃ c : Hex.Matrix.RankCert R n m, Hex.Matrix.checkRank A c = true := by
  classical
  let quot : R → R → R := fun a b => if h : ∃ q, a = q * b then h.choose else 0
  have hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a := by
    intro a b hb
    have h : ∃ q, a * b = q * b := ⟨a, rfl⟩
    simp only [quot, dite_eq_left h]
    exact mul_right_cancel₀ hb h.choose_spec.symm
  exact ⟨_, rankCertWith_check hquot one_ne_zero A⟩

end HexMatrixMathlib
