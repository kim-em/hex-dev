/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRankMathlib.Profile
public import HexRankMathlib.Extension

public section

/-!
The row rank profile.

The producer's pivot rows are, as a set, the row rank profile. The argument
is the one of the SPEC: the row chosen at a pivot step is the least-index
non-pivot row with a nonzero eliminated entry, and if it were a combination
of the rows before it, then applying the elimination (a linear map on rows)
would make its eliminated entry a combination of the eliminated entries of
the earlier non-pivot rows, all zero. So every chosen row is a profile row,
and since the number of chosen rows is the rank, which is also the number of
profile rows, the two sets agree. Ranks of row prefixes are compared over the
field of fractions, where `Matrix.rank` is the dimension of the row span.
-/

open Matrix

namespace HexMatrixMathlib

universe u

variable {R : Type u} [CommRing R] [DecidableEq R] {n m : Nat}

namespace RowReduce

omit [DecidableEq R] in
/-- The first `t` rows of `A`. -/
abbrev rowsTo (A : Matrix (Fin n) (Fin m) R) {t : Nat} (ht : t ≤ n) : Matrix (Fin t) (Fin m) R :=
  A.submatrix (Fin.castLE ht) id

omit [DecidableEq R] in
/-- The range of a tuple over `Fin (t + 1)` splits off its last entry. -/
theorem range_fin_succ {α : Type u} {t : Nat} (f : Fin (t + 1) → α) :
    Set.range f = insert (f (Fin.last t)) (Set.range (f ∘ Fin.castSucc)) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | last => exact Set.mem_insert _ _
    | cast i => exact Set.mem_insert_of_mem _ ⟨i, rfl⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

omit [DecidableEq R] in
/-- Adding a row never lowers the rank. -/
theorem rank_rowsTo_le [IsDomain R] (A : Matrix (Fin n) (Fin m) R) {t : Nat} (ht : t + 1 ≤ n) :
    (rowsTo A (Nat.le_of_succ_le ht)).rank ≤ (rowsTo A ht).rank := by
  have h : rowsTo A (Nat.le_of_succ_le ht) = (rowsTo A ht).submatrix Fin.castSucc id := by
    ext i j
    simp [rowsTo]
  rw [h]
  exact rank_submatrix_le _ _ _

omit [DecidableEq R] in
/-- Adding a row raises the rank by at most one. -/
theorem rank_rowsTo_succ_le [IsDomain R] (A : Matrix (Fin n) (Fin m) R) {t : Nat}
    (ht : t + 1 ≤ n) :
    (rowsTo A ht).rank ≤ (rowsTo A (Nat.le_of_succ_le ht)).rank + 1 := by
  classical
  let K := FractionRing R
  let φ := algebraMap R K
  rw [← rank_map_eq (K := K) (rowsTo A ht), ← rank_map_eq (K := K) (rowsTo A _)]
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
  have hrange : Set.range ((rowsTo A ht).map φ).row =
      insert (((rowsTo A ht).map φ).row (Fin.last t))
        (Set.range ((rowsTo A (Nat.le_of_succ_le ht)).map φ).row) := by
    rw [range_fin_succ]
    congr 1
  rw [hrange, Submodule.span_insert]
  refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
  rw [Nat.add_comm]
  apply Nat.add_le_add_left
  refine (finrank_span_le_card _).trans ?_
  simp

omit [DecidableEq R] in
/-- The rank of the first `t` rows, as a total function of `t`. -/
noncomputable def prefixRank [IsDomain R] (A : Matrix (Fin n) (Fin m) R) (t : Nat) : Nat :=
  if ht : t ≤ n then (rowsTo A ht).rank else 0

omit [DecidableEq R] in
theorem prefixRank_eq [IsDomain R] (A : Matrix (Fin n) (Fin m) R) {t : Nat} (ht : t ≤ n) :
    prefixRank A t = (rowsTo A ht).rank := by
  simp [prefixRank, ht]

omit [DecidableEq R] in
/-- Each row raises the prefix rank by zero or one. -/
theorem prefixRank_succ [IsDomain R] (A : Matrix (Fin n) (Fin m) R) {t : Nat} (ht : t + 1 ≤ n) :
    prefixRank A (t + 1) = prefixRank A t ∨ prefixRank A (t + 1) = prefixRank A t + 1 := by
  rw [prefixRank_eq A ht, prefixRank_eq A (Nat.le_of_succ_le ht)]
  have h1 := rank_rowsTo_le A ht
  have h2 := rank_rowsTo_succ_le A ht
  omega

omit [DecidableEq R] in
/-- The prefix rank telescopes over the rows that raise it. -/
theorem prefixRank_eq_sum [IsDomain R] (A : Matrix (Fin n) (Fin m) R) :
    ∀ (t : Nat), t ≤ n → prefixRank A t = ∑ i : Fin t,
      if prefixRank A (i.val + 1) = prefixRank A i.val + 1 then 1 else 0
  | 0, _ => by
    simp only [prefixRank, rowsTo, Nat.zero_le, dite_true, Finset.univ_eq_empty, Finset.sum_empty]
    exact Nat.le_zero.mp ((rank_le_card_height _).trans (by simp))
  | t + 1, ht => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← prefixRank_eq_sum A t (Nat.le_of_succ_le ht)]
    rcases prefixRank_succ A ht with h | h
    · simp [h]
    · simp [h]

omit [DecidableEq R] in
/-- The prefix rank of all the rows is the rank. -/
theorem prefixRank_top [IsDomain R] (A : Matrix (Fin n) (Fin m) R) :
    prefixRank A n = A.rank := by
  rw [prefixRank_eq A (le_refl n)]
  have : rowsTo A (le_refl n) = A := by
    ext i j
    simp [rowsTo]
  rw [this]

/-- The elimination by a pivot block, as a map on row vectors: `x ↦ d • x - x[cols] * U`. -/
private def elimRow {K : Type u} [CommRing K] {r : Nat} (d : K) (cols : Fin r → Fin m)
    (U : Fin r → Fin m → K) (x : Fin m → K) : Fin m → K :=
  fun j' => d * x j' - ∑ l, x (cols l) * U l j'

/-- The pivot row chosen at a step is not a combination of the rows before it:
its prefix rank increment is one. -/
theorem prefixRank_succ_of_pivot {quot : R → R → R}
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a) (h1 : (1 : R) ≠ 0)
    (A : Hex.Matrix R n m) {t : Nat} {S : Hex.Matrix.ReducedForm R n m}
    (hS : Inv (matrixEquiv A) t S) {j : Fin m} {p : Fin n}
    (hp : Hex.Matrix.findPivotRow? S.matrix S.profile.rows.toList j = some p) :
    have := isDomain_of_quot quot hquot h1
    prefixRank (matrixEquiv A) (p.val + 1) = prefixRank (matrixEquiv A) p.val + 1 := by
  have := isDomain_of_quot quot hquot h1
  classical
  obtain ⟨hp_notin, hpiv, hleast⟩ := Hex.Matrix.findPivotRow?_some hp
  set E := matrixEquiv A with hEdef
  have hpn : p.val + 1 ≤ n := p.isLt
  rcases prefixRank_succ E hpn with heq | heq
  · exfalso
    -- row `p` is a combination of the rows before it over the fraction field
    let K := FractionRing R
    let φ : R →+* K := algebraMap R K
    have hinj : Function.Injective φ := IsFractionRing.injective R K
    rw [prefixRank_eq E hpn, prefixRank_eq E (Nat.le_of_succ_le hpn)] at heq
    rw [← rank_map_eq (K := K) (rowsTo E hpn), ← rank_map_eq (K := K) (rowsTo E _),
      Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row, range_fin_succ] at heq
    have hrows : ((rowsTo E hpn).map φ).row ∘ Fin.castSucc =
        ((rowsTo E (Nat.le_of_succ_le hpn)).map φ).row := by
      funext i
      simp [rowsTo]
      rfl
    rw [hrows, Submodule.span_insert] at heq
    set v : Fin m → K := ((rowsTo E hpn).map φ).row (Fin.last p.val) with hvdef
    set rowsK := ((rowsTo E (Nat.le_of_succ_le hpn)).map φ).row with hrowsKdef
    have hspan : Submodule.span K (Set.range rowsK) = K ∙ v ⊔ Submodule.span K (Set.range rowsK) :=
      Submodule.eq_of_le_of_finrank_eq le_sup_right heq.symm
    have hv : v ∈ Submodule.span K (Set.range rowsK) := by
      rw [hspan]
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
    -- the elimination as a map on rows over `K`
    have hL_pivot : ∀ i, i ∈ S.profile.rows.toList →
        elimRow (φ S.denom) S.profile.cols.get (fun l j' => φ (coeff E S l j'))
          (fun j' => φ (E i j')) = 0 := by
      intro i hi
      obtain ⟨k, rfl⟩ := (mem_toList_iff _ _).mp hi
      funext j'
      have h := congrFun (congrFun (block_mul_coeff E S) k) j'
      rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, ← hS.denom_eq] at h
      simp only [block, Matrix.submatrix_apply, id_eq] at h
      show φ S.denom * φ (E (S.profile.rows.get k) j') -
        ∑ l, φ (E (S.profile.rows.get k) (S.profile.cols.get l)) * φ (coeff E S l j') = 0
      rw [← map_mul, ← h, map_sum, sub_eq_zero]
      exact Finset.sum_congr rfl fun l _ => map_mul φ _ _
    have hL_other : ∀ i, i ∉ S.profile.rows.toList →
        elimRow (φ S.denom) S.profile.cols.get (fun l j' => φ (coeff E S l j'))
          (fun j' => φ (E i j')) = fun j' => φ (matrixEquiv S.matrix i j') := by
      intro i hi
      funext j'
      have h := congrFun (hS.other_row i hi) j'
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct] at h
      show φ S.denom * φ (E i j') - ∑ l, φ (E i (S.profile.cols.get l)) * φ (coeff E S l j') =
        φ (matrixEquiv S.matrix i j')
      rw [h, map_sub, map_mul, map_sum]
      congr 1
      exact Finset.sum_congr rfl fun l _ => (map_mul φ _ _).symm
    -- apply the elimination to the dependence at column `j`
    have hLv : elimRow (φ S.denom) S.profile.cols.get (fun l j' => φ (coeff E S l j')) v =
        fun j' => φ (matrixEquiv S.matrix p j') := by
      have hvE : v = fun j' => φ (E p j') := by
        funext j'
        simp [hvdef, rowsTo]
        rfl
      rw [hvE]
      exact hL_other p hp_notin
    -- the mapped coefficients, as an opaque function
    generalize hW : (fun l j' => φ (coeff E S l j')) = W at hL_pivot hL_other hLv
    -- `v` is the combination `∑ c i • rowsK i`, entrywise
    have hvj : ∀ j', v j' = ∑ i, c i * rowsK i j' := by
      intro j'
      rw [← hc, Finset.sum_apply]
      rfl
    -- the elimination is linear, so it carries the combination to the
    -- eliminated rows before `p`, all zero at column `j`
    have hLv_sum : elimRow (φ S.denom) S.profile.cols.get W v j =
        ∑ i, c i * elimRow (φ S.denom) S.profile.cols.get W (rowsK i) j := by
      show φ S.denom * v j - ∑ l, v (S.profile.cols.get l) * W l j =
        ∑ i, c i * (φ S.denom * rowsK i j - ∑ l, rowsK i (S.profile.cols.get l) * W l j)
      have hvc : ∑ l, v (S.profile.cols.get l) * W l j =
          ∑ l, (∑ i, c i * rowsK i (S.profile.cols.get l)) * W l j :=
        Finset.sum_congr rfl fun l _ => by rw [hvj]
      have e1 : φ S.denom * ∑ i, c i * rowsK i j = ∑ i, c i * (φ S.denom * rowsK i j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ l, (∑ i, c i * rowsK i (S.profile.cols.get l)) * W l j =
          ∑ i, c i * ∑ l, rowsK i (S.profile.cols.get l) * W l j := by
        rw [show (∑ l, (∑ i, c i * rowsK i (S.profile.cols.get l)) * W l j) =
            ∑ l, ∑ i, c i * rowsK i (S.profile.cols.get l) * W l j from
          Finset.sum_congr rfl fun l _ => Finset.sum_mul _ _ _]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [hvj j, hvc, e1, e2, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hzero : ∀ i : Fin p.val, elimRow (φ S.denom) S.profile.cols.get W (rowsK i) j = 0 := by
      intro i
      let i' : Fin n := Fin.castLE (Nat.le_of_succ_le hpn) i
      have hi'E : rowsK i = fun j' => φ (E i' j') := by
        funext j'
        simp [hrowsKdef, rowsTo, i']
      have hi'lt : i' < p := by
        rw [Fin.lt_def]
        simp [i']
      rw [hi'E]
      by_cases hmem : i' ∈ S.profile.rows.toList
      · rw [hL_pivot i' hmem]
        rfl
      · rw [hL_other i' hmem]
        show φ (matrixEquiv S.matrix i' j) = 0
        rw [matrixEquiv_apply, hleast i' hi'lt hmem, map_zero]
    have hMpj : φ (matrixEquiv S.matrix p j) = 0 := by
      rw [← congrFun hLv j, hLv_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [hzero i, mul_zero]
    rw [matrixEquiv_apply] at hMpj
    exact hpiv ((map_eq_zero_iff φ hinj).mp hMpj)
  · exact heq

/-- The profiles only grow along the pass, as list prefixes. -/
theorem reduceCols_prefix (quot : R → R → R) (A : Hex.Matrix R n m) {t t' : Nat}
    (h : t ≤ t') (ht' : t' ≤ m) :
    (reduceCols quot A t).profile.rows.toList <+: (reduceCols quot A t').profile.rows.toList ∧
    (reduceCols quot A t).profile.cols.toList <+: (reduceCols quot A t').profile.cols.toList := by
  induction t' with
  | zero =>
    have : t = 0 := by omega
    subst this
    exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | succ t' ih =>
    rcases Nat.lt_or_ge t (t' + 1) with hlt | hge
    · obtain ⟨hr, hc⟩ := ih (by omega) (by omega)
      rw [reduceCols_succ quot A (by omega)]
      cases hp : Hex.Matrix.findPivotRow? (reduceCols quot A t').matrix
          (reduceCols quot A t').profile.rows.toList ⟨t', by omega⟩ with
      | none =>
        rw [Hex.Matrix.reduceStep_skip hp]
        exact ⟨hr, hc⟩
      | some p =>
        rw [Hex.Matrix.reduceStep_pivot_profile hp]
        simp only [Vector.toList_push]
        exact ⟨hr.trans (List.prefix_append _ _), hc.trans (List.prefix_append _ _)⟩
    · have : t = t' + 1 := by omega
      subst this
      exact ⟨List.prefix_refl _, List.prefix_refl _⟩

/-- Each recorded pivot row was found by the search at its pivot column. -/
theorem findPivotRow?_reduceCols_eq {quot : R → R → R}
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a) (h1 : (1 : R) ≠ 0)
    (A : Hex.Matrix R n m) (k : Fin (Hex.Matrix.rowReduceWith quot A).profile.rank) :
    let j := (Hex.Matrix.rowReduceWith quot A).profile.cols.get k
    Hex.Matrix.findPivotRow? (reduceCols quot A j.val).matrix
      (reduceCols quot A j.val).profile.rows.toList j =
      some ((Hex.Matrix.rowReduceWith quot A).profile.rows.get k) := by
  intro j
  have hS := inv_rowReduceWith hquot h1 A
  have hSt := inv_reduceCols hquot h1 A (t := j.val) j.isLt.le
  have hmem : j ∈ (Hex.Matrix.rowReduceWith quot A).profile.cols.toList :=
    (mem_toList_iff _ _).mpr ⟨k, rfl⟩
  have hsome := (mem_cols_iff_pivot hquot h1 A j).mp hmem
  cases hp : Hex.Matrix.findPivotRow? (reduceCols quot A j.val).matrix
      (reduceCols quot A j.val).profile.rows.toList j with
  | none => rw [hp] at hsome; exact absurd hsome (by simp)
  | some p =>
    congr 1
    -- the state after column `j` has `rows_t.push p` and `cols_t.push j`, both
    -- prefixes of the final profile, and `cols_t` has exactly `k` entries
    have hstep := reduceCols_succ quot A j.isLt
    have hj : (⟨j.val, j.isLt⟩ : Fin m) = j := rfl
    rw [hj] at hstep
    have hprof : (reduceCols quot A (j.val + 1)).profile =
        { rank := (reduceCols quot A j.val).profile.rank + 1,
          rows := (reduceCols quot A j.val).profile.rows.push p,
          cols := (reduceCols quot A j.val).profile.cols.push j } := by
      rw [hstep]
      exact Hex.Matrix.reduceStep_pivot_profile hp
    obtain ⟨hr, hc⟩ := reduceCols_prefix quot A (t := j.val + 1) j.isLt (le_refl m)
    rw [← rowReduceWith_eq_reduceCols, hprof] at hr hc
    simp only [Vector.toList_push] at hr hc
    set St := reduceCols quot A j.val
    have hlen : St.profile.cols.toList.length = k.val := by
      -- the entry after the prefix `cols_t` is `j = cols k`, so its index is `k`
      have hget := hc.getElem (i := St.profile.cols.toList.length) (by simp)
      rw [List.getElem_concat_length rfl] at hget
      have hlt : St.profile.cols.toList.length <
          (Hex.Matrix.rowReduceWith quot A).profile.cols.toList.length :=
        hc.length_le.trans_lt' (by simp)
      have hlt' : St.profile.cols.toList.length <
          (Hex.Matrix.rowReduceWith quot A).profile.rank := by
        simpa using hlt
      have hget' : (Hex.Matrix.rowReduceWith quot A).profile.cols.get ⟨_, hlt'⟩ = j := by
        rw [hget]
        simp [Vector.get]
      exact congrArg Fin.val (hS.cols_mono.injective hget')
    have hget := hr.getElem (i := St.profile.rows.toList.length) (by simp)
    rw [List.getElem_concat_length rfl] at hget
    have hlenr : St.profile.rows.toList.length = k.val := by
      rw [Vector.length_toList] at hlen ⊢
      exact hlen
    have hlt'' : St.profile.rows.toList.length < (Hex.Matrix.rowReduceWith quot A).profile.rank := by
      rw [hlenr]
      exact k.isLt
    have hget' : (Hex.Matrix.rowReduceWith quot A).profile.rows.get ⟨_, hlt''⟩ = p := by
      rw [hget]
      simp [Vector.get]
    have hk : (⟨St.profile.rows.toList.length, hlt''⟩ :
        Fin (Hex.Matrix.rowReduceWith quot A).profile.rank) = k := Fin.ext hlenr
    rw [hk] at hget'
    exact hget'.symm

end RowReduce

open RowReduce

variable {quot : R → R → R}

/-- The producer's pivot rows are, as a set, the row rank profile. -/
theorem rowReduceWith_rows_eq_rowProfile (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0) (A : Hex.Matrix R n m) :
    IsRowRankProfile (matrixEquiv A) (Hex.Matrix.rowReduceWith quot A).profile.rows.toList := by
  have := isDomain_of_quot quot hquot h1
  classical
  set D := Hex.Matrix.rowReduceWith quot A with hD
  have hS : Inv (matrixEquiv A) m D := inv_rowReduceWith hquot h1 A
  set E := matrixEquiv A with hE
  -- every recorded pivot row raises the prefix rank
  have hpiv : ∀ k, prefixRank E ((D.profile.rows.get k).val + 1) =
      prefixRank E (D.profile.rows.get k).val + 1 := by
    intro k
    have hfind := findPivotRow?_reduceCols_eq hquot h1 A k
    exact prefixRank_succ_of_pivot hquot h1 A
      (inv_reduceCols hquot h1 A (t := (D.profile.cols.get k).val) (D.profile.cols.get k).isLt.le)
      hfind
  -- the profile rows are counted by the rank, as are the recorded pivot rows
  let P : Finset (Fin n) := Finset.univ.filter fun i =>
    prefixRank E (i.val + 1) = prefixRank E i.val + 1
  have hcardP : P.card = D.profile.rank := by
    rw [Finset.card_filter, ← prefixRank_eq_sum E n (le_refl n), prefixRank_top, hS.rank_eq]
  let rowsF : Finset (Fin n) := Finset.univ.image D.profile.rows.get
  have hcardRows : rowsF.card = D.profile.rank := by
    rw [Finset.card_image_of_injective _ hS.rows_injective, Finset.card_univ, Fintype.card_fin]
  have hsub : rowsF ⊆ P := by
    intro i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpiv k⟩
  have heq : rowsF = P := Finset.eq_of_subset_of_card_le hsub (by rw [hcardP, hcardRows])
  unfold IsRowRankProfile
  intro i
  have h1' : i ∈ D.profile.rows.toList ↔ i ∈ rowsF := by
    rw [mem_toList_iff, Finset.mem_image]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, Finset.mem_univ _, hk⟩
    · rintro ⟨k, _, hk⟩; exact ⟨k, hk⟩
  rw [h1', heq, Finset.mem_filter, prefixRank_eq E (Nat.succ_le_of_lt i.isLt),
    prefixRank_eq E i.isLt.le]
  simp only [Finset.mem_univ, true_and]

end HexMatrixMathlib
