/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHermite.Hermite
public import HexMatrix.Lattice
public import HexRowReduce.Span

public section

/-! Canonicity of integer row Hermite normal form. -/

namespace Hex.Matrix

namespace IsHNF

private theorem recover {A H : Matrix Int n m} {U W : Matrix Int n n}
    (hUA : U * A = H) (hWU : W * U = Matrix.identity (R := Int) n) :
    W * H = A := by
  calc
    W * H = W * (U * A) := by rw [hUA]
    _ = (W * U) * A := (Matrix.mul_assoc W U A).symm
    _ = Matrix.identity (R := Int) n * A := by rw [hWU]
    _ = A := Matrix.identity_mul A

/-- A certified HNF and its input generate the same integer row lattice. -/
theorem memLattice_iff {A : Matrix Int n m} {D : RowEchelonData Int n m}
    (h : IsHNF A D) (v : Vector Int m) :
    A.memLattice v ↔ D.echelon.memLattice v := by
  rcases h.toIsEchelonForm.transform_inv with ⟨W, hWU⟩
  exact memLattice_iff_of_mul_eq h.transform_mul
    (recover h.transform_mul hWU) v

private theorem row_coeffs {A : Matrix Int n m} {B : Matrix Int n' m}
    {D : RowEchelonData Int n m} {E : RowEchelonData Int n' m}
    (h : IsHNF A D) (h' : IsHNF B E)
    (hL : ∀ v, A.memLattice v ↔ B.memLattice v) (i : Fin n') :
    ∃ c : Vector Int n, vecMul c D.echelon = E.echelon[i] := by
  have hi : E.echelon.memLattice E.echelon[i] := row_memLattice E.echelon i
  have hiB : B.memLattice E.echelon[i] := (h'.memLattice_iff _).2 hi
  have hiA : A.memLattice E.echelon[i] := (hL _).2 hiB
  exact (h.memLattice_iff _).1 hiA

private theorem vecMul_pivot {A : Matrix Int n m} {D : RowEchelonData Int n m}
    (h : IsHNF A D) (c : Vector Int n) (i : Fin D.rank)
    (hz : ∀ k : Fin n, k.val < i.val → c[k] = 0) :
    (vecMul c D.echelon)[D.pivotCols.get i] =
      c[h.toIsEchelonForm.pivotRow i] *
        D.echelon[h.toIsEchelonForm.pivotRow i][D.pivotCols.get i] := by
  let pivotRow := h.toIsEchelonForm.pivotRow i
  change (c * D.echelon)[D.pivotCols.get i] =
    c[pivotRow] * D.echelon[pivotRow][D.pivotCols.get i]
  rw [getElem_vecMul]
  unfold Vector.dotProduct
  calc
    (List.finRange n).foldl
        (fun acc k => acc + (col D.echelon (D.pivotCols.get i))[k] * c[k]) 0 =
      (List.finRange n).foldl
        (fun acc k => acc +
          if k = pivotRow then
            c[pivotRow] * D.echelon[pivotRow][D.pivotCols.get i]
          else 0) 0 := by
        apply List.foldl_add_congr
        intro k _hk
        rw [getElem_col]
        by_cases hki : k = pivotRow
        · subst k
          rw [if_pos rfl]
          exact Int.mul_comm _ _
        · rw [if_neg hki]
          have hkval : k.val ≠ i.val := by
            intro heq
            exact hki (Fin.ext (by simpa [pivotRow, IsEchelonForm.pivotRow] using heq))
          rcases Nat.lt_or_gt_of_ne hkval with hlt | hgt
          · rw [hz k hlt]
            omega
          · rw [h.toIsEchelonForm.below_pivot_zero i k hgt]
            omega
    _ = c[pivotRow] * D.echelon[pivotRow][D.pivotCols.get i] := by
      rw [List.foldl_add_single (List.finRange n) 0 pivotRow
        (fun _ => c[pivotRow] * D.echelon[pivotRow][D.pivotCols.get i])
        (List.mem_finRange _) (List.nodup_finRange n)]
      omega

private theorem vecMul_zero {A : Matrix Int n m} {D : RowEchelonData Int n m}
    (h : IsHNF A D) (c : Vector Int n)
    (hz : ∀ i : Fin D.rank, c[h.toIsEchelonForm.pivotRow i] = 0) :
    vecMul c D.echelon = 0 := by
  apply Vector.ext
  intro j hj
  let col : Fin m := ⟨j, hj⟩
  change (c * D.echelon)[col] = (0 : Vector Int m)[j]
  simp only [Vector.getElem_zero]
  rw [getElem_vecMul]
  unfold Vector.dotProduct
  apply List.foldl_add_eq_self
  intro k _hk
  rw [getElem_col]
  by_cases hkr : k.val < D.rank
  · let i : Fin D.rank := ⟨k.val, hkr⟩
    have hkrow : h.toIsEchelonForm.pivotRow i = k := Fin.ext rfl
    rw [← hkrow, hz i]
    omega
  · have hrow := h.toIsEchelonForm.zero_row k (by omega)
    have hentry := congrArg (fun row => row[col.val]'col.isLt) hrow
    have hentry' : D.echelon[k][col] = 0 := by
      change D.echelon[k][col.val]'col.isLt = 0
      simpa only [Vector.getElem_zero col.val col.isLt] using hentry
    rw [hentry']
    omega

private theorem firstCoeff {A : Matrix Int n m} {D : RowEchelonData Int n m}
    (h : IsHNF A D) (c : Vector Int n) (hne : vecMul c D.echelon ≠ 0) :
    ∃ q : Fin D.rank,
      c[h.toIsEchelonForm.pivotRow q] ≠ 0 ∧
      ∀ k : Fin n, k.val < q.val → c[k] = 0 := by
  have hex : ∃ q : Fin D.rank, c[h.toIsEchelonForm.pivotRow q] ≠ 0 := by
    classical
    apply Classical.byContradiction
    intro hall
    apply hne
    apply vecMul_zero h c
    intro q
    apply Classical.not_not.mp
    intro hq
    exact hall ⟨q, hq⟩
  let p : Nat → Bool := fun k =>
    if hk : k < D.rank then
      decide (c[h.toIsEchelonForm.pivotRow ⟨k, hk⟩] ≠ 0)
    else false
  cases hfind : (List.range D.rank).find? p with
  | none =>
      have hall := List.find?_range_eq_none.mp hfind
      rcases hex with ⟨q, hq⟩
      have hfalse := hall q.val q.isLt
      simp only [p, dif_pos q.isLt, decide_not, Bool.not_not] at hfalse
      have heq : c[h.toIsEchelonForm.pivotRow q] = 0 := by
        exact of_decide_eq_true hfalse
      exact absurd heq hq
  | some qv =>
      have hspec := List.find?_range_eq_some.mp hfind
      have hqrank : qv < D.rank := by simpa using hspec.2.1
      let q : Fin D.rank := ⟨qv, hqrank⟩
      have hqne : c[h.toIsEchelonForm.pivotRow q] ≠ 0 := by
        have hp := hspec.1
        simpa only [p, dif_pos hqrank, decide_eq_true_eq] using hp
      refine ⟨q, hqne, ?_⟩
      intro k hk
      have hkrank : k.val < D.rank := Nat.lt_trans hk q.isLt
      have hfalse := hspec.2.2 k.val hk
      simp only [p, dif_pos hkrank, decide_not, Bool.not_not] at hfalse
      have heq : c[h.toIsEchelonForm.pivotRow
          (⟨k.val, hkrank⟩ : Fin D.rank)] = 0 := of_decide_eq_true hfalse
      simpa only [IsEchelonForm.pivotRow] using heq

private theorem vecMul_before {A : Matrix Int n m} {D : RowEchelonData Int n m}
    (h : IsHNF A D) (c : Vector Int n) (q : Fin D.rank)
    (hz : ∀ k : Fin n, k.val < q.val → c[k] = 0)
    (j : Fin m) (hj : j < D.pivotCols.get q) :
    (vecMul c D.echelon)[j] = 0 := by
  change (c * D.echelon)[j] = 0
  rw [getElem_vecMul]
  unfold Vector.dotProduct
  apply List.foldl_add_eq_self
  intro k _hk
  rw [getElem_col]
  by_cases hkq : k.val < q.val
  · rw [hz k hkq]
    omega
  · by_cases hkr : k.val < D.rank
    · let p : Fin D.rank := ⟨k.val, hkr⟩
      have hqp : q ≤ p := by simpa [Fin.le_def] using Nat.le_of_not_gt hkq
      have hpivot : D.pivotCols.get q ≤ D.pivotCols.get p := by
        rcases Nat.lt_or_eq_of_le hqp with hlt | heq
        · exact Fin.le_of_lt (h.toIsEchelonForm.pivotCols_sorted q p hlt)
        · have hqpEq : q = p := Fin.ext heq
          rw [hqpEq]
          exact Fin.le_refl _
      have hlead := h.pivot_leading p j (Fin.lt_of_lt_of_le hj hpivot)
      have hrow : h.toIsEchelonForm.pivotRow p = k := Fin.ext rfl
      have hlead' : D.echelon[h.toIsEchelonForm.pivotRow p][j] = 0 := by
        change D.echelon[h.toIsEchelonForm.pivotRow p][j] = 0 at hlead
        exact hlead
      rw [← hrow, hlead']
      omega
    · have hrow := h.toIsEchelonForm.zero_row k (by omega)
      have hentry := congrArg (fun row => row[j.val]'j.isLt) hrow
      have hentry' : D.echelon[k][j] = 0 := by
        change D.echelon[k][j.val]'j.isLt = 0
        simpa only [Vector.getElem_zero j.val j.isLt] using hentry
      rw [hentry']
      omega

private theorem pivot_of_leading {A : Matrix Int n m}
    {D : RowEchelonData Int n m} (h : IsHNF A D) (c : Vector Int n)
    (col : Fin m)
    (hbefore : ∀ j : Fin m, j < col → (vecMul c D.echelon)[j] = 0)
    (hat : (vecMul c D.echelon)[col] ≠ 0) :
    ∃ q : Fin D.rank, D.pivotCols.get q = col := by
  have hvec : vecMul c D.echelon ≠ 0 := by
    intro hzero
    apply hat
    rw [hzero]
    exact Vector.getElem_zero col.val col.isLt
  rcases firstCoeff h c hvec with ⟨q, hqne, hqzero⟩
  have hqpivot : (vecMul c D.echelon)[D.pivotCols.get q] ≠ 0 := by
    rw [vecMul_pivot h c q hqzero]
    have hp : 0 < D.echelon[h.toIsEchelonForm.pivotRow q][D.pivotCols.get q] := by
      have hp' := h.pivot_pos q
      change 0 < D.echelon[h.toIsEchelonForm.pivotRow q][D.pivotCols.get q] at hp'
      exact hp'
    exact Int.mul_ne_zero hqne (Int.ne_of_gt hp)
  refine ⟨q, ?_⟩
  rcases Nat.lt_trichotomy (D.pivotCols.get q).val col.val with hlt | heq | hgt
  · exact absurd (hbefore _ hlt) hqpivot
  · exact Fin.ext heq
  · exact absurd (vecMul_before h c q hqzero col hgt) hat

private theorem pivot_exists {A : Matrix Int n m} {B : Matrix Int n' m}
    {D : RowEchelonData Int n m} {E : RowEchelonData Int n' m}
    (h : IsHNF A D) (h' : IsHNF B E)
    (hL : ∀ v, A.memLattice v ↔ B.memLattice v) (i : Fin E.rank) :
    ∃ q : Fin D.rank, D.pivotCols.get q = E.pivotCols.get i := by
  let row := h'.toIsEchelonForm.pivotRow i
  rcases row_coeffs h h' hL row with ⟨c, hc⟩
  apply pivot_of_leading h c (E.pivotCols.get i)
  · intro j hj
    rw [hc]
    have hlead := h'.pivot_leading i j hj
    change E.echelon[row][j] = 0
    change E.echelon[row][j] = 0 at hlead
    exact hlead
  · rw [hc]
    have hp := h'.pivot_pos i
    change 0 < E.echelon[row][E.pivotCols.get i] at hp
    exact Int.ne_of_gt hp

private theorem pairwisePivots {A : Matrix Int n m}
    {D : RowEchelonData Int n m} (h : IsHNF A D) :
    D.pivotCols.toList.Pairwise (fun a b => a < b) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < D.rank := by simpa using hi
  have hj' : j < D.rank := by simpa using hj
  change D.pivotCols.get (⟨i, hi'⟩ : Fin D.rank) <
    D.pivotCols.get (⟨j, hj'⟩ : Fin D.rank)
  exact h.toIsEchelonForm.pivotCols_sorted
    (⟨i, hi'⟩ : Fin D.rank) (⟨j, hj'⟩ : Fin D.rank) hij

private theorem pairwise_eq_of_mem {xs ys : List (Fin m)}
    (hx : xs.Pairwise (fun a b => a < b))
    (hy : ys.Pairwise (fun a b => a < b))
    (hm : ∀ x, x ∈ xs ↔ x ∈ ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          have := (hm y).2 (List.mem_cons_self)
          contradiction
  | cons x xs ih =>
      cases ys with
      | nil =>
          have := (hm x).1 (List.mem_cons_self)
          contradiction
      | cons y ys =>
          have hxy : x = y := by
            rcases Nat.lt_trichotomy x.val y.val with hlt | heq | hgt
            · have hxmem := (hm x).1 (List.mem_cons_self)
              rcases List.mem_cons.mp hxmem with hhead | htail
              · exact hhead
              · have hyx := (List.pairwise_cons.mp hy).1 x htail
                omega
            · exact Fin.ext heq
            · have hymem := (hm y).2 (List.mem_cons_self)
              rcases List.mem_cons.mp hymem with hhead | htail
              · exact hhead.symm
              · have hxy' := (List.pairwise_cons.mp hx).1 y htail
                omega
          subst y
          congr 1
          apply ih (List.pairwise_cons.mp hx).2 (List.pairwise_cons.mp hy).2
          intro z
          constructor
          · intro hz
            have hzall := (hm z).1 (List.mem_cons_of_mem x hz)
            rcases List.mem_cons.mp hzall with hzx | hzys
            · subst z
              exact absurd ((List.pairwise_cons.mp hx).1 x hz) (Fin.lt_irrefl _)
            · exact hzys
          · intro hz
            have hzall := (hm z).2 (List.mem_cons_of_mem x hz)
            rcases List.mem_cons.mp hzall with hzx | hzxs
            · subst z
              exact absurd ((List.pairwise_cons.mp hy).1 x hz) (Fin.lt_irrefl _)
            · exact hzxs

private theorem pivotLists_eq {A : Matrix Int n m} {B : Matrix Int n' m}
    {D : RowEchelonData Int n m} {E : RowEchelonData Int n' m}
    (h : IsHNF A D) (h' : IsHNF B E)
    (hL : ∀ v, A.memLattice v ↔ B.memLattice v) :
    D.pivotCols.toList = E.pivotCols.toList := by
  apply pairwise_eq_of_mem (pairwisePivots h) (pairwisePivots h')
  intro col
  simp only [Vector.mem_toList_iff, Vector.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, hcol⟩
    rcases pivot_exists h' h (fun v => (hL v).symm) (⟨i, hi⟩ : Fin D.rank) with
      ⟨q, hq⟩
    exact ⟨q.val, q.isLt, hq.trans hcol⟩
  · rintro ⟨i, hi, hcol⟩
    rcases pivot_exists h h' hL (⟨i, hi⟩ : Fin E.rank) with ⟨q, hq⟩
    exact ⟨q.val, q.isLt, hq.trans hcol⟩

private theorem vector_heq_of_toList_eq {x : Vector α n} {y : Vector α m}
    (h : x.toList = y.toList) : HEq x y := by
  have hnm : n = m := by
    have hlen := congrArg List.length h
    simpa using hlen
  subst m
  apply heq_of_eq
  apply Vector.toArray_inj.mp
  apply Array.toList_inj.mp
  exact h

private theorem positive_associates_eq {a b x y : Int}
    (ha : 0 < a) (hb : 0 < b) (hba : b = x * a) (hab : a = y * b) :
    a = b := by
  have hxa : 0 < x * a := by rw [← hba]; exact hb
  have hxb : 0 < x := Int.pos_of_mul_pos_left hxa ha
  have hyb : 0 < y * b := by rw [← hab]; exact ha
  have hy : 0 < y := Int.pos_of_mul_pos_left hyb hb
  have hyxA : (y * x) * a = (1 : Int) * a := by
    calc
      (y * x) * a = y * (x * a) := Int.mul_assoc _ _ _
      _ = y * b := by rw [← hba]
      _ = a := hab.symm
      _ = 1 * a := by omega
  have hyx : y * x = 1 :=
    Int.eq_of_mul_eq_mul_right (Int.ne_of_gt ha) hyxA
  have hxle : x ≤ y * x := by
    have hmul := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ y by omega)
      (show 0 ≤ x by omega)
    simpa only [Int.one_mul] using hmul
  have hxone : x = 1 := by omega
  rw [hba, hxone, Int.one_mul]

private theorem pivotGet_of_lists {D : RowEchelonData Int n m}
    {E : RowEchelonData Int n' m}
    (hp : D.pivotCols.toList = E.pivotCols.toList)
    {i : Nat} (hiD : i < D.rank) (hiE : i < E.rank) :
    D.pivotCols.get ⟨i, hiD⟩ = E.pivotCols.get ⟨i, hiE⟩ := by
  have hget := congrArg (fun xs => xs[i]?) hp
  rw [List.getElem?_eq_getElem (by simpa using hiD),
    List.getElem?_eq_getElem (by simpa using hiE)] at hget
  injection hget

private theorem rowCoeffLeading {A : Matrix Int n m} {B : Matrix Int n' m}
    {D : RowEchelonData Int n m} {E : RowEchelonData Int n' m}
    (h : IsHNF A D) (h' : IsHNF B E)
    (hL : ∀ v, A.memLattice v ↔ B.memLattice v)
    (hp : D.pivotCols.toList = E.pivotCols.toList)
    {i : Nat} (hiD : i < D.rank) (hiE : i < E.rank) :
    ∃ c : Vector Int n,
      vecMul c D.echelon = E.echelon[h'.toIsEchelonForm.pivotRow ⟨i, hiE⟩] ∧
      c[h.toIsEchelonForm.pivotRow ⟨i, hiD⟩] ≠ 0 ∧
      ∀ k : Fin n, k.val < i → c[k] = 0 := by
  let ei : Fin E.rank := ⟨i, hiE⟩
  let erow := h'.toIsEchelonForm.pivotRow ei
  rcases row_coeffs h h' hL erow with ⟨c, hc⟩
  have htarget : E.echelon[erow] ≠ 0 := by
    intro hzero
    have hpivot := h'.pivot_pos ei
    change 0 < E.echelon[erow][E.pivotCols.get ei] at hpivot
    have hentry := congrArg (fun row => row[(E.pivotCols.get ei).val]'
      (E.pivotCols.get ei).isLt) hzero
    have hentry' : E.echelon[erow][E.pivotCols.get ei] = 0 := by
      change E.echelon[erow][(E.pivotCols.get ei).val]'
        (E.pivotCols.get ei).isLt = 0
      simpa only [Vector.getElem_zero] using hentry
    exact (Int.ne_of_gt hpivot) hentry'
  have hvec : vecMul c D.echelon ≠ 0 := by rw [hc]; exact htarget
  rcases firstCoeff h c hvec with ⟨q, hqne, hqzero⟩
  have hqcol : D.pivotCols.get q = E.pivotCols.get ei := by
    have hbefore : ∀ j : Fin m, j < E.pivotCols.get ei →
        (vecMul c D.echelon)[j] = 0 := by
      intro j hj
      rw [hc]
      have hlead := h'.pivot_leading ei j hj
      change E.echelon[erow][j] = 0 at hlead
      exact hlead
    have hat : (vecMul c D.echelon)[E.pivotCols.get ei] ≠ 0 := by
      rw [hc]
      have hpos := h'.pivot_pos ei
      change 0 < E.echelon[erow][E.pivotCols.get ei] at hpos
      exact Int.ne_of_gt hpos
    have hqnonzero : (vecMul c D.echelon)[D.pivotCols.get q] ≠ 0 := by
      rw [vecMul_pivot h c q hqzero]
      have hpq := h.pivot_pos q
      change 0 < D.echelon[h.toIsEchelonForm.pivotRow q][D.pivotCols.get q] at hpq
      exact Int.mul_ne_zero hqne (Int.ne_of_gt hpq)
    rcases Nat.lt_trichotomy (D.pivotCols.get q).val
        (E.pivotCols.get ei).val with hlt | heq | hgt
    · exact absurd (hbefore _ hlt) hqnonzero
    · exact Fin.ext heq
    · exact absurd (vecMul_before h c q hqzero _ hgt) hat
  let di : Fin D.rank := ⟨i, hiD⟩
  have hdicol : D.pivotCols.get di = E.pivotCols.get ei :=
    pivotGet_of_lists hp hiD hiE
  have hqi : q = di :=
    h.toIsEchelonForm.pivotCols_injective (hqcol.trans hdicol.symm)
  subst q
  refine ⟨c, ?_, ?_, ?_⟩
  · simpa only [erow, ei] using hc
  · simpa only [di] using hqne
  intro k hk
  exact hqzero k hk

private theorem pivotValue_eq {A : Matrix Int n m} {B : Matrix Int n' m}
    {D : RowEchelonData Int n m} {E : RowEchelonData Int n' m}
    (h : IsHNF A D) (h' : IsHNF B E)
    (hL : ∀ v, A.memLattice v ↔ B.memLattice v)
    (hp : D.pivotCols.toList = E.pivotCols.toList)
    {i : Nat} (hiD : i < D.rank) (hiE : i < E.rank) :
    (D.echelon[h.toIsEchelonForm.pivotRow ⟨i, hiD⟩]).get
        (D.pivotCols.get ⟨i, hiD⟩) =
      (E.echelon[h'.toIsEchelonForm.pivotRow ⟨i, hiE⟩]).get
        (E.pivotCols.get ⟨i, hiE⟩) := by
  let di : Fin D.rank := ⟨i, hiD⟩
  let ei : Fin E.rank := ⟨i, hiE⟩
  let drow := h.toIsEchelonForm.pivotRow di
  let erow := h'.toIsEchelonForm.pivotRow ei
  have hrank : D.rank = E.rank := by
    have hlen := congrArg List.length hp
    simpa using hlen
  have hcol : D.pivotCols.get di = E.pivotCols.get ei :=
    pivotGet_of_lists hp hiD hiE
  rcases rowCoeffLeading h h' hL hp hiD hiE with ⟨c, hc, hcne, hczero⟩
  have hED : E.echelon[erow][E.pivotCols.get ei] =
      c[drow] * D.echelon[drow][D.pivotCols.get di] := by
    have hentry := congrArg (fun v => v[D.pivotCols.get di]) hc
    have hsolve := vecMul_pivot h c di hczero
    have hright : E.echelon[erow][D.pivotCols.get di] =
        E.echelon[erow][E.pivotCols.get ei] := by
      change (E.echelon[erow]).get (D.pivotCols.get di) =
        (E.echelon[erow]).get (E.pivotCols.get ei)
      exact congrArg (fun col : Fin m => (E.echelon[erow]).get col) hcol
    rw [hsolve, hright] at hentry
    exact hentry.symm
  rcases rowCoeffLeading h' h (fun v => (hL v).symm) hp.symm hiE hiD with
    ⟨d, hd, hdne, hdzero⟩
  have hDE : D.echelon[drow][D.pivotCols.get di] =
      d[erow] * E.echelon[erow][E.pivotCols.get ei] := by
    have hentry := congrArg (fun v => v[E.pivotCols.get ei]) hd
    have hsolve := vecMul_pivot h' d ei hdzero
    have hright : D.echelon[drow][E.pivotCols.get ei] =
        D.echelon[drow][D.pivotCols.get di] := by
      change (D.echelon[drow]).get (E.pivotCols.get ei) =
        (D.echelon[drow]).get (D.pivotCols.get di)
      exact congrArg (fun col : Fin m => (D.echelon[drow]).get col) hcol.symm
    rw [hsolve, hright] at hentry
    exact hentry.symm
  apply positive_associates_eq
  · have hpD := h.pivot_pos di
    change 0 < D.echelon[drow][D.pivotCols.get di] at hpD
    exact hpD
  · have hpE := h'.pivot_pos ei
    change 0 < E.echelon[erow][E.pivotCols.get ei] at hpE
    exact hpE
  · exact hED
  · exact hDE

private theorem vecMul_sub (H : Matrix Int n m) (c d : Vector Int n) :
    vecMul (c - d) H = vecMul c H - vecMul d H := by
  unfold vecMul
  apply Vector.ext
  intro j hj
  let col : Fin m := ⟨j, hj⟩
  change (Matrix.transpose H * (c - d))[col] =
    (Matrix.transpose H * c - Matrix.transpose H * d)[j]
  rw [Vector.getElem_sub]
  change (Matrix.transpose H * (c - d))[col] =
    (Matrix.transpose H * c)[col] - (Matrix.transpose H * d)[col]
  rw [Matrix.getElem_mulVec, Matrix.getElem_mulVec,
    Matrix.getElem_mulVec, Vector.dotProduct_sub_right]

private theorem vector_sub_eq_zero_iff (u v : Vector Int n) : u - v = 0 ↔ u = v := by
  constructor
  · intro h
    apply Vector.ext
    intro i hi
    have hget := congrArg (fun w : Vector Int n => w[i]) h
    simp only [Vector.getElem_sub, Vector.getElem_zero] at hget
    omega
  · intro h
    subst v
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_sub, Vector.getElem_zero]
    omega

private theorem vector_get_sub (u v : Vector Int n) (i : Fin n) :
    (u - v).get i = u.get i - v.get i := by
  change (u - v)[i.val]'i.isLt = u[i.val]'i.isLt - v[i.val]'i.isLt
  rw [Vector.getElem_sub]

private theorem pivotRow_eq {A : Matrix Int n m} {B : Matrix Int n' m}
    {D : RowEchelonData Int n m} {E : RowEchelonData Int n' m}
    (h : IsHNF A D) (h' : IsHNF B E)
    (hL : ∀ v, A.memLattice v ↔ B.memLattice v)
    (hp : D.pivotCols.toList = E.pivotCols.toList)
    {i : Nat} (hiD : i < D.rank) (hiE : i < E.rank) :
    D.echelon[h.toIsEchelonForm.pivotRow ⟨i, hiD⟩] =
      E.echelon[h'.toIsEchelonForm.pivotRow ⟨i, hiE⟩] := by
  let di : Fin D.rank := ⟨i, hiD⟩
  let ei : Fin E.rank := ⟨i, hiE⟩
  let drow := h.toIsEchelonForm.pivotRow di
  let erow := h'.toIsEchelonForm.pivotRow ei
  have hrank : D.rank = E.rank := by
    have hlen := congrArg List.length hp
    simpa using hlen
  rcases row_coeffs h h' hL erow with ⟨c, hc⟩
  rcases row_memLattice D.echelon drow with ⟨d, hd⟩
  have hw : vecMul (c - d) D.echelon = E.echelon[erow] - D.echelon[drow] := by
    rw [vecMul_sub, hc, hd]
  apply Classical.byContradiction
  intro hne
  have hrows : E.echelon[erow] ≠ D.echelon[drow] :=
    fun heq => hne heq.symm
  have hwne : vecMul (c - d) D.echelon ≠ 0 := by
    rw [hw]
    exact fun hz => hrows (vector_sub_eq_zero_iff _ _ |>.mp hz)
  rcases firstCoeff h (c - d) hwne with ⟨q, hqne, hqzero⟩
  have hqmul : (vecMul (c - d) D.echelon)[D.pivotCols.get q] =
      (c - d)[h.toIsEchelonForm.pivotRow q] *
        D.echelon[h.toIsEchelonForm.pivotRow q][D.pivotCols.get q] :=
    vecMul_pivot h (c - d) q hqzero
  have hqentryNe : (vecMul (c - d) D.echelon)[D.pivotCols.get q] ≠ 0 := by
    rw [hqmul]
    have hpq := h.pivot_pos q
    change 0 < D.echelon[h.toIsEchelonForm.pivotRow q][D.pivotCols.get q] at hpq
    exact Int.mul_ne_zero hqne (Int.ne_of_gt hpq)
  have hiq : i < q.val := by
    apply Classical.byContradiction
    intro hnlt
    have hqi : q.val ≤ i := Nat.le_of_not_gt hnlt
    rcases Nat.lt_or_eq_of_le hqi with hlt | heq
    · have hcolLt := h.toIsEchelonForm.pivotCols_sorted q di hlt
      have hDzero := h.pivot_leading di (D.pivotCols.get q) hcolLt
      change (D.echelon[drow]).get (D.pivotCols.get q) = 0 at hDzero
      have hcolI := pivotGet_of_lists hp hiD hiE
      have hcolE : D.pivotCols.get q < E.pivotCols.get ei := by
        calc
          D.pivotCols.get q < D.pivotCols.get di := hcolLt
          _ = E.pivotCols.get ei := hcolI
      have hEzero := h'.pivot_leading ei (D.pivotCols.get q) hcolE
      change (E.echelon[erow]).get (D.pivotCols.get q) = 0 at hEzero
      have hdiff := congrArg
        (fun v : Vector Int m => v.get (D.pivotCols.get q)) hw
      rw [vector_get_sub, hDzero, hEzero] at hdiff
      apply hqentryNe
      change (vecMul (c - d) D.echelon).get (D.pivotCols.get q) = 0
      exact hdiff.trans (Int.sub_self 0)
    · have hqdi : q = di := Fin.ext heq
      subst q
      have hpv := pivotValue_eq h h' hL hp hiD hiE
      have hpv' : (D.echelon[drow]).get (D.pivotCols.get di) =
          (E.echelon[erow]).get (E.pivotCols.get ei) := by
        simpa only [di, ei, drow, erow] using hpv
      have hcol := pivotGet_of_lists hp hiD hiE
      have hEentry : (E.echelon[erow]).get (D.pivotCols.get di) =
          (E.echelon[erow]).get (E.pivotCols.get ei) := by
        exact congrArg (fun col : Fin m => (E.echelon[erow]).get col) hcol
      have hdiff := congrArg
        (fun v : Vector Int m => v.get (D.pivotCols.get di)) hw
      rw [vector_get_sub] at hdiff
      rw [hEentry, ← hpv'] at hdiff
      apply hqentryNe
      change (vecMul (c - d) D.echelon).get (D.pivotCols.get di) = 0
      exact hdiff.trans (Int.sub_self _)
  have hqE : q.val < E.rank := by omega
  let qe : Fin E.rank := ⟨q.val, hqE⟩
  have hcolq : D.pivotCols.get q = E.pivotCols.get qe :=
    pivotGet_of_lists hp q.isLt hqE
  have hpval := pivotValue_eq h h' hL hp q.isLt hqE
  have hDnonneg := h.above_nonneg q drow hiq
  have hDltRaw := h.above_lt q drow hiq
  have hEnonnegRaw := h'.above_nonneg qe erow hiq
  have hEltRaw := h'.above_lt qe erow hiq
  have hDpos := h.pivot_pos q
  change 0 < D.echelon[h.toIsEchelonForm.pivotRow q][D.pivotCols.get q] at hDpos
  let p := (D.echelon[h.toIsEchelonForm.pivotRow q]).get (D.pivotCols.get q)
  change 0 < p at hDpos
  change 0 ≤ (D.echelon[drow]).get (D.pivotCols.get q) at hDnonneg
  have hDlt : (D.echelon[drow]).get (D.pivotCols.get q) < p := by
    change (D.echelon[drow]).get (D.pivotCols.get q) < p at hDltRaw
    exact hDltRaw
  have hElt : (E.echelon[erow]).get (D.pivotCols.get q) < p := by
    have hEcol : (E.echelon[erow]).get (D.pivotCols.get q) =
        (E.echelon[erow]).get (E.pivotCols.get qe) := by
      exact congrArg (fun col : Fin m => (E.echelon[erow]).get col) hcolq
    rw [hEcol]
    have hpval' : p =
        (E.echelon[h'.toIsEchelonForm.pivotRow qe]).get
          (E.pivotCols.get qe) := by
      simpa only [p] using hpval
    rw [hpval']
    change (E.echelon[erow]).get (E.pivotCols.get qe) <
      (E.echelon[h'.toIsEchelonForm.pivotRow qe]).get
        (E.pivotCols.get qe) at hEltRaw
    exact hEltRaw
  have hEnonneg : 0 ≤ (E.echelon[erow]).get (D.pivotCols.get q) := by
    have hEcol : (E.echelon[erow]).get (D.pivotCols.get q) =
        (E.echelon[erow]).get (E.pivotCols.get qe) := by
      exact congrArg (fun col : Fin m => (E.echelon[erow]).get col) hcolq
    rw [hEcol]
    change 0 ≤ (E.echelon[erow]).get (E.pivotCols.get qe) at hEnonnegRaw
    exact hEnonnegRaw
  have hdiff := congrArg (fun v : Vector Int m => v.get (D.pivotCols.get q)) hw
  rw [vector_get_sub] at hdiff
  change (vecMul (c - d) D.echelon).get (D.pivotCols.get q) =
    (c - d)[h.toIsEchelonForm.pivotRow q] * p at hqmul
  rw [hqmul] at hdiff
  have hlower : -p < (c - d)[h.toIsEchelonForm.pivotRow q] * p := by
    rw [hdiff]
    omega
  have hupper : (c - d)[h.toIsEchelonForm.pivotRow q] * p < p := by
    rw [hdiff]
    omega
  by_cases hcoeff : 0 < (c - d)[h.toIsEchelonForm.pivotRow q]
  · have hmul := Int.mul_le_mul_of_nonneg_right
      (show (1 : Int) ≤ (c - d)[h.toIsEchelonForm.pivotRow q] by omega)
      (Int.le_of_lt hDpos)
    have : p ≤ (c - d)[h.toIsEchelonForm.pivotRow q] * p := by
      simpa only [Int.one_mul] using hmul
    omega
  · have hcoeffNeg : (c - d)[h.toIsEchelonForm.pivotRow q] ≤ -1 := by omega
    have hmul := Int.mul_le_mul_of_nonneg_right hcoeffNeg (Int.le_of_lt hDpos)
    have : (c - d)[h.toIsEchelonForm.pivotRow q] * p ≤ -p := by
      simpa only [Int.neg_mul, Int.one_mul] using hmul
    omega

private theorem echelon_row_eq {A B : Matrix Int n m}
    {D E : RowEchelonData Int n m} (h : IsHNF A D) (h' : IsHNF B E)
    (hL : ∀ v, A.memLattice v ↔ B.memLattice v)
    (hp : D.pivotCols.toList = E.pivotCols.toList) (row : Fin n) :
    D.echelon[row] = E.echelon[row] := by
  have hrank : D.rank = E.rank := by
    have hlen := congrArg List.length hp
    simpa using hlen
  by_cases hir : row.val < D.rank
  · have hirE : row.val < E.rank := by omega
    let di : Fin D.rank := ⟨row.val, hir⟩
    let ei : Fin E.rank := ⟨row.val, hirE⟩
    let drow := h.toIsEchelonForm.pivotRow di
    let erow := h'.toIsEchelonForm.pivotRow ei
    have hdrow : drow = row := Fin.ext rfl
    have herow : erow = row := Fin.ext rfl
    rcases row_coeffs h h' hL erow with ⟨c, hc⟩
    rcases row_memLattice D.echelon drow with ⟨d, hd⟩
    have hw : vecMul (c - d) D.echelon = E.echelon[erow] - D.echelon[drow] := by
      rw [vecMul_sub, hc, hd]
    apply Classical.byContradiction
    intro hne
    have hrows : E.echelon[erow] ≠ D.echelon[drow] := by
      rw [hdrow, herow]
      exact fun heq => hne heq.symm
    have hwne : vecMul (c - d) D.echelon ≠ 0 := by
      rw [hw]
      exact fun hz => hrows (vector_sub_eq_zero_iff _ _ |>.mp hz)
    rcases firstCoeff h (c - d) hwne with ⟨q, hqne, hqzero⟩
    have hqmul : (vecMul (c - d) D.echelon)[D.pivotCols.get q] =
        (c - d)[h.toIsEchelonForm.pivotRow q] *
          D.echelon[h.toIsEchelonForm.pivotRow q][D.pivotCols.get q] :=
      vecMul_pivot h (c - d) q hqzero
    have hqentryNe : (vecMul (c - d) D.echelon)[D.pivotCols.get q] ≠ 0 := by
      rw [hqmul]
      have hpq := h.pivot_pos q
      change 0 < D.echelon[h.toIsEchelonForm.pivotRow q][D.pivotCols.get q] at hpq
      exact Int.mul_ne_zero hqne (Int.ne_of_gt hpq)
    have hiq : row.val < q.val := by
      apply Classical.byContradiction
      intro hnlt
      have hqi : q.val ≤ row.val := Nat.le_of_not_gt hnlt
      rcases Nat.lt_or_eq_of_le hqi with hlt | heq
      · have hcolLt := h.toIsEchelonForm.pivotCols_sorted q di hlt
        have hDzero := h.pivot_leading di (D.pivotCols.get q) hcolLt
        change (D.echelon[drow]).get (D.pivotCols.get q) = 0 at hDzero
        have hcolI := pivotGet_of_lists hp hir hirE
        have hcolE : D.pivotCols.get q < E.pivotCols.get ei := by
          calc
            D.pivotCols.get q < D.pivotCols.get di := hcolLt
            _ = E.pivotCols.get ei := hcolI
        have hEzero := h'.pivot_leading ei (D.pivotCols.get q) hcolE
        change (E.echelon[erow]).get (D.pivotCols.get q) = 0 at hEzero
        have hdiff := congrArg
          (fun v : Vector Int m => v.get (D.pivotCols.get q)) hw
        rw [vector_get_sub, hDzero, hEzero] at hdiff
        apply hqentryNe
        change (vecMul (c - d) D.echelon).get (D.pivotCols.get q) = 0
        exact hdiff.trans (Int.sub_self 0)
      · have hqdi : q = di := Fin.ext heq
        subst q
        have hpv := pivotValue_eq h h' hL hp hir hirE
        have hpv' : (D.echelon[drow]).get (D.pivotCols.get di) =
            (E.echelon[erow]).get (E.pivotCols.get ei) := by
          simpa only [di, ei, drow, erow] using hpv
        have hcol := pivotGet_of_lists hp hir hirE
        have hEentry : (E.echelon[erow]).get (D.pivotCols.get di) =
            (E.echelon[erow]).get (E.pivotCols.get ei) := by
          exact congrArg (fun col : Fin m => (E.echelon[erow]).get col) hcol
        have hdiff := congrArg
          (fun v : Vector Int m => v.get (D.pivotCols.get di)) hw
        rw [vector_get_sub] at hdiff
        rw [hEentry, ← hpv'] at hdiff
        apply hqentryNe
        change (vecMul (c - d) D.echelon).get (D.pivotCols.get di) = 0
        exact hdiff.trans (Int.sub_self _)
    have hqE : q.val < E.rank := by omega
    let qe : Fin E.rank := ⟨q.val, hqE⟩
    have hcolq : D.pivotCols.get q = E.pivotCols.get qe :=
      pivotGet_of_lists hp q.isLt hqE
    have hpval := pivotValue_eq h h' hL hp q.isLt hqE
    have hDnonneg := h.above_nonneg q drow hiq
    have hDltRaw := h.above_lt q drow hiq
    have hEnonnegRaw := h'.above_nonneg qe erow hiq
    have hEltRaw := h'.above_lt qe erow hiq
    have hDpos := h.pivot_pos q
    change 0 < D.echelon[h.toIsEchelonForm.pivotRow q][D.pivotCols.get q] at hDpos
    let p := (D.echelon[h.toIsEchelonForm.pivotRow q]).get (D.pivotCols.get q)
    change 0 < p at hDpos
    change 0 ≤ (D.echelon[drow]).get (D.pivotCols.get q) at hDnonneg
    have hDlt : (D.echelon[drow]).get (D.pivotCols.get q) < p := by
      change (D.echelon[drow]).get (D.pivotCols.get q) < p at hDltRaw
      exact hDltRaw
    have hElt : (E.echelon[erow]).get (D.pivotCols.get q) < p := by
      have hEcol : (E.echelon[erow]).get (D.pivotCols.get q) =
          (E.echelon[erow]).get (E.pivotCols.get qe) := by
        exact congrArg (fun col : Fin m => (E.echelon[erow]).get col) hcolq
      rw [hEcol]
      have hpval' : p =
          (E.echelon[h'.toIsEchelonForm.pivotRow qe]).get
            (E.pivotCols.get qe) := by
        simpa only [p] using hpval
      rw [hpval']
      change (E.echelon[erow]).get (E.pivotCols.get qe) <
        (E.echelon[h'.toIsEchelonForm.pivotRow qe]).get
          (E.pivotCols.get qe) at hEltRaw
      exact hEltRaw
    have hEnonneg : 0 ≤ (E.echelon[erow]).get (D.pivotCols.get q) := by
      have hEcol : (E.echelon[erow]).get (D.pivotCols.get q) =
          (E.echelon[erow]).get (E.pivotCols.get qe) := by
        exact congrArg (fun col : Fin m => (E.echelon[erow]).get col) hcolq
      rw [hEcol]
      change 0 ≤ (E.echelon[erow]).get (E.pivotCols.get qe) at hEnonnegRaw
      exact hEnonnegRaw
    have hdiff := congrArg (fun v : Vector Int m => v.get (D.pivotCols.get q)) hw
    rw [vector_get_sub] at hdiff
    change (vecMul (c - d) D.echelon).get (D.pivotCols.get q) =
      (c - d)[h.toIsEchelonForm.pivotRow q] * p at hqmul
    rw [hqmul] at hdiff
    have hlower : -p < (c - d)[h.toIsEchelonForm.pivotRow q] * p := by
      rw [hdiff]
      have := hDnonneg
      omega
    have hupper : (c - d)[h.toIsEchelonForm.pivotRow q] * p < p := by
      rw [hdiff]
      omega
    by_cases hcoeff : 0 < (c - d)[h.toIsEchelonForm.pivotRow q]
    · have hmul := Int.mul_le_mul_of_nonneg_right
        (show (1 : Int) ≤ (c - d)[h.toIsEchelonForm.pivotRow q] by omega)
        (Int.le_of_lt hDpos)
      have : p ≤ (c - d)[h.toIsEchelonForm.pivotRow q] * p := by
        simpa only [Int.one_mul] using hmul
      omega
    · have hcoeffNeg : (c - d)[h.toIsEchelonForm.pivotRow q] ≤ -1 := by omega
      have hmul := Int.mul_le_mul_of_nonneg_right hcoeffNeg (Int.le_of_lt hDpos)
      have : (c - d)[h.toIsEchelonForm.pivotRow q] * p ≤ -p := by
        simpa only [Int.neg_mul, Int.one_mul] using hmul
      omega
  · have hirD : D.rank ≤ row.val := Nat.le_of_not_gt hir
    have hirE : E.rank ≤ row.val := by omega
    have hDz := h.toIsEchelonForm.zero_row row hirD
    have hEz := h'.toIsEchelonForm.zero_row row hirE
    exact hDz.trans hEz.symm

/-- Row HNF is canonical among presentations of the same integer row lattice. -/
theorem eq_of_memLattice {A B : Matrix Int n m}
    {D E : RowEchelonData Int n m} (h : IsHNF A D) (h' : IsHNF B E)
    (hL : ∀ v, A.memLattice v ↔ B.memLattice v) :
    D.rank = E.rank ∧ D.echelon = E.echelon ∧ HEq D.pivotCols E.pivotCols := by
  have hp := pivotLists_eq h h' hL
  have hrank : D.rank = E.rank := by
    have hlen := congrArg List.length hp
    simpa using hlen
  have hechelon : D.echelon = E.echelon := by
    apply Matrix.ext_getElem
    intro i j
    have hrow := echelon_row_eq h h' hL hp i
    exact congrArg (fun row : Vector Int m => row.get j) hrow
  exact ⟨hrank, hechelon, vector_heq_of_toList_eq hp⟩

/-- Two certified HNFs of one fixed input have identical canonical data. -/
theorem eq {A : Matrix Int n m} {D E : RowEchelonData Int n m}
    (h : IsHNF A D) (h' : IsHNF A E) :
    D.rank = E.rank ∧ D.echelon = E.echelon ∧ HEq D.pivotCols E.pivotCols := by
  exact h.eq_of_memLattice h' (fun _ => Iff.rfl)

/-- A zero combination of HNF rows has zero coefficients on every nonzero row. -/
theorem coeff_eq_zero {A : Matrix Int n m} {D : RowEchelonData Int n m}
    (h : IsHNF A D) (c : Vector Int n) (hc : vecMul c D.echelon = 0)
    (i : Fin D.rank) : c[h.toIsEchelonForm.pivotRow i] = 0 := by
  have aux : ∀ value : Nat, (hv : value < D.rank) →
      c[h.toIsEchelonForm.pivotRow ⟨value, hv⟩] = 0 := by
    intro value
    induction value using Nat.strongRecOn with
    | ind value ih =>
      intro hv
      have hz : ∀ k : Fin n, k.val < value → c[k] = 0 := by
        intro k hk
        have hkRank : k.val < D.rank := Nat.lt_trans hk hv
        let q : Fin D.rank := ⟨k.val, hkRank⟩
        have hq := ih k.val hk hkRank
        have hrow : h.toIsEchelonForm.pivotRow q = k := Fin.ext rfl
        change c.get k = 0
        calc
          c.get k = c.get (h.toIsEchelonForm.pivotRow q) :=
            congrArg (fun row : Fin n => c.get row) hrow.symm
          _ = 0 := hq
      let q : Fin D.rank := ⟨value, hv⟩
      have hpivot := vecMul_pivot h c q hz
      rw [hc] at hpivot
      change (0 : Vector Int m)[(D.pivotCols.get q).val]'
        (D.pivotCols.get q).isLt = _ at hpivot
      rw [Vector.getElem_zero] at hpivot
      have hp := h.pivot_pos q
      change 0 < D.echelon[h.toIsEchelonForm.pivotRow q][D.pivotCols.get q] at hp
      rcases Int.mul_eq_zero.mp hpivot.symm with hzero | hzero
      · exact hzero
      · exact absurd hzero (Int.ne_of_gt hp)
  exact aux i.val i.isLt

/-- If a combination of HNF rows vanishes at every earlier pivot coordinate,
then all coefficients before the selected pivot row vanish. -/
theorem coeff_eq_zero_before {A : Matrix Int n m} {D : RowEchelonData Int n m}
    (h : IsHNF A D) (c : Vector Int n) (q : Fin D.rank)
    (hz : ∀ p : Fin D.rank, p.val < q.val →
      (vecMul c D.echelon)[D.pivotCols.get p] = 0)
    (k : Fin n) (hk : k.val < q.val) : c[k] = 0 := by
  have aux : ∀ value : Nat, (hv : value < q.val) →
      c[(⟨value, by
        exact Nat.lt_of_lt_of_le (Nat.lt_trans hv q.isLt)
          h.toIsEchelonForm.rank_le_n⟩ : Fin n)] = 0 := by
    intro value
    induction value using Nat.strongRecOn with
    | ind value ih =>
      intro hv
      have hvRank : value < D.rank := Nat.lt_trans hv q.isLt
      let p : Fin D.rank := ⟨value, hvRank⟩
      have hbefore : ∀ row : Fin n, row.val < value → c[row] = 0 := by
        intro row hrow
        have hi := ih row.val hrow (Nat.lt_trans hrow hv)
        have hidx : (⟨row.val, by
            exact Nat.lt_of_lt_of_le
              (Nat.lt_trans (Nat.lt_trans hrow hv) q.isLt)
              h.toIsEchelonForm.rank_le_n⟩ : Fin n) = row := Fin.ext rfl
        simpa only [hidx] using hi
      have hmul := vecMul_pivot h c p hbefore
      have hzero := hz p hv
      rw [hmul] at hzero
      have hp := h.pivot_pos p
      change 0 < D.echelon[h.toIsEchelonForm.pivotRow p][D.pivotCols.get p] at hp
      rcases Int.mul_eq_zero.mp hzero with hcoeff | hpzero
      · simpa only [p, IsEchelonForm.pivotRow] using hcoeff
      · exact absurd hpzero (Int.ne_of_gt hp)
  have hkzero := aux k.val hk
  have hidx : (⟨k.val, by
      exact Nat.lt_of_lt_of_le (Nat.lt_trans hk q.isLt)
        h.toIsEchelonForm.rank_le_n⟩ : Fin n) = k := Fin.ext rfl
  simpa only [hidx] using hkzero

/-- At the next HNF pivot, a lattice vector whose earlier pivot entries vanish
is an integer multiple of that pivot. -/
theorem pivot_factor {A : Matrix Int n m}
    {D : RowEchelonData Int n m} (h : IsHNF A D)
    {v : Vector Int m} (hv : D.echelon.memLattice v) (q : Fin D.rank)
    (hz : ∀ p : Fin D.rank, p.val < q.val →
      v[D.pivotCols.get p] = 0) :
    ∃ a : Int, v[D.pivotCols.get q] =
      a * D.echelon[h.toIsEchelonForm.pivotRow q][D.pivotCols.get q] := by
  rcases hv with ⟨c, hc⟩
  refine ⟨c[h.toIsEchelonForm.pivotRow q], ?_⟩
  rw [← hc]
  exact vecMul_pivot h c q (h.coeff_eq_zero_before c q (by
    intro p hp
    rw [hc]
    exact hz p hp))

/-- A vector in an HNF row lattice is zero when all its pivot coordinates are
zero. -/
theorem eq_zero_of_pivots {A : Matrix Int n m}
    {D : RowEchelonData Int n m} (h : IsHNF A D)
    {v : Vector Int m} (hv : D.echelon.memLattice v)
    (hz : ∀ q : Fin D.rank, v[D.pivotCols.get q] = 0) : v = 0 := by
  rcases hv with ⟨c, hc⟩
  have hcoeff : ∀ q : Fin D.rank,
      c[h.toIsEchelonForm.pivotRow q] = 0 := by
    intro q
    have hbefore := h.coeff_eq_zero_before c q (by
      intro p _hp
      rw [hc]
      exact hz p)
    have hpivot := vecMul_pivot h c q hbefore
    rw [hc, hz q] at hpivot
    have hp := h.pivot_pos q
    change 0 < D.echelon[h.toIsEchelonForm.pivotRow q][D.pivotCols.get q] at hp
    rcases Int.mul_eq_zero.mp hpivot.symm with hzero | hzero
    · exact hzero
    · exact absurd hzero (Int.ne_of_gt hp)
  exact hc.symm.trans (vecMul_zero h c hcoeff)

end IsHNF

/-- Hermite normalization is idempotent. -/
theorem hnf_idem (A : Matrix Int n m) : hnf (hnf A) = hnf A := by
  have hL : ∀ v, A.memLattice v ↔ (hnf A).memLattice v := by
    intro v
    rw [hnf_eq_hnfData_echelon]
    exact (hnfData_isHNF A).memLattice_iff v
  have heq := (hnfData_isHNF A).eq_of_memLattice
    (hnfData_isHNF (hnf A)) hL
  have hechelon := heq.2.1
  rw [← hnf_eq_hnfData_echelon A, ← hnf_eq_hnfData_echelon (hnf A)] at hechelon
  exact hechelon.symm

private theorem matrix_heq_of_entries {r s : Nat} (hrs : r = s)
    {M : Matrix Int r m} {N : Matrix Int s m}
    (h : ∀ (i : Fin r) (j : Fin m), M[i][j] = N[Fin.cast hrs i][j]) :
    HEq M N := by
  subst s
  apply heq_of_eq
  apply Matrix.ext_getElem
  intro i j
  simpa using h i j

/-- The nonzero HNF rows are canonical across presentations with different
numbers of generators. -/
theorem hnfBasis_eq_of_memLattice (A : Matrix Int n m) (B : Matrix Int n' m)
    (hL : ∀ v, A.memLattice v ↔ B.memLattice v) :
    hnfRank A = hnfRank B ∧ HEq (hnfBasis A) (hnfBasis B) := by
  let D := hnfData A
  let E := hnfData B
  have hA : IsHNF A D := hnfData_isHNF A
  have hB : IsHNF B E := hnfData_isHNF B
  have hp := IsHNF.pivotLists_eq hA hB hL
  have hrankData : D.rank = E.rank := by
    have hlen := congrArg List.length hp
    simpa using hlen
  have hrank : hnfRank A = hnfRank B := by
    rw [hnfRank_eq A, hnfRank_eq B]
    exact hrankData
  refine ⟨hrank, ?_⟩
  apply matrix_heq_of_entries hrank
  intro i j
  let ib : Fin (hnfRank B) := Fin.cast hrank i
  have hiD : i.val < D.rank := by
    rw [← hnfRank_eq A]
    exact i.isLt
  have hiE : ib.val < E.rank := by
    rw [← hnfRank_eq B]
    exact ib.isLt
  have hrow := IsHNF.pivotRow_eq hA hB hL hp hiD hiE
  have hentry := congrArg (fun row : Vector Int m => row[j.val]'j.isLt) hrow
  simp only [hnfBasis, Matrix.getElem_ofFn, Matrix.getElem_pair_eq_nested]
  rw [hnf_eq_hnfData_echelon A, hnf_eq_hnfData_echelon B]
  let rowA : Fin n := Fin.castLE
    (Hermite.checkedRun_rank_le (Hermite.formAccumulator n) A) i
  let rowB : Fin n' := Fin.castLE
    (Hermite.checkedRun_rank_le (Hermite.formAccumulator n') B) ib
  have hrowA : rowA = hA.toIsEchelonForm.pivotRow ⟨i.val, hiD⟩ := Fin.ext rfl
  have hrowB : rowB = hB.toIsEchelonForm.pivotRow ⟨ib.val, hiE⟩ := Fin.ext rfl
  change D.echelon[rowA][j] = E.echelon[rowB][j]
  calc
    D.echelon[rowA][j] =
        D.echelon[hA.toIsEchelonForm.pivotRow ⟨i.val, hiD⟩][j] := by
      rw [hrowA]
    _ = E.echelon[hB.toIsEchelonForm.pivotRow ⟨ib.val, hiE⟩][j] := by
      simpa only [ib, Fin.cast, Fin.getElem_fin] using hentry
    _ = E.echelon[rowB][j] := by rw [hrowB]

end Hex.Matrix
