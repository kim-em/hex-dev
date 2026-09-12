/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRank.Kernel
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Block
public import HexMatrixMathlib.Literal
public import Mathlib.Data.ZMod.Basic

public section

/-!
Soundness of the kernel certificate: a passing `checkRankList` on the rows of
a Mathlib matrix determines `Matrix.rank`.

The row list is identified with the Mathlib matrix through `ofLists` of the
shared literal layer (`HexMatrixMathlib.Literal`), so the kernel never
evaluates an entry through `Matrix.of`/`vecCons` inside the arithmetic.
-/

open Matrix

namespace HexMatrixMathlib

open Hex.Matrix Hex.Matrix.RankWitness

/-! # The checker's primitives -/

private theorem natMod_eq (a b : Nat) : Nat.mod a b = a % b := rfl
private theorem intMul_eq (a b : Int) : Int.mul a b = a * b := rfl
private theorem intAdd_eq (a b : Int) : Int.add a b = a + b := rfl

theorem allLt_iff (k : Nat) (l : List Nat) : allLt k l = true ↔ ∀ i ∈ l, i < k := by
  induction l with
  | nil => simp [allLt]
  | cons a l ih => simp [allLt, ih]

theorem memNat_iff (i : Nat) (l : List Nat) : memNat i l = true ↔ i ∈ l := by
  induction l with
  | nil => simp [memNat]
  | cons a l ih => simp [memNat, ih]

theorem rowsLen_iff (m : Nat) (L : List (List Int)) : rowsLen m L = true ↔ ∀ r ∈ L, r.length = m := by
  induction L with
  | nil => simp [rowsLen]
  | cons r L ih => simp [rowsLen, ih]

theorem beqInt_iff (a b : List Int) : beqInt a b = true ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [beqInt]
  | cons x xs ih => cases b <;> simp [beqInt, ih]

theorem dotNat_eq_sum (a b : List Nat) :
    dotNat a b = ∑ i : Fin a.length, a[i] * b.getD i 0 := by
  induction a generalizing b with
  | nil => simp [dotNat]
  | cons x xs ih =>
    cases b with
    | nil => simp [dotNat]
    | cons y ys => simp [dotNat, Fin.sum_univ_succ, ih]

theorem zeroRow_iff (M : Nat) (b : List Nat) (cs : List (List Nat)) :
    zeroRow M b cs = true ↔ ∀ c ∈ cs, dotNat b c % M = 0 := by
  induction cs with
  | nil => simp [zeroRow]
  | cons c cs ih => simp [zeroRow, ih, natMod_eq]

theorem unitDiag_iff (M : Nat) (b c : List Nat) : unitDiag M b c = true ↔ dotNat b c % M = 1 := by
  simp [unitDiag, natMod_eq]

theorem lowerCheck_spec (M : Nat) (bs cs : List (List Nat)) (h : lowerCheck M bs cs = true) :
    bs.length = cs.length ∧ ∀ (i : Nat) (hi : i < bs.length),
      dotNat bs[i] (cs.getD i []) % M = 1 ∧ ∀ j, i < j → dotNat bs[i] (cs.getD j []) % M = 0 := by
  induction bs generalizing cs with
  | nil =>
    cases cs with
    | nil => simp
    | cons c cs => simp [lowerCheck] at h
  | cons b bs ih =>
    cases cs with
    | nil => simp [lowerCheck] at h
    | cons c cs =>
      simp only [lowerCheck, Bool.and_eq_true] at h
      obtain ⟨⟨hd, hz⟩, ht⟩ := h
      obtain ⟨hlen, hrest⟩ := ih cs ht
      refine ⟨by simpa using hlen, fun i hi => ?_⟩
      cases i with
      | zero =>
        refine ⟨by simpa [unitDiag_iff] using hd, fun j hj => ?_⟩
        obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        simp only [List.getD_cons_succ, List.getElem_cons_zero]
        by_cases hjl : j < cs.length
        · rw [getD_eq_getElem' _ _ _ hjl]
          exact (zeroRow_iff M b cs).mp hz _ (List.getElem_mem hjl)
        · rw [getD_eq_default' _ _ _ (by omega)]
          simp [dotNat]
      | succ i =>
        obtain ⟨h1, h2⟩ := hrest i (by simpa using hi)
        refine ⟨by simpa using h1, fun j hj => ?_⟩
        obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        simpa using h2 j (by omega)

theorem scaleRow_length (d : Int) (a : List Int) : (scaleRow d a).length = a.length := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [scaleRow, ih]

theorem scaleRow_getD (d : Int) (a : List Int) (j : Nat) :
    (scaleRow d a).getD j 0 = d * a.getD j 0 := by
  induction a generalizing j with
  | nil => simp [scaleRow]
  | cons x xs ih =>
    cases j with
    | zero => simp only [scaleRow, List.getD_cons_zero, intMul_eq]
    | succ j => simp only [scaleRow, List.getD_cons_succ, ih]

theorem addScaled_length (z : Int) (p a : List Int) :
    (addScaled z p a).length = min p.length a.length := by
  induction p generalizing a with
  | nil => simp [addScaled]
  | cons x xs ih =>
    cases a with
    | nil => simp [addScaled]
    | cons y ys => simp [addScaled, ih]

theorem addScaled_getD (z : Int) (p a : List Int) (j : Nat) (hj : j < p.length)
    (hj' : j < a.length) : (addScaled z p a).getD j 0 = z * p.getD j 0 + a.getD j 0 := by
  induction p generalizing a j with
  | nil => simp at hj
  | cons x xs ih =>
    cases a with
    | nil => simp at hj'
    | cons y ys =>
      cases j with
      | zero => simp only [addScaled, List.getD_cons_zero, intMul_eq, intAdd_eq]
      | succ j =>
        simp only [addScaled, List.getD_cons_succ]
        exact ih _ _ (by simpa using hj) (by simpa using hj')

theorem zeros_length (m : Nat) : (zeros m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [zeros, ih]

theorem zeros_getD (m j : Nat) : (zeros m).getD j 0 = 0 := by
  induction m generalizing j with
  | zero => simp [zeros]
  | succ m ih =>
    cases j with
    | zero => simp only [zeros, List.getD_cons_zero]
    | succ j => simp only [zeros, List.getD_cons_succ, ih]

theorem combo_length (m : Nat) (z : List Int) (P : List (List Int))
    (hP : ∀ p ∈ P, p.length = m) : (combo m z P).length = m := by
  induction P generalizing z with
  | nil => cases z <;> simp [combo, zeros_length]
  | cons p ps ih =>
    cases z with
    | nil => simp [combo, zeros_length]
    | cons z zs =>
      have := ih zs fun q hq => hP q (List.mem_cons_of_mem _ hq)
      simp [combo, addScaled_length, this, hP p (List.mem_cons_self ..)]

theorem combo_getD (m : Nat) (z : List Int) (P : List (List Int))
    (hP : ∀ p ∈ P, p.length = m) (j : Nat) (hj : j < m) :
    (combo m z P).getD j 0 = ∑ l : Fin P.length, z.getD l 0 * (P[l]).getD j 0 := by
  induction P generalizing z with
  | nil =>
    cases z <;> simp only [combo, zeros_getD, List.length_nil, Finset.univ_eq_empty,
      Finset.sum_empty]
  | cons p ps ih =>
    have hps : ∀ q ∈ ps, q.length = m := fun q hq => hP q (List.mem_cons_of_mem _ hq)
    cases z with
    | nil => simp only [combo, zeros_getD, List.getD_nil, zero_mul, Finset.sum_const_zero]
    | cons z zs =>
      rw [combo, addScaled_getD _ _ _ _ (by rw [hP p (List.mem_cons_self ..)]; exact hj)
        (by rw [combo_length _ _ _ hps]; exact hj), ih zs hps]
      show _ = ∑ l : Fin (ps.length + 1), _
      rw [Fin.sum_univ_succ]
      simp [List.getElem_cons_succ]

theorem rowsCheck_spec (d : Int) (rows : List Nat) (P : List (List Int)) (m : Nat) :
    ∀ (i : Nat) (as zs : List (List Int)), rowsCheck d rows P m i as zs = true →
      ∀ (t : Nat) (ht : t < as.length),
        memNat (i + t) rows = true ∨ ∃ z, scaleRow d as[t] = combo m z P := by
  intro i as
  induction as generalizing i with
  | nil => intro zs _ t ht; simp at ht
  | cons a as ih =>
    intro zs h t ht
    cases hm : memNat i rows with
    | true =>
      simp only [rowsCheck, hm, Bool.cond_true] at h
      cases t with
      | zero => exact Or.inl (by simpa using hm)
      | succ t =>
        have := ih (i + 1) zs h t (by simpa using ht)
        rwa [Nat.add_assoc, Nat.add_comm 1 t] at this
    | false =>
      simp only [rowsCheck, hm, Bool.cond_false] at h
      cases zs with
      | nil => simp at h
      | cons z zs =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨hz, hrest⟩ := h
        cases t with
        | zero => exact Or.inr ⟨z, (beqInt_iff _ _).mp hz⟩
        | succ t =>
          have := ih (i + 1) zs hrest t (by simpa using ht)
          rwa [Nat.add_assoc, Nat.add_comm 1 t] at this

theorem nthRow_eq_getD (A : List (List Int)) (i : Nat) : nthRow A i = A.getD i [] := by
  induction A generalizing i with
  | nil => simp [nthRow]
  | cons a as ih =>
    cases i with
    | zero => simp [nthRow]
    | succ i => simp only [nthRow, List.getD_cons_succ, ih]

theorem nthInt_eq_getD (a : List Int) (j : Nat) : nthInt a j = a.getD j 0 := by
  induction a generalizing j with
  | nil => simp [nthInt]
  | cons x xs ih =>
    cases j with
    | zero => simp [nthInt]
    | succ j => simp only [nthInt, List.getD_cons_succ, ih]

theorem pivotRows_length (A : List (List Int)) (rows : List Nat) :
    (pivotRows A rows).length = rows.length := List.length_map ..

theorem pivotRows_getElem (A : List (List Int)) (rows : List Nat) (l : Nat)
    (hl : l < (pivotRows A rows).length) :
    (pivotRows A rows)[l] = A.getD (rows[l]'(by simpa [pivotRows] using hl)) [] := by
  simp only [pivotRows, List.getElem_map, nthRow_eq_getD]

theorem block_length (M : Nat) (A : List (List Int)) (rows cols : List Nat) :
    (block M A rows cols).length = rows.length := List.length_map ..

theorem block_getElem (M : Nat) (A : List (List Int)) (rows cols : List Nat) (i : Nat)
    (hi : i < (block M A rows cols).length) :
    (block M A rows cols)[i] =
      cols.map fun j => residue M ((A.getD (rows[i]'(by simpa [block] using hi)) []).getD j 0) := by
  simp only [block, List.getElem_map, nthRow_eq_getD, nthInt_eq_getD]

theorem residue_cast (M : Nat) (hM : M ≠ 0) (a : Int) :
    ((residue M a : Nat) : ZMod M) = (a : ZMod M) := by
  have h1 : Int.emod a (Int.ofNat M) = a % (M : ℤ) := rfl
  have h2 : ((a % (M : ℤ)).toNat : ℤ) = a % (M : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hM))
  rw [residue, h1, ← Int.cast_natCast, h2, ZMod.intCast_mod]

theorem dotNat_eq_sum' (a b : List Nat) (r : Nat) (ha : a.length = r) :
    dotNat a b = ∑ i : Fin r, a.getD i 0 * b.getD i 0 := by
  subst ha
  rw [dotNat_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [getD_eq_getElem' _ _ _ i.isLt]
  rfl

theorem combo_getD' (m : Nat) (z : List Int) (P : List (List Int))
    (hP : ∀ p ∈ P, p.length = m) (j : Nat) (hj : j < m) (r : Nat) (hr : P.length = r) :
    (combo m z P).getD j 0 = ∑ l : Fin r, z.getD l 0 * (P.getD l []).getD j 0 := by
  subst hr
  rw [combo_getD m z P hP j hj]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [getD_eq_getElem' _ _ _ l.isLt]
  rfl

/-! # Soundness -/

/-- A passing kernel check determines the rank of the row list's matrix. -/
theorem rank_eq_of_checkList (n m : Nat) (L : List (List Int)) (c : RankWitness)
    (h : checkRankList n m L c = true) : (ofLists n m L).rank = c.rank := by
  classical
  simp only [checkRankList, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  set r := c.rank with hr
  have hLlen : L.length = n := by simpa using h1
  have hLrows : ∀ x ∈ L, x.length = m := (rowsLen_iff m L).mp h2
  have hM : 1 < c.modulus := by simpa using h3
  have hrowsLen : c.rows.length = r := by simpa using h4
  have hcolsLen : c.cols.length = r := by simpa using h5
  have hrowsLt : ∀ i ∈ c.rows, i < n := (allLt_iff _ _).mp h6
  have hcolsLt : ∀ j ∈ c.cols, j < m := (allLt_iff _ _).mp h7
  have hd : c.denom ≠ 0 := by simpa using h8
  set A := ofLists n m L with hA
  have hentry : ∀ (i : Fin n) (j : Fin m), A i j = (L.getD i []).getD j 0 := ofLists_apply n m L
  have hrowsMem : ∀ k : Fin r, c.rows.getD k 0 ∈ c.rows := fun k => by
    rw [getD_eq_getElem' _ _ _ (by omega)]
    exact List.getElem_mem _
  have hcolsMem : ∀ k : Fin r, c.cols.getD k 0 ∈ c.cols := fun k => by
    rw [getD_eq_getElem' _ _ _ (by omega)]
    exact List.getElem_mem _
  let rowF : Fin r → Fin n := fun k => ⟨c.rows.getD k 0, hrowsLt _ (hrowsMem k)⟩
  let colF : Fin r → Fin m := fun k => ⟨c.cols.getD k 0, hcolsLt _ (hcolsMem k)⟩
  -- the lower bound, modulo `c.modulus`
  have hlow : r ≤ A.rank := by
    set M := c.modulus with hMdef
    have : Fact (1 < M) := ⟨hM⟩
    have hM0 : M ≠ 0 := by omega
    let B : Matrix (Fin r) (Fin r) ℤ := A.submatrix rowF colF
    let Bz : Matrix (Fin r) (Fin r) (ZMod M) := B.map (Int.cast : ℤ → ZMod M)
    let V : Matrix (Fin r) (Fin r) (ZMod M) := fun k j => ((c.vt.getD j []).getD k 0 : ZMod M)
    obtain ⟨_, hspec⟩ := lowerCheck_spec M _ _ h9
    have hblen : (block M L c.rows c.cols).length = r := by rw [block_length, hrowsLen]
    have hmul : ∀ i j : Fin r, (Bz * V) i j =
        ((dotNat ((block M L c.rows c.cols)[i.val]'(by omega)) (c.vt.getD j []) : ℕ) : ZMod M) := by
      intro i j
      rw [Matrix.mul_apply, dotNat_eq_sum' _ _ r (by rw [block_getElem]; simp [hcolsLen]),
        Nat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.cast_mul, block_getElem, getD_eq_getElem' _ _ _ (by simp; omega), List.getElem_map,
        residue_cast M hM0]
      simp only [Bz, B, V, Matrix.map_apply, Matrix.submatrix_apply, hentry, rowF, colF]
      rw [getD_eq_getElem' c.cols _ _ (by omega), getD_eq_getElem' c.rows _ _ (by omega)]
    have hdiag : ∀ i, (Bz * V) i i = 1 := fun i => by
      rw [hmul]
      have := congrArg (Nat.cast : ℕ → ZMod M) (hspec i (by omega)).1
      rwa [ZMod.natCast_mod, Nat.cast_one] at this
    have hupper : ∀ i j, i < j → (Bz * V) i j = 0 := fun i j hij => by
      rw [hmul]
      have := congrArg (Nat.cast : ℕ → ZMod M) ((hspec i (by omega)).2 j hij)
      rwa [ZMod.natCast_mod, Nat.cast_zero] at this
    have htri : (Bz * V).IsLowerTriangular := fun i j hij =>
      hupper i j (by simpa using hij)
    have hdet : (Bz * V).det = 1 := by
      rw [Matrix.det_of_isLowerTriangular _ htri]
      simp [hdiag]
    have hBz : Bz.det ≠ 0 := by
      intro h0
      rw [Matrix.det_mul, h0, zero_mul] at hdet
      exact zero_ne_one hdet
    have hB : B.det ≠ 0 := by
      intro h0
      apply hBz
      show (B.map fun x => (x : ZMod M)).det = 0
      rw [← Int.cast_det, h0, Int.cast_zero]
    calc r = Fintype.card (Fin r) := (Fintype.card_fin r).symm
      _ = B.rank := (Matrix.rank_of_det_ne_zero hB).symm
      _ ≤ A.rank := Matrix.rank_submatrix_le _ _ _
  -- the upper bound, over `Int`
  have hup : A.rank ≤ r := by
    let P : Matrix (Fin r) (Fin m) ℤ := A.submatrix rowF id
    have hP' : ∀ p ∈ pivotRows L c.rows, p.length = m := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      have hi' : i < L.length := by rw [hLlen]; exact hrowsLt i hi
      rw [nthRow_eq_getD, getD_eq_getElem' _ _ _ hi']
      exact hLrows _ (List.getElem_mem _)
    have key : ∀ i : Fin n, ∃ w : Fin r → ℤ,
        ∀ j : Fin m, c.denom * A i j = ∑ l, w l * A (rowF l) j := by
      intro i
      rcases rowsCheck_spec c.denom c.rows _ m 0 L c.z h10 i (by omega) with hmem | ⟨z, hz⟩
      · rw [Nat.zero_add, memNat_iff] at hmem
        obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.mp hmem
        let k0 : Fin r := ⟨k, by omega⟩
        have hrowFk : rowF k0 = i := by
          apply Fin.ext
          show c.rows.getD k 0 = i
          rw [getD_eq_getElem' _ _ _ hk, hki]
        refine ⟨fun l => if l = k0 then c.denom else 0, fun j => ?_⟩
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hrowFk]
      · refine ⟨fun l => z.getD l 0, fun j => ?_⟩
        have hzj : (scaleRow c.denom (L[(i : Nat)]'(by omega))).getD j 0 =
            (combo m z (pivotRows L c.rows)).getD j 0 := by rw [hz]
        rw [scaleRow_getD, combo_getD' m z _ hP' j j.isLt r (by rw [pivotRows_length, hrowsLen]),
          ← getD_eq_getElem' L i [] (by omega)] at hzj
        rw [hentry, hzj]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hentry]
        congr 2
        show (pivotRows L c.rows).getD l [] = L.getD (c.rows.getD l 0) []
        rw [getD_eq_getElem' _ _ _ (by rw [pivotRows_length]; omega), pivotRows_getElem,
          getD_eq_getElem' c.rows _ _ (by omega)]
    let W : Matrix (Fin n) (Fin r) ℤ := Matrix.of fun i l => Classical.choose (key i) l
    have hW : c.denom • A = W * P := by
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
      simp only [W, P, Matrix.of_apply, Matrix.submatrix_apply, id]
      exact Classical.choose_spec (key i) j
    calc A.rank = (c.denom • A).rank :=
          (Matrix.rank_smul_of_mem_nonZeroDivisors A (mem_nonZeroDivisors_of_ne_zero hd)).symm
      _ = (W * P).rank := by rw [hW]
      _ ≤ P.rank := Matrix.rank_mul_le_right _ _
      _ ≤ Fintype.card (Fin r) := Matrix.rank_le_card_height _
      _ = r := Fintype.card_fin r
  exact le_antisymm hup hlow

/-- `rank_eq_of_checkList` for a matrix identified with its row list; the
tactic supplies `hA` by `rfl`, which the kernel checks one entry at a time. -/
theorem rank_eq_of_checkList' {n m : Nat} (A : Matrix (Fin n) (Fin m) ℤ)
    (L : List (List Int)) (c : RankWitness) (hA : A = ofLists n m L)
    (h : checkRankList n m L c = true) : A.rank = c.rank :=
  hA ▸ rank_eq_of_checkList n m L c h

/-- The upper bound as a standalone inequality. -/
theorem rank_le_of_checkList' {n m : Nat} (A : Matrix (Fin n) (Fin m) ℤ)
    (L : List (List Int)) (c : RankWitness) (hA : A = ofLists n m L)
    (h : checkRankList n m L c = true) {r : Nat} (hr : c.rank ≤ r) : A.rank ≤ r :=
  (rank_eq_of_checkList' A L c hA h).le.trans hr

/-- The lower bound as a standalone inequality. -/
theorem le_rank_of_checkList' {n m : Nat} (A : Matrix (Fin n) (Fin m) ℤ)
    (L : List (List Int)) (c : RankWitness) (hA : A = ofLists n m L)
    (h : checkRankList n m L c = true) {r : Nat} (hr : r ≤ c.rank) : r ≤ A.rank :=
  hr.trans (rank_eq_of_checkList' A L c hA h).ge

end HexMatrixMathlib
