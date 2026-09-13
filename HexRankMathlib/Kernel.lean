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

theorem Rank.rowsLen_iff (m : Nat) (L : List (List Int)) : rowsLen m L = true ↔ ∀ r ∈ L, r.length = m := by
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

theorem Rank.nthRow_eq_getD (A : List (List Int)) (i : Nat) : nthRow A i = A.getD i [] := by
  induction A generalizing i with
  | nil => simp [nthRow]
  | cons a as ih =>
    cases i with
    | zero => simp [nthRow]
    | succ i => simp only [nthRow, List.getD_cons_succ, ih]

theorem Rank.nthInt_eq_getD (a : List Int) (j : Nat) : nthInt a j = a.getD j 0 := by
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
  simp only [pivotRows, List.getElem_map, Rank.nthRow_eq_getD]

theorem residue_zero (M : Nat) : residue M 0 = 0 := by
  have h : Int.emod 0 (Int.ofNat M) = 0 := Int.zero_emod _
  show Int.toNat (Int.emod 0 (Int.ofNat M)) = 0
  rw [h]
  rfl

theorem zerosLike_eq (cs : List Nat) : zerosLike cs = cs.map fun _ => 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [zerosLike, ih]

theorem strictInc_iff (l : List Nat) : strictInc l = true ↔ l.Pairwise (· < ·) := by
  induction l with
  | nil => simp [strictInc]
  | cons a l ih =>
    cases l with
    | nil => simp [strictInc]
    | cons b l =>
      rw [List.pairwise_cons, List.pairwise_cons]
      simp only [strictInc, Bool.and_eq_true, Nat.blt_eq, ih, List.pairwise_cons, List.mem_cons,
        forall_eq_or_imp]
      constructor
      · rintro ⟨hab, hb, hl⟩
        exact ⟨⟨hab, fun x hx => lt_trans hab (hb x hx)⟩, hb, hl⟩
      · rintro ⟨⟨hab, _⟩, hb, hl⟩
        exact ⟨hab, hb, hl⟩

/-- The one-pass read agrees with indexed reads when the positions increase
and start at or after the head's position `k`. -/
theorem pickCols_eq (M : Nat) (row : List Int) (cols : List Nat) (k : Nat)
    (hinc : cols.Pairwise (· < ·)) (hk : ∀ c ∈ cols, k ≤ c) :
    pickCols M cols k row = cols.map fun j => residue M (row.getD (j - k) 0) := by
  induction row generalizing cols k with
  | nil =>
    cases cols with
    | nil => rfl
    | cons c cs => simp [pickCols, zerosLike_eq, residue_zero]
  | cons a as ih =>
    cases cols with
    | nil => rfl
    | cons c cs =>
      have hkc : k ≤ c := hk c (List.mem_cons_self ..)
      have hcs : ∀ d ∈ cs, c < d := (List.pairwise_cons.mp hinc).1
      have hinc' : cs.Pairwise (· < ·) := (List.pairwise_cons.mp hinc).2
      by_cases hck : c = k
      · subst hck
        have hbeq : Nat.beq c c = true := by
          cases h : Nat.beq c c with
          | true => rfl
          | false => exact absurd rfl (Nat.ne_of_beq_eq_false h)
        simp only [pickCols, hbeq, Bool.cond_true, List.map_cons, Nat.sub_self,
          List.getD_cons_zero]
        rw [ih cs (c + 1) hinc' (fun d hd => hcs d hd)]
        congr 1
        apply List.map_congr_left
        intro j hj
        have : c + 1 ≤ j := hcs j hj
        rw [show j - c = (j - (c + 1)) + 1 by omega, List.getD_cons_succ]
      · have hbeq : Nat.beq c k = false := by
          cases h : Nat.beq c k with
          | true => exact absurd (Nat.eq_of_beq_eq_true h) hck
          | false => rfl
        simp only [pickCols, hbeq, Bool.cond_false]
        have hk1 : ∀ d ∈ c :: cs, k + 1 ≤ d := by
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd'
          · omega
          · have := hcs d hd'
            omega
        rw [ih (c :: cs) (k + 1) hinc hk1]
        apply List.map_congr_left
        intro j hj
        have := hk1 j hj
        rw [show j - k = (j - (k + 1)) + 1 by omega, List.getD_cons_succ]

theorem block_length (M : Nat) (A : List (List Int)) (rows cols : List Nat) :
    (block M A rows cols).length = rows.length := List.length_map ..

theorem block_getElem (M : Nat) (A : List (List Int)) (rows cols : List Nat)
    (hinc : cols.Pairwise (· < ·)) (i : Nat) (hi : i < (block M A rows cols).length) :
    (block M A rows cols)[i] =
      cols.map fun j => residue M ((A.getD (rows[i]'(by simpa [block] using hi)) []).getD j 0) := by
  simp only [block, List.getElem_map, Rank.nthRow_eq_getD]
  rw [pickCols_eq M _ cols 0 hinc (fun _ _ => Nat.zero_le _)]
  simp

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

/-! # Packed evaluation

`packRow` is `Nat.ofDigits` at the base `2^W`; the product of two packed
rows is the digit list of the convolution of the rows, exact as long as
every convolution coefficient stays below the base; and slot `r − 1` of
the product of a row with a reversed column is their dot product. -/

theorem allLtRows_iff (k : Nat) (rs : List (List Nat)) :
    allLtRows k rs = true ↔ ∀ r ∈ rs, ∀ x ∈ r, x < k := by
  induction rs with
  | nil => simp [allLtRows]
  | cons r rs ih => simp [allLtRows, allLt_iff, ih]

theorem residue_lt (M : Nat) (hM : 0 < M) (a : Int) : residue M a < M := by
  have hpos : (0 : Int) < (M : Int) := by exact_mod_cast hM
  have h0 : 0 ≤ a % (M : Int) := Int.emod_nonneg a (by omega)
  have h1 : a % (M : Int) < (M : Int) := Int.emod_lt_of_pos a hpos
  show (a % (M : Int)).toNat < M
  exact (Int.toNat_lt h0).mpr h1

theorem packRow_eq_ofDigits (W : Nat) (l : List Nat) : packRow W l = Nat.ofDigits (2 ^ W) l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have hs : Nat.shiftLeft (packRow W as) W = packRow W as * 2 ^ W := Nat.shiftLeft_eq _ _
    show a + Nat.shiftLeft (packRow W as) W = _
    rw [hs, Nat.ofDigits_cons, ih, Nat.mul_comm]

/-- Pointwise sum, the shorter list padded with zeros. -/
def addLists : List Nat → List Nat → List Nat
  | a :: as, b :: bs => (a + b) :: addLists as bs
  | [], l => l
  | l, [] => l

theorem addLists_getD (l m : List Nat) (t : Nat) :
    (addLists l m).getD t 0 = l.getD t 0 + m.getD t 0 := by
  induction l generalizing m t with
  | nil => simp [addLists]
  | cons a as ih =>
    cases m with
    | nil => simp [addLists]
    | cons b bs =>
      cases t with
      | zero => simp [addLists]
      | succ t =>
        simp only [addLists, List.getD_cons_succ]
        exact ih bs t

theorem ofDigits_addLists (B : Nat) (l m : List Nat) :
    Nat.ofDigits B (addLists l m) = Nat.ofDigits B l + Nat.ofDigits B m := by
  induction l generalizing m with
  | nil => simp [addLists]
  | cons a as ih =>
    cases m with
    | nil => simp [addLists]
    | cons b bs =>
      simp only [addLists, Nat.ofDigits_cons, ih]
      ring

theorem ofDigits_map_mul (B a : Nat) (l : List Nat) :
    Nat.ofDigits B (l.map (a * ·)) = a * Nat.ofDigits B l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, Nat.ofDigits_cons, ih]
    ring

/-- The coefficient list of the product of two coefficient lists. -/
def conv : List Nat → List Nat → List Nat
  | [], _ => []
  | a :: as, l => addLists (l.map (a * ·)) (0 :: conv as l)

theorem ofDigits_conv (B : Nat) (l m : List Nat) :
    Nat.ofDigits B (conv l m) = Nat.ofDigits B l * Nat.ofDigits B m := by
  induction l with
  | nil => simp [conv]
  | cons a as ih =>
    simp only [conv, ofDigits_addLists, ofDigits_map_mul, Nat.ofDigits_cons, ih]
    ring

theorem map_mul_getD (a : Nat) (m : List Nat) (t : Nat) :
    (m.map (a * ·)).getD t 0 = a * m.getD t 0 := by
  by_cases h : t < m.length
  · rw [getD_eq_getElem' _ _ _ (by simpa using h), getD_eq_getElem' _ _ _ h, List.getElem_map]
  · rw [getD_eq_default' _ _ _ (by simpa using not_lt.mp h), getD_eq_default' _ _ _ (not_lt.mp h)]
    simp

theorem conv_getD (l m : List Nat) (t : Nat) :
    (conv l m).getD t 0 = ∑ i ∈ Finset.range (t + 1), l.getD i 0 * m.getD (t - i) 0 := by
  induction l generalizing t with
  | nil => simp [conv]
  | cons a as ih =>
    simp only [conv, addLists_getD, map_mul_getD]
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.sub_zero]
    rw [add_comm]
    congr 1
    cases t with
    | zero => simp
    | succ t =>
      simp only [List.getD_cons_succ, ih]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.add_sub_add_right]

theorem conv_getD_le (M : Nat) (l m : List Nat) (hl : ∀ x ∈ l, x < M) (hm : ∀ x ∈ m, x < M)
    (t : Nat) : (conv l m).getD t 0 ≤ l.length * (M * M) := by
  rw [conv_getD]
  have hle : ∀ i ∈ Finset.range (t + 1), l.getD i 0 * m.getD (t - i) 0 ≤
      (if i < l.length then M * M else 0) := by
    intro i _
    by_cases hi : i < l.length
    · rw [if_pos hi]
      have h1 : l.getD i 0 < M := by
        rw [getD_eq_getElem' _ _ _ hi]; exact hl _ (List.getElem_mem hi)
      have h2 : m.getD (t - i) 0 ≤ M := by
        by_cases hj : t - i < m.length
        · rw [getD_eq_getElem' _ _ _ hj]; exact (hm _ (List.getElem_mem hj)).le
        · rw [getD_eq_default' _ _ _ (not_lt.mp hj)]; exact Nat.zero_le _
      exact Nat.mul_le_mul h1.le h2
    · rw [if_neg hi, getD_eq_default' _ _ _ (not_lt.mp hi)]
      simp
  refine (Finset.sum_le_sum hle).trans ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  calc (Finset.filter (fun i => i < l.length) (Finset.range (t + 1))).card
      ≤ (Finset.range l.length).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        exact Finset.mem_range.mpr hi.2
    _ = l.length := Finset.card_range _

theorem dotNat_eq_conv_reverse (b c : List Nat) (r : Nat) (hb : b.length = r) (hc : c.length = r) :
    dotNat b c = (conv b c.reverse).getD (r - 1) 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · cases b with
    | nil => simp [dotNat, conv]
    | cons => simp at hb
  · rw [conv_getD, dotNat_eq_sum' b c r hb, Finset.sum_range, Nat.sub_add_cancel hr]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (i : Nat) < r := i.isLt
    congr 1
    rw [getD_eq_getElem' _ _ _ (by omega),
      getD_eq_getElem' _ _ _ (by rw [List.length_reverse, hc]; omega), List.getElem_reverse]
    congr 1
    rw [hc]
    omega

theorem ofDigits_digit (B : Nat) (hB : 1 < B) (D : List Nat) (hD : ∀ d ∈ D, d < B) (k : Nat) :
    Nat.ofDigits B D / B ^ k % B = D.getD k 0 := by
  induction D generalizing k with
  | nil => simp
  | cons d rest ih =>
    have hd : d < B := hD d (by simp)
    cases k with
    | zero =>
      simp only [Nat.pow_zero, Nat.div_one, Nat.ofDigits_cons, List.getD_cons_zero]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    | succ k =>
      simp only [Nat.ofDigits_cons, List.getD_cons_succ]
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by omega),
        Nat.div_eq_of_lt hd, Nat.zero_add]
      exact ih (fun x hx => hD x (by simp [hx])) k

theorem dotPacked_eq (M W r : Nat) (b c : List Nat) (hb : b.length = r) (hc : c.length = r)
    (hbM : ∀ x ∈ b, x < M) (hcM : ∀ x ∈ c, x < M) (hW : r * (M * M) < 2 ^ W) :
    dotPacked W r (packRow W b) (packRow W c.reverse) = dotNat b c := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · cases b with
    | cons => simp at hb
    | nil =>
      cases c with
      | cons => simp at hc
      | nil =>
        show ((0 : Nat) * 0) >>> (W * (0 - 1)) &&& (2 ^ W - 1) = 0
        simp
  · have hM : 0 < M := by
      cases b with
      | nil => simp at hb; omega
      | cons x xs => exact lt_of_le_of_lt (Nat.zero_le _) (hbM x (by simp))
    have hB : 1 < 2 ^ W := by
      have : 1 ≤ r * (M * M) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    have hdig : ∀ d ∈ conv b c.reverse, d < 2 ^ W := by
      intro d hd
      obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hd
      rw [← getD_eq_getElem' _ _ _ ht]
      refine lt_of_le_of_lt (conv_getD_le M b c.reverse hbM (fun x hx => hcM x (List.mem_reverse.mp hx)) t) ?_
      rw [hb]; exact hW
    show (packRow W b * packRow W c.reverse) >>> (W * (r - 1)) &&& (2 ^ W - 1) = dotNat b c
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, packRow_eq_ofDigits,
      packRow_eq_ofDigits, ← ofDigits_conv, Nat.pow_mul, ofDigits_digit _ hB _ hdig,
      dotNat_eq_conv_reverse b c r hb hc]

theorem dotNat_pad (b c : List Nat) (r : Nat) (hb : b.length = r) :
    dotNat b (List.take r c ++ List.replicate (r - c.length) 0) = dotNat b c := by
  induction b generalizing c r with
  | nil => simp [dotNat]
  | cons x xs ih =>
    cases r with
    | zero => simp at hb
    | succ r =>
      have hxs : xs.length = r := by simpa using hb
      cases c with
      | nil =>
        have := ih [] r hxs
        simp only [List.take_nil, List.length_nil, Nat.sub_zero, List.nil_append] at this ⊢
        rw [List.replicate_succ]
        simp [dotNat, this]
      | cons y ys =>
        have := ih ys r hxs
        simp only [List.take_succ_cons, List.length_cons, Nat.add_sub_add_right, List.cons_append]
        simp [dotNat, this]

theorem padded_length (r : Nat) (c : List Nat) :
    (List.take r c ++ List.replicate (r - c.length) 0).length = r := by
  simp only [List.length_append, List.length_take, List.length_replicate]
  omega

theorem padded_lt (M r : Nat) (hM : 0 < M) (c : List Nat) (hc : ∀ x ∈ c, x < M) :
    ∀ x ∈ List.take r c ++ List.replicate (r - c.length) 0, x < M := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hc x (List.mem_of_mem_take hx)
  · rw [List.eq_of_mem_replicate hx]; exact hM

theorem packRow_replicate_zero (W k : Nat) : packRow W (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, packRow_eq_ofDigits, Nat.ofDigits_cons, ← packRow_eq_ofDigits, ih]
    simp

theorem packRevAux_eq (W : Nat) (k acc : Nat) (l : List Nat) :
    packRevAux W k acc l =
      acc * 2 ^ (W * k) + packRow W (List.reverse (List.take k l ++ List.replicate (k - l.length) 0)) := by
  induction k generalizing acc l with
  | zero => simp [packRevAux, packRow]
  | succ k ih =>
    have hs : ∀ x : Nat, Nat.shiftLeft x W = x * 2 ^ W := fun x => Nat.shiftLeft_eq x W
    cases l with
    | nil =>
      simp only [packRevAux, hs, ih, List.take_nil, List.length_nil, Nat.sub_zero, List.nil_append,
        List.reverse_replicate, packRow_replicate_zero, Nat.add_zero]
      rw [Nat.mul_succ, Nat.pow_add]
      ring
    | cons a as =>
      simp only [packRevAux, hs, Nat.add_eq, ih, List.take_succ_cons, List.length_cons,
        Nat.add_sub_add_right, List.cons_append, List.reverse_cons, packRow_eq_ofDigits,
        Nat.ofDigits_append,
        Nat.ofDigits_singleton, List.length_reverse, List.length_append, List.length_take,
        List.length_replicate]
      have hk : min k as.length + (k - as.length) = k := by omega
      rw [hk, Nat.mul_succ, Nat.pow_add]
      ring

theorem packCol_eq (W r : Nat) (c : List Nat) :
    packCol W r c = packRow W (List.reverse (List.take r c ++ List.replicate (r - c.length) 0)) := by
  rw [packCol, packRevAux_eq]
  simp

theorem zeroRowPacked_eq (M W r : Nat) (hM : 0 < M) (hW : r * (M * M) < 2 ^ W) (b : List Nat)
    (hb : b.length = r) (hbM : ∀ x ∈ b, x < M) (cs : List (List Nat))
    (hcs : ∀ c ∈ cs, ∀ x ∈ c, x < M) :
    zeroRowPacked M W r (packRow W b) (packCols W r cs) = zeroRow M b cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [packCols, zeroRowPacked, zeroRow, packCol_eq]
    rw [dotPacked_eq M W r b _ hb (padded_length r c) hbM
      (padded_lt M r hM c (hcs c (by simp))) hW, dotNat_pad b c r hb,
      ih (fun c hc => hcs c (by simp [hc]))]

theorem lowerCheckPacked_eq (M W r : Nat) (hM : 0 < M) (hW : r * (M * M) < 2 ^ W)
    (bs : List (List Nat)) (hbs : ∀ b ∈ bs, b.length = r ∧ ∀ x ∈ b, x < M)
    (cs : List (List Nat)) (hcs : ∀ c ∈ cs, ∀ x ∈ c, x < M) :
    lowerCheckPacked M W r (packRows W bs) (packCols W r cs) = lowerCheck M bs cs := by
  induction bs generalizing cs with
  | nil => cases cs <;> rfl
  | cons b bs ih =>
    cases cs with
    | nil => rfl
    | cons c cs =>
      obtain ⟨hb, hbM⟩ := hbs b (by simp)
      simp only [packRows, packCols, lowerCheckPacked, lowerCheck, unitDiag, packCol_eq]
      rw [dotPacked_eq M W r b _ hb (padded_length r c) hbM
        (padded_lt M r hM c (hcs c (by simp))) hW, dotNat_pad b c r hb,
        zeroRowPacked_eq M W r hM hW b hb hbM cs (fun c hc => hcs c (by simp [hc])),
        ih (fun b hb => hbs b (by simp [hb])) cs (fun c hc => hcs c (by simp [hc]))]

/-- A passing packed check is a passing plain check. -/
theorem checkRankList_of_packed (W n m : Nat) (L : List (List Int)) (c : RankWitness)
    (h : checkRankListPacked W n m L c = true) : checkRankList n m L c = true := by
  simp only [checkRankListPacked, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, hinc⟩, h8⟩, hvt⟩, hW⟩, hlow⟩, h10⟩ := h
  simp only [checkRankList, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, hinc⟩, h8⟩, ?_⟩, h10⟩
  have hM : 1 < c.modulus := by simpa using h3
  have hcolsLen : c.cols.length = c.rank := by simpa using h5
  have hcolsInc := (strictInc_iff _).mp hinc
  have hW' : c.rank * (c.modulus * c.modulus) < 2 ^ W := by simpa using hW
  have hvt' := (allLtRows_iff _ _).mp hvt
  have hbs : ∀ b ∈ block c.modulus L c.rows c.cols, b.length = c.rank ∧ ∀ x ∈ b, x < c.modulus := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    rw [block_getElem _ _ _ _ hcolsInc]
    refine ⟨by simp [hcolsLen], ?_⟩
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact residue_lt _ (by omega) _
  rw [← lowerCheckPacked_eq c.modulus W c.rank (by omega) hW' _ hbs _ hvt']
  exact hlow

/-! # Soundness -/

/-- A passing kernel check determines the rank of the row list's matrix. -/
theorem rank_eq_of_checkList (n m : Nat) (L : List (List Int)) (c : RankWitness)
    (h : checkRankList n m L c = true) : (ofLists n m L).rank = c.rank := by
  classical
  simp only [checkRankList, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, hinc⟩, h8⟩, h9⟩, h10⟩ := h
  set r := c.rank with hr
  have hLlen : L.length = n := by simpa using h1
  have hLrows : ∀ x ∈ L, x.length = m := (Rank.rowsLen_iff m L).mp h2
  have hM : 1 < c.modulus := by simpa using h3
  have hrowsLen : c.rows.length = r := by simpa using h4
  have hcolsLen : c.cols.length = r := by simpa using h5
  have hrowsLt : ∀ i ∈ c.rows, i < n := (allLt_iff _ _).mp h6
  have hcolsLt : ∀ j ∈ c.cols, j < m := (allLt_iff _ _).mp h7
  have hcolsInc : c.cols.Pairwise (· < ·) := (strictInc_iff _).mp hinc
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
      rw [Matrix.mul_apply,
        dotNat_eq_sum' _ _ r (by rw [block_getElem _ _ _ _ hcolsInc]; simp [hcolsLen]),
        Nat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.cast_mul, block_getElem _ _ _ _ hcolsInc, getD_eq_getElem' _ _ _ (by simp; omega),
        List.getElem_map,
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
      rw [Rank.nthRow_eq_getD, getD_eq_getElem' _ _ _ hi']
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


/-- `rank_eq_of_checkList` through the packed check. -/
theorem rank_eq_of_checkListPacked (W n m : Nat) (L : List (List Int)) (c : RankWitness)
    (h : checkRankListPacked W n m L c = true) : (ofLists n m L).rank = c.rank :=
  rank_eq_of_checkList n m L c (checkRankList_of_packed W n m L c h)

theorem rank_eq_of_checkListPacked' {n m : Nat} (A : Matrix (Fin n) (Fin m) ℤ)
    (L : List (List Int)) (c : RankWitness) (W : Nat) (hA : A = ofLists n m L)
    (h : checkRankListPacked W n m L c = true) : A.rank = c.rank :=
  hA ▸ rank_eq_of_checkListPacked W n m L c h

theorem rank_le_of_checkListPacked' {n m : Nat} (A : Matrix (Fin n) (Fin m) ℤ)
    (L : List (List Int)) (c : RankWitness) (W : Nat) (hA : A = ofLists n m L)
    (h : checkRankListPacked W n m L c = true) {r : Nat} (hr : c.rank ≤ r) : A.rank ≤ r :=
  (rank_eq_of_checkListPacked' A L c W hA h).le.trans hr

theorem le_rank_of_checkListPacked' {n m : Nat} (A : Matrix (Fin n) (Fin m) ℤ)
    (L : List (List Int)) (c : RankWitness) (W : Nat) (hA : A = ofLists n m L)
    (h : checkRankListPacked W n m L c = true) {r : Nat} (hr : r ≤ c.rank) : r ≤ A.rank :=
  hr.trans (rank_eq_of_checkListPacked' A L c W hA h).ge

end HexMatrixMathlib
