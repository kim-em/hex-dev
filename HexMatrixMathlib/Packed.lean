/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Packed
public import HexMatrixMathlib.Literal
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

public section

/-!
Soundness of the Kronecker-packed dot products of `Hex.Matrix.Packed`:
`packRow` is `Nat.ofDigits` at the base `2^W`, the product of two packed
lists is `ofDigits` of their convolution, a convolution coefficient of
lists with entries below `M` is at most `r · M²`, digit `k` of an
`ofDigits` with digits below the base is read off by division and
remainder, and the coefficient `r − 1` of a row against a reversed column
is their dot product; hence `dotPacked_eq`, which every packed checker's
equality to its plain form reduces to.
-/

namespace HexMatrixMathlib

open Hex.Matrix.Packed

theorem dotNat_eq_sum (a b : List Nat) :
    dotNat a b = ∑ i : Fin a.length, a[i] * b.getD i 0 := by
  induction a generalizing b with
  | nil => simp [dotNat]
  | cons x xs ih =>
    cases b with
    | nil => simp [dotNat]
    | cons y ys => simp [dotNat, Fin.sum_univ_succ, ih]

theorem dotNat_eq_sum' (a b : List Nat) (r : Nat) (ha : a.length = r) :
    dotNat a b = ∑ i : Fin r, a.getD i 0 * b.getD i 0 := by
  subst ha
  rw [dotNat_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [getD_eq_getElem' _ _ _ i.isLt]
  rfl

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

end HexMatrixMathlib
