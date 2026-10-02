/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.Denote

public section

namespace Hex.Kronecker.Saturating

theorem small_mul_lt (cap a b : Nat)
    (h : (a < 4294967296 && b < 4294967296 && 18446744073709551616 ≤ cap) = true) :
    a * b < cap := by
  simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at h
  have hm := Nat.mul_lt_mul_of_lt_of_lt h.1.1 h.1.2
  exact hm.trans_le h.2

theorem small_add_lt (cap a b : Nat)
    (h : (a < 4294967296 && b < 4294967296 && 18446744073709551616 ≤ cap) = true) :
    a + b < cap := by
  simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at h
  omega

theorem add_eq (cap a b : Nat) : add cap a b = min (a + b) cap := by
  unfold add
  split_ifs with hf ha hb
  · exact (min_eq_left (Nat.le_of_lt (small_add_lt cap a b hf))).symm
  all_goals omega

theorem mul_eq (cap a b : Nat) : mul cap a b = min (a * b) cap := by
  unfold mul
  split_ifs with hf hz hc hd
  · exact (min_eq_left (Nat.le_of_lt (small_mul_lt cap a b hf))).symm
  · rcases Bool.or_eq_true_iff.mp hz with ha | hb
    · simp [eq_of_beq ha]
    · simp [eq_of_beq hb]
  · apply (min_eq_right _).symm
    have hb : b ≠ 0 := by intro hb; simp [hb] at hz
    exact hc.trans (Nat.le_mul_of_pos_right _ (by omega))
  · apply (min_eq_right _).symm
    have ha : a ≠ 0 := by intro ha; simp [ha] at hz
    have := (Nat.div_lt_iff_lt_mul (by omega : 0 < a)).mp hd
    rw [Nat.mul_comm b a] at this
    omega
  · apply (min_eq_left _).symm
    have ha : a ≠ 0 := by intro ha; simp [ha] at hz
    have := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mp (Nat.le_of_not_gt hd)
    rw [Nat.mul_comm b a] at this
    omega

theorem min_add (cap a b : Nat) :
    min (min a cap + min b cap) cap = min (a + b) cap := by omega

theorem min_mul_left (cap a b : Nat) : min (min a cap * b) cap = min (a * b) cap := by
  by_cases hb : b = 0
  · simp [hb]
  by_cases ha : a ≤ cap
  · rw [min_eq_left ha]
  · rw [min_eq_right (by omega : cap ≤ a)]
    have h₁ : cap ≤ cap * b := Nat.le_mul_of_pos_right _ (by omega)
    have h₂ : cap ≤ a * b := (by omega : cap ≤ a).trans
      (Nat.le_mul_of_pos_right _ (by omega))
    rw [min_eq_right h₁, min_eq_right h₂]

theorem min_mul (cap a b : Nat) :
    min (min a cap * min b cap) cap = min (a * b) cap := by
  rw [min_mul_left, Nat.mul_comm a, min_mul_left, Nat.mul_comm b]

theorem powAux_eq (cap a fuel n : Nat) (hn : n ≤ fuel) :
    powAux cap fuel a n = min (a ^ n) cap := by
  induction fuel generalizing n with
  | zero =>
      have : n = 0 := by omega
      subst n
      simp [powAux]
  | succ fuel ih =>
      by_cases hz : n = 0
      · subst n; simp [powAux]
      by_cases ha : a = 0
      · subst a; simp [powAux, hz]
      have hd : n / 2 ≤ fuel := by
        have := Nat.div_lt_self (by omega : 0 < n) (by decide : 1 < 2)
        omega
      simp only [powAux, beq_iff_eq, hz, ha, ↓reduceIte, ih _ hd]
      split_ifs with hcap he
      · apply (min_eq_right _).symm
        have hbase : cap ≤ a ^ (n / 2) := by omega
        exact hbase.trans (Nat.pow_le_pow_right (by omega) (Nat.div_le_self n 2))
      · rw [mul_eq, min_mul, ← Nat.pow_add]
        congr 2
        have := Nat.mod_add_div n 2
        omega
      · rw [mul_eq, mul_eq, min_mul, min_mul_left, ← Nat.pow_add, ← Nat.pow_succ]
        congr 2
        have := Nat.mod_add_div n 2
        have := Nat.mod_lt n (by decide : 0 < 2)
        omega

theorem pow_eq (cap a n : Nat) : pow cap a n = min (a ^ n) cap :=
  powAux_eq cap a n n le_rfl

theorem min_pow (cap a n : Nat) : min (min a cap ^ n) cap = min (a ^ n) cap := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.pow_succ, Nat.pow_succ, ← min_mul_left, ih, Nat.mul_comm (min (a ^ n) cap),
        min_mul, Nat.mul_comm]

end Hex.Kronecker.Saturating

namespace Hex.Kronecker

theorem Expr.cappedHeight_eq (cap : Nat) (e : Expr) :
    e.cappedHeight cap = min e.height cap := by
  induction e with
  | int | atom => rfl
  | add a b ha hb | sub a b ha hb =>
      simp only [Expr.cappedHeight, Expr.height, ha, hb, Saturating.add_eq, Saturating.min_add]
      rfl
  | mul a b ha hb =>
      simp only [Expr.cappedHeight, Expr.height, ha, hb, Saturating.mul_eq, Saturating.min_mul]
      rfl
  | neg a ha => exact ha
  | pow a n ha =>
      simp only [Expr.cappedHeight, Expr.height, ha, Saturating.pow_eq, Saturating.min_pow]
      rfl

theorem Expr.analyzeCore_bound (cap k : Nat) (e : Expr) :
    (e.analyzeCore cap k).1 = ⟨e.degrees k, e.cappedHeight cap⟩ := by
  induction e <;>
    simp_all [Expr.analyzeCore, Expr.degrees, Expr.cappedHeight, Bounds.add, Bounds.mul, Bounds.pow]

theorem Expr.scan_eq (cap k : Nat) (e : Expr) :
    (e.scan cap k).1 = (e.analyzeCore cap k).1 ∧
      ∀ acc, (e.scan cap k).2 acc = (e.analyzeCore cap k).2 ++ acc := by
  induction e <;> simp_all [Expr.scan, Expr.analyzeCore, List.append_assoc]
  all_goals intro acc; split_ifs <;> simp_all [List.append_assoc]

theorem Expr.analyze_eq (cap k : Nat) (e : Expr) (acc : List Bounds) :
    e.analyze cap k acc =
      ((e.analyzeCore cap k).1, (e.analyzeCore cap k).1 :: ((e.analyzeCore cap k).2 ++ acc)) := by
  simp only [Expr.analyze, (e.scan_eq cap k).1, (e.scan_eq cap k).2]

theorem Expr.analyze_bound (cap k : Nat) (e : Expr) (acc : List Bounds) :
    (e.analyze cap k acc).1 = ⟨e.degrees k, e.cappedHeight cap⟩ := by
  rw [e.analyze_eq]
  exact e.analyzeCore_bound cap k

end Hex.Kronecker
