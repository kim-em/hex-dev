/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.Saturation
public import HexKroneckerMathlib.Degree

public section

namespace Hex.Kronecker

theorem Expr.analyze_root (cap k : Nat) (e : Expr) (acc : List Bounds) :
    (e.analyze cap k acc).1 ∈ (e.analyze cap k acc).2 := by
  cases e <;> simp [Expr.analyze]

theorem Expr.analyze_acc (cap k : Nat) (e : Expr) (acc : List Bounds) :
    acc ⊆ (e.analyze cap k acc).2 := by
  induction e generalizing acc with
  | int | atom => simp [Expr.analyze]
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
      intro v hv
      exact List.mem_cons_of_mem _ (hb _ (ha _ hv))
  | neg a ha | pow a n ha =>
      intro v hv
      exact List.mem_cons_of_mem _ (ha _ hv)

theorem le_maxBits (ss : List Nat) (w : Nat) (bs : List Bounds) (b : Bounds)
    (hb : b ∈ bs) : b.bits ss w ≤ maxBits ss w bs := by
  induction bs with
  | nil => simp at hb
  | cons a as ih =>
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Nat.le_max_left _ _
      · exact (ih hb).trans (Nat.le_max_right _ _)

theorem bits_of_accept (budget : Budget) (common : Bounds) (bs : List Bounds)
    (h : (makeSize budget common bs).accepts budget = true) (b : Bounds) (hb : b ∈ bs) :
    b.bits (makeStrides 1 common.degrees) (common.height.log2 + 2) ≤ budget.maxPackedBits := by
  have hm := le_maxBits (makeStrides 1 common.degrees) (common.height.log2 + 2) bs b hb
  have hh : min (maxBits (makeStrides 1 common.degrees) (common.height.log2 + 2) bs)
      (budget.maxPackedBits + 1) ≤ budget.maxPackedBits :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
  omega

theorem height_of_accept (budget : Budget) (common : Bounds) (bs : List Bounds)
    (h : (makeSize budget common bs).accepts budget = true) (b : Bounds) (hb : b ∈ bs) :
    b.height < 2 ^ budget.maxPackedBits := by
  have hbits := bits_of_accept budget common bs h b hb
  by_cases hz : b.height = 0
  · simp [hz]
  · apply (Nat.log2_lt hz).mp
    unfold Bounds.bits at hbits
    omega

theorem height_eq_of_accept (budget : Budget) (common : Bounds) (bs : List Bounds)
    (h : (makeSize budget common bs).accepts budget = true) (e : Expr) (k : Nat)
    (he : (⟨e.degrees k, e.cappedHeight (2 ^ budget.maxPackedBits)⟩ : Bounds) ∈ bs) :
    e.height = e.cappedHeight (2 ^ budget.maxPackedBits) := by
  have hh := height_of_accept budget common bs h _ he
  simp only [Expr.cappedHeight_eq] at hh ⊢
  omega

theorem width_bound (H : Nat) : 2 * H < 2 ^ (H.log2 + 2) := by
  have h := Nat.lt_log2_self (n := H)
  rw [show H.log2 + 2 = (H.log2 + 1) + 1 from rfl, Nat.pow_succ]
  omega

theorem Saturating.le_add_left (cap a b : Nat) (ha : a ≤ cap) : a ≤ Saturating.add cap a b := by
  rw [Saturating.add_eq]
  omega

theorem Saturating.le_add_right (cap a b : Nat) (hb : b ≤ cap) : b ≤ Saturating.add cap a b := by
  rw [Saturating.add_eq]
  omega

end Hex.Kronecker
