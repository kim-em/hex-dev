/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Init.Data.Range.Lemmas
public import Init.Data.List.Monadic

public section

namespace Hex.GraphIso.Nauty.Sparse.Loop

/-- Related loop steps make the same stop/continue choice. -/
inductive Rel (R : α → β → Prop) : ForInStep α → ForInStep β → Prop
  | done (h : R a b) : Rel R (.done a) (.done b)
  | yield (h : R a b) : Rel R (.yield a) (.yield b)

/-- Pointwise related pure callbacks give related executed list loops. -/
theorem list_rel (xs : List γ) (f : γ → α → Id (ForInStep α))
    (g : γ → β → Id (ForInStep β)) (R : α → β → Prop)
    (hstep : ∀ x a b, R a b → Rel R (f x a) (g x b))
    {a : α} {b : β} (h : R a b) :
    R (forIn xs a f) (forIn xs b g) := by
  induction xs generalizing a b with
  | nil => exact h
  | cons x xs ih =>
    have hc := hstep x a b h
    cases ha : f x a <;> cases hb : g x b <;> rw [ha, hb] at hc <;> cases hc
    · simpa only [List.forIn_cons, ha, hb, bind, pure] using ‹R _ _›
    · simpa only [List.forIn_cons, ha, hb, bind, pure] using ih ‹R _ _›

/-- The same relation applies to the literal bounded range loops used by
refinement, including early breaks. -/
theorem range_rel (n : Nat) (f : Nat → α → Id (ForInStep α))
    (g : Nat → β → Id (ForInStep β)) (R : α → β → Prop)
    (hstep : ∀ x a b, R a b → Rel R (f x a) (g x b))
    {a : α} {b : β} (h : R a b) :
    R (forIn [0:n] a f) (forIn [0:n] b g) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact list_rel _ f g R hstep h

/-- A continuing callback retains the loop invariant; an early return
only needs the final postcondition. -/
def Preserves (P Q : α → Prop) : ForInStep α → Prop
  | .yield a => P a
  | .done a => Q a

/-- Callbacks need agree only on the states and inputs that can actually
be visited. The final postcondition also covers early breaks. -/
theorem list_congr (xs : List γ) (f g : γ → α → Id (ForInStep α))
    (P Q : α → Prop) (hpq : ∀ a, P a → Q a)
    (hstep : ∀ x ∈ xs, ∀ a, P a →
      f x a = g x a ∧ Preserves P Q (f x a))
    {a : α} (h : P a) :
    forIn xs a f = forIn xs a g ∧ Q (forIn xs a f) := by
  induction xs generalizing a with
  | nil => exact ⟨rfl, hpq a h⟩
  | cons x xs ih =>
    have hs := hstep x (by simp) a h
    cases he : f x a with
    | done b =>
      have hg : g x a = .done b := hs.1.symm.trans he
      simpa only [List.forIn_cons, he, hg, bind, pure] using
        (show b = b ∧ Q b from ⟨rfl, by simpa [Preserves, he] using hs.2⟩)
    | yield b =>
      have hg : g x a = .yield b := hs.1.symm.trans he
      have hb : P b := by simpa [Preserves, he] using hs.2
      simpa only [List.forIn_cons, he, hg, bind, pure] using
        ih (fun y hy => hstep y (by simp [hy])) hb

/-- Congruence for the literal bounded ranges used by the executable. -/
theorem range_congr (first last : Nat) (f g : Nat → α → Id (ForInStep α))
    (P Q : α → Prop) (hpq : ∀ a, P a → Q a)
    (hstep : ∀ x, first ≤ x → x < last → ∀ a, P a →
      f x a = g x a ∧ Preserves P Q (f x a))
    {a : α} (h : P a) :
    forIn [first:last] a f = forIn [first:last] a g ∧ Q (forIn [first:last] a f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  apply list_congr _ f g P Q hpq ?_ h
  intro x hx a ha
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one,
    List.mem_range'] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact hstep _ (by omega) (by omega) a ha

private theorem indexed_list (count first : Nat) (f g : Nat → α → Id (ForInStep α))
    (P : Nat → α → Prop) (Q : α → Prop) (hpq : ∀ i a, P i a → Q a)
    (hstep : ∀ i, first ≤ i → i < first + count → ∀ a, P i a →
      f i a = g i a ∧ Preserves (P (i + 1)) Q (f i a))
    {a : α} (h : P first a) :
    forIn (List.range' first count) a f = forIn (List.range' first count) a g ∧
      Q (forIn (List.range' first count) a f) := by
  induction count generalizing first a with
  | zero => exact ⟨rfl, hpq first a h⟩
  | succ count ih =>
    have hs := hstep first (by omega) (by omega) a h
    cases he : f first a with
    | done b =>
      have hg : g first a = .done b := hs.1.symm.trans he
      simpa only [List.range'_succ, List.forIn_cons, he, hg, bind, pure] using
        (show b = b ∧ Q b from ⟨rfl, by simpa [Preserves, he] using hs.2⟩)
    | yield b =>
      have hg : g first a = .yield b := hs.1.symm.trans he
      have hb : P (first + 1) b := by simpa [Preserves, he] using hs.2
      simpa only [List.range'_succ, List.forIn_cons, he, hg, bind, pure] using
        ih (first + 1) (fun i hi hi' => hstep i (by omega) (by omega)) hb

/-- A literal range loop may use its current position in the invariant.
This accounts for scans whose final increment reaches the exclusive end. -/
theorem indexed_congr (first last : Nat) (f g : Nat → α → Id (ForInStep α))
    (P : Nat → α → Prop) (Q : α → Prop) (hpq : ∀ i a, P i a → Q a)
    (hstep : ∀ i, first ≤ i → i < last → ∀ a, P i a →
      f i a = g i a ∧ Preserves (P (i + 1)) Q (f i a))
    {a : α} (h : P first a) :
    forIn [first:last] a f = forIn [first:last] a g ∧ Q (forIn [first:last] a f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  exact indexed_list (last - first) first f g P Q hpq
    (fun i hi hi' => hstep i hi (by omega)) h

end Hex.GraphIso.Nauty.Sparse.Loop
