/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.Conditional
public import Std

public section

/-!
Lexicographic comparison of serialized coloured graphs.

The reference canonical form serializes each candidate to a digit list and
selects the greatest under lexicographic order. This module provides the
executable comparison `lexLe`, the order facts the argmax fold needs
(reflexive, total, transitive, antisymmetric), and the fold itself with its
membership and maximality lemmas.
-/

namespace Hex.GraphIso

/-- Lexicographic comparison of digit lists: earlier digits dominate, and a
prefix precedes every extension. -/
@[expose] def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: l, b :: m => decide (a < b) || (a == b && lexLe l m)

@[simp] theorem lexLe_refl (l : List Nat) : lexLe l l = true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [lexLe, ih]

theorem lexLe_total (l m : List Nat) : lexLe l m || lexLe m l := by
  induction l generalizing m with
  | nil => simp [lexLe]
  | cons a l ih =>
    cases m with
    | nil => simp [lexLe]
    | cons b m =>
      rcases Nat.lt_trichotomy a b with h | h | h
      · simp [lexLe, h]
      · subst h
        simpa [lexLe] using ih m
      · simp [lexLe, h]

theorem lexLe_trans {l m o : List Nat} (h1 : lexLe l m) (h2 : lexLe m o) :
    lexLe l o := by
  induction l generalizing m o with
  | nil => simp [lexLe]
  | cons a l ih =>
    cases m with
    | nil => simp [lexLe] at h1
    | cons b m =>
      cases o with
      | nil => simp [lexLe] at h2
      | cons c o =>
        simp only [lexLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq] at h1 h2 ⊢
        rcases h1 with h1 | ⟨rfl, h1⟩
        · rcases h2 with h2 | ⟨rfl, h2⟩
          · exact Or.inl (Nat.lt_trans h1 h2)
          · exact Or.inl h1
        · rcases h2 with h2 | ⟨rfl, h2⟩
          · exact Or.inl h2
          · exact Or.inr ⟨rfl, ih h1 h2⟩

theorem lexLe_antisymm {l m : List Nat} (h1 : lexLe l m) (h2 : lexLe m l) :
    l = m := by
  induction l generalizing m with
  | nil =>
    cases m with
    | nil => rfl
    | cons b m => simp [lexLe] at h2
  | cons a l ih =>
    cases m with
    | nil => simp [lexLe] at h1
    | cons b m =>
      simp only [lexLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at h1 h2
      rcases h1 with h1 | ⟨rfl, h1⟩
      · rcases h2 with h2 | ⟨he, h2⟩
        · omega
        · omega
      · rcases h2 with h2 | ⟨_, h2⟩
        · omega
        · rw [ih h1 h2]

/-! # Argmax fold -/

variable {α : Type u} (key : α → List Nat)

/-- Select the last entry with the greatest key, scanning left to right from
a seed. -/
@[expose] def pick (best : α) : List α → α
  | [] => best
  | x :: rest => pick (if lexLe (key best) (key x) then x else best) rest

theorem pick_mem (best : α) (rest : List α) :
    pick key best rest = best ∨ pick key best rest ∈ rest := by
  induction rest generalizing best with
  | nil => exact Or.inl rfl
  | cons x rest ih =>
    rw [pick]
    rcases ih (if lexLe (key best) (key x) then x else best) with h | h
    · rw [h]
      split
      · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem le_pick (best : α) (rest : List α) :
    ∀ y ∈ best :: rest, lexLe (key y) (key (pick key best rest)) := by
  induction rest generalizing best with
  | nil =>
    intro y hy
    rw [List.mem_singleton] at hy
    subst hy
    simp [pick]
  | cons x rest ih =>
    intro y hy
    rw [pick]
    have hb : lexLe (key best) (key (if lexLe (key best) (key x) then x else best)) := by
      split
      · assumption
      · simp
    have hx : lexLe (key x) (key (if lexLe (key best) (key x) then x else best)) := by
      split
      · simp
      · rename_i hf
        have := lexLe_total (key best) (key x)
        simp [hf] at this
        exact this
    rcases List.mem_cons.mp hy with rfl | hy
    · exact lexLe_trans hb (ih _ _ (List.mem_cons_self ..))
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact lexLe_trans hx (ih _ _ (List.mem_cons_self ..))
      · exact ih _ _ (List.mem_cons_of_mem _ hy)

end Hex.GraphIso
