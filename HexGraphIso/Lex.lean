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

/-! # Sorting

A structural insertion sort under `lexLe`. `List.mergeSort` is
well-founded recursion, which the kernel cannot unfold; certificate and
search replay need sorting that kernel-reduces. -/

/-- Insert into a `lexLe`-sorted list, keeping it sorted. -/
@[expose] def insertLe (x : List Nat) : List (List Nat) → List (List Nat)
  | [] => [x]
  | y :: rest => if lexLe x y then x :: y :: rest else y :: insertLe x rest

/-- Structural insertion sort under `lexLe`. -/
@[expose] def sortLe (l : List (List Nat)) : List (List Nat) :=
  l.foldr insertLe []

theorem perm_insertLe (x : List Nat) (l : List (List Nat)) :
    List.Perm (insertLe x l) (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y rest ih =>
    rw [insertLe]
    split
    · exact List.Perm.refl _
    · exact (ih.cons y).trans (List.Perm.swap x y rest)

theorem perm_sortLe (l : List (List Nat)) : List.Perm (sortLe l) l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x rest ih =>
    exact (perm_insertLe x (sortLe rest)).trans (ih.cons x)

theorem pairwise_insertLe {x : List Nat} {l : List (List Nat)}
    (h : l.Pairwise (lexLe · ·)) :
    (insertLe x l).Pairwise (lexLe · ·) := by
  induction l with
  | nil => simp [insertLe]
  | cons y rest ih =>
    rw [insertLe]
    rcases hp : lexLe x y with _ | _
    · simp only [Bool.false_eq_true, ite_false]
      rcases List.pairwise_cons.mp h with ⟨hy, hrest⟩
      refine List.pairwise_cons.mpr ⟨?_, ih hrest⟩
      intro z hz
      rcases List.mem_cons.mp ((perm_insertLe x rest).mem_iff.mp hz) with hzx | hz
      · rw [hzx]
        have := lexLe_total x y
        simp [hp] at this
        exact this
      · exact hy z hz
    · simp only [ite_true]
      refine List.pairwise_cons.mpr ⟨?_, h⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hp
      · exact lexLe_trans hp (List.pairwise_cons.mp h |>.1 z hz)

theorem pairwise_sortLe (l : List (List Nat)) :
    (sortLe l).Pairwise (lexLe · ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x rest ih => exact pairwise_insertLe ih

/-- Two `lexLe`-sorted lists with the same multiset of entries are
equal. With `perm_sortLe` and `pairwise_sortLe`, `sortLe` is therefore a
canonical multiset representative: permuted inputs sort to the same
list. -/
theorem eq_of_perm_of_pairwise {l m : List (List Nat)}
    (hp : List.Perm l m) (hl : l.Pairwise (lexLe · ·))
    (hm : m.Pairwise (lexLe · ·)) : l = m := by
  induction l generalizing m with
  | nil => exact (hp.nil_eq).symm ▸ rfl
  | cons x l ih =>
    cases m with
    | nil => exact absurd hp.symm.nil_eq (by simp)
    | cons y m =>
      have hxy : x = y := by
        have hxm : x ∈ y :: m := hp.mem_iff.mp (List.mem_cons_self ..)
        have hyl : y ∈ x :: l := hp.symm.mem_iff.mp (List.mem_cons_self ..)
        rcases List.mem_cons.mp hxm with rfl | hxm
        · rfl
        · rcases List.mem_cons.mp hyl with rfl | hyl
          · rfl
          · have h1 := (List.pairwise_cons.mp hl).1 y hyl
            have h2 := (List.pairwise_cons.mp hm).1 x hxm
            exact lexLe_antisymm h1 h2
      subst hxy
      have hp' : List.Perm l m := hp.cons_inv
      exact congrArg (x :: ·)
        (ih hp' (List.pairwise_cons.mp hl).2 (List.pairwise_cons.mp hm).2)

theorem sortLe_eq_of_perm {l m : List (List Nat)} (h : List.Perm l m) :
    sortLe l = sortLe m :=
  eq_of_perm_of_pairwise ((perm_sortLe l).trans (h.trans (perm_sortLe m).symm))
    (pairwise_sortLe l) (pairwise_sortLe m)

/-- Remove adjacent duplicates; on a sorted list this removes all
duplicates. -/
@[expose] def dedupAdj : List (List Nat) → List (List Nat)
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
    if x == y then dedupAdj (y :: rest) else x :: dedupAdj (y :: rest)

@[simp] theorem mem_dedupAdj {a : List Nat} :
    ∀ {l : List (List Nat)}, a ∈ dedupAdj l ↔ a ∈ l
  | [] => by simp [dedupAdj]
  | [x] => by simp [dedupAdj]
  | x :: y :: rest => by
    rw [dedupAdj]
    split
    · next hxy =>
        have hxy := beq_iff_eq.mp hxy
        subst hxy
        rw [mem_dedupAdj (l := x :: rest)]
        simp only [List.mem_cons]
        constructor
        · exact fun h => Or.inr h
        · rintro (h | h)
          · exact Or.inl h
          · exact h
    · next hxy =>
        simp only [List.mem_cons, mem_dedupAdj (l := y :: rest)]

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
