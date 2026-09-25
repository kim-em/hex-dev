/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Complete

public section

namespace Hex.SignDet.Thom

/-- The strict rule either compares the common tails first or compares the
current entries in the orientation selected by their equal next sign. -/
theorem compareFrom_cons_lt (a b : Int) (as bs : List Int) :
    compareFrom (a :: as) (b :: bs) = some .lt ↔
      compareFrom as bs = some .lt ∨
      (as = bs ∧ ((as.head? = some 1 ∧ a < b) ∨ (as.head? = some (-1) ∧ b < a))) := by
  cases ht : compareFrom as bs with
  | none =>
    have hne : as ≠ bs := by intro h; subst bs; simp [compareFrom_self] at ht
    simp [compareFrom, ht, hne]
  | some order =>
    cases order with
    | lt => simp [compareFrom, ht]
    | gt =>
      have hne : as ≠ bs := by intro h; subst bs; simp [compareFrom_self] at ht
      simp [compareFrom, ht, hne]
    | eq =>
      have he := compareFrom_eq ht
      subst bs
      by_cases hab : a = b
      · subst b; simp [compareFrom, compareFrom_self]
      · cases as with
        | nil => simp [compareFrom, hab]
        | cons next rest =>
          by_cases hp : next = 1
          · simp [compareFrom, compareFrom_self, hab, hp, Int.compare_eq_lt]
          · by_cases hn : next = -1
            · simp [compareFrom, compareFrom_self, hab, hn, Int.compare_eq_lt]
            · simp [compareFrom, compareFrom_self, hab, hp, hn]

/-- The finite strict comparison is transitive even before assigning root
semantics to the vectors. Unorderable pairs do not supply a premise. -/
theorem compareFrom_trans {as bs cs : List Int}
    (hab : compareFrom as bs = some .lt) (hbc : compareFrom bs cs = some .lt) :
    compareFrom as cs = some .lt := by
  induction as generalizing bs cs with
  | nil => cases bs <;> simp [compareFrom] at hab
  | cons a as ih =>
    cases bs with
    | nil => simp [compareFrom] at hab
    | cons b bs =>
      cases cs with
      | nil => simp [compareFrom] at hbc
      | cons c cs =>
        obtain hab | ⟨he, hhead⟩ := (compareFrom_cons_lt a b as bs).mp hab
        · obtain hbc | ⟨he, _⟩ := (compareFrom_cons_lt b c bs cs).mp hbc
          · exact (compareFrom_cons_lt a c as cs).mpr (Or.inl (ih hab hbc))
          · subst cs
            exact (compareFrom_cons_lt a c as bs).mpr (Or.inl hab)
        · subst bs
          obtain hbc | ⟨he, hnext⟩ := (compareFrom_cons_lt b c as cs).mp hbc
          · exact (compareFrom_cons_lt a c as cs).mpr (Or.inl hbc)
          · subst cs
            apply (compareFrom_cons_lt a c as as).mpr
            right
            refine ⟨rfl, ?_⟩
            rcases hhead with ⟨hp, hab⟩ | ⟨hn, hba⟩
            · rcases hnext with ⟨_, hbc⟩ | ⟨hn, _⟩
              · exact Or.inl ⟨hp, by omega⟩
              · simp [hp] at hn
            · rcases hnext with ⟨hp, _⟩ | ⟨_, hcb⟩
              · simp [hn] at hp
              · exact Or.inr ⟨hn, by omega⟩

/-- Swapping the vectors swaps the returned finite ordering, including
failure. Equal tails choose the same orientation for both directions. -/
theorem compareFrom_swap (as bs : List Int) :
    (compareFrom as bs).map Ordering.swap = compareFrom bs as := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [compareFrom]
  | cons a as ih =>
    cases bs with
    | nil => simp [compareFrom]
    | cons b bs =>
      have hi := ih bs
      cases ht : compareFrom as bs with
      | none =>
        simp only [ht, Option.map_none] at hi
        simp [compareFrom, ht, ← hi]
      | some order =>
        cases order with
        | lt =>
          simp only [ht, Option.map_some, Ordering.swap] at hi
          simp [compareFrom, ht, ← hi]
        | gt =>
          simp only [ht, Option.map_some, Ordering.swap] at hi
          simp [compareFrom, ht, ← hi]
        | eq =>
          have he := compareFrom_eq ht
          subst bs
          by_cases hab : a = b
          · subst b; simp [compareFrom_self]
          · cases as with
            | nil => simp [compareFrom, hab, Ne.symm hab]
            | cons next rest =>
              by_cases hp : next = 1
              · simp [compareFrom, compareFrom_self, hab, Ne.symm hab, hp, Int.compare_swap]
              · by_cases hn : next = -1
                · simp [compareFrom, compareFrom_self, hab, Ne.symm hab, hn, Int.compare_swap]
                · simp [compareFrom, compareFrom_self, hab, Ne.symm hab, hp, hn]

/-- Shape validation is preserved when composing two strict comparisons. -/
theorem compareSigns_trans {as bs cs : List Int}
    (hab : compareSigns as bs = some .lt) (hbc : compareSigns bs cs = some .lt) :
    compareSigns as cs = some .lt := by
  unfold compareSigns at hab hbc ⊢
  split at hab
  · contradiction
  · split at hbc
    · contradiction
    · split
      · simp_all only [Bool.or_eq_true, not_or, Bool.not_eq_true, Bool.false_eq_true, or_self]
      · exact compareFrom_trans hab hbc

/-- Shape checking is symmetric and preserves reversal of the finite rule. -/
theorem compareSigns_swap (as bs : List Int) :
    (compareSigns as bs).map Ordering.swap = compareSigns bs as := by
  have hg : (as.isEmpty || bs.isEmpty ||
      !as.all (fun s => decide (s = -1 ∨ s = 0 ∨ s = 1)) ||
      !bs.all (fun s => decide (s = -1 ∨ s = 0 ∨ s = 1))) =
      (bs.isEmpty || as.isEmpty ||
      !bs.all (fun s => decide (s = -1 ∨ s = 0 ∨ s = 1)) ||
      !as.all (fun s => decide (s = -1 ∨ s = 0 ∨ s = 1))) := by
    simp only [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  simp only [compareSigns, ← hg]
  split
  · rfl
  · exact compareFrom_swap as bs

end Hex.SignDet.Thom

namespace Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
  [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Literal head and full-slot bindings compose with the finite order. -/
theorem Descriptor.fullOrder_trans {sign : E → Int} {context : Ctx}
    {a b c : Descriptor E Ctx sign context}
    (hab : a.fullOrder b = some .lt) (hbc : b.fullOrder c = some .lt) :
    a.fullOrder c = some .lt := by
  obtain ⟨hab, hsigns⟩ := fullOrder_eq hab
  obtain ⟨hbc, hnext⟩ := fullOrder_eq hbc
  unfold fullOrder
  rw [ite_eq_left ⟨hab.1.trans hbc.1, hab.2.1, hbc.2.2⟩]
  exact Thom.compareSigns_trans hsigns hnext

/-- Swapping full descriptors swaps the result of a finite comparison. -/
theorem Descriptor.fullOrder_swap {sign : E → Int} {context : Ctx}
    (a b : Descriptor E Ctx sign context) :
    (a.fullOrder b).map Ordering.swap = b.fullOrder a := by
  have hs := Thom.compareSigns_swap a.raw.signs b.raw.signs
  simp only [fullOrder]
  split
  · rename_i hguard
    rw [ite_eq_left ⟨hguard.1.symm, hguard.2.2, hguard.2.1⟩]
    exact hs
  · rename_i hguard
    have hreverse : ¬(b.raw.head = a.raw.head ∧
        b.raw.indices = (List.range b.raw.head.natDegree).map (· + 1) ∧
        a.raw.indices = (List.range a.raw.head.natDegree).map (· + 1)) := by
      intro h
      exact hguard ⟨h.1.symm, h.2.2, h.2.1⟩
    rw [ite_eq_right hreverse]
    rfl

/-- Reversing a successful strict comparison reverses its finite result. -/
theorem Descriptor.fullOrder_reverse {sign : E → Int} {context : Ctx}
    {a b : Descriptor E Ctx sign context} (h : a.fullOrder b = some .gt) :
    b.fullOrder a = some .lt := by
  have hs := fullOrder_swap a b
  rw [h] at hs
  exact hs.symm

end Hex.SignDet
