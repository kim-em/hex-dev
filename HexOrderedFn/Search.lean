/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Init

@[expose] public section

namespace Hex.OrderedFn

universe u
variable {α : Type u}

/-- Refinement advances exactly when the current attempt fails. -/
def Next (trial : Nat → Option α) (m n : Nat) : Prop :=
  m = n + 1 ∧ trial n = none

/-- One checked success proves termination from any earlier precision.
The trial need not be monotone or remain successful afterwards. -/
theorem acc_of_success (trial : Nat → Option α) (N : Nat) (s : α)
    (success : trial N = some s) (n : Nat) (hn : n ≤ N) : Acc (Next trial) n := by
  have build : ∀ k n, n ≤ N → N - n = k → Acc (Next trial) n := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro n hn hk
      refine Acc.intro n ?_
      intro m hstep
      obtain ⟨hm, hf⟩ := hstep
      have hne : n ≠ N := by
        intro he
        subst n
        simp [success] at hf
      exact ih (N - m) (by omega) m (by omega) rfl
  exact build (N - n) n hn rfl

/-- Eventual success supplies the erased termination premise for every start. -/
theorem next_acc (trial : Nat → Option α)
    (eventually : ∃ N, ∀ n ≥ N, (trial n).isSome = true)
    (n : Nat) : Acc (Next trial) n := by
  obtain ⟨N, hN⟩ := eventually
  have h := hN (max N n) (by omega)
  cases hs : trial (max N n) with
  | none => simp [hs] at h
  | some s => exact acc_of_success trial (max N n) s hs n (by omega)

private instance accessibleWf (trial : Nat → Option α) :
    WellFoundedRelation {n : Nat // Acc (Next trial) n} where
  rel := InvImage (Next trial) Subtype.val
  wf := ⟨fun x => InvImage.accessible Subtype.val x.property⟩

/-- Execute every attempt from the requested start until the first success.
The accessibility proof erases; it supplies neither fuel nor a runtime answer. -/
def firstSome (trial : Nat → Option α) (n : Nat)
    (h : Acc (Next trial) n) : α :=
  match eq : trial n with
  | some s => s
  | none => firstSome trial (n + 1) (h.inv ⟨rfl, eq⟩)
termination_by (⟨n, h⟩ : {n : Nat // Acc (Next trial) n})
decreasing_by exact ⟨rfl, eq⟩

/-- A successful attempt is returned immediately. -/
theorem firstSome_some (trial : Nat → Option α) (n : Nat)
    (h : Acc (Next trial) n) {s : α} (hs : trial n = some s) :
    firstSome trial n h = s := by
  rw [firstSome]
  split <;> simp_all

/-- A failed attempt advances by one precision. -/
theorem firstSome_none (trial : Nat → Option α) (n : Nat)
    (h : Acc (Next trial) n) (hn : trial n = none) :
    firstSome trial n h = firstSome trial (n + 1) (h.inv ⟨rfl, hn⟩) := by
  conv => lhs; rw [firstSome]
  split <;> simp_all

/-- The returned value occurs at the first successful precision. -/
theorem firstSome_first (trial : Nat → Option α) (n : Nat)
    (h : Acc (Next trial) n) :
    ∃ m, n ≤ m ∧ trial m = some (firstSome trial n h) ∧
      ∀ k, n ≤ k → k < m → trial k = none := by
  induction h with
  | intro n h ih =>
    cases hn : trial n with
    | some s =>
      exact ⟨n, Nat.le_refl _, by rw [firstSome_some _ _ _ hn, hn], by omega⟩
    | none =>
      obtain ⟨m, hm, hs, hf⟩ := ih (n + 1) ⟨rfl, hn⟩
      refine ⟨m, by omega, ?_, ?_⟩
      · simpa only [firstSome_none _ _ _ hn] using hs
      · intro k hk hkm
        by_cases he : k = n
        · simpa [he] using hn
        · exact hf k (by omega) hkm

/-- The result is a successful trial, without reducing the accessibility proof. -/
theorem firstSome_spec (trial : Nat → Option α) (n : Nat)
    (h : Acc (Next trial) n) :
    ∃ m, n ≤ m ∧ trial m = some (firstSome trial n h) := by
  obtain ⟨m, hm, hs, _⟩ := firstSome_first trial n h
  exact ⟨m, hm, hs⟩

/-- Prove a total result by a finite success and agreement of successful trials.
Agreement is a separate premise: termination alone proves no semantic validity. -/
theorem firstSome_eq (trial : Nat → Option α) (n : Nat)
    (h : Acc (Next trial) n) {N : Nat} {s : α} (hs : trial N = some s)
    (unique : ∀ i j a b, trial i = some a → trial j = some b → a = b) :
    firstSome trial n h = s := by
  obtain ⟨m, _, hm⟩ := firstSome_spec trial n h
  exact unique m N _ s hm hs

end Hex.OrderedFn
