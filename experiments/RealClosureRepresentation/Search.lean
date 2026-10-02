/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Init
import Init.Data.Rat.Lemmas

namespace Search

def Next (trial : Nat → Option Int) (m n : Nat) : Prop :=
  m = n+1 ∧ trial n = none

/-- A single checked successful precision suffices; no semantic theorem or
monotonicity assumption is needed for termination from an earlier precision. -/
theorem acc_of_success (trial : Nat → Option Int) (N : Nat) (s : Int)
    (success : trial N = some s) (n : Nat) (hn : n ≤ N) : Acc (Next trial) n := by
  have build : ∀ k n, n ≤ N → N-n = k → Acc (Next trial) n := by
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
      exact ih (N-m) (by omega) m (by omega) rfl
  exact build (N-n) n hn rfl

private instance accessibleWf (trial : Nat → Option Int) :
    WellFoundedRelation {n : Nat // Acc (Next trial) n} where
  rel := InvImage (Next trial) Subtype.val
  wf := ⟨fun x => InvImage.accessible Subtype.val x.property⟩

def firstSome (trial : Nat → Option Int) (n : Nat)
    (h : Acc (Next trial) n) : Int :=
  match eq : trial n with
  | some s => s
  | none => firstSome trial (n+1) (h.inv ⟨rfl, eq⟩)
termination_by (⟨n,h⟩ : {n : Nat // Acc (Next trial) n})
decreasing_by exact ⟨rfl, eq⟩

def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1)*factorial n

def lower (n : Nat) : Rat :=
  ((List.range (n+1)).map fun i => (1 : Rat) / ((2 : Rat) ^ factorial i)).foldl (· + ·) 0

def upper (n : Nat) : Rat := lower n + 2 / ((2 : Rat) ^ factorial (n+1))

-- Evaluate X² - 8/5 using these positive rational enclosures of the test-only
-- Liouville number. Its actual containment/transcendence proof stays separate.
def trial (n : Nat) : Option Int :=
  let lo := lower n
  let hi := upper n
  if lo*lo > (8 : Rat)/5 then some 1
  else if hi*hi < (8 : Rat)/5 then some (-1)
  else none

example : trial 0 = none := by decide +kernel
example : trial 1 = none := by decide +kernel
example : trial 2 = none := by decide +kernel

theorem at_three : trial 3 = some 1 := by decide +kernel

def result : Int := firstSome trial 0 (acc_of_success trial 3 1 at_three 0 (by omega))

#print axioms acc_of_success
#print axioms at_three
#eval result
end Search
