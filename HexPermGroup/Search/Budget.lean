/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Trials

public section

namespace Hex.PermGroup.Search

inductive Resource where
  | nodes
  | refinements
  | sifts
  | certificates
  deriving DecidableEq, BEq, Repr

/-- Search work is accounted separately by visited nodes, constraint tests
(pruning reasons and leaf predicates), membership queries, and certificate nodes. -/
structure Work where
  nodes : Nat := 0
  refinements : Nat := 0
  sifts : Nat := 0
  certificates : Nat := 0
  deriving DecidableEq, BEq, Repr

abbrev Budget := Work

namespace Work

@[expose] def get (w : Work) : Resource → Nat
  | .nodes => w.nodes
  | .refinements => w.refinements
  | .sifts => w.sifts
  | .certificates => w.certificates

@[expose] def add (w : Work) (r : Resource) (k : Nat) : Work :=
  match r with
  | .nodes => { w with nodes := w.nodes + k }
  | .refinements => { w with refinements := w.refinements + k }
  | .sifts => { w with sifts := w.sifts + k }
  | .certificates => { w with certificates := w.certificates + k }

@[simp] theorem get_add (w : Work) (r s : Resource) (k : Nat) :
    (w.add r k).get s = w.get s + if s = r then k else 0 := by
  cases r <;> cases s <;> simp [add, get]

end Work

/-- Counters never exceed the supplied allowances. Every successful charge
retains this invariant, including when a later operation exhausts its budget. -/
structure Meter (budget : Budget) where
  used : Work
  bounded : ∀ r, used.get r ≤ budget.get r

namespace Meter

@[expose] def empty (budget : Budget) : Meter budget where
  used := {}
  bounded := by intro r; cases r <;> exact Nat.zero_le _

@[expose] def available {budget : Budget} (m : Meter budget) (r : Resource) : Nat :=
  budget.get r - m.used.get r

@[expose] def charge {budget : Budget} (m : Meter budget) (r : Resource) (k : Nat)
    (h : k ≤ m.available r) : Meter budget where
  used := m.used.add r k
  bounded := by
    intro s
    rw [Work.get_add]
    by_cases he : s = r
    · subst s
      simp only [ite_true]
      have hb := m.bounded r
      simp only [available] at h
      omega
    · simpa only [he, ite_false, Nat.add_zero] using m.bounded s

theorem charge_mono {budget : Budget} (m : Meter budget) (r : Resource) (k : Nat)
    (h : k ≤ m.available r) (s : Resource) : m.used.get s ≤ (m.charge r k h).used.get s := by
  simp only [charge, Work.get_add]
  exact Nat.le_add_right _ _

@[simp] theorem available_charge {budget : Budget} (m : Meter budget) (r : Resource) (k : Nat)
    (h : k ≤ m.available r) : (m.charge r k h).available r = m.available r - k := by
  simp only [available, charge, Work.get_add, ite_true]
  omega

end Meter

/-- An unmet charge identifies both the exhausted resource and the counters
at the stopping point. It makes no claim that the search has finished. -/
structure Exhausted (budget : Budget) where
  meter : Meter budget
  resource : Resource
  requested : Nat
  insufficient : meter.available resource < requested

@[expose] def Meter.spend {budget : Budget} (m : Meter budget) (r : Resource) (k : Nat) :
    Except (Exhausted budget) (Meter budget) :=
  if h : k ≤ m.available r then .ok (m.charge r k h)
  else .error ⟨m, r, k, Nat.lt_of_not_ge h⟩

/-- A primitive operation either returns its result and updated counters or
the exact stopping point. Both alternatives retain the budget invariant. -/
inductive Measured (budget : Budget) (α : Type) where
  | ok (value : α) (meter : Meter budget)
  | exhausted (failure : Exhausted budget)

end Hex.PermGroup.Search
