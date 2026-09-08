/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic

public section

/-! Resource reservations shared by producers, including recursive chain builds. -/

namespace Hex.PermGroup.Execution

/-- Independent cumulative work allowances. These count logical operations and
slots, not bytes or elapsed time. `sifts` counts visited chain levels (including
terminal levels); `points` counts point visits; `pairs` counts Schreier pairs.
`images` counts permutation-image slots. `certificates` counts program and
certificate nodes, including reserved copies. `storage` counts auxiliary
container slots. Search nodes and refinement tests have their own counters. -/
inductive Resource where
  | nodes
  | refinements
  | sifts
  | certificates
  | points
  | pairs
  | images
  | storage
  deriving DecidableEq, BEq, Repr

/-- Cumulative producer reservations. Batches may reserve an upper bound before
execution; unused reservations are retained, so surplus budget never changes the
reported usage. Image slots count permutation storage separately from program
nodes and traversal work. -/
structure Work where
  nodes : Nat := 0
  refinements : Nat := 0
  sifts : Nat := 0
  certificates : Nat := 0
  points : Nat := 0
  pairs : Nat := 0
  images : Nat := 0
  storage : Nat := 0
  deriving DecidableEq, BEq, Repr

abbrev Budget := Work

namespace Work

@[expose] def get (w : Work) : Resource → Nat
  | .nodes => w.nodes
  | .refinements => w.refinements
  | .sifts => w.sifts
  | .certificates => w.certificates
  | .points => w.points
  | .pairs => w.pairs
  | .images => w.images
  | .storage => w.storage

@[expose] def add (w : Work) (r : Resource) (k : Nat) : Work :=
  match r with
  | .nodes => { w with nodes := w.nodes + k }
  | .refinements => { w with refinements := w.refinements + k }
  | .sifts => { w with sifts := w.sifts + k }
  | .certificates => { w with certificates := w.certificates + k }
  | .points => { w with points := w.points + k }
  | .pairs => { w with pairs := w.pairs + k }
  | .images => { w with images := w.images + k }
  | .storage => { w with storage := w.storage + k }

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

/-- A computation threads one meter through all nested operations. Failure
retains the counters at the first reservation that could not be met. -/
abbrev Run (budget : Budget) (α : Type) := StateT (Meter budget) (Except (Exhausted budget)) α

/-- Continue an operation with an existing meter; nested work never receives
fresh allowances. -/
@[expose] def Meter.execute {budget : Budget} (meter : Meter budget)
    (computation : Run budget α) : Measured budget α :=
  match computation.run meter with
  | .error failure => .exhausted failure
  | .ok (value, meter) => .ok value meter

/-- Reserve work before invoking the operation that uses it. -/
@[expose] def reserve {budget : Budget} (r : Resource) (k : Nat) : Run budget Unit := do
  let meter ← get
  match meter.spend r k with
  | .error failure => throw failure
  | .ok meter => set meter

/-- Evaluate a producer from zero usage. Replay uses a separate invocation and
its own allowances; it cannot consume a producer's remaining budget. -/
@[expose] def run (budget : Budget) (computation : Run budget α) : Measured budget α :=
  (Meter.empty budget).execute computation

end Hex.PermGroup.Execution
