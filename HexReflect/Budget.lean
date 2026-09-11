/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public section

/-!
Resource accounting for symbolic reflection.

A budget bounds every dimension of a reflection request independently. The
session records the initial budget, the consumed amounts, and derives the
remaining amounts; a check happens before an operation whose cost can exceed
the remaining amount, and exhaustion reports the dimension, limit, consumed
amount, and requested increment.
-/

namespace Hex.Reflect

/-- The independently bounded dimensions of a reflection request. -/
inductive BudgetDimension where
  /-- Source syntax nodes and batch entries. -/
  | sourceNodes
  /-- Atoms allocated in the growing environment. -/
  | atoms
  /-- Reflected syntax nodes. -/
  | reflectedNodes
  /-- Literal exponent size. This dimension is a limit, not a running total. -/
  | exponent
  /-- Converted monomials and polynomial terms. -/
  | terms
  /-- Coefficient size in bits. This dimension is a limit, not a running total. -/
  | coefficientBits
  /-- Proof-reconstruction nodes and quoted expression size. -/
  | proofNodes
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

/-- Per-dimension amounts, used both for limits and for consumed usage. -/
structure Budget where
  /-- Source syntax nodes and batch entries. -/
  sourceNodes : Nat
  /-- Atoms in the growing environment. -/
  atoms : Nat
  /-- Reflected syntax nodes. -/
  reflectedNodes : Nat
  /-- Literal exponent size. -/
  exponent : Nat
  /-- Converted monomials and polynomial terms. -/
  terms : Nat
  /-- Coefficient size in bits. -/
  coefficientBits : Nat
  /-- Proof-reconstruction nodes and quoted expression size. -/
  proofNodes : Nat
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

/-- Consumed amounts, one per dimension. -/
abbrev BudgetUsage := Budget

namespace Budget

/-- The amount recorded for one dimension. -/
def get (b : Budget) : BudgetDimension → Nat
  | .sourceNodes => b.sourceNodes
  | .atoms => b.atoms
  | .reflectedNodes => b.reflectedNodes
  | .exponent => b.exponent
  | .terms => b.terms
  | .coefficientBits => b.coefficientBits
  | .proofNodes => b.proofNodes

/-- Replace the amount recorded for one dimension. -/
def set (b : Budget) : BudgetDimension → Nat → Budget
  | .sourceNodes, v => { b with sourceNodes := v }
  | .atoms, v => { b with atoms := v }
  | .reflectedNodes, v => { b with reflectedNodes := v }
  | .exponent, v => { b with exponent := v }
  | .terms, v => { b with terms := v }
  | .coefficientBits, v => { b with coefficientBits := v }
  | .proofNodes, v => { b with proofNodes := v }

/-- Nothing consumed. -/
def zero : Budget :=
  { sourceNodes := 0, atoms := 0, reflectedNodes := 0, exponent := 0, terms := 0,
    coefficientBits := 0, proofNodes := 0 }

/-- The default limits for an interactive request. -/
def default : Budget :=
  { sourceNodes := 100000, atoms := 4096, reflectedNodes := 100000, exponent := 64,
    terms := 100000, coefficientBits := 4096, proofNodes := 1000000 }

/-- Pointwise difference, saturating at zero. -/
def sub (a b : Budget) : Budget :=
  { sourceNodes := a.sourceNodes - b.sourceNodes
    atoms := a.atoms - b.atoms
    reflectedNodes := a.reflectedNodes - b.reflectedNodes
    exponent := a.exponent - b.exponent
    terms := a.terms - b.terms
    coefficientBits := a.coefficientBits - b.coefficientBits
    proofNodes := a.proofNodes - b.proofNodes }

/-- Pointwise maximum. -/
def max (a b : Budget) : Budget :=
  { sourceNodes := Nat.max a.sourceNodes b.sourceNodes
    atoms := Nat.max a.atoms b.atoms
    reflectedNodes := Nat.max a.reflectedNodes b.reflectedNodes
    exponent := Nat.max a.exponent b.exponent
    terms := Nat.max a.terms b.terms
    coefficientBits := Nat.max a.coefficientBits b.coefficientBits
    proofNodes := Nat.max a.proofNodes b.proofNodes }

@[simp] theorem get_set_same (b : Budget) (d : BudgetDimension) (v : Nat) :
    (b.set d v).get d = v := by
  cases d <;> rfl

@[simp] theorem get_zero (d : BudgetDimension) : zero.get d = 0 := by
  cases d <;> rfl

theorem get_sub (a b : Budget) (d : BudgetDimension) :
    (a.sub b).get d = a.get d - b.get d := by
  cases d <;> rfl

end Budget

/-- The report returned when a request exceeds one budget dimension. -/
structure BudgetExhausted where
  /-- The exceeded dimension. -/
  dimension : BudgetDimension
  /-- The limit of that dimension. -/
  limit : Nat
  /-- The amount consumed before the request. -/
  consumed : Nat
  /-- The requested increment. -/
  requested : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Initial limits together with the running usage. -/
structure BudgetState where
  initial : Budget
  consumed : BudgetUsage := Budget.zero
  deriving Repr, BEq, Inhabited

namespace BudgetState

/-- Start accounting against `limits`. -/
def ofBudget (limits : Budget) : BudgetState :=
  { initial := limits }

/-- Remaining amounts, pointwise. -/
def remaining (s : BudgetState) : Budget :=
  s.initial.sub s.consumed

/-- Whether an increment of `amount` in dimension `d` fits the remaining
budget. Limit dimensions compare `amount` itself against the limit. -/
def fits (s : BudgetState) (d : BudgetDimension) (amount : Nat) : Bool :=
  match d with
  | .exponent | .coefficientBits => amount ≤ s.initial.get d
  | _ => s.consumed.get d + amount ≤ s.initial.get d

/-- The exhaustion report for dimension `d` and increment `amount`. -/
def exhausted (s : BudgetState) (d : BudgetDimension) (amount : Nat) :
    BudgetExhausted :=
  { dimension := d, limit := s.initial.get d, consumed := s.consumed.get d,
    requested := amount }

/-- Check an increment without consuming it. -/
def check (s : BudgetState) (d : BudgetDimension) (amount : Nat) :
    Except BudgetExhausted Unit :=
  if s.fits d amount then .ok () else .error (s.exhausted d amount)

/-- Consume an increment. Limit dimensions record the largest value seen. -/
def charge (s : BudgetState) (d : BudgetDimension) (amount : Nat) :
    Except BudgetExhausted BudgetState :=
  if s.fits d amount then
    match d with
    | .exponent | .coefficientBits =>
      .ok { s with consumed := s.consumed.set d (Nat.max (s.consumed.get d) amount) }
    | _ => .ok { s with consumed := s.consumed.set d (s.consumed.get d + amount) }
  else
    .error (s.exhausted d amount)

theorem check_of_charge {s s' : BudgetState} {d : BudgetDimension} {amount : Nat}
    (h : s.charge d amount = .ok s') : s.check d amount = .ok () := by
  unfold charge at h
  unfold check
  split at h
  · rename_i hfits
    rw [ite_eq_left hfits]
  · cases h

end BudgetState

end Hex.Reflect
