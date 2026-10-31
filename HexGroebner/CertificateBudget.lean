/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateBasis

public section

namespace Hex.Groebner.Certificate

/-- Cumulative resources for certificate production and independent replay. -/
inductive Resource where
  | work | bytes | terms | steps | nodes | pairs | variables | exponentBits
  deriving BEq, Repr

/-- Work counts charged scalar/coordinate visits and arithmetic operations.
Bytes conservatively reserve logical term storage: list cells, pairs and exponent limbs;
terms count cumulative input and produced term slots, including temporaries.
Steps count attempted division transitions. Nodes and pairs have separate caps.
Exponent bits are a resource allowance, not a polynomial-ring restriction.
Work includes reserved worst-case arithmetic. Logical bytes exclude allocator
capacity, call stacks and general runtime control objects. -/
structure Budget where
  work : Nat := 100000000
  bytes : Nat := 256 * 1024 * 1024
  terms : Nat := 1000000
  steps : Nat := 1000000
  nodes : Nat := 1000000
  pairs : Nat := 1000000
  variables : Nat := 10000
  exponentBits : Nat := 64
  deriving Inhabited

/-- Charged resources survive failure and retried atomic transitions. -/
structure Usage where
  work : Nat := 0
  bytes : Nat := 0
  terms : Nat := 0
  steps : Nat := 0
  nodes : Nat := 0
  pairs : Nat := 0
  maxExponentBits : Nat := 0
  deriving Repr, BEq, Inhabited

/-- Invalid representations, rejection, allowance exhaustion and platform
addressability remain distinct. Polynomial indices number divisors first and
then the dividend. -/
inductive Error where
  | invalid (polynomial : Nat)
  | rejected
  | exhausted (resource : Resource)
  | address
  | arithmetic
  deriving Repr, BEq

abbrev Work := ExceptT Error (StateM Usage)

/-- Charge a complete operation before executing it; failed reservations retain
the already consumed prefix without claiming the denied work was performed. -/
def spend (budget : Budget) (amount : Nat) : Work Unit := do
  let s ← get
  let used := s.work + amount
  if used > budget.work then throw (.exhausted .work)
  set { s with work := used }

/-- Reserve non-term logical payload, including temporary exponent lists. -/
def reserveBytes (budget : Budget) (amount : Nat) : Work Unit := do
  let s ← get
  let total := s.bytes + amount
  if total > budget.bytes then throw (.exhausted .bytes)
  if total ≥ USize.size then throw .address
  set { s with bytes := total }

/-- Reserve ordinary term storage before constructing it. The limb bound
includes the one-bit intermediate possible when adding exponent coordinates. -/
def reserve (budget : Budget) (variables terms : Nat) : Work Unit := do
  let s ← get
  let count := s.terms + terms
  if count > budget.terms then throw (.exhausted .terms)
  let bytes := terms * (128 + variables * (64 + 16 * ((budget.exponentBits + 1) / 64 + 1)))
  let total := s.bytes + bytes
  if total > budget.bytes then throw (.exhausted .bytes)
  if total ≥ USize.size then throw .address
  set { s with bytes := total, terms := count }

/-- Count one attempted atomic division transition. -/
def step (budget : Budget) : Work Unit := do
  let s ← get
  if s.steps ≥ budget.steps then throw (.exhausted .steps)
  set { s with steps := s.steps + 1 }

/-- Validate a coordinate's limb allowance before it enters a checkpoint. -/
def exponent (budget : Budget) (value : Nat) : Work Unit := do
  let bits := if value == 0 then 0 else value.log2 + 1
  spend budget (bits / 64 + 1)
  if bits > budget.exponentBits then throw (.exhausted .exponentBits)
  modify fun s => { s with maxExponentBits := max s.maxExponentBits bits }

/-- Reject a smaller cumulative allowance before resuming existing work. -/
def checkUsage (budget : Budget) (s : Usage) : Except Error Unit := do
  if s.work > budget.work then throw (.exhausted .work)
  if s.bytes > budget.bytes then throw (.exhausted .bytes)
  if s.terms > budget.terms then throw (.exhausted .terms)
  if s.steps > budget.steps then throw (.exhausted .steps)
  if s.nodes > budget.nodes then throw (.exhausted .nodes)
  if s.pairs > budget.pairs then throw (.exhausted .pairs)
  if s.maxExponentBits > budget.exponentBits then throw (.exhausted .exponentBits)

end Hex.Groebner.Certificate
