/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateBasis

public section

namespace Hex.Groebner.Certificate

/-- Cumulative work and allocation counters for certificate production and replay. -/
inductive Resource where
  | work | allocatedBytes | allocatedTerms | steps | nodes | pairs | variables | exponentBits
  deriving BEq, Repr

/-- Work counts scalar/coordinate visits and arithmetic operations.
`allocatedBytes` and `allocatedTerms` reserve cumulative logical input,
temporary and output payload; they are allocation allowances, not live or peak
memory limits. Bytes include list cells, pairs and exponent limbs, excluding
allocator capacity, call stacks and general runtime control objects. Steps count
attempted division transitions. Nodes/pairs separately bound witness structure.
Exponent bits are an allowance, not a polynomial-ring restriction. -/
structure Budget where
  work : Nat := 100000000
  allocatedBytes : Nat := 256 * 1024 * 1024
  allocatedTerms : Nat := 1000000
  steps : Nat := 1000000
  nodes : Nat := 1000000
  pairs : Nat := 1000000
  variables : Nat := 10000
  exponentBits : Nat := 64
  deriving Inhabited

/-- Charged work and allocation survive failure and retried atomic transitions.
Allocation counters measure cumulative logical allocation, not live or peak memory. -/
structure Usage where
  work : Nat := 0
  allocatedBytes : Nat := 0
  allocatedTerms : Nat := 0
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

/-- Reject an unaddressable single allocation before allocating it. This is
separate from cumulative allocation accounting, which may exceed `USize.size`. -/
def checkAddress (size : Nat) : Work Unit := do
  if size ≥ USize.size then throw .address

/-- Reserve non-term logical payload, including temporary exponent lists. -/
def reserveBytes (budget : Budget) (amount : Nat) : Work Unit := do
  let s ← get
  let total := s.allocatedBytes + amount
  if total > budget.allocatedBytes then throw (.exhausted .allocatedBytes)
  set { s with allocatedBytes := total }

/-- Reserve ordinary term storage before constructing it. The limb bound
includes the one-bit intermediate possible when adding exponent coordinates. -/
def reserve (budget : Budget) (variables allocatedTerms : Nat) : Work Unit := do
  let s ← get
  let count := s.allocatedTerms + allocatedTerms
  if count > budget.allocatedTerms then throw (.exhausted .allocatedTerms)
  let allocatedBytes := allocatedTerms * (128 + variables * (64 + 16 * ((budget.exponentBits + 1) / 64 + 1)))
  let total := s.allocatedBytes + allocatedBytes
  if total > budget.allocatedBytes then throw (.exhausted .allocatedBytes)
  set { s with allocatedBytes := total, allocatedTerms := count }

/-- Reserve a repeated pure evaluation of work performed during preflight.
Node and pair caps count witness structure once. -/
def reserveAgain (budget : Budget) (before after : Usage) : Work Unit := do
  spend budget (after.work - before.work)
  reserveBytes budget (after.allocatedBytes - before.allocatedBytes)
  let current ← get
  let allocatedTerms := current.allocatedTerms + (after.allocatedTerms - before.allocatedTerms)
  if allocatedTerms > budget.allocatedTerms then throw (.exhausted .allocatedTerms)
  modify fun s => { s with allocatedTerms }

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
  if s.allocatedBytes > budget.allocatedBytes then throw (.exhausted .allocatedBytes)
  if s.allocatedTerms > budget.allocatedTerms then throw (.exhausted .allocatedTerms)
  if s.steps > budget.steps then throw (.exhausted .steps)
  if s.nodes > budget.nodes then throw (.exhausted .nodes)
  if s.pairs > budget.pairs then throw (.exhausted .pairs)
  if s.maxExponentBits > budget.exponentBits then throw (.exhausted .exponentBits)

end Hex.Groebner.Certificate
