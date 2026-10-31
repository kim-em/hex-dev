/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateBudget

public section

namespace Hex.Groebner.Certificate.Arithmetic

/-- Validate arity after at most n+1 list constructors, even on malformed data. -/
def arity : Nat → List Nat → Bool
  | 0, [] => true
  | n + 1, _ :: es => arity n es
  | _, _ => false

/-- Count a supplied polynomial incrementally, charging before every visit. -/
def size (budget : Budget) (f : Polynomial) : Work Nat := do
  spend budget 1
  let mut count := 0
  for _ in f do
    spend budget 1
    count := count + 1
  return count

/-- Validate canonical certificate input within the parent allowance. -/
def validate (context : Context) (budget : Budget) (index : Nat) (f : Polynomial) : Work Unit := do
  spend budget 1
  let mut previous : Option (List Nat) := none
  for term in f do
    spend budget ((context.variables + 1) * (budget.exponentBits / 64 + 2))
    if !arity context.variables term.1 || term.2 == 0 || term.2 ≥ context.field.modulus.toNat then
      throw (.invalid index)
    for e in term.1 do exponent budget e
    if let some p := previous then
      if Hex.MvPoly.Kernel.expCmp p term.1 != .gt then throw (.invalid index)
    reserve budget context.variables 1
    previous := some term.1

/-- Find the actual leading term after reserving comparison work and temporary
reverse lists used by grevlex. The reservation is independent of the order. -/
def leading (context : Context) (budget : Budget) (f : Polynomial) :
    Work (Option (List Nat × Nat)) := do
  let count ← size budget f
  spend budget (count * (3 * context.variables + 1) * (budget.exponentBits / 64 + 2))
  reserveBytes budget (count * context.variables * 48)
  return Certificate.leading context.order f

/-- Exact inverse using the existing wide modular arithmetic, with every
multiply charged to the same parent certificate budget. -/
def inverse (context : Context) (budget : Budget) (coefficient : Nat) : Work Nat := do
  spend budget 1
  if coefficient == 0 || coefficient ≥ context.field.modulus.toNat then throw .arithmetic
  if coefficient == 1 then return 1
  let ctx := context.field.barrett
  let mut a := coefficient.toUInt64
  let mut power := context.field.modulus.toNat - 2
  let mut value : UInt64 := 1
  for _ in [:context.field.modulus.toNat.log2 + 1] do
    if power == 0 then break
    if power % 2 == 1 then
      spend budget 1
      value := ctx.mulMod value a
    power := power / 2
    if power != 0 then
      spend budget 1
      a := ctx.mulMod a a
  return value.toNat

/-- Add canonical rows, reserving all result term slots before the linear merge. -/
def add (context : Context) (budget : Budget) (a b : Polynomial) : Work Polynomial := do
  let left ← size budget a
  let right ← size budget b
  spend budget ((left + right) * (context.variables + 1) * (budget.exponentBits / 64 + 2) * 4)
  reserve budget context.variables (left + right)
  return Hex.MvPoly.Kernel.addMod context.field.modulus.toNat a b

/-- Exact subtraction, including the temporary negated row in the reservation. -/
def subtract (context : Context) (budget : Budget) (a b : Polynomial) : Work Polynomial := do
  let left ← size budget a
  let right ← size budget b
  spend budget ((left + right) * (context.variables + 1) * (budget.exponentBits / 64 + 2) * 4 + right)
  reserve budget context.variables (left + 2 * right)
  return Hex.MvPoly.Kernel.subMod context.field.modulus.toNat a b

/-- Monomial translation preserves descending lex storage. Exact prime-field
products are canonical; zeros are removed defensively. Result exponent widths
are checked before the caller can commit a division checkpoint. -/
def multiply (context : Context) (budget : Budget) (factor : List Nat × Nat)
    (f : Polynomial) : Work Polynomial := do
  spend budget (context.variables + 1)
  if !arity context.variables factor.1 || factor.2 ≥ context.field.modulus.toNat then throw .arithmetic
  let count ← size budget f
  spend budget (count * (context.variables + 1) * (budget.exponentBits / 64 + 2) * 2)
  reserve budget context.variables (2 * count)
  let ctx := context.field.barrett
  let mut output := []
  for term in f do
    let e := factor.1.zipWith Nat.add term.1
    for coordinate in e do exponent budget coordinate
    let c := (ctx.mulMod factor.2.toUInt64 term.2.toUInt64).toNat
    if c != 0 then output := (e, c) :: output
  return output.reverse

end Hex.Groebner.Certificate.Arithmetic
