/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.NormalForm

public section

namespace Hex.Groebner.Certificate.BasisVerification

private def witness (context : Context) (budget : Budget) (f : Polynomial) : Work Unit := do
  try Arithmetic.validate context budget 0 f
  catch e => match e with
    | .invalid _ => throw .rejected
    | e => throw e

/-- Bound balanced polynomial multiplication and validate every resulting
exponent before retaining its value in the replay workspace. -/
private def multiply (context : Context) (budget : Budget) (a b : Polynomial) : Work Polynomial := do
  let x ← Arithmetic.size budget a
  let y ← Arithmetic.size budget b
  let depth := x.log2 + 4
  let width := (context.variables + 1) * (budget.exponentBits / 64 + 3)
  spend budget ((x * y * (depth + 2) + x + y + 1) * width * 8)
  reserve budget context.variables (x * y * depth)
  let result := Hex.MvPoly.Kernel.mulMod context.field.modulus.toNat a b
  witness context budget result
  return result

private def containment (context : Context) (budget : Budget)
    (generators targets : Array Polynomial) (certificate : Containment) : Work Unit := do
  spend budget 1
  if certificate.roots.size != targets.size then throw .rejected
  let mut values : Array Polynomial := #[]
  for node in certificate.nodes do
    spend budget 1
    let used ← get
    if used.nodes ≥ budget.nodes then throw (.exhausted .nodes)
    modify fun s => { s with nodes := s.nodes + 1 }
    reserveBytes budget 64
    let value ← match node with
      | .zero => pure []
      | .generator i => match generators[i]? with
        | none => throw .rejected
        | some f => pure f
      | .add i j => match values[i]?, values[j]? with
        | some a, some b => Arithmetic.add context budget a b
        | _, _ => throw .rejected
      | .scale c i => do
        if c ≥ context.field.modulus.toNat then throw .rejected
        let some f := values[i]? | throw .rejected
        let size ← Arithmetic.size budget f
        spend budget (size * 4 + 1)
        reserve budget context.variables size
        pure (Hex.MvPoly.Kernel.smulMod context.field.modulus.toNat c f)
      | .multiply factor i => do
        witness context budget factor
        let some f := values[i]? | throw .rejected
        multiply context budget factor f
    values := values.push value
  for i in [:targets.size] do
    spend budget 1
    let some value := values[certificate.roots[i]!]? | throw .rejected
    let size ← Arithmetic.size budget value
    let targetSize ← Arithmetic.size budget targets[i]!
    spend budget ((size + targetSize + 1) * (context.variables + 1) *
      (budget.exponentBits / 64 + 3) * 4)
    if !Hex.MvPoly.Kernel.beq value targets[i]! then throw .rejected

private def prepare (context : Context) (budget : Budget) (generators basis : Array Polynomial)
    (certificate : Basis) : Work Unit := do
  for i in [:generators.size] do Arithmetic.validate context budget i generators[i]!
  for f in basis do witness context budget f
  containment context budget generators basis certificate.forward
  containment context budget basis generators certificate.backward
  let mut total := 0
  for f in basis do total := total + (← Arithmetic.size budget f)
  let width := (context.variables + 1) * (budget.exponentBits / 64 + 3)
  spend budget ((total + basis.size + 1) * (basis.size + 1) * width * 8)
  reserveBytes budget ((total + 1) * context.variables * 48 + basis.size * 64)
  spend budget 1
  if certificate.pairs.size != basis.size then throw .rejected
  for i in [:basis.size] do
    spend budget 1
    if certificate.pairs[i]!.size != basis.size then throw .rejected
    for j in [:basis.size] do
      spend budget 1
      let used ← get
      if used.pairs ≥ budget.pairs then throw (.exhausted .pairs)
      modify fun s => { s with pairs := s.pairs + 1 }
      let a ← Arithmetic.leading context budget basis[i]!
      let b ← Arithmetic.leading context budget basis[j]!
      let target ← match a,b with
        | some a, some b => do
          spend budget (width * 4)
          reserve budget context.variables 2
          let left ← Arithmetic.multiply context budget (difference b.1 a.1,b.2) basis[i]!
          let right ← Arithmetic.multiply context budget (difference a.1 b.1,a.2) basis[j]!
          Arithmetic.subtract context budget left right
        | _,_ => pure []
      Verification.reserveReplay context budget basis target ⟨certificate.pairs[i]![j]!,[]⟩

/-- Sealed identity and cumulative replay reservations. -/
structure State where
  private mk ::
  context : Context
  generators : Array Polynomial
  basis : Array Polynomial
  certificate : Basis
  usage : Usage

inductive Result where
  | checked (basis : CheckedBasis) (usage : Usage)
  | invalid (index : Nat) (usage : Usage)
  | rejected (usage : Usage)
  | exhausted (resource : Resource) (state : State)
  | address (state : State)
  | internal (usage : Usage)

private def failure (state : State) : Error → Result
  | .invalid i => .invalid i state.usage
  | .rejected => .rejected state.usage
  | .exhausted r => .exhausted r state
  | .address => .address state
  | .arithmetic => .internal state.usage

/-- Resume independent complete basis replay. All pure replay work is reserved
before invoking its Boolean predicate. Retrying charges the repeated preflight. -/
def resumeWith (budget : Budget) (initial : State) : Result := Id.run do
  if initial.context.variables > budget.variables then return .exhausted .variables initial
  match checkUsage budget initial.usage with
  | .error e => return failure initial e
  | .ok _ => pure ()
  let operation : Work Unit := do
    let before ← get
    prepare initial.context budget initial.generators initial.basis initial.certificate
    let after ← get
    -- Replaying the pure checker repeats polynomial operations even when a
    -- large expression cancels to zero. Reserve operand-based preflight costs
    -- again; charging only the final value size would miss that work.
    spend budget (after.work - before.work)
    reserveBytes budget (after.bytes - before.bytes)
    let current ← get
    let terms := current.terms + (after.terms - before.terms)
    if terms > budget.terms then throw (.exhausted .terms)
    modify fun s => { s with terms }
  let (result,usage) := operation.run initial.usage
  let state := { initial with usage }
  match result with
  | .error e => return failure state e
  | .ok _ =>
    if h : checkBasis state.context state.generators state.basis state.certificate = true then
      return .checked (.ofCertificate state.context state.generators state.basis state.certificate h) usage
    else return .rejected usage

/-- Check a literal complete basis witness using the remaining parent budget. -/
def verifyFrom (context : Context) (budget : Budget) (generators basis : Array Polynomial)
    (certificate : Basis) (usage : Usage) : Result :=
  resumeWith budget ⟨context,generators,basis,certificate,usage⟩

def verifyWith (context : Context) (budget : Budget) (generators basis : Array Polynomial)
    (certificate : Basis) : Result :=
  verifyFrom context budget generators basis certificate {}

end Hex.Groebner.Certificate.BasisVerification
