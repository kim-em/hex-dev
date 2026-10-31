/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateArithmetic

public section

namespace Hex.Groebner.Certificate

/-- Exact quotient and remainder data; the producer result remains unchecked
until independent reconstruction and irreducibility replay succeeds. -/
structure Division where
  quotients : Array Polynomial
  remainder : Polynomial
  deriving Repr, Inhabited

namespace Division

/-- A complete atomic division prefix. The active dividend and all previous
quotients/remainder remain committed only after a whole transition succeeds. -/
structure Checkpoint where
  active : Polynomial := []
  quotients : Array Polynomial := #[]
  remainder : Polynomial := []
  inverses : Array Nat := #[]
  heads : Array (Option (List Nat × Nat)) := #[]
  deriving Inhabited

/-- Sealed identity and cumulative counters for certificate division. -/
structure State where
  private mk ::
  context : Context
  divisors : Array Polynomial
  dividend : Polynomial
  checkpoint : Option Checkpoint
  usage : Usage

/-- Successful production is explicitly an unchecked candidate. Exhaustion
retains the original field/order, divisors, dividend and committed prefix. -/
inductive Result where
  | candidate (value : Division) (usage : Usage)
  | invalid (index : Nat) (usage : Usage)
  | exhausted (resource : Resource) (state : State)
  | address (state : State)
  | internal (usage : Usage)

private def failure (state : State) : Error → Result
  | .invalid i => .invalid i state.usage
  | .exhausted resource => .exhausted resource state
  | .address => .address state
  | _ => .internal state.usage

private def prepare (context : Context) (budget : Budget) (divisors : Array Polynomial)
    (dividend : Polynomial) : Work Checkpoint := do
  checkAddress (64 + divisors.size * 16)
  reserveBytes budget (64 + divisors.size * 32)
  let mut heads := Array.emptyWithCapacity divisors.size
  let mut inverses := Array.emptyWithCapacity divisors.size
  for i in [:divisors.size] do
    Arithmetic.validate context budget i divisors[i]!
    let head ← Arithmetic.leading context budget divisors[i]!
    heads := heads.push head
    inverses := inverses.push (← match head with
      | none => pure 0
      | some term => Arithmetic.inverse context budget term.2)
  Arithmetic.validate context budget divisors.size dividend
  return { active := dividend, heads, inverses, quotients := Array.replicate divisors.size [] }

private def advance (context : Context) (budget : Budget) (divisors : Array Polynomial)
    (checkpoint : Checkpoint) : Work Checkpoint := do
  step budget
  spend budget 1
  if checkpoint.heads.size != divisors.size || checkpoint.inverses.size != divisors.size ||
      checkpoint.quotients.size != divisors.size then
    throw .arithmetic
  let some term ← Arithmetic.leading context budget checkpoint.active | throw .arithmetic
  let mut selected : Option (Nat × (List Nat × Nat)) := none
  for i in [:divisors.size] do
    spend budget ((context.variables + 1) * (budget.exponentBits / 64 + 2))
    if let some head := checkpoint.heads[i]! then
      if divides head.1 term.1 then
        selected := some (i, head)
        break
  match selected with
  | none =>
    reserve budget context.variables 1
    let singleton := [term]
    let active ← Arithmetic.subtract context budget checkpoint.active singleton
    let remainder ← Arithmetic.add context budget checkpoint.remainder singleton
    return { checkpoint with active, remainder }
  | some (i, head) =>
    spend budget ((context.variables + 1) * (budget.exponentBits / 64 + 2))
    reserve budget context.variables 1
    let shift := difference term.1 head.1
    let inverse := checkpoint.inverses[i]!
    if inverse == 0 then throw .arithmetic
    spend budget 1
    let coefficient := (context.field.barrett.mulMod term.2.toUInt64 inverse.toUInt64).toNat
    if coefficient == 0 then throw .arithmetic
    let factor := (shift, coefficient)
    let product ← Arithmetic.multiply context budget factor divisors[i]!
    let active ← Arithmetic.subtract context budget checkpoint.active product
    let quotient ← Arithmetic.add context budget checkpoint.quotients[i]! [factor]
    checkAddress (64 + checkpoint.quotients.size * 16)
    reserveBytes budget (checkpoint.quotients.size * 8)
    return { checkpoint with active, quotients := checkpoint.quotients.set! i quotient }

/-- Continue under absolute cumulative allowances. Every transition consumes the
remaining parent budget; retrying a failed transition charges its work again. -/
def resumeWith (budget : Budget) (initial : State) : Result := Id.run do
  let mut state := initial
  if state.context.variables > budget.variables then return .exhausted .variables state
  match checkUsage budget state.usage with
  | .error e => return failure state e
  | .ok _ => pure ()
  if state.checkpoint.isNone then
    let (result, usage) := (prepare state.context budget state.divisors state.dividend).run state.usage
    state := { state with usage }
    match result with
    | .error e => return failure state e
    | .ok checkpoint => state := { state with checkpoint := some checkpoint }
  for _ in [:budget.steps - state.usage.steps] do
    let checkpoint := state.checkpoint.getD {}
    if checkpoint.active.isEmpty then
      return .candidate ⟨checkpoint.quotients, checkpoint.remainder⟩ state.usage
    let (result, usage) := (advance state.context budget state.divisors checkpoint).run state.usage
    state := { state with usage }
    match result with
    | .error e => return failure state e
    | .ok checkpoint => state := { state with checkpoint := some checkpoint }
  let checkpoint := state.checkpoint.getD {}
  if checkpoint.active.isEmpty then
    return .candidate ⟨checkpoint.quotients, checkpoint.remainder⟩ state.usage
  return .exhausted .steps state

/-- Bounded deterministic division candidate production on canonical ordinary
residue lists. Zero divisors are skipped. No native success flag or unchecked
candidate is promoted to a checked division result by this operation. -/
def computeWith (context : Context) (budget : Budget) (divisors : Array Polynomial)
    (dividend : Polynomial) : Result :=
  resumeWith budget ⟨context, divisors, dividend, none, {}⟩

end Division
end Hex.Groebner.Certificate
