/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateDivisionCheck

public section

namespace Hex.Groebner.Certificate

/-- Independent acceptance is tied to the original division metadata and data.
Compiled verification and a downstream kernel proof remain separate stages. -/
structure CheckedDivision (context : Context) (divisors : Array Polynomial) (dividend : Polynomial) where
  private mk ::
  value : Division
  accepted : checkDivision context.field.modulus.toNat context.variables context.order
    divisors dividend value = true

namespace Verification

/-- A sealed replay attempt retains the source identity and charged prefix. -/
structure State (context : Context) (divisors : Array Polynomial) (dividend : Polynomial) where
  private mk ::
  witness : Division
  usage : Usage

inductive Result (context : Context) (divisors : Array Polynomial) (dividend : Polynomial) where
  | checked (value : CheckedDivision context divisors dividend) (usage : Usage)
  | invalid (index : Nat) (usage : Usage)
  | rejected (usage : Usage)
  | exhausted (resource : Resource) (state : State context divisors dividend)
  | address (state : State context divisors dividend)
  | internal (usage : Usage)

private def validateWitness (context : Context) (budget : Budget) (f : Polynomial) : Work Unit := do
  try Arithmetic.validate context budget 0 f
  catch e => match e with
    | .invalid _ => throw .rejected
    | e => throw e

/-- Reserve pure cofactor reduction with previously validated divisor sizes.
This performs no divisor revalidation or polynomial multiplication. -/
def reserveReduction (context : Context) (budget : Budget) (divisorSizes : Array Nat)
    (cofactors : Array Polynomial) (target : Polynomial) : Work Unit := do
  spend budget 1
  if cofactors.size != divisorSizes.size then throw .rejected
  validateWitness context budget target
  let f ← Arithmetic.size budget target
  let width := (context.variables + 1) * (budget.exponentBits / 64 + 3)
  let mut total := 0
  let mut quotientTerms := 0
  for i in [:divisorSizes.size] do
    validateWitness context budget cofactors[i]!
    let a ← Arithmetic.size budget cofactors[i]!
    let b := divisorSizes[i]!
    quotientTerms := quotientTerms+a
    let product := a*b
    let depth := a.log2+4
    reserve budget context.variables (product*depth)
    spend budget ((product*(depth+2)+a+b+1)*width*8)
    reserveBytes budget ((product+1)*context.variables*48)
    total := total+product
    reserve budget context.variables (total+product)
    spend budget ((total+product+1)*width*4)
  spend budget ((quotientTerms+f+divisorSizes.size+1)*width*4)
  reserveBytes budget ((f+1)*context.variables*48 + divisorSizes.size*32)
  spend budget ((total+f+1)*width*4)

/-- Reserve the pure checker's nested work before invoking it. Canonical
translated product rows have linear construction and balanced merge cost;
folded summation additionally reserves every possible growing prefix.
All reservations are cumulative, and none enables an unbounded fallback. -/
def reserveReplay (context : Context) (budget : Budget) (divisors : Array Polynomial)
    (dividend : Polynomial) (result : Division) : Work Unit := do
  spend budget 1
  if result.quotients.size != divisors.size then throw .rejected
  reserveBytes budget (64 + divisors.size * 32)
  for i in [:divisors.size] do Arithmetic.validate context budget i divisors[i]!
  Arithmetic.validate context budget divisors.size dividend
  for quotient in result.quotients do validateWitness context budget quotient
  validateWitness context budget result.remainder
  let f ← Arithmetic.size budget dividend
  let r ← Arithmetic.size budget result.remainder
  let width := (context.variables + 1) * (budget.exponentBits / 64 + 3)
  let mut total := 0
  let mut divisorTerms := 0
  let mut quotientTerms := 0
  for i in [:divisors.size] do
    let a ← Arithmetic.size budget result.quotients[i]!
    let b ← Arithmetic.size budget divisors[i]!
    divisorTerms := divisorTerms + b
    quotientTerms := quotientTerms + a
    let product := a * b
    let depth := a.log2 + 4
    reserve budget context.variables (product * depth)
    spend budget ((product * (depth + 2) + a + b + f + 1) * width * 8)
    reserveBytes budget ((product + f + 1) * context.variables * 48)
    total := total + product
    reserve budget context.variables (total + product)
    spend budget ((total + product + 1) * width * 4)
  -- The pure predicate validates canonicality again and compares actual degrees.
  spend budget ((divisorTerms + quotientTerms + f + r + divisors.size + 1) * width * 4)
  reserve budget context.variables (total + r)
  spend budget ((total + r + f + 1) * width * 4)
  spend budget ((r + f + 1) * width * 4)
  reserveBytes budget ((r + f + 1) * context.variables * 48)
  spend budget ((divisorTerms + r * (divisors.size + 1) + 1) * width * 4)
  reserveBytes budget (divisorTerms * context.variables * 48 + divisors.size * 64)

private def failure {context : Context} {divisors : Array Polynomial} {dividend : Polynomial}
    (state : State context divisors dividend) : Error → Result context divisors dividend
  | .invalid i => .invalid i state.usage
  | .rejected => .rejected state.usage
  | .exhausted resource => .exhausted resource state
  | .address => .address state
  | .arithmetic => .internal state.usage

/-- Resume replay with absolute allowances. A retried atomic preflight charges
its repeated work; no completed result is exposed before the independent check. -/
def resumeWith {context : Context} {divisors : Array Polynomial} {dividend : Polynomial}
    (budget : Budget) (initial : State context divisors dividend) : Result context divisors dividend := Id.run do
  if context.variables > budget.variables then return .exhausted .variables initial
  match checkUsage budget initial.usage with
  | .error e => return failure initial e
  | .ok _ => pure ()
  let (result, usage) := (reserveReplay context budget divisors dividend initial.witness).run initial.usage
  let state := { initial with usage }
  match result with
  | .error e => return failure state e
  | .ok _ =>
    if h : checkDivision context.field.modulus.toNat context.variables context.order
        divisors dividend state.witness = true then
      return .checked ⟨state.witness, h⟩ usage
    else return .rejected usage

/-- Check explicitly supplied division data under a fresh cumulative budget. -/
def verifyWith (context : Context) (budget : Budget) (divisors : Array Polynomial)
    (dividend : Polynomial) (result : Division) : Result context divisors dividend :=
  resumeWith budget ⟨result, {}⟩

/-- Use caller-supplied cumulative parent counters after a production pass.
The caller is responsible for preserving that parent accounting. -/
def verifyFrom (context : Context) (budget : Budget) (divisors : Array Polynomial)
    (dividend : Polynomial) (result : Division) (usage : Usage) : Result context divisors dividend :=
  resumeWith budget ⟨result, usage⟩

end Verification
end Hex.Groebner.Certificate
