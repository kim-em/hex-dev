/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Producer.Pipeline

public section

namespace Hex.Groebner.Checked

/-- A complete accepted result is indexed by the exact original context and
canonical input generators, independently of producer metadata. -/
structure Basis (context : Context) (generators : Array Certificate.Polynomial)
    (expected : Option (Array Certificate.Polynomial)) where
  private mk ::
  value : CheckedBasis
  history : Producer.History
  context_eq : value.context = context
  generators_eq : value.generators = generators
  candidate_eq : ∀ candidate, expected = some candidate → value.polynomials = candidate

private inductive Stage where
  | prepare (usage : Certificate.Usage)
  | running (state : Producer.BasisState)
  | receipt (value : CheckedBasis) (usage : Certificate.Usage) (history : Producer.History)

structure State (context : Context) (generators : Array Certificate.Polynomial)
    (expected : Option (Array Certificate.Polynomial)) where
  private mk ::
  private stage : Stage

inductive Result (context : Context) (generators : Array Certificate.Polynomial)
    (expected : Option (Array Certificate.Polynomial)) where
  | success (basis : Basis context generators expected) (usage : Certificate.Usage)
  | invalid (index : Nat) (usage : Certificate.Usage)
  | rejected (usage : Certificate.Usage)
  | computeExhausted (resource : F4Resource) (state : State context generators expected)
  | certificateExhausted (resource : Certificate.Resource) (state : State context generators expected)
  | representation (error : MonomialError) (state : State context generators expected)
  | address (state : State context generators expected)
  | internal (usage : Certificate.Usage)

private def finish (context : Context) (budget : Producer.Budget)
    (generators : Array Certificate.Polynomial) (expected : Option (Array Certificate.Polynomial))
    (value : CheckedBasis) (initial : Certificate.Usage) (history : Producer.History) : Result context generators expected := Id.run do
  let certificateBudget := { budget.certificate with work := min budget.certificate.work budget.computation.work, allocatedBytes := min budget.certificate.allocatedBytes budget.computation.packedBytes }
  let state : State context generators expected := ⟨.receipt value initial history⟩
  if context.variables > min budget.computation.variables budget.certificate.variables then
    return .certificateExhausted .variables state
  match Producer.checkHistory budget.computation history with
  | .error (.exhausted resource) => return .computeExhausted resource state
  | .error _ => return .internal initial
  | .ok _ => pure ()
  match Certificate.checkUsage certificateBudget initial with
  | .error (.exhausted resource) => return .certificateExhausted resource state
  | .error _ => return .internal initial
  | .ok _ => pure ()
  let action : Certificate.Work Unit := do
    Certificate.spend certificateBudget 1
    Certificate.reserveBytes certificateBudget 64
    for polynomials in [generators, value.polynomials] do
      for polynomial in polynomials do
        let count ← Certificate.Arithmetic.size certificateBudget polynomial
        Certificate.spend certificateBudget (count*(context.variables+1)*(certificateBudget.exponentBits/64+3))
  let (result,usage) := action.run initial
  let state : State context generators expected := ⟨.receipt value usage history⟩
  match result with
  | .error (.exhausted resource) => return .certificateExhausted resource state
  | .error .address => return .address state
  | .error _ => return .internal usage
  | .ok _ =>
    if hc : value.context = context then
      if hg : value.generators = generators then
        match he : expected with
        | none => return .success ⟨value,history,hc,hg,by intro candidate h; rw [he] at h; cases h⟩ usage
        | some candidate =>
          if hp : value.polynomials = candidate then
            return .success ⟨value,history,hc,hg,by intro data h; exact hp.trans (Option.some.inj (he.symm.trans h))⟩ usage
          else return .internal usage
      else return .internal usage
    else return .internal usage

private def produced (context : Context) (budget : Producer.Budget)
    (generators : Array Certificate.Polynomial) (expected : Option (Array Certificate.Polynomial)) :
    Producer.BasisResult → Result context generators expected
  | .success value usage history => finish context budget generators expected value usage history
  | .invalid (.arity i _) statistics => .invalid i { work := statistics.work,allocatedBytes := statistics.allocatedBytes }
  | .invalid (.coefficient i _) statistics => .invalid i { work := statistics.work,allocatedBytes := statistics.allocatedBytes }
  | .invalid _ statistics => .internal { work := statistics.work,allocatedBytes := statistics.allocatedBytes }
  | .rejected usage => .rejected usage
  | .computeExhausted resource state => .computeExhausted resource ⟨.running state⟩
  | .certificateExhausted resource state => .certificateExhausted resource ⟨.running state⟩
  | .representation error state => .representation error ⟨.running state⟩
  | .address state => .address ⟨.running state⟩
  | .internal usage => .internal usage

private def prepare (context : Context) (budget : Certificate.Budget)
    (generators : Array Certificate.Polynomial) : Certificate.Work (Array RawPolynomial) := do
  if context.variables > budget.variables then throw (.exhausted .variables)
  Certificate.checkAddress (64+generators.size*16)
  Certificate.reserveBytes budget (64+generators.size*16)
  let mut result := Array.emptyWithCapacity generators.size
  for i in [:generators.size] do
    let polynomial := generators[i]!
    Certificate.Arithmetic.validate context budget i polynomial
    let count ← Certificate.Arithmetic.size budget polynomial
    Certificate.checkAddress (64+count*16)
    Certificate.reserveBytes budget (64+count*(64+context.variables*16))
    let mut raw := Array.emptyWithCapacity count
    for term in polynomial do
      Certificate.spend budget (context.variables+1)
      let mut powers := Array.emptyWithCapacity context.variables
      for exponent in term.1 do
        if exponent > 4294967295 then throw .arithmetic
        powers := powers.push exponent
      raw := raw.push ⟨powers,term.2.toUInt64⟩
    result := result.push raw
  return result

/-- Canonical prime-field inputs are retained in the result type and sealed
continuation. All conversions and nested work consume the parent allowance. -/
def resumeWith {context : Context} {generators : Array Certificate.Polynomial}
    (budget : Producer.Budget) (state : State context generators expected) : Result context generators expected := Id.run do
  match state.stage with
  | .running computation => return produced context budget generators expected (Producer.resumeBasisWith budget computation)
  | .receipt value usage history => return finish context budget generators expected value usage history
  | .prepare previous =>
    let cb : Certificate.Budget := { budget.certificate with
      work := min budget.certificate.work budget.computation.work
      allocatedBytes := min budget.certificate.allocatedBytes budget.computation.packedBytes
      variables := min budget.certificate.variables budget.computation.variables }
    match Certificate.checkUsage cb previous with
    | .error (.exhausted resource) => return .certificateExhausted resource state
    | .error _ => return .internal previous
    | .ok _ => pure ()
    let (result,usage) := (prepare context cb generators).run previous
    let state : State context generators expected := ⟨.prepare usage⟩
    match result with
    | .ok raw =>
      return produced context budget generators expected (match expected with
        | none => Producer.basisFrom context budget raw usage
        | some expected => Producer.certifyCandidateFrom context budget raw expected usage)
    | .error (.invalid i) => return .invalid i usage
    | .error (.exhausted resource) => return .certificateExhausted resource state
    | .error .address => return .address state
    | .error .arithmetic => return .representation .exponent state
    | .error .rejected => return .rejected usage

def basisWith (context : Context) (budget : Producer.Budget)
    (generators : Array Certificate.Polynomial) : Result context generators none :=
  resumeWith budget ⟨.prepare {}⟩

def certifyWith (context : Context) (budget : Producer.Budget)
    (generators candidate : Array Certificate.Polynomial) : Result context generators (some candidate) :=
  resumeWith budget ⟨.prepare {}⟩

end Hex.Groebner.Checked

namespace Hex.Groebner

/-- Packed F4 shape limits and certificate allowances, with shared cumulative
work/allocation caps across conversion, production, generation and replay. -/
abbrev BasisLimits := Producer.Budget
abbrev BasisReceipt := Checked.Basis
abbrev BasisResult := Checked.Result
abbrev BasisState := Checked.State

/-- Compute and independently certify the reduced basis of canonical
natural-residue generators in descending lex storage. The context selects the
mathematical order. Success is tied to these exact original generators. -/
def basisWith (context : Context) (limits : BasisLimits)
    (generators : Array Certificate.Polynomial) : BasisResult context generators none :=
  Checked.basisWith context limits generators

/-- Certify explicit canonical candidate polynomials against the original
canonical generators. Producer seeds and internal state are not prerequisites. -/
def certifyWith (context : Context) (limits : BasisLimits)
    (generators candidate : Array Certificate.Polynomial) : BasisResult context generators (some candidate) :=
  Checked.certifyWith context limits generators candidate

/-- Resume a sealed checked computation with its original input identity. -/
def resumeBasisWith {context : Context} {generators : Array Certificate.Polynomial}
    {candidate : Option (Array Certificate.Polynomial)} (limits : BasisLimits)
    (state : BasisState context generators candidate) : BasisResult context generators candidate :=
  Checked.resumeWith limits state

end Hex.Groebner
