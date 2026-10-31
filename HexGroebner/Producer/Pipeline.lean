/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Producer.Certificate

public section

namespace Hex.Groebner.Producer

/-- F4 shape limits and certificate allowances share the smaller work,
allocation and variable cap across all phases. Other counters retain their
separate F4 and certificate units. -/
structure Budget where
  computation : Limits := {}
  certificate : Certificate.Budget := {}

private def effective (budget : Budget) : Limits × Certificate.Budget :=
  let work := min budget.computation.work budget.certificate.work
  let bytes := min budget.computation.packedBytes budget.certificate.allocatedBytes
  let variables := min budget.computation.variables budget.certificate.variables
  ({ budget.computation with work,packedBytes := bytes,variables },
    { budget.certificate with work,allocatedBytes := bytes,variables })

inductive Stage where
  | validation (context : Context) (generators : Array RawPolynomial)
      (expected : Array Certificate.Polynomial) (usage : Certificate.Usage)
  | computation (state : State) (usage : Certificate.Usage)
  | certification (state : CertState) (history : History)

structure BasisState where
  private mk ::
  stage : Stage
  expected : Option (Array Certificate.Polynomial)

inductive BasisResult where
  | success (basis : CheckedBasis) (usage : Certificate.Usage) (history : History)
  | invalid (error : ComputeError) (statistics : Statistics)
  | rejected (usage : Certificate.Usage)
  | computeExhausted (resource : F4Resource) (state : BasisState)
  | certificateExhausted (resource : Certificate.Resource) (state : BasisState)
  | representation (error : MonomialError) (state : BasisState)
  | address (state : BasisState)
  | internal (usage : Certificate.Usage)

private def certified (expected : Option (Array Certificate.Polynomial)) (history : History) : CertResult → BasisResult
  | .success basis usage => .success basis usage history
  | .invalid _ usage => .internal usage
  | .rejected usage => .internal usage
  | .exhausted resource state => .certificateExhausted resource ⟨.certification state history,expected⟩
  | .address state => .address ⟨.certification state history,expected⟩
  | .internal usage => .internal usage

private def produced (budget : Budget) (expected : Option (Array Certificate.Polynomial))
    (parent : Certificate.Usage) : Outcome → BasisResult
  | .candidate value statistics =>
    let usage := { parent with maxExponentBits := max parent.maxExponentBits value.maxExponentBits, allocatedTerms := parent.allocatedTerms+value.allocatedTerms, work := statistics.work, allocatedBytes := statistics.allocatedBytes+value.monomialBytes }
    if expected.any (· != value.polynomials) then .rejected usage else
      certified expected value.history (certifyFrom (effective budget).2 value usage)
  | .exhausted resource state => .computeExhausted resource ⟨.computation state parent,expected⟩
  | .certificateExhausted resource state => .certificateExhausted resource ⟨.computation state parent,expected⟩
  | .traceExhausted state => .certificateExhausted .nodes ⟨.computation state parent,expected⟩
  | .representation error state => .representation error ⟨.computation state parent,expected⟩
  | .invalid error statistics => .invalid error statistics
  | .internal _ statistics => .internal { parent with work := statistics.work, allocatedBytes := statistics.allocatedBytes }

private def validate (context : Context) (budget : Certificate.Budget)
    (candidate : Array Certificate.Polynomial) : Certificate.Work Unit := do
  if context.variables > budget.variables then throw (.exhausted .variables)
  -- Reserve the later exact candidate comparison here, before entering F4.
  -- The validated candidate bounds every compared prefix, even on rejection.
  Certificate.spend budget 1
  for polynomial in candidate do
    try Certificate.Arithmetic.validate context budget 0 polynomial
    catch error => match error with
      | .invalid _ => throw .rejected
      | e => throw e
    let count ← Certificate.Arithmetic.size budget polynomial
    Certificate.spend budget (1+count*(context.variables+1)*(budget.exponentBits/64+3))

/-- Resume the retained original identity and cumulative counters. Candidate
validation and certificate generation are atomic; retries charge repeated work. -/
def resumeBasisWith (budget : Budget) (state : BasisState) : BasisResult :=
  match state.stage with
  | .validation context generators expected previous =>
    match Certificate.checkUsage (effective budget).2 previous with
    | .error (.exhausted resource) => .certificateExhausted resource state
    | .error _ => .internal previous
    | .ok _ =>
      let (result,usage) := (validate context (effective budget).2 expected).run previous
      let state : BasisState := ⟨.validation context generators expected usage,some expected⟩
      match result with
      | .ok _ =>
        let initial := begin context generators { work := usage.work,allocatedBytes := usage.allocatedBytes }
        produced budget (some expected) usage
          (resumeWith (effective budget).1 ((effective budget).2.nodes-usage.nodes) initial
            ((effective budget).2.allocatedTerms-usage.allocatedTerms) (effective budget).2.exponentBits)
      | .error .rejected => .rejected usage
      | .error (.exhausted resource) => .certificateExhausted resource state
      | .error .address => .address state
      | .error _ => .internal usage
  | .computation computation parent =>
    match Certificate.checkUsage (effective budget).2 parent with
    | .error (.exhausted resource) => .certificateExhausted resource state
    | .error _ => .internal parent
    | .ok _ => produced budget state.expected parent
        (resumeWith (effective budget).1 ((effective budget).2.nodes-parent.nodes) computation
          ((effective budget).2.allocatedTerms-parent.allocatedTerms) (effective budget).2.exponentBits)
  | .certification certification history =>
    match checkHistory (effective budget).1 history with
    | .error (.exhausted resource) => .computeExhausted resource state
    | .error _ => .internal certification.usage
    | .ok _ => certified state.expected history (resumeCertifyWith (effective budget).2 certification)

/-- Compute a packed F4 candidate, construct its complete witness, and replay it
independently before exposing an accepted-basis receipt. -/
def basisWith (context : Context) (budget : Budget) (generators : Array RawPolynomial) : BasisResult :=
  resumeBasisWith budget ⟨.computation (begin context generators) {},none⟩

/-- Certify canonical external candidate data with no producer-seed or strategy
precondition. A separate traced rerun constructs its forward derivation; complete
independent replay proves the final postcondition. -/
def certifyWith (context : Context) (budget : Budget) (generators : Array RawPolynomial)
    (candidate : Array Certificate.Polynomial) : BasisResult :=
  resumeBasisWith budget ⟨.validation context generators candidate {},some candidate⟩

end Hex.Groebner.Producer

namespace Hex.Groebner.Producer

/-- Continue a nested checked computation without resetting parent counters. -/
def basisFrom (context : Context) (budget : Budget) (generators : Array RawPolynomial)
    (usage : Certificate.Usage) : BasisResult :=
  resumeBasisWith budget ⟨.computation
    (begin context generators { work := usage.work,allocatedBytes := usage.allocatedBytes }) usage,none⟩

def certifyCandidateFrom (context : Context) (budget : Budget) (generators : Array RawPolynomial)
    (candidate : Array Certificate.Polynomial) (usage : Certificate.Usage) : BasisResult :=
  resumeBasisWith budget ⟨.validation context generators candidate usage,some candidate⟩

end Hex.Groebner.Producer
