/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Producer.Compute

public section

namespace Hex.Groebner.Producer
open Certificate

private def childBudget (budget : Budget) (usage : Usage) : Budget := { budget with
  work := budget.work-usage.work
  allocatedBytes := budget.allocatedBytes-usage.allocatedBytes
  allocatedTerms := budget.allocatedTerms-usage.allocatedTerms
  steps := budget.steps-usage.steps
  nodes := budget.nodes-usage.nodes
  pairs := budget.pairs-usage.pairs }

private def chargeChild (usage : Usage) : Certificate.Work Unit := do
  modify fun s => { s with
    work := s.work+usage.work
    allocatedBytes := s.allocatedBytes+usage.allocatedBytes
    allocatedTerms := s.allocatedTerms+usage.allocatedTerms
    steps := s.steps+usage.steps
    nodes := s.nodes+usage.nodes
    pairs := s.pairs+usage.pairs
    maxExponentBits := max s.maxExponentBits usage.maxExponentBits }

private def divide (context : Context) (budget : Budget) (basis : Array Certificate.Polynomial)
    (target : Certificate.Polynomial) : Certificate.Work (Array Certificate.Polynomial) := do
  let remaining := childBudget budget (← get)
  let result := Certificate.Division.computeWith context remaining basis target
  let value ← match result with
    | .candidate value usage => chargeChild usage; pure value
    | .invalid i usage => chargeChild usage; throw (.invalid i)
    | .exhausted resource state => chargeChild state.usage; throw (.exhausted resource)
    | .address state => chargeChild state.usage; throw .address
    | .internal usage => chargeChild usage; throw .arithmetic
  spend budget 1
  if !value.remainder.isEmpty then throw .rejected
  return value.quotients

private def node (budget : Budget) (nodes : Array Certificate.Node) (value : Certificate.Node) :
    Certificate.Work (Array Certificate.Node) := do
  spend budget 1
  let used ← get
  if used.nodes ≥ budget.nodes then throw (.exhausted .nodes)
  modify fun s => { s with nodes := s.nodes+1 }
  reserveBytes budget 64
  checkAddress (64+(nodes.size+1)*16)
  return nodes.push value

/-- Separate certificate generation from a traced F4 candidate. Quotients and
S-pair witnesses remain untrusted until complete independent basis replay. -/
def assemble (context : Context) (budget : Budget) (candidate : Candidate) :
    Certificate.Work Certificate.Basis := do
  let mut nodes : Array Certificate.Node := #[]
  checkAddress (64+candidate.polynomials.size*16)
  reserveBytes budget (64+candidate.polynomials.size*8)
  let mut sources := Array.replicate candidate.polynomials.size 0
  if !candidate.generators.isEmpty then nodes ← node budget nodes .zero
  let zeroRoot := nodes.size-1
  checkAddress (64+candidate.generators.size*16)
  reserveBytes budget (64+candidate.generators.size*8)
  let mut roots := Array.emptyWithCapacity candidate.generators.size
  for target in candidate.generators do
    let cofactors ← divide context budget candidate.polynomials target
    let mut root := zeroRoot
    for i in [:cofactors.size] do
      spend budget 1
      if !cofactors[i]!.isEmpty then
        let source ← if sources[i]! != 0 then pure (sources[i]!-1) else do
          let source := nodes.size
          nodes ← node budget nodes (.generator i)
          sources := sources.set! i (source+1)
          pure source
        let product := nodes.size
        nodes ← node budget nodes (.multiply cofactors[i]! source)
        nodes ← node budget nodes (.add root product)
        root := nodes.size-1
    roots := roots.push root
  spend budget nodes.size
  reserveBytes budget (nodes.size*24)
  let backward : Containment := ⟨nodes.toList,roots⟩
  checkAddress (64+candidate.polynomials.size*16)
  reserveBytes budget (64+candidate.polynomials.size*16)
  let mut heads : Array (Option (List Nat × Nat)) := Array.emptyWithCapacity candidate.polynomials.size
  for polynomial in candidate.polynomials do
    heads := heads.push (← Arithmetic.leading context budget polynomial)
  let mut pairs : Array (Array (Array Certificate.Polynomial)) := #[]
  checkAddress (64+candidate.polynomials.size*16)
  reserveBytes budget (64+candidate.polynomials.size*8)
  for i in [:candidate.polynomials.size] do
    reserveBytes budget (64+candidate.polynomials.size*8)
    let mut row := Array.emptyWithCapacity candidate.polynomials.size
    for j in [:candidate.polynomials.size] do
      spend budget 1
      let usage ← get
      if usage.pairs ≥ budget.pairs then throw (.exhausted .pairs)
      modify fun s => { s with pairs := s.pairs+1 }
      let target ← match heads[i]!,heads[j]! with
        | some a,some b => do
          spend budget ((context.variables+1)*(budget.exponentBits/64+3))
          reserve budget context.variables 2
          let left ← Arithmetic.multiply context budget (difference b.1 a.1,b.2) candidate.polynomials[i]!
          let right ← Arithmetic.multiply context budget (difference a.1 b.1,a.2) candidate.polynomials[j]!
          Arithmetic.subtract context budget left right
        | _,_ => throw .rejected
      row := row.push (← divide context budget candidate.polynomials target)
    pairs := pairs.push row
  return ⟨candidate.forward,backward,pairs⟩

/-- Atomic certificate generation/replay continuation, retaining the separately
completed traced candidate and all consumed work/allocation. -/
structure CertState where
  private mk ::
  candidate : Candidate
  usage : Usage
  nodeBase : Nat
  pairBase : Nat

inductive CertResult where
  | success (basis : CheckedBasis) (usage : Usage)
  | invalid (index : Nat) (usage : Usage)
  | rejected (usage : Usage)
  | exhausted (resource : Certificate.Resource) (state : CertState)
  | address (state : CertState)
  | internal (usage : Usage)

private def failure (state : CertState) : Certificate.Error → CertResult
  | .invalid i => .invalid i state.usage
  | .rejected => .rejected state.usage
  | .exhausted resource => .exhausted resource state
  | .address => .address state
  | .arithmetic => .internal state.usage

/-- Repeated atomic generation charges repeated work, while structural caps
count the proposed certificate once. Final replay is independent of F4. -/
def resumeCertifyWith (budget : Budget) (initial : CertState) : CertResult := Id.run do
  match checkUsage budget initial.usage with
  | .error error => return failure initial error
  | .ok _ => pure ()
  let action : Certificate.Work Certificate.Basis := do
    if initial.candidate.context.variables > budget.variables then throw (.exhausted .variables)
    let mut count := 0
    for _ in initial.candidate.forward.nodes do
      spend budget 1
      count := count+1
      if initial.nodeBase+count > budget.nodes then throw (.exhausted .nodes)
    modify fun s => { s with nodes := initial.nodeBase+count }
    assemble initial.candidate.context budget initial.candidate
  let (result,usage) := action.run { initial.usage with nodes := initial.nodeBase,pairs := initial.pairBase }
  let state := { initial with usage }
  match result with
  | .error e => return failure state e
  | .ok certificate =>
    let replayUsage := { usage with nodes := initial.nodeBase,pairs := initial.pairBase }
    match Certificate.BasisVerification.verifyFrom state.candidate.context budget state.candidate.generators
        state.candidate.polynomials certificate replayUsage with
    | .checked basis usage => return .success basis usage
    | .invalid i usage => return .invalid i usage
    | .rejected usage => return .rejected usage
    | .exhausted resource replay => return .exhausted resource { state with usage := replay.usage }
    | .address replay => return .address { state with usage := replay.usage }
    | .internal usage => return .internal usage

def certifyFrom (budget : Budget) (candidate : Candidate) (usage : Usage) : CertResult :=
  resumeCertifyWith budget ⟨candidate,usage,usage.nodes,usage.pairs⟩

end Hex.Groebner.Producer
