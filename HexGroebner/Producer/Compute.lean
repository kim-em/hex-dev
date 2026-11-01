/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Producer.F4
public import HexGroebner.Producer.Prune

public section

namespace Hex.Groebner.Producer

structure History where
  statistics : Statistics
  monomials : Nat
  monomialBytes : Nat
  basisSize : Nat
  scheduling : Scheduling := .degree

def checkHistory (limits : Limits) (history : History) : Except ComputeError Unit := do
  let s := history.statistics
  if s.work > limits.work then throw (.exhausted .work)
  if s.allocatedBytes+history.monomialBytes > limits.packedBytes then throw (.exhausted .packedBytes)
  if s.pairs > limits.pairs then throw (.exhausted .pairs)
  if s.rounds > limits.rounds then throw (.exhausted .rounds)
  if s.matrixEntries > limits.matrixEntries then throw (.exhausted .matrixEntries)
  if s.matrixRows > limits.matrixRows then throw (.exhausted .matrixRows)
  if history.monomials > limits.monomials then throw (.exhausted .monomials)
  if history.basisSize > limits.basis then throw (.exhausted .basis)

structure Candidate where
  context : Context
  generators : Array Certificate.Polynomial
  polynomials : Array Certificate.Polynomial
  forward : Certificate.Containment
  monomialBytes : Nat
  allocatedTerms : Nat
  maxExponentBits : Nat
  history : History

structure State where
  private mk ::
  context : Context
  generators : Array RawPolynomial
  workspace : Workspace
  derivation : Derivation
  checkpoint : Checkpoint
  scheduling : Scheduling

inductive Outcome where
  | candidate (value : Candidate) (statistics : Statistics)
  | exhausted (resource : F4Resource) (state : State)
  | traceExhausted (state : State)
  | certificateExhausted (resource : Certificate.Resource) (state : State)
  | representation (error : MonomialError) (state : State)
  | invalid (error : ComputeError) (statistics : Statistics)
  | internal (error : MatrixError) (statistics : Statistics)

private def fail (state : State) : ComputeError → Outcome
  | .exhausted r => .exhausted r state
  | .representation e => .representation e state
  | .matrix (.exhausted .traceNodes) => .traceExhausted state
  | .matrix e => .internal e state.workspace.statistics
  | e => .invalid e state.workspace.statistics

private def canonical (context : Context) (limits : Limits) (raw : RawPolynomial) :
    Work Certificate.Polynomial := do
  let count := raw.size
  let depth := count.log2+3
  lift (Computation.spend limits (count*depth*(context.variables+1)*4))
  reserveTerms (count*(depth+2))
  lift (Computation.allocate limits (count*(depth+2)*(128+context.variables*32)))
  for term in raw do
    for exponent in term.exponents do reserveExponent limits exponent
  let rows := raw.toList.filterMap fun term => if term.coefficient == 0 then none else
    some [(term.exponents.toList,term.coefficient.toNat)]
  letI : Add Nat := ⟨Hex.MvPoly.Kernel.residueAdd context.field.modulus.toNat⟩
  return Hex.MvPoly.Kernel.mergeRows count rows

private def decode (state : State) (limits : Limits) : Work Candidate := do
  let mut polynomials := #[]
  let mut roots := #[]
  for g in state.checkpoint.basis do
    lift (Computation.spend limits (g.value.polynomial.size*(state.context.variables+1)))
    lift (Computation.allocate limits (8*g.value.polynomial.size*(state.context.variables+1)))
    let raw := g.value.polynomial.toRaw state.context.field (← lift get).table
    polynomials := polynomials.push (← canonical state.context limits raw)
    roots := roots.push g.root
  let generators ← state.generators.mapM (canonical state.context limits)
  let forward ← prune limits state.derivation.nodes roots
  return ⟨state.context,generators,polynomials,forward,
    (← lift get).table.bytes,(← get).derivation.allocatedTerms,(← get).derivation.maxExponentBits,
    ⟨(← lift get).statistics,(← lift get).table.count,(← lift get).table.bytes,
      polynomials.size,state.scheduling⟩⟩

private def traceFailure (state : State) : Producer.Error → Outcome
  | .compute error => fail state error
  | .exhausted resource => fail state (.exhausted resource)
  | .representation error => fail state (.representation error)
  | .matrix error => fail state (.matrix error)
  | .certificate resource => .certificateExhausted resource state

/-- Traced F4 checkpoints retain all work/allocation, including failed attempts.
Only successful stages commit new basis roots and derivation nodes. -/
def resumeWith (limits : Limits) (nodeLimit : Nat) (initial : State)
    (termLimit : Nat := 1000000) (exponentBits : Nat := 64) : Outcome := Id.run do
  let limits := { limits with scheduling := initial.scheduling }
  let mut state := { initial with derivation.termLimit := termLimit,derivation.exponentBits := exponentBits }
  if state.derivation.maxExponentBits > exponentBits then return .certificateExhausted .exponentBits state
  if state.derivation.allocatedTerms > termLimit then return .certificateExhausted .allocatedTerms state
  let usage := state.workspace.statistics
  if usage.work > limits.work then return fail state (.exhausted .work)
  if usage.allocatedBytes+state.workspace.table.bytes > limits.packedBytes then
    return fail state (.exhausted .packedBytes)
  if usage.pairs > limits.pairs then return fail state (.exhausted .pairs)
  if usage.rounds > limits.rounds then return fail state (.exhausted .rounds)
  if usage.matrixEntries > limits.matrixEntries then return fail state (.exhausted .matrixEntries)
  if usage.matrixRows > limits.matrixRows then return fail state (.exhausted .matrixRows)
  if state.context.variables > limits.variables then return fail state (.exhausted .variables)
  if state.workspace.table.count > limits.monomials then return fail state (.exhausted .monomials)
  if state.checkpoint.basis.size > limits.basis then return fail state (.exhausted .basis)
  if state.derivation.nodes.size > nodeLimit then return .traceExhausted state
  for _ in [:limits.rounds+4] do
    if state.checkpoint.phase == .complete then
      let (result,execution) := (decode state limits).run ⟨state.workspace,state.derivation⟩
      match result with
      | .ok candidate => return .candidate candidate execution.workspace.statistics
      | .error error => return traceFailure { state with workspace := execution.workspace, derivation.allocatedTerms := execution.derivation.allocatedTerms, derivation.maxExponentBits := execution.derivation.maxExponentBits } error
    let (result,execution) := (step state.context limits nodeLimit state.generators state.checkpoint).run
      ⟨state.workspace,state.derivation⟩
    match result with
    | .ok checkpoint => state := { state with workspace := execution.workspace, checkpoint,derivation := execution.derivation }
    | .error error => return traceFailure { state with workspace := execution.workspace, derivation.allocatedTerms := execution.derivation.allocatedTerms, derivation.maxExponentBits := execution.derivation.maxExponentBits } error
  return fail state (.exhausted .rounds)

/-- Start with explicit parent statistics; callers preserve cumulative counters. -/
def begin (context : Context) (generators : Array RawPolynomial) (statistics : Statistics := {})
    (scheduling : Scheduling := .degree) : State :=
  ⟨context,generators,⟨{ arity := context.variables },statistics⟩,{},{},scheduling⟩

def computeWith (context : Context) (limits : Limits) (nodeLimit : Nat)
    (generators : Array RawPolynomial) : Outcome :=
  resumeWith limits nodeLimit (begin context generators (scheduling := limits.scheduling))

end Hex.Groebner.Producer
