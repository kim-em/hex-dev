/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Symbolic
public import HexGroebner.Pairs

public section

/-! Deterministic finite-prime-field F4 candidate production. Sugar batches use
symbolic preprocessing and joint Macaulay elimination. Candidates are explicitly
unchecked; no constructor promotes one to a certified result. -/

/-! `HexGroebner/Producer/F4.lean` mirrors this driver with shared polynomial
derivations. Scheduling and interreduction changes must preserve the default
output comparisons on every emitter fixture and both final-reduction strategies
on the named `TraceConformance` cases. -/

namespace Hex.Groebner
open Computation

namespace F4

/-- Atomic checkpoints delimit input normalization, F4 rounds and interreduction. -/
inductive Phase where
  | input | pairs | interreduce | complete
  deriving BEq, Inhabited

/-- Basis, unresolved pairs and reducer cache commit only after a whole stage succeeds.
On exhaustion the old checkpoint remains valid, including all pair obligations. -/
structure Checkpoint where
  basis : Array BasisElement := #[]
  queue : PairQueue := {}
  phase : Phase := .input
  cache : ReducerCache := .empty

private def degree (limits : Limits) (p : Polynomial) : Computation Nat := do
  spend limits p.size
  let table := (← get).table
  let mut degree := 0
  for i in [:p.size] do degree := max degree (table.degree (p.monomial i))
  return degree

private def unit (limits : Limits) (basis : Array BasisElement) : Computation (Option BasisElement) := do
  spend limits basis.size
  let table := (← get).table
  return basis.find? fun g => g.polynomial.size != 0 && table.degree (g.polynomial.monomial 0) == 0

private def install (context : Context) (limits : Limits) (basis : Array BasisElement)
    (queue : PairQueue) (start : Nat) : Computation PairQueue := do
  if basis.size > limits.basis then throw (.exhausted .basis)
  let mut queue := queue
  for i in [start:basis.size] do queue ← queue.install context limits basis i
  return queue

private def inputBasis (context : Context) (limits : Limits) (raw : Array RawPolynomial) :
    Computation Checkpoint := do
  spend limits raw.size
  let mut inputs := #[]
  for i in [:raw.size] do
    let p ← Polynomial.normalize context limits i raw[i]!
    let sugar ← degree limits p
    if p.size != 0 then inputs := inputs.push ⟨p, sugar⟩
  let matrix ← SymbolicMatrix.prepare context limits #[] inputs
  let basis ← matrix.eliminate context limits
  if let some g ← unit limits basis then
    if limits.basis == 0 then throw (.exhausted .basis)
    return { basis := #[g], phase := .complete }
  let queue ← install context limits basis {} 0
  return { basis, queue, phase := .pairs }

private def round (context : Context) (limits : Limits) (checkpoint : Checkpoint) :
    Computation Checkpoint := do
  if checkpoint.queue.heap.isEmpty then return { checkpoint with phase := .interreduce }
  let s ← get
  if s.statistics.rounds ≥ limits.rounds then throw (.exhausted .rounds)
  set { s with statistics.rounds := s.statistics.rounds + 1 }
  let index ← ReducerIndex.build context limits checkpoint.basis
  let (pairs, queue) ← checkpoint.queue.select context limits index checkpoint.basis
  modify fun s => { s with statistics.largestBatch := max s.statistics.largestBatch pairs.size }
  if pairs.isEmpty then return { checkpoint with queue }
  let mut targets := #[]
  for pair in pairs do
    let f := checkpoint.basis[pair.left]!.polynomial
    let g := checkpoint.basis[pair.right]!.polynomial
    let p ← f.sPolynomial context limits g
    if p.size != 0 then targets := targets.push ⟨p, pair.sugar⟩
  let matrix ← SymbolicMatrix.prepareWith context limits index checkpoint.basis targets checkpoint.cache
  let new ← matrix.eliminate context limits
  let basis := checkpoint.basis ++ new
  if let some g ← unit limits new then
    if limits.basis == 0 then throw (.exhausted .basis)
    return { basis := #[g], phase := .complete }
  let mut queue := queue
  for pair in pairs do queue ← queue.resolve limits pair.left pair.right
  queue ← install context limits basis queue checkpoint.basis.size
  return { basis, queue, phase := .pairs, cache := matrix.cache }

private def interreduce (context : Context) (limits : Limits) (basis : Array BasisElement) (cache : ReducerCache) :
    Computation (Array BasisElement) := do
  let table := (← get).table
  let mut minimal := #[]
  for i in [:basis.size] do
    let leading := basis[i]!.polynomial.monomial 0
    let mut redundant := false
    for j in [:basis.size] do
      spend limits (context.variables + 1)
      let other := basis[j]!.polynomial.monomial 0
      if j != i && table.divides other leading && (other != leading || j < i) then
        redundant := true
        break
    if !redundant then minimal := minimal.push basis[i]!
  let index ← ReducerIndex.build context limits minimal
  let mut inputs : Array BasisElement := #[]
  for g in minimal do
    let p := g.polynomial
    let mut tail : Polynomial := {}
    if p.size > 1 then
      allocate limits ((p.size - 1) * (4 + context.field.width.bytes))
      spend limits p.size
      tail := {
        support := p.support.extract 4 p.support.size
        coefficients := p.coefficients.extract context.field.width.bytes p.coefficients.size }
    inputs := inputs.push ⟨tail, g.sugar⟩
  let tails ← if limits.batchInterreduce then do
    spend limits inputs.size
    let nonzero := inputs.filter (fun p => p.polynomial.size != 0)
    if nonzero.isEmpty then pure inputs else
      let matrix ← SymbolicMatrix.prepareWith context limits index minimal nonzero cache
      let remainders ← matrix.reduce context limits
      let mut cursor := 0
      let mut output := #[]
      for p in inputs do
        spend limits 1
        if p.polynomial.size == 0 then output := output.push p else
          output := output.push remainders[cursor]!
          cursor := cursor + 1
      pure output
  else inputs.mapM fun tail => do
    return ⟨← Polynomial.remainderWith context limits index minimal tail.polynomial, tail.sugar⟩
  let mut reduced := #[]
  for i in [:minimal.size] do
    let g := minimal[i]!
    let p := g.polynomial
    let tail := tails[i]!.polynomial
    allocate limits ((tail.size + 1) * (4 + context.field.width.bytes))
    spend limits tail.size
    let mut support := Packed.push .u32 {} (p.monomial 0).toUInt64
    let mut coefficients := Packed.push context.field.width {} (p.coefficient context.field 0)
    for i in [:tail.size] do
      support := Packed.push .u32 support (tail.monomial i).toUInt64
      coefficients := Packed.push context.field.width coefficients (tail.coefficient context.field i)
    let p ← Polynomial.monic context limits { support, coefficients }
    reduced := reduced.push ⟨p, g.sugar⟩
  let leading := reduced.map fun g => g.polynomial.monomial 0
  let order ← sort context limits leading
  spend limits reduced.size
  let positions := (reduced.zipIdx).foldl
    (fun (m : Std.HashMap Nat Nat) (g, i) => m.insert (g.polynomial.monomial 0) i) {}
  return order.map fun id => reduced[positions[id]!]!

/-- Advance one atomic checkpoint. Temporary monomial interning may survive a
failed attempt, but no basis change or popped pair is committed on failure. -/
def step (context : Context) (limits : Limits) (raw : Array RawPolynomial)
    (checkpoint : Checkpoint) : Computation Checkpoint := do
  spend limits 1
  match checkpoint.phase with
  | .input => inputBasis context limits raw
  | .pairs => round context limits checkpoint
  | .interreduce =>
    let basis ← interreduce context limits checkpoint.basis checkpoint.cache
    return { checkpoint with basis, phase := .complete }
  | .complete => return checkpoint

end F4

/-- Unchecked reduced-basis candidate. Independent certification is required
before any normal-form or negative-membership result may claim completeness. -/
structure Candidate where
  context : Context
  polynomials : Array RawPolynomial
  randomState : UInt64
  /-- Cap supplied at completion; earlier resumed stages may use different caps.
  `Statistics.largestBatch` records the largest batch actually selected. -/
  batchSize : Nat
  /-- Implementation controls at completion; resumed stages may have differed. -/
  nativeRows : Bool
  nativeMonomials : Bool
  gebauerMoller : Bool
  batchInterreduce : Bool

/-- A sealed resumable computation fixes its field, order, generators and random
state. Ordinary callers cannot substitute incompatible metadata or fabricate a
checkpoint that substitutes its generators or its pair state. Pair omissions
follow the producer's criteria and remain distinct from completed reductions. -/
structure ResumeState where
  private mk ::
  context : Context
  generators : Array RawPolynomial
  workspace : Workspace
  checkpoint : F4.Checkpoint
  randomState : UInt64

/-- Candidate production distinguishes invalid input, internal matrix failures,
representation exhaustion and consumed allowances. Only representation and
allowance exhaustion expose a resumable checkpoint. -/
inductive ComputeResult where
  | candidate (value : Candidate) (statistics : Statistics)
  | invalid (error : ComputeError) (statistics : Statistics)
  | internal (error : MatrixError) (statistics : Statistics)
  | exhausted (resource : F4Resource) (state : ResumeState)
  | representation (error : MonomialError) (state : ResumeState)

private def fail (state : ResumeState) (error : ComputeError) : ComputeResult :=
  match error with
  | .exhausted resource => .exhausted resource state
  | .representation error => .representation error state
  | .matrix error => .internal error state.workspace.statistics
  | error => .invalid error state.workspace.statistics

private def decode (state : ResumeState) (limits : Limits) : Computation Candidate := do
  let field := state.context.field
  let mut polynomials := #[]
  for g in state.checkpoint.basis do
    spend limits (g.polynomial.size * (state.context.variables + 1))
    allocate limits (8 * g.polynomial.size * (state.context.variables + 1))
    polynomials := polynomials.push (g.polynomial.toRaw field (← get).table)
  return ⟨state.context, polynomials, state.randomState, limits.batchSize,
    limits.nativeRows, limits.nativeMonomials, limits.gebauerMoller, limits.batchInterreduce⟩

/-- Resume under new absolute cumulative allowances. Used work is never reset;
restarting an exhausted stage charges its work again. Identity is sealed inside
the state, so resumption cannot change its field, order or generators. -/
def resumeWith (limits : Limits) (initial : ResumeState) : ComputeResult := Id.run do
  let mut state := initial
  let statistics := state.workspace.statistics
  if statistics.work > limits.work then return fail state (.exhausted .work)
  if statistics.allocatedBytes + state.workspace.table.bytes > limits.packedBytes then
    return fail state (.exhausted .packedBytes)
  if statistics.pairs > limits.pairs then return fail state (.exhausted .pairs)
  if statistics.rounds > limits.rounds then return fail state (.exhausted .rounds)
  if statistics.matrixEntries > limits.matrixEntries then return fail state (.exhausted .matrixEntries)
  if statistics.matrixRows > limits.matrixRows then return fail state (.exhausted .matrixRows)
  if state.checkpoint.basis.size > limits.basis then return fail state (.exhausted .basis)
  if state.context.variables > limits.variables then return fail state (.exhausted .variables)
  if state.workspace.table.count > limits.monomials then return fail state (.exhausted .monomials)
  for _ in [:limits.rounds + 4] do
    if state.checkpoint.phase == .complete then
      let (result, workspace) := (decode state limits).run state.workspace
      match result with
      | .ok candidate => return .candidate candidate workspace.statistics
      | .error error => return fail { state with workspace } error
    let (result, workspace) := (F4.step state.context limits state.generators state.checkpoint).run state.workspace
    match result with
    | .ok checkpoint => state := { state with workspace, checkpoint }
    | .error error => return fail { state with workspace } error
  return fail state (.exhausted .rounds)

/-- Deterministic finite-prime-field F4 with sugar batching, exact symbolic
closure, joint Macaulay elimination, product/chain criteria and final canonical
interreduction. Success is explicitly an unchecked candidate. Deterministic
execution consumes no random samples and returns the supplied state unchanged. -/
def computeWith (context : Context) (limits : Limits) (generators : Array RawPolynomial)
    (randomState : UInt64 := 0) : ComputeResult :=
  resumeWith limits ⟨context, generators, ⟨{ arity := context.variables }, {}⟩, {}, randomState⟩

end Hex.Groebner
