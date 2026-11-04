/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.F4
public import HexGroebner.SamplingRound

public section

namespace Hex.Groebner.Sampled

/-- Sampling work, separate from submitted matrix targets and complete-basis
certification. Counters include every consumed prefix of exhausted calls. -/
structure Statistics where
  calls : Nat := 0
  inputTargets : Nat := 0
  randomWords : Nat := 0
  combinations : Nat := 0
  combinationEntries : Nat := 0
  completedBlocks : Nat := 0
  deriving BEq, Repr, Inhabited

/-- Unchecked output retains its original random state and sampling policy.
The arena counts complete the parent allocation/representation accounting;
they provide no basis certificate or rank-preservation claim. -/
structure Candidate extends Hex.Groebner.Candidate where
  initialRandom : Hex.Rand
  config : Sampling.Config
  minimumTargets : Nat
  monomials : Nat
  monomialBytes : Nat

/-- Sealed F4 continuation with the advanced generator and any partial sampled
matrix. Field, order, generators, scheduling and sampling policy are immutable.
A pending pair batch retains its original selection and native mode. -/
structure State where
  private mk ::
  context : Context
  generators : Array RawPolynomial
  workspace : Workspace
  checkpoint : F4.Checkpoint
  random : Hex.Rand
  initialRandom : Hex.Rand
  config : Sampling.Config
  minimumTargets : Nat
  scheduling : Scheduling
  pending : Option Round := none
  statistics : Statistics := {}

/-- A sampled basis remains an unchecked candidate. Suspension is a scheduling
quantum ending, distinct from a consumed allowance; either continuation retains
its pending matrix and advanced random state. Invalid/internal results return
that advanced state too. -/
inductive Result where
  | candidate (value : Candidate) (statistics : Hex.Groebner.Statistics) (sampling : Statistics)
  | invalidConfig (random : Hex.Rand)
  | invalid (error : ComputeError) (statistics : Hex.Groebner.Statistics) (sampling : Statistics) (random : Hex.Rand)
  | internal (error : MatrixError) (statistics : Hex.Groebner.Statistics) (sampling : Statistics) (random : Hex.Rand)
  | exhausted (resource : F4Resource) (state : State)
  | representation (error : MonomialError) (state : State)
  | suspended (state : State)

private def failure (state : State) : ComputeError → Result
  | .exhausted resource => .exhausted resource state
  | .representation error => .representation error state
  | .matrix error => .internal error state.workspace.statistics state.statistics state.random
  | error => .invalid error state.workspace.statistics state.statistics state.random

private def matrixError : MatrixError → ComputeError
  | .exhausted .columns => .exhausted .monomials
  | .exhausted .rows => .exhausted .matrixRows
  | .exhausted .inputEntries | .exhausted .outputEntries => .exhausted .matrixEntries
  | .exhausted .packedBytes => .exhausted .packedBytes
  | .exhausted .work => .exhausted .work
  | error => .matrix error

private def check (state : State) (limits : Limits) : Option F4Resource :=
  let stats := state.workspace.statistics
  if stats.work > limits.work then some .work
  else if stats.allocatedBytes+state.workspace.table.bytes > limits.packedBytes then some .packedBytes
  else if stats.pairs > limits.pairs then some .pairs
  else if stats.rounds > limits.rounds then some .rounds
  else if stats.matrixEntries > limits.matrixEntries then some .matrixEntries
  else if stats.matrixRows > limits.matrixRows then some .matrixRows
  else if state.checkpoint.basis.size > limits.basis then some .basis
  else if state.context.variables > limits.variables then some .variables
  else if state.workspace.table.count > limits.monomials then some .monomials
  else none

private def decode (state : State) (limits : Limits) : Computation Candidate := do
  let polynomials ← F4.decodeBasis state.context limits state.checkpoint.basis
  return ⟨⟨state.context,polynomials,state.random.state,limits.batchSize,limits.nativeRows,
    limits.nativeMonomials,limits.gebauerMoller,limits.batchInterreduce,state.scheduling⟩,
    state.initialRandom,state.config,state.minimumTargets,(← get).table.count,(← get).table.bytes⟩

private def account (state : State) (before : Sampling.Statistics) (frame : Frame)
    (matrix : Sampling.State) : State :=
  let after := matrix.statistics
  let (frame,workspace) := frame.account after state.workspace
  { state with
    workspace,pending := some ⟨frame,matrix⟩,random := matrix.random,
    statistics := { state.statistics with
      randomWords := state.statistics.randomWords+(after.randomWords-before.randomWords)
      combinations := state.statistics.combinations+(after.combinations-before.combinations)
      combinationEntries := state.statistics.combinationEntries+(after.combinationEntries-before.combinationEntries)
      completedBlocks := state.statistics.completedBlocks+(after.completedBlocks-before.completedBlocks) } }

/-- Resume under absolute cumulative allowances. At most one million outer
scheduling slices are performed per call; a smaller explicit quantum supports
cooperative callers. Each sampled slice advances `matrixSteps`, clamped to
1–64 bounded phases. Preparation, basis updates and deterministic F4 steps
remain atomic stages; retries charge their repeated work.
Input normalization and final interreduction use deterministic F4. No completed
sampled candidate is promoted to a checked basis by this operation. -/
def resumeWith (limits : Limits) (initial : State) (slices := 1000000)
    (matrixSteps := 64) : Result := Id.run do
  let limits := { limits with scheduling := initial.scheduling }
  let mut state := initial
  if let some resource := check state limits then return .exhausted resource state
  for _ in [:min slices 1000000] do
    if let some round := state.pending then
      if round.matrix.phase == .done && round.matrix.failure.isNone then
        let workspace := state.workspace
        state := { state with workspace := { table := { arity := state.context.variables } } }
        let (result,workspace) := (finish state.context limits state.checkpoint round).run workspace
        state := { state with workspace }
        match result with
        | .error error => return failure state error
        | .ok checkpoint => state := { state with checkpoint,pending := none }
      else
        let frame := round.frame
        let matrix := round.matrix
        let previous := matrix.statistics
        let childLimits := frame.limits limits state.workspace
        -- Retain scalar accounting, not a second owner of the matrix arrays.
        state := { state with pending := none }
        let matrix := Sampling.advance childLimits (min 64 (max 1 matrixSteps)) matrix
        let failed := matrix.failure
        state := account state previous frame matrix
        if let some error := failed then return failure state (matrixError error)
    else if state.checkpoint.phase == .complete then
      let workspace := state.workspace
      state := { state with workspace := { table := { arity := state.context.variables } } }
      let (result,workspace) := (decode state limits).run workspace
      state := { state with workspace }
      match result with
      | .ok candidate => return .candidate candidate workspace.statistics state.statistics
      | .error error => return failure state error
    else if state.checkpoint.phase == .pairs then
      let workspace := state.workspace
      state := { state with workspace := { table := { arity := state.context.variables } } }
      let (result,workspace) :=
        (prepare state.context limits state.checkpoint state.random state.config state.minimumTargets).run workspace
      state := { state with workspace }
      match result with
      | .error error => return failure state error
      | .ok (checkpoint,pending) =>
        state := { state with
          checkpoint,pending,
          statistics.calls := state.statistics.calls+(if pending.isSome then 1 else 0),
          statistics.inputTargets := state.statistics.inputTargets+(pending.map (·.matrix.targets.size)).getD 0 }
    else
      let workspace := state.workspace
      state := { state with workspace := { table := { arity := state.context.variables } } }
      let (result,workspace) := (F4.step state.context limits state.generators state.checkpoint).run workspace
      state := { state with workspace }
      match result with
      | .error error => return failure state error
      | .ok checkpoint => state := { state with checkpoint }
  return .suspended state

/-- Explicitly seeded, unchecked F4 with sampled pair-round elimination. Full
field coefficients come from SplitMix64 rejection draws; no uniformity or
independence bound is claimed. An independent complete-basis certificate is
required before using this candidate for complete normal forms or nonmembership.
Invalid configuration is rejected before any computation or random draw.
Pair matrices with fewer than `minimumTargets` targets use deterministic
elimination. This explicit policy is retained across resumptions; zero samples
every selected matrix, preserving the default policy.
The optional slice quantum has the same cooperative suspension contract as
`resumeWith`; callers seeking completion continue its `.suspended` states. -/
def computeWith (context : Context) (limits : Limits) (generators : Array RawPolynomial)
    (random : Hex.Rand) (config : Sampling.Config := {}) (slices := 1000000) (minimumTargets := 0) : Result :=
  if config.blockRows == 0 || config.blockRows > 4096 || config.zeroTests == 0 then .invalidConfig random
  else resumeWith limits
    ⟨context,generators,{ table := { arity := context.variables }, statistics := {} },{},random,random,config,minimumTargets,limits.scheduling,none,{}⟩ slices

end Hex.Groebner.Sampled
