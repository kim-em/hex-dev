/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.Symbolic
import all HexGroebner.F4
public import HexGroebner.F4
public import HexGroebner.SamplingStep

public section

namespace Hex.Groebner.Sampled
open Computation

/-- A selected pair batch and its immutable symbolic column map survive all
sampling, output-decoding and basis-update exhaustion. No pair is resolved
until the whole stage commits. -/
structure Frame where
  columns : Array Nat
  queue : PairQueue
  pairs : Array CriticalPair
  cache : ReducerCache
  base : Statistics
  inputBytes : Nat
  inputEntries : Nat
  inputRows : Nat
  accounted : MatrixStats := {}
  accountedCombinations : Nat := 0

/-- Immutable round metadata is separate from the owned matrix continuation. -/
structure Round where
  frame : Frame
  matrix : Sampling.State

private def translate (context : Context) (limits : Limits) (matrix : SymbolicMatrix)
    (queue : PairQueue) (pairs : Array CriticalPair) (random : Hex.Rand)
    (config : Sampling.Config) : Computation Round := do
  let input ← SymbolicMatrix.translate context limits matrix
  let reducers := input.reducers
  let targets := input.targets
  let sugars := input.sugars
  let inputBytes := input.inputBytes
  let entries := input.entries
  let rows := reducers.size+targets.size
  let state ← get
  modify fun s => { s with statistics := { s.statistics with
    matrixRows := s.statistics.matrixRows+rows
    matrixTargets := s.statistics.matrixTargets+targets.size
    matrixCalls := s.statistics.matrixCalls+1
    peakMatrixRows := max s.statistics.peakMatrixRows rows } }
  return {
    frame := {
      columns := matrix.columns,queue,pairs,cache := matrix.cache,base := state.statistics,
      inputBytes,inputEntries := entries,inputRows := rows }
    matrix := Sampling.start context.field matrix.columns.size reducers targets random config sugars limits.nativeRows }

/-- Prepare exactly one pair batch. Empty selections commit only their lawful
pair-criterion work, without consuming random words. -/
def prepare (context : Context) (limits : Limits) (checkpoint : F4.Checkpoint)
    (random : Hex.Rand) (config : Sampling.Config) :
    Computation (F4.Checkpoint × Option Round) := do
  spend limits 1
  match ← F4.select context limits checkpoint with
  | .inl checkpoint => return (checkpoint,none)
  | .inr batch =>
    return (checkpoint,some (← translate context limits batch.matrix batch.queue batch.pairs random config))

/-- Remaining parent allowances expressed as cumulative limits within this call.
Input and output entries share the parent matrix-entry allowance. Input packed
payload was already charged by polynomial/column translation. -/
def Frame.limits (round : Frame) (limits : Limits) (workspace : Workspace) : MatrixLimits := {
  columns := limits.monomials
  rows := limits.matrixRows-round.base.matrixRows
  inputEntries := min round.inputEntries (limits.matrixEntries-round.base.matrixEntries)
  outputEntries := limits.matrixEntries-round.base.matrixEntries-round.inputEntries
  packedBytes := limits.packedBytes-round.base.allocatedBytes-workspace.table.bytes+round.inputBytes
  work := limits.work-round.base.work }

/-- Merge only newly consumed matrix work. Submitted rows/calls were counted at
initialization; resumption neither resubmits the matrix nor resets its counters. -/
def Frame.account (round : Frame) (sampling : Sampling.Statistics) (workspace : Workspace) : Frame × Workspace :=
  let current := sampling.matrix
  let old := round.accounted
  let stats := workspace.statistics
  let statistics := { stats with
    work := stats.work+(current.work-old.work)
    allocatedBytes := stats.allocatedBytes+
      ((current.packedBytes-round.inputBytes)-(old.packedBytes-round.inputBytes))
    matrixRows := stats.matrixRows+(sampling.combinations-round.accountedCombinations)
    matrixTargets := stats.matrixTargets+(sampling.combinations-round.accountedCombinations)
    peakMatrixRows := max stats.peakMatrixRows
      (round.inputRows+sampling.combinations)
    matrixEntries := stats.matrixEntries+
      ((current.inputEntries+current.outputEntries)-(old.inputEntries+old.outputEntries))
    matrixReductions := stats.matrixReductions+(current.reductions-old.reductions)
    matrixZeroRows := stats.matrixZeroRows+(current.zeroRows-old.zeroRows)
    peakMatrixEntries := max stats.peakMatrixEntries (current.inputEntries+current.outputEntries) }
  ({ round with accounted := current,accountedCombinations := sampling.combinations },{ workspace with statistics })

/-- Commit completed unchecked sample pivots to the F4 basis and pair queue.
This does not certify that their span equals that of all selected targets. -/
def finish (context : Context) (limits : Limits) (checkpoint : F4.Checkpoint)
    (round : Round) : Computation F4.Checkpoint := do
  let frame := round.frame
  let some rows := round.matrix.candidate? | throw (.matrix .rowUpdate)
  let mut new := #[]
  for pivot in rows do
    new := new.push (← SymbolicMatrix.decode context limits frame.columns pivot.row 1 pivot.sugar)
  F4.commit context limits checkpoint frame.queue frame.pairs frame.cache new

end Hex.Groebner.Sampled
