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
structure Round where
  columns : Array Nat
  queue : PairQueue
  pairs : Array CriticalPair
  cache : ReducerCache
  matrix : Sampling.State
  base : Statistics
  inputBytes : Nat
  inputEntries : Nat
  accounted : MatrixStats := {}
  accountedCombinations : Nat := 0

private def translate (context : Context) (limits : Limits) (matrix : SymbolicMatrix)
    (queue : PairQueue) (pairs : Array CriticalPair) (random : Hex.Rand)
    (config : Sampling.Config) : Computation Round := do
  if matrix.columns.size > 4294967295 then throw (.representation .index)
  let positions ← ColumnMap.build limits matrix.columns
  let mut reducers := #[]
  let mut targets := #[]
  let mut inputBytes := 0
  let mut entries := 0
  let mut sugars := #[]
  for reducer in matrix.reducers do
    let row ← SymbolicMatrix.row context limits positions reducer.polynomial
    reducers := reducers.push row
    sugars := sugars.push reducer.sugar
    inputBytes := inputBytes+row.columns.size+row.coefficients.size
    entries := entries+row.size
  -- Preserve the deterministic target order so block membership has a stable
  -- meaning across native/scalar implementations and resumed computations.
  spend limits (2*matrix.targets.size*(matrix.targets.size+1).log2*positions.lookupCost)
  let ordered := (matrix.targets.toList.mergeSort fun a b =>
    let left := if a.polynomial.size == 0 then matrix.columns.size
      else positions.getD (a.polynomial.monomial 0) matrix.columns.size
    let right := if b.polynomial.size == 0 then matrix.columns.size
      else positions.getD (b.polynomial.monomial 0) matrix.columns.size
    left > right || (left == right && a.polynomial.size ≤ b.polynomial.size)).toArray
  for target in ordered do
    let row ← SymbolicMatrix.row context limits positions target.polynomial
    targets := targets.push row
    sugars := sugars.push target.sugar
    inputBytes := inputBytes+row.columns.size+row.coefficients.size
    entries := entries+row.size
  let state ← get
  let rows := reducers.size+targets.size
  if rows > 4294967295 then throw (.representation .index)
  if matrix.columns.size*(context.field.width.bytes+4) ≥ USize.size then throw (.representation .address)
  if state.statistics.matrixRows+rows > limits.matrixRows then throw (.exhausted .matrixRows)
  if state.statistics.matrixEntries+entries > limits.matrixEntries then throw (.exhausted .matrixEntries)
  modify fun s => { s with statistics := { s.statistics with
    matrixRows := s.statistics.matrixRows+rows
    matrixTargets := s.statistics.matrixTargets+targets.size
    matrixCalls := s.statistics.matrixCalls+1
    peakMatrixRows := max s.statistics.peakMatrixRows rows } }
  return {
    columns := matrix.columns,queue,pairs,cache := matrix.cache,base := state.statistics,
    matrix := Sampling.start context.field matrix.columns.size reducers targets random config sugars limits.nativeRows,
    inputBytes,inputEntries := entries }

/-- Prepare exactly one pair batch. Empty selections commit only their lawful
pair-criterion work, without consuming random words. -/
def prepare (context : Context) (limits : Limits) (checkpoint : F4.Checkpoint)
    (random : Hex.Rand) (config : Sampling.Config) :
    Computation (F4.Checkpoint × Option Round) := do
  spend limits 1
  if checkpoint.queue.heap.isEmpty then return ({ checkpoint with phase := .interreduce },none)
  let state ← get
  if state.statistics.rounds ≥ limits.rounds then throw (.exhausted .rounds)
  modify fun s => { s with statistics.rounds := s.statistics.rounds+1 }
  let index ← ReducerIndex.build context limits checkpoint.basis
  let (pairs,queue) ← checkpoint.queue.select context limits index checkpoint.basis
  modify fun s => { s with statistics.largestBatch := max s.statistics.largestBatch pairs.size }
  if pairs.isEmpty then return ({ checkpoint with queue },none)
  let rows ← PairRows.prepare context limits checkpoint.basis pairs checkpoint.cache
  spend limits rows.targets.size
  let targets := rows.targets.map fun row => BasisElement.mk row.polynomial row.sugar
  let matrix ← SymbolicMatrix.prepareWith context limits index checkpoint.basis targets rows.cache rows.reducers
  return (checkpoint,some (← translate context limits matrix queue pairs random config))

/-- Remaining parent allowances expressed as cumulative limits within this call.
Input and output entries share the parent matrix-entry allowance. Input packed
payload was already charged by polynomial/column translation. -/
def Round.limits (round : Round) (limits : Limits) (workspace : Workspace) : MatrixLimits := {
  columns := limits.monomials
  rows := limits.matrixRows-round.base.matrixRows
  inputEntries := min round.inputEntries (limits.matrixEntries-round.base.matrixEntries)
  outputEntries := limits.matrixEntries-round.base.matrixEntries-round.inputEntries
  packedBytes := limits.packedBytes-round.base.allocatedBytes-workspace.table.bytes+round.inputBytes
  work := limits.work-round.base.work }

/-- Merge only newly consumed matrix work. Submitted rows/calls were counted at
initialization; resumption neither resubmits the matrix nor resets its counters. -/
def Round.account (round : Round) (workspace : Workspace) : Round × Workspace :=
  let current := round.matrix.statistics.matrix
  let old := round.accounted
  let stats := workspace.statistics
  let statistics := { stats with
    work := stats.work+(current.work-old.work)
    allocatedBytes := stats.allocatedBytes+
      ((current.packedBytes-round.inputBytes)-(old.packedBytes-round.inputBytes))
    matrixRows := stats.matrixRows+(round.matrix.statistics.combinations-round.accountedCombinations)
    matrixTargets := stats.matrixTargets+(round.matrix.statistics.combinations-round.accountedCombinations)
    peakMatrixRows := max stats.peakMatrixRows
      (round.matrix.reducers.size+round.matrix.targets.size+round.matrix.statistics.combinations)
    matrixEntries := stats.matrixEntries+
      ((current.inputEntries+current.outputEntries)-(old.inputEntries+old.outputEntries))
    matrixReductions := stats.matrixReductions+(current.reductions-old.reductions)
    matrixZeroRows := stats.matrixZeroRows+(current.zeroRows-old.zeroRows)
    peakMatrixEntries := max stats.peakMatrixEntries (current.inputEntries+current.outputEntries) }
  ({ round with accounted := current,accountedCombinations := round.matrix.statistics.combinations },{ workspace with statistics })

/-- Commit completed unchecked sample pivots to the F4 basis and pair queue.
This does not certify that their span equals that of all selected targets. -/
def finish (context : Context) (limits : Limits) (checkpoint : F4.Checkpoint)
    (round : Round) : Computation F4.Checkpoint := do
  let some rows := round.matrix.candidate? | throw (.matrix .rowUpdate)
  let mut new := #[]
  for pivot in rows do
    spend limits pivot.row.size
    allocate limits pivot.row.columns.size
    let mut support := ByteArray.emptyWithCapacity pivot.row.columns.size
    for i in [:pivot.row.size] do
      let column := (Packed.read .u32 pivot.row.columns i).toNat
      support := Packed.push .u32 support round.columns[column]!.toUInt64
    new := new.push (BasisElement.mk { support,coefficients := pivot.row.coefficients } pivot.sugar)
  let basis := checkpoint.basis++new
  if let some g ← F4.unit limits new then
    if limits.basis == 0 then throw (.exhausted .basis)
    return { basis := #[g],phase := .complete }
  let mut queue := round.queue
  for pair in round.pairs do queue ← queue.resolve limits pair.left pair.right
  queue ← F4.install context limits basis queue checkpoint.basis.size
  return { basis,queue,cache := round.cache,phase := .pairs }

end Hex.Groebner.Sampled
