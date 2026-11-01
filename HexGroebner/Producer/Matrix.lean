/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Producer.Basic

public section

namespace Hex.Groebner.Producer
open Computation

private def row (_context : Context) (limits : Limits) (positions : Std.HashMap Nat Nat)
    (p : Polynomial) : Computation SparseRow := do
  spend limits p.size
  allocate limits p.support.size
  let mut columns := ByteArray.emptyWithCapacity p.support.size
  for i in [:p.size] do
    let id := p.monomial i
    match positions[id]? with
    | none => throw (.representation .index)
    | some column => columns := Packed.push .u32 columns column.toUInt64
  return ⟨columns, p.coefficients⟩

/-- Run the matrix kernel within the remaining parent allowances. Its validated
input payload is already live, so only workspace and output payload are newly
charged to the cumulative allocation counter. -/
def solve (context : Context) (limits : Limits) (nodeLimit : Nat)
    (basis targetsTraced : Array Element) (matrix : SymbolicMatrix)
    (monic independent : Bool) :
    Work (Array Element) := do
  lift (Computation.spend limits (matrix.columns.size))
  let mut positions : Std.HashMap Nat Nat := {}
  for i in [:matrix.columns.size] do positions := positions.insert matrix.columns[i]! i
  let mut reducers := #[]
  let mut targets := #[]
  let mut entries := 0
  let mut inputBytes := 0
  let mut sugars := #[]
  for r in matrix.reducers do
    sugars := sugars.push r.sugar
    let r ← lift (row context limits positions r.polynomial)
    entries := entries + r.size
    inputBytes := inputBytes + r.columns.size + r.coefficients.size
    reducers := reducers.push r
  if matrix.targets.size != targetsTraced.size then throw (.matrix .dimensions)
  let targetPairs ← if independent then pure (matrix.targets.zip targetsTraced) else do
    lift (Computation.spend limits (matrix.targets.size * (matrix.targets.size + 1).log2))
    pure (((matrix.targets.zip targetsTraced).toList.mergeSort
      (fun a b => a.1.polynomial.size ≤ b.1.polynomial.size)).toArray)
  for (p, _) in targetPairs do
    sugars := sugars.push p.sugar
    let r ← lift (row context limits positions p.polynomial)
    entries := entries + r.size
    inputBytes := inputBytes + r.columns.size + r.coefficients.size
    targets := targets.push r
  let mut inputRoots := #[]
  for reducer in matrix.reducers do
    let some source := basis[reducer.basis]? | throw (.matrix .dimensions)
    inputRoots := inputRoots.push (← monomial context limits nodeLimit reducer.multiplier source.root)
  for (_, target) in targetPairs do inputRoots := inputRoots.push target.root
  let rows := reducers.size + targets.size
  -- Input records reuse roots and consume no polynomial certificate node.
  let traceCapacity := min (nodeLimit-(← get).derivation.nodes.size+rows)
    (rows*(matrix.columns.size+2))
  let s ← lift get
  if matrix.columns.size > 4294967295 || rows > 4294967295 then throw (.representation .index)
  if matrix.columns.size * (context.field.width.bytes + 4) ≥ USize.size then
    throw (.representation .address)
  if s.statistics.matrixRows + rows > limits.matrixRows then throw (.exhausted .matrixRows)
  if s.statistics.matrixEntries + entries > limits.matrixEntries then
    throw (.exhausted .matrixEntries)
  let remainingBytes := limits.packedBytes - s.statistics.allocatedBytes - s.table.bytes
  let matrixLimits : MatrixLimits := {
    columns := limits.monomials, rows := limits.matrixRows - s.statistics.matrixRows
    inputEntries := entries
    outputEntries := limits.matrixEntries - s.statistics.matrixEntries - entries
    packedBytes := remainingBytes + inputBytes
    work := limits.work - s.statistics.work
    traceNodes := traceCapacity }
  let (result,stats) := if independent then
    let outcome := reduceRowsWith context.field matrixLimits matrix.columns.size reducers targets true sugars limits.nativeRows
    (outcome.result.map (fun e => (e.rows.map fun r => (r.row,(1:UInt64),r.sugar,r.derivation),e.trace)),outcome.stats)
  else
    let outcome := eliminateWith context.field matrixLimits matrix.columns.size reducers targets true sugars limits.nativeRows
    (outcome.result.map (fun e => (e.rows.filterMap fun r => if r.fromTarget then
      some (r.row,r.multiplier,r.sugar,r.derivation) else none,e.trace)),outcome.stats)
  lift (set { s with statistics := { s.statistics with
    work := s.statistics.work + stats.work
    allocatedBytes := s.statistics.allocatedBytes + (stats.packedBytes - inputBytes)
    matrixEntries := s.statistics.matrixEntries + stats.inputEntries + stats.outputEntries
    matrixRows := s.statistics.matrixRows + rows
    matrixCalls := s.statistics.matrixCalls + 1
    peakMatrixRows := max s.statistics.peakMatrixRows rows
    peakMatrixEntries := max s.statistics.peakMatrixEntries (stats.inputEntries + stats.outputEntries) } })
  let (rows,trace) ← match result with
    | .ok e => pure e
    | .error (.exhausted r) => match r with
      | .work => throw (.exhausted .work)
      | .packedBytes => throw (.exhausted .packedBytes)
      | .inputEntries | .outputEntries => throw (.exhausted .matrixEntries)
      | .columns => throw (.exhausted .monomials)
      | .rows => throw (.exhausted .matrixRows)
      -- Trace exhaustion retains the committed F4 checkpoint and counters.
      | .traceNodes => throw (.matrix (.exhausted .traceNodes))
    | .error e => throw (.matrix e)
  let mut nodes : Array Nat := #[]
  for operation in trace do
    let root ← match operation with
      | .input i => match inputRoots[i]? with
        | some root => pure root
        | none => throw (.matrix .dimensions)
      | .scale i c => match nodes[i]? with
        | some root => emit limits nodeLimit (.scale c.toNat root)
        | none => throw (.matrix .dimensions)
      | .addScaled i j c => match nodes[i]?,nodes[j]? with
        | some left,some right => do
          let scaled ← emit limits nodeLimit (.scale c.toNat right)
          emit limits nodeLimit (.add left scaled)
        | _,_ => throw (.matrix .dimensions)
    nodes := nodes.push root
  let mut output := #[]
  for (row,multiplier,sugar,derivation) in rows do
    let some index := derivation | throw (.matrix .dimensions)
    let some root := nodes[index]? | throw (.matrix .dimensions)
    let mut root := root
    lift (Computation.spend limits (row.size))
    lift (Computation.allocate limits (row.columns.size))
    let mut support := ByteArray.emptyWithCapacity row.columns.size
    for i in [:row.size] do
      let column := (Packed.read .u32 row.columns i).toNat
      support := Packed.push .u32 support matrix.columns[column]!.toUInt64
    let p : Polynomial := { support, coefficients := row.coefficients }
    let p ← if monic || multiplier == 1 then pure p else do
      let factor ← lift (Computation.inverse context.field limits multiplier)
      root ← emit limits nodeLimit (.scale factor.toNat root)
      lift (p.scale context limits factor)
    output := output.push ⟨⟨p,sugar⟩,root⟩
  return output


end Hex.Groebner.Producer
