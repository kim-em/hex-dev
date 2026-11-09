/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Producer.Basic
public import HexGroebner.ColumnMap

public section

namespace Hex.Groebner.Producer
open Computation

private def row (_context : Context) (limits : Limits) (positions : ColumnMap)
    (p : Polynomial) : Computation SparseRow := do
  spend limits (p.size * positions.lookupCost)
  allocate limits p.support.size
  let some columns := positions.encode p.support limits.nativeRows |
    throw (.representation .index)
  return ⟨columns, p.coefficients⟩

private def outcome {α : Type} : Except MatrixError α → Work α
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

/-- Emit one certificate node per matrix row operation. -/
private def replay (limits : Limits) (nodeLimit : Nat) (inputRoots : Array Nat)
    (trace : Array RowOp) : Work (Array Nat) := do
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
  return nodes

/-- Traced counterpart of the candidate's back-substitution among new monic pivots.
Each pivot re-enters with its own derivation, so the traced elimination output
denotes the back-substituted pivot. -/
private def interreduce (context : Context) (limits : Limits) (nodeLimit columns : Nat)
    (rows : Array (SparseRow × UInt64 × Nat × Nat)) :
    Work (Array (SparseRow × UInt64 × Nat × Nat)) := do
  lift (Computation.spend limits rows.size)
  let targets := rows.reverse
  let entries := targets.foldl (fun n (row, _, _, _) => n + row.size) 0
  let inputBytes := targets.foldl (fun n (row, _, _, _) => n + row.columns.size + row.coefficients.size) 0
  let count := targets.size
  let traceCapacity := min (nodeLimit-(← get).derivation.nodes.size+count) (count*(columns+2))
  let s ← lift get
  if s.statistics.matrixRows + count > limits.matrixRows then throw (.exhausted .matrixRows)
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
  let result := eliminateWith context.field matrixLimits columns #[] (targets.map (·.1)) true
    (targets.map (·.2.2.1)) limits.nativeRows
  lift (set { s with statistics := (s.statistics.recordMatrix result.stats
    (inputBytes := inputBytes) (rows := count) (targets := count)) })
  let echelon ← outcome result.result
  if echelon.rows.size != rows.size then throw (.matrix .dimensions)
  let nodes ← replay limits nodeLimit (targets.map (·.2.2.2)) echelon.trace
  let mut output := #[]
  for ((_, multiplier, _, _), r) in rows.zip echelon.rows do
    let some index := r.derivation | throw (.matrix .dimensions)
    let some root := nodes[index]? | throw (.matrix .dimensions)
    output := output.push (r.row, multiplier, r.sugar, root)
  return output

/-- Run the matrix kernel within the remaining parent allowances. Its validated
input payload is already live, so only workspace and output payload are newly
charged to the cumulative allocation counter. -/
def solve (context : Context) (limits : Limits) (nodeLimit : Nat)
    (basis targetsTraced : Array Element) (matrix : SymbolicMatrix)
    (monic independent : Bool) :
    Work (Array Element) := do
  if matrix.columns.size > 4294967295 then throw (.representation .index)
  let positions ← lift (ColumnMap.build limits matrix.columns)
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
  let targetPairs ← if independent || matrix.targets.size ≤ 1 then pure (matrix.targets.zip targetsTraced) else do
    lift (Computation.spend limits (2 * matrix.targets.size * (matrix.targets.size + 1).log2 * positions.lookupCost))
    pure (((matrix.targets.zip targetsTraced).toList.mergeSort
      (fun a b =>
        let x := a.1.polynomial
        let y := b.1.polynomial
        let left := if x.size == 0 then matrix.columns.size else positions.getD (x.monomial 0) matrix.columns.size
        let right := if y.size == 0 then matrix.columns.size else positions.getD (y.monomial 0) matrix.columns.size
        left > right || (left == right && x.size ≤ y.size))).toArray)
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
  if rows > 4294967295 then throw (.representation .index)
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
  lift (set { s with statistics := (s.statistics.recordMatrix stats
    (inputBytes := inputBytes) (rows := rows) (targets := targets.size)) })
  let (rows,trace) ← outcome result
  let nodes ← replay limits nodeLimit inputRoots trace
  let mut resolved := #[]
  for (row,multiplier,sugar,derivation) in rows do
    let some index := derivation | throw (.matrix .dimensions)
    let some root := nodes[index]? | throw (.matrix .dimensions)
    resolved := resolved.push (row,multiplier,sugar,root)
  let pivots ← if independent || !monic || resolved.size < 2 then pure resolved else
    interreduce context limits nodeLimit matrix.columns.size resolved
  let mut output := #[]
  for (row,multiplier,sugar,root) in pivots do
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
