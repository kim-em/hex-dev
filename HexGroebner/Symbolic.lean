/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Reducer
public import HexGroebner.ColumnMap
public import HexGroebner.ReducerCache

public section

/-! F4 symbolic preprocessing closes the selected supports under multiplied
reducers, assigns decreasing monomial columns once, then calls the packed
Macaulay kernel. Reducer search uses a basis-specific divisibility trie. -/

namespace Hex.Groebner
open Computation

/-- One symbolic reducer, with the basis row and quotient monomial retained for
derivation recording and future validated trace reuse. -/
structure SymbolicReducer where
  basis : Nat
  multiplier : Nat
  polynomial : Polynomial
  sugar : Nat

/-- Exact monomial column map and symbolic rows of one Macaulay matrix. -/
structure SymbolicMatrix where
  columns : Array Nat
  reducers : Array SymbolicReducer
  targets : Array BasisElement
  cache : ReducerCache := .empty

namespace SymbolicMatrix

/-- Close every selected term under the required reducers. A monomial is queued
once and has at most one chosen reducer. Multiplication can extend the arena and
trigger checked exponent widening, without invalidating any existing identifier.
Optional initial reducers are nonzero basis multiples with distinct leading IDs;
their source indices and multipliers must refer to this basis/arena, and each
payload must equal that multiplier times its source basis polynomial. This is
a trusted internal precondition; complete certificate replay independently
checks the resulting derivations. -/
def prepareWith (context : Context) (limits : Limits) (index : ReducerIndex)
    (basis : Array BasisElement) (targets : Array BasisElement)
    (cache : ReducerCache := .empty) (initial : Array SymbolicReducer := #[]) :
    Computation SymbolicMatrix := do
  let mut cache := cache
  resetSupport limits
  let mut closed : Std.HashSet Nat := {}
  let seeded := !initial.isEmpty
  for reducer in initial do
    let p := reducer.polynomial
    if p.size == 0 || closed.contains (p.monomial 0) then throw (.matrix .dimensions)
    closed := closed.insert (p.monomial 0)
    spend limits (p.size + 1)
    queueSupport limits p.support
  for target in targets do
    let p := target.polynomial
    spend limits p.size
    queueSupport limits p.support
  let mut cursor := 0
  let mut reducers := initial
  for _ in [:limits.monomials] do
    if cursor ≥ (← get).support.queue.size then break
    let monomial := (← get).support.queue[cursor]!
    cursor := cursor + 1
    if seeded && closed.contains monomial then continue
    if let some reducer ← index.find context limits basis monomial then
      let g := basis[reducer]!.polynomial
      let multiplier ← combine limits .quotient monomial (g.monomial 0)
      let (p, nextCache) ← cache.multiply context limits g multiplier
      cache := nextCache
      reducers := reducers.push ⟨reducer, multiplier, p,
        basis[reducer]!.sugar + (← get).table.degree multiplier⟩
      spend limits p.size
      queueSupport limits p.support
  if cursor < (← get).support.queue.size then throw (.exhausted .monomials)
  let columns ← sortSupport context limits
  return ⟨columns, reducers, targets, cache⟩

/-- Build a basis-specific reducer index and close the selected supports.
Call `prepareWith` when the immutable basis index can be reused. -/
def prepare (context : Context) (limits : Limits) (basis : Array BasisElement)
    (targets : Array BasisElement) : Computation SymbolicMatrix := do
  prepareWith context limits (← ReducerIndex.build context limits basis) basis targets

private def row (_context : Context) (limits : Limits) (positions : ColumnMap)
    (p : Polynomial) : Computation SparseRow := do
  spend limits (p.size * positions.lookupCost)
  allocate limits p.support.size
  let some columns := positions.encode p.support limits.nativeRows |
    throw (.representation .index)
  return ⟨columns, p.coefficients⟩

private structure Input where
  reducers : Array SparseRow
  targets : Array SparseRow
  sugars : Array Nat
  entries : Nat
  inputBytes : Nat

private def translate (context : Context) (limits : Limits) (matrix : SymbolicMatrix)
    (independent : Bool := false) : Computation Input := do
  if matrix.columns.size > 4294967295 then throw (.representation .index)
  let positions ← ColumnMap.build limits matrix.columns
  let mut reducers := #[]
  let mut targets := #[]
  let mut entries := 0
  let mut inputBytes := 0
  let mut sugars := #[]
  for r in matrix.reducers do
    sugars := sugars.push r.sugar
    let r ← row context limits positions r.polynomial
    entries := entries + r.size
    inputBytes := inputBytes + r.columns.size + r.coefficients.size
    reducers := reducers.push r
  let orderedTargets ← if independent || matrix.targets.size ≤ 1 then pure matrix.targets else do
    spend limits (2 * matrix.targets.size * (matrix.targets.size + 1).log2 * positions.lookupCost)
    pure ((matrix.targets.toList.mergeSort
      (fun a b =>
        let x := a.polynomial
        let y := b.polynomial
        let left := if x.size == 0 then matrix.columns.size else positions.getD (x.monomial 0) matrix.columns.size
        let right := if y.size == 0 then matrix.columns.size else positions.getD (y.monomial 0) matrix.columns.size
        left > right || (left == right && x.size ≤ y.size))).toArray)
  for p in orderedTargets do
    sugars := sugars.push p.sugar
    let r ← row context limits positions p.polynomial
    entries := entries + r.size
    inputBytes := inputBytes + r.columns.size + r.coefficients.size
    targets := targets.push r
  let s ← get
  let rows := reducers.size + targets.size
  if rows > 4294967295 then throw (.representation .index)
  if matrix.columns.size * (context.field.width.bytes + 4) ≥ USize.size then
    throw (.representation .address)
  if s.statistics.matrixRows + rows > limits.matrixRows then throw (.exhausted .matrixRows)
  if s.statistics.matrixEntries + entries > limits.matrixEntries then
    throw (.exhausted .matrixEntries)
  return ⟨reducers,targets,sugars,entries,inputBytes⟩

private def decode (context : Context) (limits : Limits) (columns : Array Nat)
    (row : SparseRow) (multiplier : UInt64) (sugar : Nat) (monic := true) :
    Computation BasisElement := do
  spend limits row.size
  allocate limits row.columns.size
  let mut support := ByteArray.emptyWithCapacity row.columns.size
  for i in [:row.size] do
    let column := (Packed.read .u32 row.columns i).toNat
    support := Packed.push .u32 support columns[column]!.toUInt64
  let p : Polynomial := { support, coefficients := row.coefficients }
  let p ← if monic || multiplier == 1 then pure p else do
    let factor ← inverse context.field limits multiplier
    p.scale context limits factor
  return ⟨p,sugar⟩

private def matrixLimits (limits : Limits) (entries inputBytes : Nat) : Computation MatrixLimits := do
  let s ← get
  let remainingBytes := limits.packedBytes - s.statistics.allocatedBytes - s.table.bytes
  return {
    columns := limits.monomials, rows := limits.matrixRows - s.statistics.matrixRows
    inputEntries := entries
    outputEntries := limits.matrixEntries - s.statistics.matrixEntries - entries
    packedBytes := remainingBytes + inputBytes
    work := limits.work - s.statistics.work
    densePivots := limits.densePivots, binaryPivots := limits.binaryPivots, delayedReduction := limits.delayedReduction }

private def matrixOutcome {α : Type} : Except MatrixError α → Computation α
  | .ok e => pure e
  | .error (.exhausted r) => match r with
    | .work => throw (.exhausted .work)
    | .packedBytes => throw (.exhausted .packedBytes)
    | .inputEntries | .outputEntries => throw (.exhausted .matrixEntries)
    | .columns => throw (.exhausted .monomials)
    | .rows => throw (.exhausted .matrixRows)
    -- Provenance is disabled here, so this is an internal invariant failure.
    -- A traced F4 route must supply its own resumable provenance allowance.
    | .traceNodes => throw (.matrix (.exhausted .traceNodes))
  | .error e => throw (.matrix e)

/-- Back-substitute among the new monic pivots, so they are in reduced echelon form
among themselves. The pivots, in ascending leading column, re-enter elimination as
targets in descending leading column. Each is then fully reduced by the already
reduced pivots to its right; none can cancel another's leading entry, so leading
columns, monic scalars and pivot order are unchanged. New pivots are already
reduced by every known pivot, so no known reducer is supplied. -/
private def interreduce (context : Context) (limits : Limits) (columns : Nat)
    (rows : Array (SparseRow × UInt64 × Nat)) : Computation (Array (SparseRow × UInt64 × Nat)) := do
  spend limits rows.size
  let targets := rows.reverse
  let entries := targets.foldl (fun n (row, _, _) => n + row.size) 0
  let inputBytes := targets.foldl (fun n (row, _, _) => n + row.columns.size + row.coefficients.size) 0
  let s ← get
  if s.statistics.matrixRows + targets.size > limits.matrixRows then throw (.exhausted .matrixRows)
  if s.statistics.matrixEntries + entries > limits.matrixEntries then
    throw (.exhausted .matrixEntries)
  let outcome := eliminateWith context.field (← matrixLimits limits entries inputBytes) columns
    #[] (targets.map (·.1)) false (targets.map (·.2.2)) limits.nativeRows
  set { s with statistics := (s.statistics.recordMatrix outcome.stats
    (inputBytes := inputBytes) (rows := targets.size) (targets := targets.size)) }
  let echelon ← matrixOutcome outcome.result
  if echelon.rows.size != rows.size then throw (.matrix .dimensions)
  return (rows.zip echelon.rows).map fun ((_, multiplier, _), r) => (r.row, multiplier, r.sugar)

/-- Run the matrix kernel within the remaining parent allowances. Its validated
input payload is already live, so only workspace and output payload are newly
charged to the cumulative allocation counter. Joint monic elimination then
interreduces the new pivots. -/
private def solve (context : Context) (limits : Limits) (matrix : SymbolicMatrix)
    (monic independent : Bool) :
    Computation (Array BasisElement) := do
  let input ← translate context limits matrix independent
  let reducers := input.reducers
  let targets := input.targets
  let sugars := input.sugars
  let rows := reducers.size+targets.size
  let s ← get
  let matrixLimits ← matrixLimits limits input.entries input.inputBytes
  let (result, stats) := if independent then
    let outcome := reduceRowsWith context.field matrixLimits matrix.columns.size reducers targets false sugars limits.nativeRows
    (outcome.result.map (fun e => e.rows.map fun r => (r.row, (1 : UInt64), r.sugar)), outcome.stats)
  else
    let outcome := eliminateWith context.field matrixLimits matrix.columns.size reducers targets false sugars limits.nativeRows
    (outcome.result.map (fun e => e.rows.filterMap fun r =>
      if r.fromTarget then some (r.row, r.multiplier, r.sugar) else none), outcome.stats)
  set { s with statistics := (s.statistics.recordMatrix stats
    (inputBytes := input.inputBytes) (rows := rows) (targets := targets.size)) }
  let rows ← matrixOutcome result
  let rows ← if independent || !monic || rows.size < 2 then pure rows else
    interreduce context limits matrix.columns.size rows
  let mut output := #[]
  for (row,multiplier,sugar) in rows do
    output := output.push (← decode context limits matrix.columns row multiplier sugar monic)
  return output

/-- Joint target elimination. Return new target rows spanning the quotient by
reducer rows. Rows are monic by default; `monic := false` undoes each pivot's
normalization. Targets are stably ordered by decreasing leading-column index,
then increasing support size, before using preceding target pivots. -/
def eliminate (context : Context) (limits : Limits) (matrix : SymbolicMatrix) (monic := true) :
    Computation (Array BasisElement) := solve context limits matrix monic false

/-- Independent target reduction with one shared symbolic closure. Every target
retains its input position, zero rows and original scalar. -/
def reduce (context : Context) (limits : Limits) (matrix : SymbolicMatrix) :
    Computation (Array BasisElement) := solve context limits matrix false true

end SymbolicMatrix

/-- Linear polynomial remainder by symbolic closure and triangular elimination.
Requires canonical polynomials from the current workspace and an index built
from exactly the supplied unchecked divisors. No field equations are added. -/
def Polynomial.remainderWith (context : Context) (limits : Limits) (index : ReducerIndex)
    (basis : Array BasisElement) (p : Polynomial) : Computation Polynomial := do
  if p.size == 0 then return p
  let table := (← get).table
  spend limits p.size
  let sugar := (Array.range p.size).foldl (fun d i => max d (table.degree (p.monomial i))) 0
  let matrix ← SymbolicMatrix.prepareWith context limits index basis #[⟨p, sugar⟩]
  let output ← matrix.eliminate context limits false
  return (output[0]?.map BasisElement.polynomial).getD {}

/-- Remainder with respect to unchecked internal divisors. All packed
polynomials and identifiers must belong to the supplied workspace/context.
This helper supplies no certified-basis or ideal-membership claim. -/
def Polynomial.remainder (context : Context) (limits : Limits) (basis : Array BasisElement)
    (p : Polynomial) : Computation Polynomial := do
  Polynomial.remainderWith context limits (← ReducerIndex.build context limits basis) basis p

end Hex.Groebner
