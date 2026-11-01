/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Reducer
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
  let mut support : Std.HashSet Nat := {}
  let mut pending : Array Nat := #[]
  let mut closed : Std.HashSet Nat := {}
  let seeded := !initial.isEmpty
  for reducer in initial do
    let p := reducer.polynomial
    if p.size == 0 || closed.contains (p.monomial 0) then throw (.matrix .dimensions)
    closed := closed.insert (p.monomial 0)
    spend limits (p.size + 1)
    for i in [:p.size] do
      let id := p.monomial i
      if !support.contains id then
        support := support.insert id
        pending := pending.push id
  for target in targets do
    let p := target.polynomial
    spend limits p.size
    for i in [:p.size] do
      let id := p.monomial i
      if !support.contains id then
        support := support.insert id
        pending := pending.push id
  let mut cursor := 0
  let mut reducers := initial
  for _ in [:limits.monomials] do
    if cursor ≥ pending.size then break
    let monomial := pending[cursor]!
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
      for i in [:p.size] do
        let id := p.monomial i
        if !support.contains id then
          support := support.insert id
          pending := pending.push id
  if cursor < pending.size then throw (.exhausted .monomials)
  let columns ← sort context limits pending
  return ⟨columns, reducers, targets, cache⟩

/-- Build a basis-specific reducer index and close the selected supports.
Call `prepareWith` when the immutable basis index can be reused. -/
def prepare (context : Context) (limits : Limits) (basis : Array BasisElement)
    (targets : Array BasisElement) : Computation SymbolicMatrix := do
  prepareWith context limits (← ReducerIndex.build context limits basis) basis targets

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
private def solve (context : Context) (limits : Limits) (matrix : SymbolicMatrix)
    (monic independent : Bool) :
    Computation (Array BasisElement) := do
  spend limits matrix.columns.size
  let mut positions : Std.HashMap Nat Nat := {}
  for i in [:matrix.columns.size] do positions := positions.insert matrix.columns[i]! i
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
  let targetsBySize := (matrix.targets.toList.mergeSort
    (fun a b => a.polynomial.size ≤ b.polynomial.size)).toArray
  spend limits (matrix.targets.size * (matrix.targets.size + 1).log2)
  for p in targetsBySize do
    sugars := sugars.push p.sugar
    let r ← row context limits positions p.polynomial
    entries := entries + r.size
    inputBytes := inputBytes + r.columns.size + r.coefficients.size
    targets := targets.push r
  let s ← get
  let rows := reducers.size + targets.size
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
    work := limits.work - s.statistics.work }
  let (result, stats) := if independent then
    let outcome := reduceRowsWith context.field matrixLimits matrix.columns.size reducers targets false sugars limits.nativeRows
    (outcome.result.map (fun e => e.rows.map fun r => (r.row, (1 : UInt64), r.sugar)), outcome.stats)
  else
    let outcome := eliminateWith context.field matrixLimits matrix.columns.size reducers targets false sugars limits.nativeRows
    (outcome.result.map (fun e => e.rows.filterMap fun r =>
      if r.fromTarget then some (r.row, r.multiplier, r.sugar) else none), outcome.stats)
  set { s with statistics := { s.statistics with
    work := s.statistics.work + stats.work
    allocatedBytes := s.statistics.allocatedBytes + (stats.packedBytes - inputBytes)
    matrixEntries := s.statistics.matrixEntries + stats.inputEntries + stats.outputEntries
    matrixRows := s.statistics.matrixRows + rows
    matrixCalls := s.statistics.matrixCalls + 1
    peakMatrixRows := max s.statistics.peakMatrixRows rows
    peakMatrixEntries := max s.statistics.peakMatrixEntries (stats.inputEntries + stats.outputEntries) } }
  let rows ← match result with
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
  let mut output := #[]
  for (row, multiplier, sugar) in rows do
    spend limits row.size
    allocate limits row.columns.size
    let mut support := ByteArray.emptyWithCapacity row.columns.size
    for i in [:row.size] do
      let column := (Packed.read .u32 row.columns i).toNat
      support := Packed.push .u32 support matrix.columns[column]!.toUInt64
    let p : Polynomial := { support, coefficients := row.coefficients }
    let p ← if monic || multiplier == 1 then pure p else do
      let factor ← inverse context.field limits multiplier
      p.scale context limits factor
    output := output.push ⟨p, sugar⟩
  return output

/-- Joint target elimination. Return new target rows spanning the quotient by
reducer rows. Rows are monic by default; `monic := false` undoes each pivot's
normalization. Later targets may reduce by earlier target pivots. -/
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
