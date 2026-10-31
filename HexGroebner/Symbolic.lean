/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Reducer

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

namespace SymbolicMatrix

/-- Close every selected term under the required reducers. A monomial is queued
once and has at most one chosen reducer. Multiplication can extend the arena and
trigger checked exponent widening, without invalidating any existing identifier. -/
def prepareWith (context : Context) (limits : Limits) (index : ReducerIndex)
    (basis : Array BasisElement) (targets : Array BasisElement) : Computation SymbolicMatrix := do
  let mut support : Std.HashSet Nat := {}
  let mut pending : Array Nat := #[]
  for target in targets do
    let p := target.polynomial
    spend limits p.size
    for i in [:p.size] do
      let id := p.monomial i
      if !support.contains id then
        support := support.insert id
        pending := pending.push id
  let mut cursor := 0
  let mut reducers := #[]
  for _ in [:limits.monomials] do
    if cursor ≥ pending.size then break
    let monomial := pending[cursor]!
    cursor := cursor + 1
    if let some reducer ← index.find context limits basis monomial then
      let g := basis[reducer]!.polynomial
      let multiplier ← combine limits .quotient monomial (g.monomial 0)
      let p ← g.multiply context limits multiplier
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
  return ⟨columns, reducers, targets⟩

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
def eliminate (context : Context) (limits : Limits) (matrix : SymbolicMatrix) (monic := true) :
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
  for p in matrix.targets do
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
  let remainingBytes := limits.packedBytes - s.statistics.allocatedBytes - s.table.exponents.size - s.table.metadata.size
  let matrixLimits : MatrixLimits := {
    columns := limits.monomials, rows := limits.matrixRows - s.statistics.matrixRows
    inputEntries := entries
    outputEntries := limits.matrixEntries - s.statistics.matrixEntries - entries
    packedBytes := remainingBytes + inputBytes
    work := limits.work - s.statistics.work }
  let outcome := eliminateWith context.field matrixLimits matrix.columns.size reducers targets false sugars limits.nativeRows
  let stats := outcome.stats
  set { s with statistics := { s.statistics with
    work := s.statistics.work + stats.work
    allocatedBytes := s.statistics.allocatedBytes + (stats.packedBytes - inputBytes)
    matrixEntries := s.statistics.matrixEntries + stats.inputEntries + stats.outputEntries
    matrixRows := s.statistics.matrixRows + rows
    matrixCalls := s.statistics.matrixCalls + 1 } }
  let echelon ← match outcome.result with
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
  for pivot in echelon.rows do
    if pivot.fromTarget then
      spend limits pivot.row.size
      allocate limits pivot.row.columns.size
      let mut support := ByteArray.emptyWithCapacity pivot.row.columns.size
      for i in [:pivot.row.size] do
        let column := (Packed.read .u32 pivot.row.columns i).toNat
        support := Packed.push .u32 support matrix.columns[column]!.toUInt64
      let p : Polynomial := { support, coefficients := pivot.row.coefficients }
      let p ← if monic || pivot.multiplier == 1 then pure p else do
        let factor ← inverse context.field limits pivot.multiplier
        p.scale context limits factor
      output := output.push ⟨p, pivot.sugar⟩
  return output

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
