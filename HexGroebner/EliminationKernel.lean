/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.MatrixValidation
public import HexGroebner.Native
public import HexGroebner.NativeScan
public import HexGroebner.NativeGather

public section

/-! Deterministic sparse/dense Macaulay elimination. Reducers are processed
before target rows; the column map is fixed throughout. Only sparse pivot
rows are retained, with one reusable packed dense accumulator. -/

/- The elimination carrier may import only other carrier-owned modules.
Do not introduce an executable-library import here; see PLAN/Conventions.md. -/

namespace Hex.Groebner

open Matrix

private def record (limits : MatrixLimits) (enabled : Bool)
    (trace : Array RowOp) (op : RowOp) : Work (Array RowOp × Option Nat) := do
  if !enabled then return (trace, none)
  charge .traceNodes 1 limits.traceNodes (·.traceNodes) fun s n => { s with traceNodes := n }
  packedBytes limits 64
  let index := trace.size
  return (trace.push op, some index)

/-- Flat loop state avoids a nested tuple of mutable values at every column.
Keep it uniquely owned through the loop: sharing it can force dense/trace
copies. Changes to its ownership should be checked with the matrix benchmarks. -/
private structure Scan where
  dense : ByteArray
  last : Nat
  chargedUntil : Nat
  leading : Option Nat
  trace : Array RowOp
  node : Option Nat
  sugar : Nat

@[noinline] private def takeDense (scan : Scan) : ByteArray × Scan :=
  (scan.dense,{ scan with dense := {} })

private def nativeScan (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (slots : ByteArray) (pivots : Array Pivot) (nativePivots : Array Native.Scan.Pivot)
    (first : Nat) (scan : Scan) (provenance : Bool) : Work Scan := do
  let (dense,scan) := takeDense scan
  let mut state : Native.Scan.State := {
    dense, column := first, last := scan.last, chargedUntil := scan.chargedUntil
    sugar := scan.sugar }
  let mut trace := scan.trace
  let mut node := scan.node
  for _ in [:((columns*(columns+2)+4095)/4096+1)] do
    let stats ← get
    let traces := limits.traceNodes-stats.traceNodes
    let traceBytes := if provenance then (limits.packedBytes-stats.packedBytes)/64 else traces
    let result := Native.Scan.transition field.modulus slots nativePivots state 4096
      (limits.work-stats.work) (min traces traceBytes) provenance
    work limits result.work
    modify fun s => { s with reductions := s.reductions+result.reductions }
    for event in result.events do
      let pivot := pivots[event.1]!
      if let (some left,some right) := (node,pivot.derivation) then
        let (nextTrace,nextNode) ← record limits provenance trace
          (.addScaled left right (field.modulus-event.2))
        trace := nextTrace
        node := nextNode
      else throw .rowUpdate
    state := result.state
    if result.status == 1 then
      return { scan with dense := state.dense, last := state.last, chargedUntil := state.chargedUntil, leading := if state.leading == 0 then none else some (state.leading-1), trace, node, sugar := state.sugar }
    if result.status == 2 then throw (.exhausted .work)
    if result.status == 3 then
      if provenance && traceBytes < traces then
        let _ ← record limits provenance trace (.input 0)
        throw .rowUpdate
      throw (.exhausted .traceNodes)
    if result.status != 0 then throw .rowUpdate
  throw .rowUpdate

private def nativeGather (field : PrimeField) (limits : MatrixLimits) (dense : ByteArray)
    (column last : Nat) (factor : UInt64) : Work (SparseRow × ByteArray) := do
  let mut state : Native.Gather.State := ⟨dense,{},{},column⟩
  for _ in [:((last+1-column+4095)/4096+1)] do
    let stats ← get
    let result := Native.Gather.gather field.modulus state (last+1) 4096
      (limits.outputEntries-stats.outputEntries) (limits.packedBytes-stats.packedBytes)
      (limits.work-stats.work) factor
    charge .outputEntries result.entries limits.outputEntries (·.outputEntries)
      fun s n => { s with outputEntries := n }
    packedBytes limits result.bytes
    work limits result.work
    state := result.state
    if result.status == 1 then return (⟨state.columns,state.coefficients⟩,state.dense)
    if result.status == 2 then throw (.exhausted .outputEntries)
    if result.status == 3 then throw (.exhausted .packedBytes)
    if result.status == 4 then throw (.exhausted .work)
    if result.status == 5 then throw .dimensions
    if result.status != 0 then throw .rowUpdate
  throw .rowUpdate

/-- Reduce against sparse pivots in a fixed column map. Each scalar update uses
canonical residues: `a + p - (b*c mod p)` fits below `2*p < 2^32`, and the
Barrett product fits below `p^2 < 2^62`. No floating-point arithmetic is used. -/
private def eliminate (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (provenance : Bool) (sugars : Array Nat)
    (native independent : Bool) : Work (Echelon × Array RemainderRow) := do
  if columns > 4294967295 || reducers.size + targets.size > 4294967295 then
    throw .dimensions
  if columns > limits.columns then throw (.exhausted .columns)
  if reducers.size + targets.size > limits.rows then throw (.exhausted .rows)
  if !sugars.isEmpty && sugars.size != reducers.size + targets.size then throw .dimensions
  validateRows field limits columns reducers targets native
  let width := field.width
  let workspaceBytes := columns * (width.bytes + 4)
  -- Keep all allocation sizes inside both the logical limit and the platform's
  -- addressable range, even on 32-bit hosts. Do not narrow unchecked products.
  if workspaceBytes ≥ USize.size then throw .dimensions
  packedBytes limits workspaceBytes
  work limits workspaceBytes
  let mut dense := if native then zerosWith (columns * width.bytes) else zeros (columns * width.bytes)
  -- A slot stores pivot index + 1. Zero means no pivot, never monomial identity.
  let mut slots := if native then zerosWith (columns * 4) else zeros (columns * 4)
  let mut pivots : Array Pivot := #[]
  let mut nativePivots : Array Native.Scan.Pivot := #[]
  let mut trace : Array RowOp := #[]
  let mut remainders : Array RemainderRow := #[]
  let mut reducerRank := 0
  let ctx := field.barrett
  for input in [:reducers.size + targets.size] do
    work limits 1
    let fromTarget := input ≥ reducers.size
    let row := if fromTarget then targets[input - reducers.size]! else reducers[input]!
    let (nextTrace, node) ← record limits provenance trace (.input input)
    trace := nextTrace
    let mut node := node
    let mut sugar := sugars[input]?.getD 0
    if row.size == 0 then
      if independent && fromTarget then remainders := remainders.push ⟨{}, node, sugar⟩
      modify fun s => { s with zeroRows := s.zeroRows + 1 }
    else
      let first := (Packed.read .u32 row.columns 0).toNat
      if !fromTarget && Packed.read .u32 slots first == 0 then
        let inv ← inverse field ctx limits (Packed.read width row.coefficients 0)
        let output ← scaleSparse field ctx limits row inv
        let (nextTrace, nextNode) ← if inv == 1 then pure (trace, node) else
          match node with
          | some n => record limits provenance trace (.scale n inv)
          | none => pure (trace, none)
        trace := nextTrace
        let stats ← get
        let prepared := Matrix.preparePivot field limits columns ⟨output.columns,output.coefficients,sugar⟩ stats
        modify fun s => Matrix.cacheStats s prepared.work prepared.packedBytes
        slots := Packed.set .u32 slots first (pivots.size + 1).toUInt64
        pivots := pivots.push ⟨output, false, nextNode, inv, sugar⟩
        if native then nativePivots := nativePivots.push ⟨output.columns,output.coefficients,sugar⟩
        reducerRank := reducerRank + 1
      else
        work limits row.size
        for i in [:row.size] do
          let column := (Packed.read .u32 row.columns i).toNat
          dense := Packed.set width dense column (Packed.read width row.coefficients i)
        let mut scan : Scan := ⟨dense, (Packed.read .u32 row.columns (row.size - 1)).toNat,
          first, none, trace, node, sugar⟩
        if native then
          scan ← nativeScan field limits columns slots pivots nativePivots first scan provenance
        else
          for column in [first:columns] do
            if column > scan.last then break
            -- Reserve bounded scan blocks; a pivot can extend the active range.
            if column ≥ scan.chargedUntil then
              scan := { scan with chargedUntil := min (column + 64) (scan.last + 1) }
              work limits (scan.chargedUntil - column)
            let a := Packed.read width scan.dense column
            if a != 0 then
              let slot := (Packed.read .u32 slots column).toNat
              if slot != 0 then
                let pivot := pivots[slot - 1]!
                scan := { scan with
                  sugar := max scan.sugar pivot.sugar
                  last := max scan.last (Packed.read .u32 pivot.row.columns (pivot.row.size - 1)).toNat }
                work limits pivot.row.size
                for i in [:pivot.row.size] do
                  let j := (Packed.read .u32 pivot.row.columns i).toNat
                  let b := Packed.read width pivot.row.coefficients i
                  let product := ctx.mulMod a b
                  let difference := Packed.read width scan.dense j + field.modulus - product
                  let value := if difference ≥ field.modulus then difference - field.modulus else difference
                  scan := { scan with dense := Packed.set width scan.dense j value }
                modify fun s => { s with reductions := s.reductions + 1 }
                if let (some left, some right) := (scan.node, pivot.derivation) then
                  let (nextTrace, nextNode) ← record limits provenance scan.trace
                    (.addScaled left right (field.modulus - a))
                  scan := { scan with trace := nextTrace, node := nextNode }
              else if scan.leading.isNone then
                scan := { scan with leading := some column }
        dense := scan.dense
        trace := scan.trace
        node := scan.node
        sugar := scan.sugar
        let last := scan.last
        let leading := scan.leading
        if let some column := leading then
          let a := Packed.read width dense column
          let inv ← if independent && fromTarget then pure 1 else inverse field ctx limits a
          let (nextTrace, nextNode) ← if inv == 1 then pure (trace, node) else
            match node with
            | some n => record limits provenance trace (.scale n inv)
            | none => pure (trace, none)
          trace := nextTrace
          let mut output : SparseRow := {}
          work limits (last + 1 - column)
          if native then
            let (row,nextDense) ← nativeGather field limits dense column last inv
            output := row
            dense := nextDense
          else
            for j in [column:last + 1] do
              let a := Packed.read width dense j
              if a != 0 then
                charge .outputEntries 1 limits.outputEntries (·.outputEntries)
                  fun s n => { s with outputEntries := n }
                packedBytes limits (4 + width.bytes)
                if output.columns.size + 4 ≥ USize.size ||
                    output.coefficients.size + width.bytes ≥ USize.size then throw .dimensions
                let value ← if inv == 1 then pure a else do
                  work limits 1
                  pure (ctx.mulMod a inv)
                output := {
                  columns := Packed.push .u32 output.columns j.toUInt64
                  coefficients := Packed.push width output.coefficients value }
                dense := Packed.set width dense j 0
          if independent && fromTarget then
            remainders := remainders.push ⟨output, nextNode, sugar⟩
          else
            let stats ← get
            let prepared := Matrix.preparePivot field limits columns ⟨output.columns,output.coefficients,sugar⟩ stats
            modify fun s => Matrix.cacheStats s prepared.work prepared.packedBytes
            slots := Packed.set .u32 slots column (pivots.size + 1).toUInt64
            pivots := pivots.push ⟨output, fromTarget, nextNode, inv, sugar⟩
            if native then nativePivots := nativePivots.push ⟨output.columns,output.coefficients,sugar⟩
            if !fromTarget then reducerRank := reducerRank + 1
        else
          if independent && fromTarget then remainders := remainders.push ⟨{}, node, sugar⟩
          modify fun s => { s with zeroRows := s.zeroRows + 1 }
    modify fun s => { s with processedRows := s.processedRows + 1 }
  if independent then return (⟨#[], reducerRank, trace⟩, remainders)
  let mut ordered := #[]
  work limits columns
  for column in [:columns] do
    let slot := (Packed.read .u32 slots column).toNat
    if slot != 0 then ordered := ordered.push pivots[slot - 1]!
  return (⟨ordered, reducerRank, trace⟩, remainders)

namespace Elimination

/-- Complete matrix outcome used by the optional bulk provider.
Layout mirrored in `HexGroebner/ffi/matrix_eliminate.c`. -/
structure Result where
  result : Except MatrixError (Echelon × Array RemainderRow)
  stats : MatrixStats

/-- Deterministic reference for an untraced whole matrix operation. -/
def reference (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool) : Result :=
  let (result, stats) :=
    (eliminate field limits columns reducers targets false sugars true independent).run {}
  ⟨result, stats⟩

/-- A private bit matrix is used only by explicitly requested F2 frames. -/
def binaryEnabled (field : PrimeField) (limits : MatrixLimits) : Bool :=
  limits.binaryPivots && field.modulus == 2

/-- Exact UInt64 accumulation is bounded for these explicitly requested fields. -/
def delayedEnabled (field : PrimeField) (limits : MatrixLimits) : Bool :=
  limits.delayedReduction && field.modulus > 2 && field.modulus ≤ 65536

/-- Additional accumulator bytes and flat borrowed-pivot metadata. -/
def delayedBytes (field : PrimeField) (columns reducers targets : Nat) : Nat :=
  (8-field.width.bytes)*columns+40*min (reducers+targets) columns

/-- Logical reference work cap, distinct from the physical word-operation cap. -/
def frameQuantum (field : PrimeField) (limits : MatrixLimits) : Nat :=
  if binaryEnabled field limits then 2^38 else if delayedEnabled field limits then 2^34 else 2^20

/-- Large F2 frames project targets through known reducers in column order. -/
def binaryProject (columns reducers targets : Nat) : Bool :=
  columns ≥ 64 && reducers ≥ 4 && targets ≥ 64

/-- Private pivot rows, accumulator, metadata, optional projected targets
and one reusable sixteen-row XOR table,
reserved against the parent peak. -/
def binaryBytes (columns reducers targets : Nat) : Nat :=
  let capacity := min (reducers+targets) columns
  let words := (columns+63)/64
  (capacity+1)*words*8+16*capacity+
    if binaryProject columns reducers targets then targets*(words*8+16)+16*words*8 else 0

/-- Word XORs, packing, validation and scalar scanning have this conservative
shape bound, including metadata packing. A pivot is visited at most once
for each target. Projected frames additionally bound target-buffer initialization,
copies, metadata, table construction, mask selection and known-head visits. -/
def binaryBound (columns reducers targets entries : Nat) : Nat :=
  let rows := reducers+targets
  let words := (columns+63)/64
  rows*(words+8)+3*entries+4*targets*columns+5*columns+
    targets*(rows*words+64)+columns+
    if binaryProject columns reducers targets then targets*(columns+2*words+8)+((reducers+3)/4)*(16*words+512)+8*targets*reducers+5*columns else 0

/-- Count exactly the groups consumed by column-ordered known-pivot tables.
Sparse pivots interrupt a run; gaps and empty rows do not. -/
def binaryGroups (columns : Nat) (reducers : Array SparseRow) : Nat := Id.run do
  let mut slots := Array.replicate columns 0
  for i in [:reducers.size] do
    let row := reducers[i]!
    if row.size != 0 then
      let head := (Packed.read .u32 row.columns 0).toNat
      if head ≥ columns || slots[head]! != 0 then return 0
      slots := slots.set! head (i+1)
  let mut run := 0
  let mut groups := 0
  for head in [:columns] do
    let id := slots[head]!
    if id != 0 then
      let row := reducers[id-1]!
      let last := (Packed.read .u32 row.columns (row.size-1)).toNat
      if row.size > last/64-head/64+1 then
        run := run+1
        if run == 4 then
          groups := groups+1
          run := 0
      else run := 0
  return groups

/-- A four-row table replaces four full-width row updates by at most one.
Preparation and mask selection remain in the conservative bound. -/
def binaryCost (columns : Nat) (reducers targets : Array SparseRow) (entries : Nat) : Nat :=
  let full := binaryBound columns reducers.size targets.size entries
  if binaryProject columns reducers.size targets.size then
    full-3*((columns+63)/64)*targets.size*(binaryGroups columns reducers)
  else full

/-- Known reducers have distinct leading columns. The conservative work bound
uses `65 * rows` for row visits and inversion products, `2 * entries` for
validation, sparse scaling and scattering, and `columns * (width + 4)` for
workspace initialization. For each target, `entries` covers known-pivot updates,
`(targets + 3) * columns` covers target-pivot updates, dense scanning, gathering
and normalization, and 64 allows inversion. A pivot is used at most once per
target because scanning advances through its leading column. The final
`columns` covers pivot ordering. These deliberately overlapping bounds cover
the sparse computation. Optional dense preparation adds separately charged work;
`attemptPortable` also checks the final total against the selected frame quantum.
Opt-in F2 frames additionally bound packing, scanning and word updates by `2^34`
visits and reserve their complete temporary payload against the packed-byte allowance.
Opt-in delayed frames over primes below `2^16` use these same dimension ceilings
and a `2^38` conservative admission bound; successful reference work is at most
`2^34`. Each accumulator cell receives at most one product per column, so it
stays below `(p-1)+columns*(p-1)^2 < 2^50`. Private UInt64 accumulation and
forty-byte pivot descriptors are reserved against the parent payload. -/
def fits (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) : Bool := Id.run do
  let rows := reducers.size + targets.size
  if USize.size != 2^64 then return false
  let binary := binaryEnabled field limits
  let delayed := delayedEnabled field limits
  let wide := binary || delayed
  if columns > (if wide then 131072 else 4096) ||
      reducers.size > (if wide then 131072 else 1024) ||
      targets.size > (if wide then 4096 else 64) ||
      columns > limits.columns || rows > limits.rows ||
      (!sugars.isEmpty && sugars.size != rows) then return false
  if !(sugars.all (· < USize.size / 2)) then return false
  let workspace := columns * (field.width.bytes + 4)
  if limits.work < 2 * rows + workspace || limits.packedBytes < workspace then return false
  let mut entries := 0
  for group in [reducers, targets] do
    for row in group do
      if row.columns.size % 4 != 0 ||
          row.coefficients.size != row.size * field.width.bytes then return false
      entries := entries + row.size
  let bound := rows * 65 + 2 * entries + columns * (field.width.bytes + 4) +
    targets.size * (entries + (targets.size + 3) * columns + 64) + columns
  if bound > (if delayed then 2^38 else frameQuantum field limits) then return false
  if binary && binaryCost columns reducers targets entries > 2^34 then return false
  let mut seen := Array.replicate columns false
  for row in reducers do
    if row.size != 0 then
      let column := (Packed.read .u32 row.columns 0).toNat
      if column ≥ columns || seen[column]! then return false
      seen := seen.set! column true
  return true

/-- A successful bulk attempt has the complete reference result; unsupported
inputs and reference failures retain the ordinary matrix boundary. -/
def attemptPortable (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool) :
    Option Result :=
  if !(fits field limits columns reducers targets sugars) then none else
    let result := reference field limits columns reducers targets sugars independent
    if result.result.isOk && result.stats.work ≤ frameQuantum field limits &&
        (!binaryEnabled field limits || result.stats.packedBytes+
          binaryBytes columns reducers.size targets.size ≤ limits.packedBytes) &&
        (!delayedEnabled field limits || result.stats.packedBytes+
          delayedBytes field columns reducers.size targets.size ≤ limits.packedBytes) then some result else none

/-- On the 64-bit ABI, `PrimeField` is passed as its `UInt64` modulus; limits,
column count, row arrays and sugars are borrowed Lean objects, and `independent`
is an unboxed Boolean. `Result` holds an `Except` matrix/remainder pair and eight
`Nat` counters. Native code returns `some` only for a complete successful
reference result, including exact rows, aliases, sugars and counters. It admits
ordinary frames with at most 4096 columns, 1024 known reducers, 64 targets and
`2^20` charged work. Opt-in F2 frames admit at most 131072 columns, 131072 reducers
and 4096 targets, with a `2^38` logical-work bound and a separate `2^34` bound
on packing/scalar/word visits. Their private pivot/accumulator bytes must fit
the packed-byte allowance in addition to the complete reference payload. Known leading
columns are distinct. Large limits saturate above all
possible accepted totals; non-machine-size sugars use checked Lean arithmetic.

The matrix owns its dense workspace; all inputs remain immutable, including
shared reducer/target arrays. Unsupported shapes return `none` without changing
inputs, and a reference-equivalent continuation runs after the native frame. A declined
attempt's physical work is unreported; the continuation retains the reference counters. Ordinary-frame
speculation is bounded by the remaining logical allowance and `2^20`; opt-in
F2 packing and word visits have their separate shape bound. Delayed frames
have a `2^34` logical-work cap and an additional at-most `targets*columns`
accumulator-clear bound. Their UInt64 accumulator and flat pivot metadata can
also cause a late byte refusal, followed by the reference-equivalent continuation. Without dense
preparation, private F2 payload or delayed frames, the shape bound makes a charged decline imply
reference failure. F2 payload admission can decline a successful reference. With dense preparation, a successful reference may
exceed the frame quantum and continue outside the frame. Such a declined
prefix costs less than that frame's reference work; this can occur on multiple
matrices, so the overhead bound is per frame rather than per computation. -/
@[extern "lean_hex_groebner_eliminate_matrix"]
def attempt (field : PrimeField) (limits : @& MatrixLimits) (columns : @& Nat)
    (reducers targets : @& Array SparseRow) (sugars : @& Array Nat) (independent : Bool) :
    Option Result := attemptPortable field limits columns reducers targets sugars independent

/-- The transparent provider returns its reference result or declines. -/
theorem attemptPortable_spec (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool) :
    (attemptPortable field limits columns reducers targets sugars independent).getD
      (reference field limits columns reducers targets sugars independent) =
      reference field limits columns reducers targets sugars independent := by
  unfold attemptPortable
  split <;> simp only [Option.getD_none]
  split <;> rfl

end Elimination

end Hex.Groebner
