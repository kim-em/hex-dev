/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Packed
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

/-- Both representations choose the same minimal residue width. -/
theorem native_width (field : PrimeField) :
    Native.width field.modulus.toNat = field.width.bytes := by
  simp only [Native.width, PrimeField.width, UInt64.le_iff_toNat_le]
  simp only [show (256 : UInt64).toNat = 256 from rfl,
    show (65536 : UInt64).toNat = 65536 from rfl]
  split <;> (try split) <;> rfl

/-- Resource categories. Packed bytes count logical input, workspace and output
payload and 64 logical bytes per recorded derivation operation, excluding
allocator capacity and other Lean object headers. Work counts row
visits, sparse entry updates (including their product), dense column visits,
normalization/inversion products and workspace bytes initialized. -/
inductive Resource where
  | columns | rows | inputEntries | outputEntries | packedBytes | work | traceNodes
  deriving BEq, Repr

/-- Invalid serialized data, resource exhaustion and internal row-provider failure remain distinct. -/
inductive MatrixError where
  | dimensions
  /-- The checked native row provider rejected a validated row; internal invariant failure. -/
  | rowUpdate
  | rowLength (row : Nat)
  | column (row entry : Nat)
  | coefficient (row entry : Nat)
  | exhausted (resource : Resource)
  deriving BEq, Repr

/-- Bounds for one matrix call. All sizes use `Nat` arithmetic, so size products
are checked before narrowing or allocation. There is no unbounded fallback.  Layout mirrored in `HexGroebner/ffi/matrix_eliminate.c`. -/
structure MatrixLimits where
  columns : Nat := 1000000
  rows : Nat := 100000
  inputEntries : Nat := 10000000
  outputEntries : Nat := 10000000
  packedBytes : Nat := 256 * 1024 * 1024
  work : Nat := 100000000
  traceNodes : Nat := 1000000
  deriving Inhabited

/-- Charged work is retained on failure as well as success.  Layout mirrored in `HexGroebner/ffi/matrix_eliminate.c`. -/
structure MatrixStats where
  work : Nat := 0
  inputEntries : Nat := 0
  outputEntries : Nat := 0
  packedBytes : Nat := 0
  traceNodes : Nat := 0
  processedRows : Nat := 0
  reductions : Nat := 0
  zeroRows : Nat := 0
  deriving Repr, BEq, Inhabited

/-- Shared row provenance. Inputs are numbered reducers first, then targets.
Every operation refers only to earlier nodes. This is derivation data, not a
complete basis certificate and not a proof of any Gröbner property. Interpret
`addScaled l r c` as `l + c*r` and `scale r c` as `c*r` in the call's field
and fixed column map. Coefficients lie in `[1,p)`. The trace borrows that field
identity from the call; it is not a standalone serialized certificate. Nodes
for rows reducing to zero may be unreferenced by the output pivots. -/
inductive RowOp where
  | input (row : Nat)
  | addScaled (left right : Nat) (coefficient : UInt64)
  | scale (row : Nat) (coefficient : UInt64)
  deriving Repr, BEq

/-- A monic sparse pivot, optionally referring to its derivation. Target pivots
are precisely the rows adding dimension beyond the reducer row space.  Layout mirrored in `HexGroebner/ffi/matrix_eliminate.c`. -/
structure Pivot where
  row : SparseRow
  fromTarget : Bool
  derivation : Option Nat
  /-- Scalar applied to the residual row when making this pivot monic. Retaining
  it allows a one-target triangular solve to return the unscaled remainder. -/
  multiplier : UInt64 := 1
  /-- Maximum propagated sugar label of the rows actually used in this pivot. -/
  sugar : Nat := 0
  deriving Inhabited

/-- Echelon rows in increasing pivot-column order, without permuting columns.
The reducer rank separates the reducer subspace from new target information.
No reduced-basis or polynomial-ideal conclusion is attached to this result.  Layout mirrored in `HexGroebner/ffi/matrix_eliminate.c`. -/
structure Echelon where
  rows : Array Pivot
  reducerRank : Nat
  trace : Array RowOp

/-- An unscaled target remainder after reduction by the supplied reducer rows.
Targets are independent: none becomes a reducer for another target. Empty rows
retain their input position and optional zero derivation.  Layout mirrored in `HexGroebner/ffi/matrix_eliminate.c`. -/
structure RemainderRow where
  row : SparseRow
  derivation : Option Nat
  sugar : Nat
  deriving Inhabited

/-- Independent target remainders in input order, including zeros. -/
structure Remainders where
  rows : Array RemainderRow
  trace : Array RowOp

/-- Bounded independent triangular solves, retaining charged counters on failure. -/
structure RemainderResult where
  result : Except MatrixError Remainders
  stats : MatrixStats

/-- Explicit success/failure with the counters charged against the caller's
allowance. Exhaustion exposes no incomplete matrix as a completed answer. -/
structure MatrixResult where
  result : Except MatrixError Echelon
  stats : MatrixStats

private abbrev Work := ExceptT MatrixError (StateM MatrixStats)

private def charge (resource : Resource) (amount limit : Nat)
    (getCount : MatrixStats → Nat) (setCount : MatrixStats → Nat → MatrixStats) : Work Unit := do
  let stats ← get
  let count := getCount stats + amount
  if count > limit then throw (.exhausted resource)
  set (setCount stats count)

private def work (limits : MatrixLimits) (amount : Nat) : Work Unit :=
  charge .work amount limits.work (·.work) fun s n => { s with work := n }

private def packedBytes (limits : MatrixLimits) (amount : Nat) : Work Unit :=
  charge .packedBytes amount limits.packedBytes (·.packedBytes)
    fun s n => { s with packedBytes := n }

private def validate (field : PrimeField) (limits : MatrixLimits)
    (columns index : Nat) (row : SparseRow) : Work Unit := do
  work limits 1
  if row.columns.size % 4 != 0 || row.coefficients.size != row.size * field.width.bytes then
    throw (.rowLength index)
  charge .inputEntries row.size limits.inputEntries (·.inputEntries)
    fun s n => { s with inputEntries := n }
  packedBytes limits (row.columns.size + row.coefficients.size)
  work limits row.size
  let mut previous : Option Nat := none
  for i in [:row.size] do
    let column := (Packed.read .u32 row.columns i).toNat
    if column ≥ columns then throw (.column index i)
    if let some p := previous then
      if column ≤ p then throw (.column index i)
    let c := Packed.read field.width row.coefficients i
    if c == 0 || c ≥ field.modulus then throw (.coefficient index i)
    previous := some column

private def zeros (size : Nat) : ByteArray := Id.run do
  let mut data := ByteArray.emptyWithCapacity size
  for _ in [:size] do data := data.push 0
  return data

private def record (limits : MatrixLimits) (enabled : Bool)
    (trace : Array RowOp) (op : RowOp) : Work (Array RowOp × Option Nat) := do
  if !enabled then return (trace, none)
  charge .traceNodes 1 limits.traceNodes (·.traceNodes) fun s n => { s with traceNodes := n }
  packedBytes limits 64
  let index := trace.size
  return (trace.push op, some index)

/-- Square-and-multiply, with each multiply charged to the parent allowance.
The modulus bit length bounds the loop; `PrimeField.bound` makes it at most
31 bits. Fermat inversion also covers characteristic two. -/
private def inverse (field : PrimeField) (ctx : BarrettCtx field.modulus)
    (limits : MatrixLimits) (a : UInt64) : Work UInt64 := do
  if a == 1 then return 1
  let mut exponent := field.modulus.toNat - 2
  let mut a := a
  let mut value : UInt64 := 1
  for _ in [:field.modulus.toNat.log2 + 1] do
    if exponent == 0 then break
    if exponent % 2 == 1 then
      work limits 1
      value := ctx.mulMod value a
    exponent := exponent / 2
    if exponent > 0 then
      work limits 1
      a := ctx.mulMod a a
  return value

/-- Install a known sparse reducer without scattering or scanning empty columns.
Its free leading column guarantees independence of the preceding pivots; its
tail need not be reduced to maintain forward echelon form. -/
private def scaleSparse (field : PrimeField) (ctx : BarrettCtx field.modulus)
    (limits : MatrixLimits) (row : SparseRow) (inverse : UInt64) : Work SparseRow := do
  charge .outputEntries row.size limits.outputEntries (·.outputEntries)
    fun s n => { s with outputEntries := n }
  packedBytes limits (row.columns.size + row.coefficients.size)
  if inverse == 1 then return row
  work limits row.size
  let width := field.width
  let mut coefficients := ByteArray.emptyWithCapacity row.coefficients.size
  for i in [:row.size] do
    coefficients := Packed.push width coefficients
      (ctx.mulMod (Packed.read width row.coefficients i) inverse)
  return ⟨row.columns, coefficients⟩

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
  for i in [:reducers.size] do validate field limits columns i reducers[i]!
  for i in [:targets.size] do validate field limits columns (reducers.size + i) targets[i]!
  let width := field.width
  let workspaceBytes := columns * (width.bytes + 4)
  -- Keep all allocation sizes inside both the logical limit and the platform's
  -- addressable range, even on 32-bit hosts. Do not narrow unchecked products.
  if workspaceBytes ≥ USize.size then throw .dimensions
  packedBytes limits workspaceBytes
  work limits workspaceBytes
  let mut dense := zeros (columns * width.bytes)
  -- A slot stores pivot index + 1. Zero means no pivot, never monomial identity.
  let mut slots := zeros (columns * 4)
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

/-- Complete matrix outcome used by the optional bulk provider.  Layout mirrored in `HexGroebner/ffi/matrix_eliminate.c`. -/
structure Result where
  result : Except MatrixError (Echelon × Array RemainderRow)
  stats : MatrixStats

/-- Deterministic reference for an untraced whole matrix operation. -/
def reference (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool) : Result :=
  let (result, stats) :=
    (eliminate field limits columns reducers targets false sugars true independent).run {}
  ⟨result, stats⟩

/-- Known reducers have distinct leading columns. The conservative work bound
uses `65 * rows` for row visits and inversion products, `2 * entries` for
validation, sparse scaling and scattering, and `columns * (width + 4)` for
workspace initialization. For each target, `entries` covers known-pivot updates,
`(targets + 3) * columns` covers target-pivot updates, dense scanning, gathering
and normalization, and 64 allows inversion. A pivot is used at most once per
target because scanning advances through its leading column. The final
`columns` covers pivot ordering. These deliberately overlapping bounds ensure
at most `2^20` work on every supported successful reference computation. -/
def fits (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) : Bool := Id.run do
  let rows := reducers.size + targets.size
  if USize.size != 2^64 then return false
  if columns > 4096 || reducers.size > 1024 || targets.size > 64 ||
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
  if bound > 2^20 then return false
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
    if result.result.isOk && result.stats.work ≤ 2^20 then some result else none

/-- On the 64-bit ABI, `PrimeField` is passed as its `UInt64` modulus; limits,
column count, row arrays and sugars are borrowed Lean objects, and `independent`
is an unboxed Boolean. `Result` holds an `Except` matrix/remainder pair and eight
`Nat` counters. Native code returns `some` only for a complete successful
reference result, including exact rows, aliases, sugars and counters. It admits
at most 4096 columns, 1024 known reducers and 64 targets, with distinct known
leading columns and at most `2^20` charged work. Large limits saturate above all
possible accepted totals; non-machine-size sugars use portable continuation.

The matrix owns its dense workspace; all inputs remain immutable, including
shared reducer/target arrays. Unsupported shapes return `none` without changing
inputs, and the ordinary reference runs after the native frame. A declined
attempt's physical work is unreported but bounded by the remaining allowance
and `2^20`. By `fits`'s bound, a decline after charged work implies reference
failure; F4 terminates that computation/resumption at the matrix failure, so
there is at most one such speculative failure per computation or resumption. -/
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

/-- Select bounded bulk elimination for untraced native calls. Deferred calls
retain the ordinary matrix operation and its exact failure/counter boundary. -/
def run (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (provenance : Bool) (sugars : Array Nat)
    (native independent : Bool) : Result :=
  if native && !provenance then
    match attempt field limits columns reducers targets sugars independent with
    | some result => result
    | none => reference field limits columns reducers targets sugars independent
  else
    let (result,stats) :=
      (eliminate field limits columns reducers targets provenance sugars native independent).run {}
    ⟨result,stats⟩

/-- The optimized untraced route has exactly the deterministic reference result. -/
theorem run_spec (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool) :
    run field limits columns reducers targets false sugars true independent =
      reference field limits columns reducers targets sugars independent := by
  unfold run attempt
  change (match attemptPortable field limits columns reducers targets sugars independent with
    | some result => result
    | none => reference field limits columns reducers targets sugars independent) = _
  have h := attemptPortable_spec field limits columns reducers targets sugars independent
  cases hx : attemptPortable field limits columns reducers targets sugars independent with
  | none => rfl
  | some result => simpa only [hx, Option.getD_some] using h

end Elimination

/-- Deterministic finite-prime-field Macaulay elimination, with sparse reducers,
packed dense accumulation, monic output, stable columns and optional provenance.
`native := false` retains scalar Lean updates; the default uses bounded native
chunks with identical rows, provenance and counters. Untraced 64-bit calls first
try a complete frame bounded by 4096 columns, 1024 reducers, 64 targets and
`2^20` work; cancellation is observed between calls. Input rows must be canonical
and use the field's coefficient width. Limits cover
validation and nested arithmetic as well as elimination. Successful rows span
the input row space; they are echelon, not reduced echelon. The polynomial layer
is responsible for supplying columns in the chosen lawful monomial order. -/
def eliminateWith (field : PrimeField) (limits : MatrixLimits)
    (columns : Nat) (reducers targets : Array SparseRow) (provenance : Bool := false)
    (sugars : Array Nat := #[]) (native : Bool := true) : MatrixResult :=
  let output := Elimination.run field limits columns reducers targets provenance sugars native false
  ⟨output.result.map Prod.fst, output.stats⟩

/-- Reduce each target by the same reducer echelon space, preserving its scalar
and input position. Targets never reduce each other. Validation, sparse reducer
installation, bounded native updates and allowances are shared with elimination.
Untraced 64-bit calls use the same optional `2^20`-work matrix frame and shape
caps as `eliminateWith`; other cases retain bounded scan/gather chunks.
This is a linear triangular solve; polynomial normal-form claims additionally
require the symbolic closure and a Gröbner basis. -/
def reduceRowsWith (field : PrimeField) (limits : MatrixLimits)
    (columns : Nat) (reducers targets : Array SparseRow) (provenance : Bool := false)
    (sugars : Array Nat := #[]) (native : Bool := true) : RemainderResult :=
  let output := Elimination.run field limits columns reducers targets provenance sugars native true
  ⟨output.result.map (fun (e, rows) => ⟨rows, e.trace⟩), output.stats⟩

end Hex.Groebner
