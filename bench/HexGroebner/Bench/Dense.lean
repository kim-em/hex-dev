/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.NativeDense
import HexGroebner.Packed
import LeanBench

namespace Hex.Groebner.Bench

private def denseModulus : UInt64 := 2147483647

/-- One half-full pivot and an already charged pending reduction. -/
structure DenseInput where
  columns : Nat
  source : Native.Scan.Pivot
  row : Native.Dense.Row denseModulus columns
  slots : ByteArray
  initial : Native.Scan.State

instance : Hashable DenseInput where
  hash input := hash (input.columns,
    (input.source.columns,input.source.coefficients,input.source.sugar),
    (input.row.source.columns,input.row.source.coefficients,input.row.source.sugar,
      input.row.dense,input.row.first,input.row.size),input.slots,
    (input.initial.dense,input.initial.column,input.initial.last,input.initial.chargedUntil,
      input.initial.leading,input.initial.pending,input.initial.entry,input.initial.sugar,input.initial.factor))

/-- Materialization and target construction are excluded from update timing. -/
def prepareDenseShape (n shape : Nat) : DenseInput := Id.run do
  let column := fun i => if shape == 0 then i else if shape == 1 then i+i/3 else 2*i
  let columns := if shape == 2 then 2*n else column (n-1)+1
  let mut ids : ByteArray := {}
  let mut coefficients : ByteArray := {}
  let mut dense := Native.Dense.zeros (4*columns)
  for i in [:n] do
    ids := Packed.push .u32 ids (column i).toUInt64
    coefficients := Packed.push .u32 coefficients (i+1).toUInt64
  for i in [:columns] do dense := Native.write dense 4 (4*i) (i+1)
  let source : Native.Scan.Pivot := ⟨ids,coefficients,11⟩
  let prepared := Native.Dense.prepare denseModulus columns source 100000 100000
  return {
    columns := columns
    source := source
    row := prepared.row
    slots := Native.Dense.zeros (4*columns)
    initial := {
      dense := dense
      column := 0
      last := columns-1
      chargedUntil := columns
      pending := 1
      factor := 17
      sugar := 11 } }

/-- Half-full, three-quarter-full and full packed pivot spans. -/
def prepareDensePivot (n : Nat) := prepareDenseShape n 2
def prepareThreeQuarters (n : Nat) := prepareDenseShape n 1
def prepareFullPivot (n : Nat) := prepareDenseShape n 0

private def consumeDense (input : DenseInput) (result : Native.Scan.Result) :=
  (result.status == 0 && result.state.pending == 1 && result.state.entry == input.source.columns.size/4 &&
      result.work == 0 && result.reductions == 0 && result.events.isEmpty,
    result.state.dense,
    #[result.state.column,result.state.last,result.state.chargedUntil,result.state.leading,
      result.state.pending,result.state.entry,result.state.sugar,result.state.factor.toNat,
      result.work,result.reductions,result.traceNodes,result.status.toNat])

/-- Update all pending sparse entries using checked dense optimization data. -/
def densePivot (input : DenseInput) := consumeDense input
  (Native.Dense.transition denseModulus input.columns input.slots #[input.row]
    input.initial (input.source.columns.size/4) 100000 0 false)

/-- Identical pending reduction through the ordinary sparse SIMD kernel. -/
def sparsePivot (input : DenseInput) := consumeDense input
  (Native.Scan.transition denseModulus input.slots #[input.source]
    input.initial (input.source.columns.size/4) 100000 0 false)

/-- The kernel-reducible scalar semantics of the same pending reduction. -/
def densePivotPortable (input : DenseInput) := consumeDense input
  (Native.Dense.portable denseModulus input.columns input.slots #[input.row]
    input.initial (input.source.columns.size/4) 100000 0 false)

#guard (#[128,256,512,1024,2048,4096].all fun n => Id.run do
  let input := prepareDensePivot n
  let result := densePivot input
  if !result.1 || input.row.dense.isEmpty || result != sparsePivot input ||
      result != densePivotPortable input then return false
  for i in [:input.columns] do
    let expected := if i%2 == 0 then
      (i+1+2147483647-(17*(i/2+1))%2147483647)%2147483647 else i+1
    if Native.read result.2.1 4 (4*i) != expected then return false
  return true)

private def updateBatch (native : Bool) (input : DenseInput) := Id.run do
  let mut state := input.initial
  let mut valid := true
  for _ in [:64] do
    let result := if native then
      Native.Dense.transition denseModulus input.columns input.slots #[input.row]
        state (input.source.columns.size/4) 100000 0 false
      else Native.Scan.transition denseModulus input.slots #[input.source]
        state (input.source.columns.size/4) 100000 0 false
    valid := valid && (consumeDense input result).1
    state := { result.state with pending := 1,entry := 0 }
  return (valid,state.dense)

/-- Sixty-four owned updates, with complete final output consumed once. -/
def denseBatch (input : DenseInput) := updateBatch true input
def sparseBatch (input : DenseInput) := updateBatch false input
def denseFull (input : DenseInput) := denseBatch input
def sparseFull (input : DenseInput) := sparseBatch input
def denseThreeQuarters (input : DenseInput) := denseBatch input
def sparseThreeQuarters (input : DenseInput) := sparseBatch input

#guard (#[128,256,512,1024,2048,4096].all fun n => Id.run do
  for shape in [:3] do
    let input := prepareDenseShape n shape
    let result := denseBatch input
    if !result.1 || input.row.dense.isEmpty || result != sparseBatch input ||
        densePivot input != densePivotPortable input then return false
    let mut entry := 0
    for i in [:input.columns] do
      let present := entry < n && Native.read input.source.columns 4 (4*entry) == i
      let expected := if present then
        (i+1+2147483647-(64*17*(entry+1))%2147483647)%2147483647 else i+1
      if Native.read result.2 4 (4*i) != expected then return false
      if present then entry := entry+1
  return true)

-- O(n): update a span shorter than 2*n and consume every output byte.
setup_benchmark densePivot n => n
  with prep := prepareDensePivot
  where {
    paramFloor := 128
    paramCeiling := 4096
    paramSchedule := .custom #[128,256,512,1024,2048,4096]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

-- O(n): inspect n sparse entries and consume the same 2*n-column output.
setup_benchmark sparsePivot n => n
  with prep := prepareDensePivot
  where {
    paramFloor := 128
    paramCeiling := 4096
    paramSchedule := .custom #[128,256,512,1024,2048,4096]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

-- O(n): scalar updates visit n entries and hash every output byte.
setup_benchmark densePivotPortable n => n
  with prep := prepareDensePivot
  where {
    paramFloor := 128
    paramCeiling := 4096
    paramSchedule := .custom #[128,256,512,1024,2048,4096]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

-- O(n): 64 fixed owned updates of a span at most 2*n and full output hashing.
setup_benchmark denseBatch n => n
  with prep := prepareDensePivot
  where {
    paramFloor := 128
    paramCeiling := 4096
    paramSchedule := .custom #[128,256,512,1024,2048,4096]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

-- O(n): 64 fixed owned updates of a span at most 2*n and full output hashing.
setup_benchmark sparseBatch n => n
  with prep := prepareDensePivot
  where {
    paramFloor := 128
    paramCeiling := 4096
    paramSchedule := .custom #[128,256,512,1024,2048,4096]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

-- O(n): 64 fixed owned updates of a span at most 2*n and full output hashing.
setup_benchmark denseFull n => n
  with prep := prepareFullPivot
  where {
    paramFloor := 128
    paramCeiling := 4096
    paramSchedule := .custom #[128,256,512,1024,2048,4096]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

-- O(n): 64 fixed owned updates of a span at most 2*n and full output hashing.
setup_benchmark sparseFull n => n
  with prep := prepareFullPivot
  where {
    paramFloor := 128
    paramCeiling := 4096
    paramSchedule := .custom #[128,256,512,1024,2048,4096]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

-- O(n): 64 fixed owned updates of a span at most 2*n and full output hashing.
setup_benchmark denseThreeQuarters n => n
  with prep := prepareThreeQuarters
  where {
    paramFloor := 128
    paramCeiling := 4096
    paramSchedule := .custom #[128,256,512,1024,2048,4096]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

-- O(n): 64 fixed owned updates of a span at most 2*n and full output hashing.
setup_benchmark sparseThreeQuarters n => n
  with prep := prepareThreeQuarters
  where {
    paramFloor := 128
    paramCeiling := 4096
    paramSchedule := .custom #[128,256,512,1024,2048,4096]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

end Hex.Groebner.Bench
