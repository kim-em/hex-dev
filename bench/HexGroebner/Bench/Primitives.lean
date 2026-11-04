/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Elimination
import LeanBench

namespace Hex.Groebner.Bench

private def binaryField : PrimeField :=
  ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩

/-- Dense ordinary-F2 matrices with distinct known leading columns and random
target rows. Preparation is quadratic and remains outside the timed call. -/
def prepareBinary (n : Nat) : Nat × Array SparseRow × Array SparseRow := Id.run do
  let columns := 2*n
  let mut reducers := #[]
  let mut targets := #[]
  let mut state : UInt64 := 10987
  for i in [:2*n] do
    let mut support : ByteArray := {}
    let mut coefficients : ByteArray := {}
    for j in [:columns] do
      state := state*6364136223846793005+1442695040888963407
      let keep := if i < n then j == i || (j ≥ n && state >>> 63 != 0)
        else state >>> 63 != 0
      if keep then
        support := Packed.push .u32 support j.toUInt64
        coefficients := coefficients.push 1
    let row : SparseRow := ⟨support,coefficients⟩
    if i < n then reducers := reducers.push row else targets := targets.push row
  return (columns,reducers,targets)

private def binaryResult (packed : Bool) (input : Nat × Array SparseRow × Array SparseRow) :
    Bool × Array (Bool × Array (Nat × UInt64) × Nat) × Array Nat :=
  let result := eliminateWith binaryField { work := 1000000000,binaryPivots := packed }
    input.1 input.2.1 input.2.2
  let stats := result.stats
  let counters := #[stats.work,stats.inputEntries,stats.outputEntries,stats.packedBytes,
    stats.traceNodes,stats.processedRows,stats.reductions,stats.zeroRows]
  match result.result with
  | .ok echelon => (echelon.reducerRank == input.2.1.size,
      echelon.rows.map (fun (pivot : Pivot) =>
        (pivot.fromTarget,pivot.row.entries binaryField,pivot.sugar)),counters)
  | .error _ => (false,#[],counters)

/-- Validation, private bitmap construction, elimination and complete decoded
output/counter consumption; no polynomial Boolean-quotient relations apply. -/
def binaryEliminate (input : Nat × Array SparseRow × Array SparseRow) :=
  binaryResult true input

/-- Identical input/output through the existing sparse/native-phase route. -/
def binaryEliminateSparse (input : Nat × Array SparseRow × Array SparseRow) :=
  binaryResult false input

#guard (#[1,2,4,8].all fun n =>
  let input := prepareBinary n
  (binaryEliminate input).1 && binaryEliminate input == binaryEliminateSparse input)

-- Dense elimination is O(n³); preparation and complete output hashing are O(n²).
setup_benchmark binaryEliminate n => n^3
  with prep := prepareBinary
  where {
    paramFloor := 32
    paramCeiling := 512
    paramSchedule := .custom #[32,64,128,256,512]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }

-- O(n³) sparse elimination, with O(n²) preparation and complete output hashing.
setup_benchmark binaryEliminateSparse n => n^3
  with prep := prepareBinary
  where {
    paramFloor := 32
    paramCeiling := 512
    paramSchedule := .custom #[32,64,128,256,512]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }

private def primitiveField : PrimeField :=
  ⟨65537,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩

/-- Dense valid packed rows with unit coefficients, prepared outside timing. -/
def prepareValidation (n : Nat) : SparseRow := Id.run do
  let mut row : SparseRow := {}
  for i in [:n] do
    row := {
      columns := Packed.push .u32 row.columns i.toUInt64
      coefficients := Packed.push primitiveField.width row.coefficients 1 }
  return row

private def consumeValidation (result : Except MatrixError Unit × MatrixStats) :=
  (result.1.isOk,let s := result.2
    #[s.work,s.inputEntries,s.outputEntries,s.packedBytes,s.traceNodes,
      s.processedRows,s.reductions,s.zeroRows])

/-- Complete validity and charged-prefix consumption through the native provider. -/
def matrixValidate (row : SparseRow) :=
  consumeValidation ((Matrix.validateWith primitiveField {} row.size 0 row).run {})

/-- The same original validator, independent of the new row-validation primitive. -/
def matrixValidateReference (row : SparseRow) :=
  consumeValidation ((Matrix.validate primitiveField {} row.size 0 row).run {})

/-- Short rows with a large ambient column count, without a wide dense workspace. -/
def matrixValidateWide (row : SparseRow) :=
  consumeValidation ((Matrix.validateWith primitiveField {} 4294967295 0 row).run {})

/-- The same wide geometry through the original portable validator. -/
def matrixValidateWideReference (row : SparseRow) :=
  consumeValidation ((Matrix.validate primitiveField {} 4294967295 0 row).run {})

#guard (#[1,4,16,64,256,1024,4096,16384,65536].all fun n =>
  let row := prepareValidation n
  (matrixValidateWide row).1 && matrixValidateWide row == matrixValidateWideReference row)

/-- All zero-buffer bytes are consumed by structural hashing. -/
def matrixZeros (n : Nat) := Matrix.zerosWith n

/-- The original checked byte-by-byte zero-buffer model. -/
def matrixZerosReference (n : Nat) := Matrix.zeros n

#guard (#[0,1,4,16,64,256,1024,4096,16384,65536].all fun n =>
  let row := prepareValidation n
  (matrixValidate row).1 && matrixValidate row == matrixValidateReference row &&
    (matrixZeros n).data == (matrixZerosReference n).data)

-- Each entry is inspected once. Hashing the fixed-size result counters is O(1).
setup_benchmark matrixValidate n => n
  with prep := prepareValidation
  where {
    paramFloor := 1
    paramCeiling := 65536
    paramSchedule := .custom #[1,4,16,64,256,1024,4096,16384,65536]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }

-- O(n): the original validator visits n entries once and consumes eight counters.
setup_benchmark matrixValidateReference n => n
  with prep := prepareValidation
  where {
    paramFloor := 1
    paramCeiling := 65536
    paramSchedule := .custom #[1,4,16,64,256,1024,4096,16384,65536]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }

-- Allocation/zeroing and complete byte consumption each cost O(n).
setup_benchmark matrixZeros n => n
  where {
    paramFloor := 1
    paramCeiling := 65536
    paramSchedule := .custom #[1,4,16,64,256,1024,4096,16384,65536]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }

-- Portable allocation/zeroing and identical complete byte consumption cost O(n).
setup_benchmark matrixZerosReference n => n
  where {
    paramFloor := 1
    paramCeiling := 65536
    paramSchedule := .custom #[1,4,16,64,256,1024,4096,16384,65536]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }


-- O(n): ambient column count is metadata; validation reads n sparse entries.
setup_benchmark matrixValidateWide n => n
  with prep := prepareValidation
  where {
    paramFloor := 1
    paramCeiling := 65536
    paramSchedule := .custom #[1,4,16,64,256,1024,4096,16384,65536]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }

-- O(n): the original validator reads the same n entries and exact counters.
setup_benchmark matrixValidateWideReference n => n
  with prep := prepareValidation
  where {
    paramFloor := 1
    paramCeiling := 65536
    paramSchedule := .custom #[1,4,16,64,256,1024,4096,16384,65536]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }

end Hex.Groebner.Bench
