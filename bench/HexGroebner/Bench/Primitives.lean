/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Elimination
import LeanBench

namespace Hex.Groebner.Bench

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

/-- All zero-buffer bytes are consumed by structural hashing. -/
def matrixZeros (n : Nat) := Matrix.zerosWith n

/-- The original checked byte-by-byte zero-buffer model. -/
def matrixZerosReference (n : Nat) := Matrix.zeros n

#guard (#[0,1,64,256,1024,4096,16384,65536].all fun n =>
  let row := prepareValidation n
  (matrixValidate row).1 && matrixValidate row == matrixValidateReference row &&
    (matrixZeros n).data == (matrixZerosReference n).data)

-- Each entry is inspected once. Hashing the fixed-size result counters is O(1).
setup_benchmark matrixValidate n => n
  with prep := prepareValidation
  where {
    paramFloor := 64
    paramCeiling := 65536
    paramSchedule := .custom #[64,256,1024,4096,16384,65536]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }

-- O(n): the original validator visits n entries once and consumes eight counters.
setup_benchmark matrixValidateReference n => n
  with prep := prepareValidation
  where {
    paramFloor := 64
    paramCeiling := 65536
    paramSchedule := .custom #[64,256,1024,4096,16384,65536]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }

-- Allocation/zeroing and complete byte consumption each cost O(n).
setup_benchmark matrixZeros n => n
  where {
    paramFloor := 64
    paramCeiling := 65536
    paramSchedule := .custom #[64,256,1024,4096,16384,65536]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }

-- Portable allocation/zeroing and identical complete byte consumption cost O(n).
setup_benchmark matrixZerosReference n => n
  where {
    paramFloor := 64
    paramCeiling := 65536
    paramSchedule := .custom #[64,256,1024,4096,16384,65536]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }

end Hex.Groebner.Bench
