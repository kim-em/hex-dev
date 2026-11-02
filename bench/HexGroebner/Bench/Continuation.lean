/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Bench.Cauchy
import HexGroebnerStateNative
import HexGroebner.Elimination
import LeanBench

namespace Hex.Groebner.Bench

private def frameField : PrimeField :=
  ⟨65537,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩

/-- The same Cauchy matrix and packing for both matrix implementations. -/
def prepareFrame (n : Nat) : Input := prepareOver frameField n

private def consumeFrame (input : Input) (result : Elimination.Result) (rows := input.columns) :
    Bool × Array (Array (Nat × UInt64) × Bool × UInt64 × Nat) × Array Nat :=
  match result.result with
  | .error _ => (false,#[],#[])
  | .ok (e,r) =>
    (e.reducerRank == input.reducers.size && e.rows.size == rows && e.trace.isEmpty && r.isEmpty,
      e.rows.map fun row => (row.row.entries frameField,row.fromTarget,row.multiplier,row.sugar),
      let s := result.stats
      #[s.work,s.inputEntries,s.outputEntries,s.packedBytes,s.traceNodes,
        s.processedRows,s.reductions,s.zeroRows])

/-- Validation, allocation, bounded native continuation and full output hashing. -/
def matrixFrame (input : Input) :=
  let (result,stats) := MatrixState.finishWith 64
    (MatrixState.start frameField { work := 1000000000 } input.columns
      input.reducers input.targets #[] false) true
  consumeFrame input ⟨result,stats⟩

/-- Identical deterministic elimination using the existing Lean matrix frame. -/
def matrixFrameReference (input : Input) :=
  consumeFrame input (Elimination.reference frameField { work := 1000000000 }
    input.columns input.reducers input.targets #[] false)

#guard (matrixFrame (prepareFrame 0)).1
#guard (matrixFrame (prepareFrame 1)).1
#guard (#[16,64,128,256,512,1024].all fun n =>
  let input := prepareFrame n
  let native := matrixFrame input
  let reference := matrixFrameReference input
  native.1 && reference.1 && native == reference)

-- Cauchy elimination performs (n^3-n)/3 sparse entry updates. Validation,
-- workspace initialization, packing of outputs and full hashing cost O(n^2).
setup_benchmark matrixFrame n => n*n*n
  with prep := prepareFrame
  where {
    paramFloor := 64
    paramCeiling := 1024
    paramSchedule := .custom #[64,128,256,512,1024]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }

-- The same updates and complete outputs give the same cubic model. Its
-- ordinary Lean frame uses the existing bounded native scan/gather kernels.
setup_benchmark matrixFrameReference n => n*n*n
  with prep := prepareFrame
  where {
    paramFloor := 64
    paramCeiling := 1024
    paramSchedule := .custom #[64,128,256,512,1024]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }

/-- Distinct known pivots, sparse tails and eight targets with one new pivot.
These shapes are accepted by the existing whole-matrix native provider. -/
def prepareSparseFrame (n : Nat) : Input := Id.run do
  let half := n/2
  let mut reducers := #[]
  for i in [:half] do
    let columns := Packed.push .u32 (Packed.push .u32 {} i.toUInt64) (half+i).toUInt64
    let coefficients := Packed.push frameField.width
      (Packed.push frameField.width {} 1) 1
    reducers := reducers.push ⟨columns,coefficients⟩
  let mut targets := #[]
  for i in [:8] do
    let columns := Packed.push .u32
      (Packed.push .u32 (Packed.push .u32 {} i.toUInt64) (half+i).toUInt64) (n-1).toUInt64
    let coefficients := Packed.push frameField.width
      (Packed.push frameField.width (Packed.push frameField.width {} 1) 1) 1
    targets := targets.push ⟨columns,coefficients⟩
  return ⟨n,reducers,targets⟩

/-- Sparse known-pivot installation in the bounded continuation. -/
def matrixSparse (input : Input) :=
  let (result,stats) := MatrixState.finishWith 64
    (MatrixState.start frameField { work := 1000000000 } input.columns
      input.reducers input.targets #[] false) true
  consumeFrame input ⟨result,stats⟩ (input.reducers.size+1)

/-- Identical sparse input using the ordinary Lean matrix frame. -/
def matrixSparseReference (input : Input) :=
  consumeFrame input (Elimination.reference frameField { work := 1000000000 }
    input.columns input.reducers input.targets #[] false) (input.reducers.size+1)

/-- Identical sparse input using the existing whole-matrix native provider. -/
def matrixSparseBulk (input : Input) :=
  consumeFrame input (Elimination.run frameField { work := 1000000000 }
    input.columns input.reducers input.targets false #[] true false) (input.reducers.size+1)

#guard (#[64,128,256,512,1024].all fun n =>
  let input := prepareSparseFrame n
  let candidate := matrixSparse input
  let reference := matrixSparseReference input
  let bulk := matrixSparseBulk input
  Elimination.fits frameField { work := 1000000000 } input.columns
    input.reducers input.targets #[] &&
    (Elimination.attempt frameField { work := 1000000000 } input.columns
      input.reducers input.targets #[] false).isSome &&
    candidate.1 && reference.1 && bulk.1 && candidate == reference && bulk == reference)

-- There are n/2 two-entry known rows and eight targets. Row installation,
-- validation and output consumption are linear in n. Each target scans at
-- most n columns, and there are a fixed eight of them, so the model is O(n).
setup_benchmark matrixSparse n => n
  with prep := prepareSparseFrame
  where {
    paramFloor := 64
    paramCeiling := 1024
    paramSchedule := .custom #[64,128,256,512,1024]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }

-- The identical fixed-eight-target sparse work is linear in the column count.
setup_benchmark matrixSparseReference n => n
  with prep := prepareSparseFrame
  where {
    paramFloor := 64
    paramCeiling := 1024
    paramSchedule := .custom #[64,128,256,512,1024]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }

-- Bulk admission succeeds at every registered size; its work is also linear.
setup_benchmark matrixSparseBulk n => n
  with prep := prepareSparseFrame
  where {
    paramFloor := 64
    paramCeiling := 1024
    paramSchedule := .custom #[64,128,256,512,1024]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 32.0
  }

end Hex.Groebner.Bench
