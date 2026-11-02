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

private def consumeFrame (input : Input) (result : Elimination.Result) :
    Bool × Array (Array (Nat × UInt64) × Bool × UInt64 × Nat) × Array Nat :=
  match result.result with
  | .error _ => (false,#[],#[])
  | .ok (e,r) =>
    (e.reducerRank == input.reducers.size && e.rows.size == input.columns && e.trace.isEmpty && r.isEmpty,
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

end Hex.Groebner.Bench
