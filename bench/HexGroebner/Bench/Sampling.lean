/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Bench.Cauchy
import HexGroebnerStateNative
import LeanBench

namespace Hex.Groebner.Bench

private def samplingField : PrimeField :=
  ⟨2147483647,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩

/-- Distinct monic reducers e_i-e_(n+i), with one target already in their span.
The number of targets and random trials is constant while known metadata grows. -/
def prepareSampling (n : Nat) : Input := Id.run do
  let mut reducers := #[]
  for i in [:n] do
    let columns := Packed.push .u32 (Packed.push .u32 {} i.toUInt64) (n+i).toUInt64
    let coefficients := Packed.push samplingField.width
      (Packed.push samplingField.width {} 1) (samplingField.modulus-1)
    reducers := reducers.push ⟨columns,coefficients⟩
  return ⟨2*n,reducers,reducers.extract 0 1⟩

private def samplingRun (native : Bool) (input : Input) :
    Bool × Array (Array (Nat × UInt64)) × Array Nat × UInt64 := Id.run do
  let limits : MatrixLimits := { work := 1000000000 }
  let mut state := Sampling.start samplingField input.columns input.reducers input.targets
    (Hex.Rand.ofSeed 0) {} #[] native
  for _ in [:3*input.reducers.size+64] do
    state := Sampling.advance limits 64 state
    if state.phase == .done || state.failure.isSome then break
  let rows := state.pivots.map fun pivot =>
    (SparseRow.mk pivot.columns pivot.coefficients).entries samplingField
  let s := state.statistics
  let trials := if input.targets.isEmpty then 0 else 3
  return (state.candidate?.isSome && state.rows.isEmpty &&
      state.pivots.size == input.reducers.size && s.combinations == trials &&
      s.matrix.zeroRows == trials && s.randomWords == trials,
    rows,#[s.matrix.work,s.matrix.inputEntries,s.matrix.outputEntries,s.matrix.packedBytes,
      s.matrix.processedRows,s.matrix.reductions,s.matrix.zeroRows,s.randomWords,
      s.combinationEntries,s.combinations],state.random.state)

/-- Validation, known-pivot installation, three sampled zero reductions and
complete decoded-pivot/counter hashing. Preparation is excluded. -/
def samplingKnown (input : Input) := samplingRun true input

/-- The same operation and full output using scalar Lean primitives. -/
def samplingKnownPortable (input : Input) := samplingRun false input

#guard (#[128,256,512,1024,2048,4096,8192].all fun n =>
  let input := prepareSampling n
  let native := samplingKnown input
  native.1 && native == samplingKnownPortable input)

-- Two entries per reducer, 2*n workspace columns, three fixed target trials
-- and hashing all n decoded pivots give a linear model with unique workspace.
setup_benchmark samplingKnown n => n
  with prep := prepareSampling
  where {
    paramFloor := 128
    paramCeiling := 8192
    paramSchedule := .custom #[128,256,512,1024,2048,4096,8192]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

-- Scalar primitives visit the same two entries per reducer, 2*n workspace
-- columns, three fixed target trials and all n decoded pivots: linear in n.
setup_benchmark samplingKnownPortable n => n
  with prep := prepareSampling
  where {
    paramFloor := 128
    paramCeiling := 8192
    paramSchedule := .custom #[128,256,512,1024,2048,4096,8192]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

end Hex.Groebner.Bench
