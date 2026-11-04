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

/-- Known rows have an identity leading block and deterministic dense tails.
Each target is their shared sum plus a distinct free-column unit. Preparation
is excluded; the known projection is therefore independently known exactly. -/
structure ProjectionInput where
  n : Nat
  reducers : Array SparseRow
  targets : Array SparseRow
  deriving Hashable

def prepareProjection (n : Nat) : ProjectionInput := Id.run do
  let n := max 64 n
  let mut reducers := #[]
  let mut total := Array.replicate (2*n) false
  for i in [:n] do
    let mut row : SparseRow := {}
    row := { columns := Packed.push .u32 row.columns i.toUInt64, coefficients := row.coefficients.push 1 }
    total := total.set! i true
    for j in [:n] do
      if ((i+3)*(j+7)+i*i+3*j*j)%11 < 6 then
        row := { columns := Packed.push .u32 row.columns (n+j).toUInt64, coefficients := row.coefficients.push 1 }
        total := total.set! (n+j) (!total[n+j]!)
    reducers := reducers.push row
  let mut targets := #[]
  for i in [:n] do
    let mut row : SparseRow := {}
    for j in [:2*n] do
      if total[j]! != (j == n+i) then
        row := { columns := Packed.push .u32 row.columns j.toUInt64, coefficients := row.coefficients.push 1 }
    targets := targets.push row
  return ⟨n,reducers,targets⟩

private def projection (input : ProjectionInput) (packed : Bool) :
    Bool × Array (Bool × Array (Nat × UInt64) × Nat) × Array Nat := Id.run do
  let limits : MatrixLimits := { work := 10000000000,packedBytes := 1000000000,inputEntries := 1000000000,outputEntries := 1000000000,binaryPivots := true }
  let some result := if packed then
      Elimination.attempt binaryField limits (2*input.n) input.reducers input.targets #[] false
    else Elimination.attemptPortable binaryField limits (2*input.n) input.reducers input.targets #[] false |
      return (false,#[],#[])
  let .ok (echelon,remainders) := result.result | return (false,#[],#[])
  let rows := echelon.rows.map (fun row => (row.fromTarget,row.row.entries binaryField,row.sugar))
  let mut valid := rows.size == 2*input.n && echelon.reducerRank == input.n && remainders.isEmpty
  for i in [:input.n] do
    if !(rows.any (fun row => row.1 && row.2.1 == #[(input.n+i,(1:UInt64))] && row.2.2 == 0)) then valid := false
  return (valid,rows,#[result.stats.inputEntries,result.stats.outputEntries,
    result.stats.packedBytes,result.stats.work,result.stats.zeroRows,
    result.stats.traceNodes,result.stats.reductions,result.stats.processedRows])

/-- Known-row table construction, projected targets, complete elimination,
independent free-column checks and structural hashing of all rows/counters. -/
def binaryProjection (input : ProjectionInput) := projection input true

/-- Identical matrix, allowances, independent checks and complete output via
the sparse reference with bounded native phases. -/
def projectionSparse (input : ProjectionInput) := projection input false

#guard (binaryProjection (prepareProjection 0)).1
#guard binaryProjection (prepareProjection 64) == projectionSparse (prepareProjection 64)

-- O(n³/64+n²) packed elimination at fixed word width; table creation is
-- O(n²), selected known combinations cost O(n³/64), decoding/checking and
-- hashing the n dense known rows cost O(n²). Target units are exact.
setup_benchmark binaryProjection n => n*n*n
  with prep := prepareProjection
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64,128,256,512]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 20.0
  }

-- O(n³) sparse/reference elimination applies n known dense tails to each target.
-- Preparation is excluded; validation and complete result hashing are included.
setup_benchmark projectionSparse n => n*n*n
  with prep := prepareProjection
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64,128,256,512]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 20.0
  }

end Hex.Groebner.Bench
