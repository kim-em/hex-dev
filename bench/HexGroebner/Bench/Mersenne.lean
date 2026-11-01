/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner
import HexArith.Montgomery.Context
import LeanBench

namespace Hex.Groebner.Bench

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

private def mersenne : PrimeField :=
  ⟨2147483647, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩

/-- Packed full-rank Cauchy input over the largest admitted prime. -/
structure MersenneInput where
  columns : Nat
  reducers : Array SparseRow
  targets : Array SparseRow
  deriving Hashable

/-- Hilbert entries `1/(i+j+1)`. The registered domain satisfies `2*n < p`,
so every square minor is nonzero. Preparation is outside the timed region. -/
def prepare31 (n : Nat) : MersenneInput := Id.run do
  let mut rows := #[]
  for i in [:n] do
    let mut row : SparseRow := {}
    for j in [:n] do
      let c := (HexArith.powMod (i+j+1) (mersenne.modulus.toNat-2)
        mersenne.modulus.toNat).toUInt64
      row := ⟨Packed.push .u32 row.columns j.toUInt64,Packed.push .u32 row.coefficients c⟩
    rows := rows.push row
  return ⟨n,rows.extract 0 (n/2),rows.extract (n/2) n⟩

/-- The same rows on even columns, forcing scattered vector updates. -/
def prepare31Strided (n : Nat) : MersenneInput := Id.run do
  let input := prepare31 n
  let remap (row : SparseRow) : SparseRow := Id.run do
    let mut columns := ByteArray.emptyWithCapacity row.columns.size
    for i in [:row.size] do columns := Packed.push .u32 columns (2*Packed.read .u32 row.columns i)
    return { row with columns }
  return ⟨2*n+3,input.reducers.map remap,input.targets.map remap⟩

/-- Validation, allocation, elimination and full decoded output are timed.
Every coefficient and column participates in structural result hashing. -/
def cauchy31 (input : MersenneInput) : Bool × Array (Array (Nat × UInt64)) :=
  match (eliminateWith mersenne { work := 1000000000 } input.columns input.reducers input.targets).result with
  | .ok e => (e.rows.size == input.reducers.size+input.targets.size,e.rows.map (·.row.entries mersenne))
  | .error _ => (false,#[])

def cauchy31Strided (input : MersenneInput) := cauchy31 input

#guard (cauchy31 (prepare31 16)).1
#guard (cauchy31Strided (prepare31Strided 16)).1

-- Full-rank dense pivot tails perform exactly (n^3-n)/3 entry updates.
-- Validation, scans, allocation and full result consumption cost O(n^2).
setup_benchmark cauchy31 n => n*n*n
  with prep := prepare31
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64,128,256,512]
    maxSecondsPerCall := 32.0
    targetInnerNanos := 4000000000
  }

-- Column remapping preserves those cubic updates and adds quadratic scans.
setup_benchmark cauchy31Strided n => n*n*n
  with prep := prepare31Strided
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64,128,256,512]
    maxSecondsPerCall := 32.0
    targetInnerNanos := 4000000000
  }

end Hex.Groebner.Bench
