/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner
import HexArith.Montgomery.Context
import LeanBench

/-! Full-rank Cauchy matrices exercise dense tails of sparse pivots. Preparation
is excluded; validation, workspace allocation, elimination and output decoding
are included. This measures a Macaulay kernel, not full-system F4. -/

namespace Hex.Groebner.Bench

/-- A prime just above the 16-bit storage boundary. -/
def field : PrimeField :=
  ⟨65537, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩

/-- Immutable packed input, with the first half of the rows serving as reducers. -/
structure Input where
  columns : Nat
  reducers : Array SparseRow
  targets : Array SparseRow
  deriving Hashable

/-- Cauchy entries `1 / (i + j + 1)` over the prime field. For the registered
domain `2*n < p`, all square minors are nonzero. Every elimination update visits
a dense trailing support, without rank defects or accidental zero pivots. -/
def prepare (n : Nat) : Input := Id.run do
  let mut rows := #[]
  for i in [:n] do
    let mut row : SparseRow := {}
    for j in [:n] do
      let c := (HexArith.powMod (i + j + 1) 65535 65537).toUInt64
      row := {
        columns := Packed.push .u32 row.columns j.toUInt64
        coefficients := Packed.push .u32 row.coefficients c }
    rows := rows.push row
  return ⟨n, rows.extract 0 (n / 2), rows.extract (n / 2) n⟩

/-- Return the actual decoded result for structural hashing, including an
explicit failure flag. No parameter-only digest replaces the matrix output. -/
def cauchy (input : Input) : Bool × Array (Array (Nat × UInt64)) :=
  match (eliminateWith field {} input.columns input.reducers input.targets).result with
  | .ok e => (e.rows.size == input.columns, e.rows.map (·.row.entries field))
  | .error _ => (false, #[])

#guard (cauchy (prepare 0)).1
#guard (cauchy (prepare 4)).1
#guard (cauchy (prepare 16)).1

-- Independently derived model: n full-rank Cauchy rows encounter n monic pivots
-- with trailing supports of lengths n-j. Sum_i sum_{j<i} (n-j) = Theta(n^3)
-- fixed-word updates. Validation, dense scans, output decoding and structural
-- hashing each take O(n^2), and n bounded-exponent inversions take O(n).
setup_benchmark cauchy n => n * n * n
  with prep := prepare
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 64, 128, 256]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 100000000
  }

end Hex.Groebner.Bench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
