/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner
import HexArith.Montgomery.Context
import LeanBench

/-! Full-rank Hilbert matrices (a Cauchy family) exercise dense pivot tails.
Sparse rectangular matrices exercise known pivots and rank defects. Preparation
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

/-- Hilbert entries `1 / (i + j + 1)` over the prime field. For the registered
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

private def wireOp : RowOp → Array UInt64
  | .input i => #[0, i.toUInt64]
  | .addScaled l r c => #[1, l.toUInt64, r.toUInt64, c]
  | .scale i c => #[2, i.toUInt64, c]

/-- The same dense elimination with shared provenance generation and full
structural hashing of the derivation as well as the decoded matrix. -/
def cauchyTrace (input : Input) :
    Bool × Array (Array (Nat × UInt64)) × Array (Array UInt64) :=
  match (eliminateWith field {} input.columns input.reducers input.targets true).result with
  | .ok e => (e.rows.size == input.columns, e.rows.map (·.row.entries field), e.trace.map wireOp)
  | .error _ => (false, #[], #[])

/-- Rectangular matrices with three nonzeros per row and a large zero prefix.
The targets duplicate the independent reducers, so their rank contribution is
zero. Both dimensions grow with `n`, while support size stays fixed. -/
def prepareSparse (n : Nat) : Input := Id.run do
  let columns := n * 256
  let mut rows := #[]
  for i in [:n] do
    let first := columns / 2 + i * 4
    let mut row : SparseRow := {}
    for j in [:3] do
      row := {
        columns := Packed.push .u32 row.columns (first + j).toUInt64
        coefficients := Packed.push .u32 row.coefficients (j + 1).toUInt64 }
    rows := rows.push row
  return ⟨columns, rows, rows⟩

/-- Sparse rank-deficient matrix output, structurally hashed. -/
def sparse (input : Input) : Bool × Array (Array (Nat × UInt64)) :=
  match (eliminateWith field {} input.columns input.reducers input.targets).result with
  | .ok e => (e.reducerRank == input.reducers.size && e.rows.size == e.reducerRank,
      e.rows.map (·.row.entries field))
  | .error _ => (false, #[])

#guard (cauchy (prepare 0)).1
#guard (cauchy (prepare 4)).1
#guard (cauchy (prepare 16)).1
#guard (cauchyTrace (prepare 16)).1
#guard (sparse (prepareSparse 16)).1

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
    targetInnerNanos := 500000000
  }

-- The same cubic fixed-word updates as cauchy, plus O(n^2) shared trace
-- insertions and structural hashing. Amortized constant-time push is required;
-- copying the whole trace at each node would instead introduce O(n^4) work.
setup_benchmark cauchyTrace n => n * n * n
  with prep := prepare
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 64, 128, 256]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 500000000
  }

-- Independently derived model: 256*n columns need O(n) workspace initialization
-- and one final pivot scan. Each of 2*n rows has three nonzeros. Reducers install
-- directly and targets cancel in one three-entry update, so validation, actual
-- support work, bounded inversion, decoding and structural hashing are O(n).
setup_benchmark sparse n => n
  with prep := prepareSparse
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 64, 128, 256]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 500000000
  }

end Hex.Groebner.Bench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
