/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner
import HexArith.Montgomery.Context

/-! Shared packed Cauchy inputs and complete-output consumption. -/

namespace Hex.Groebner.Bench

/-- Immutable packed input, with the first half of the rows serving as reducers. -/
structure Input where
  columns : Nat
  reducers : Array SparseRow
  targets : Array SparseRow
  deriving Hashable

/-- Hilbert entries `1 / (i + j + 1)` over the prime field. For the registered
domain `2*n < p`, all square minors are nonzero. Every elimination update visits
a dense trailing support, without rank defects or accidental zero pivots. -/
def prepareOver (coefficientField : PrimeField) (n : Nat) : Input := Id.run do
  let mut rows := #[]
  for i in [:n] do
    let mut row : SparseRow := {}
    for j in [:n] do
      let c := (HexArith.powMod (i + j + 1) (coefficientField.modulus.toNat - 2)
        coefficientField.modulus.toNat).toUInt64
      row := {
        columns := Packed.push .u32 row.columns j.toUInt64
        coefficients := Packed.push coefficientField.width row.coefficients c }
    rows := rows.push row
  return ⟨n, rows.extract 0 (n / 2), rows.extract (n / 2) n⟩

/-- Complete decoded echelon output for structural hashing. -/
def cauchyOver (coefficientField : PrimeField) (input : Input) :
    Bool × Array (Array (Nat × UInt64)) :=
  match (eliminateWith coefficientField { work := 1000000000 }
      input.columns input.reducers input.targets).result with
  | .ok e => (e.rows.size == input.reducers.size + input.targets.size, e.rows.map (·.row.entries coefficientField))
  | .error _ => (false, #[])

/-- The same coefficients on even columns, with bounded trailing padding. -/
def prepareStridedOver (coefficientField : PrimeField) (n : Nat) : Input := Id.run do
  let input := prepareOver coefficientField n
  let remap (row : SparseRow) : SparseRow := Id.run do
    let mut columns := ByteArray.emptyWithCapacity row.columns.size
    for i in [:row.size] do
      columns := Packed.push .u32 columns (2 * Packed.read .u32 row.columns i)
    return { row with columns }
  return ⟨2*n+3, input.reducers.map remap, input.targets.map remap⟩

end Hex.Groebner.Bench
