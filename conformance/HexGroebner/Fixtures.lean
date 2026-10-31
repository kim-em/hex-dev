/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner

namespace Hex.Groebner.Fixtures

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

/-- Literal prime contexts spanning every coefficient-width boundary. -/
def fields : Array PrimeField := #[
  ⟨2, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩,
  ⟨3, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩,
  ⟨251, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩,
  ⟨257, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩,
  ⟨65521, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩,
  ⟨65537, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩,
  ⟨2147483647, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩]

/-- Dense interchange rows are converted once, outside elimination. -/
def sparse (field : PrimeField) (columns : Nat) (rows : Array (Array UInt64)) :
    Except String (Array SparseRow) := do
  rows.mapM fun row => do
    if row.size != columns then throw "fixture row length"
    let entries := (row.zipIdx).filterMap fun (c, i) =>
      if c == 0 then none else some (i, c)
    match SparseRow.ofEntries field columns entries with
    | some row => pure row
    | none => throw "noncanonical fixture"

/-- The same raw matrix fixture feeds the core checks and the external oracle. -/
structure Case where
  name : String
  columns : Nat
  reducers : Array (Array UInt64)
  targets : Array (Array UInt64)

/-- Deliberate rank defects, later reducer pivots and near-modulus products. -/
def cases (field : PrimeField) : Array Case := Id.run do
  let p := field.modulus
  let mut out := #[
    ⟨"empty", 0, #[], #[]⟩,
    ⟨"zero-columns", 0, #[#[]], #[#[], #[]]⟩,
    ⟨"zero-rows", 3, #[#[0, 0, 0]], #[#[0, 0, 0]]⟩,
    ⟨"later-reducer", 4, #[#[0, 0, p - 1, 1]],
      #[#[1, 0, p - 1, 0], #[0, 1, 1, 0], #[0, 0, 1, p - 1]]⟩,
    ⟨"dependent", 3, #[#[p - 1, 1, p - 1], #[p - 1, 1, p - 1]],
      #[#[p - 1, 1, p - 1], #[0, 0, 0]]⟩,
    ⟨"full-rank", 3, #[], #[#[0, p - 1, 1], #[1, 0, p - 1], #[0, 0, 1]]⟩]
  out := out.push ⟨"tail-extension", 130,
    #[(Array.replicate 130 0).set! 0 1 |>.set! 129 (p - 1)],
    #[(Array.replicate 130 0).set! 0 1, (Array.replicate 130 0).set! 0 1]⟩
  let reducers : Array (Array UInt64) := (Array.range 20).map fun i =>
    (Array.range 60).map fun j => if j / 3 == i then
      (if j % 3 == 1 then 1 else p - 1) else 0
  let targets : Array (Array UInt64) := (Array.range 20).map fun i =>
    (Array.range 60).map fun j =>
      (reducers[i]![j]! + (p - (1 : UInt64)) * reducers[(i + 1) % 20]![j]!) % p
  out := out.push ⟨"wide-dependent", 60, reducers, targets⟩
  for seed in [:16] do
    let columns := seed % 7 + 1
    let rows := (Array.range (seed % 9 + 1)).map fun i =>
      (Array.range columns).map fun j =>
        let x := ((i + 1) * 1664525 + (j + 3) * 1013904223 + seed * 69069)
        if (x + i * j) % 4 == 0 then 0 else (x.toUInt64 * 65537 + p - 1) % p
    out := out.push ⟨s!"generated-{seed}", columns, rows.extract 0 (rows.size / 2),
      rows.extract (rows.size / 2) rows.size⟩
  return out

/-- Call the matrix entry point with validated fixture rows. -/
def run (field : PrimeField) (c : Case) (limits : MatrixLimits := {})
    (provenance := true) : Except String MatrixResult := do
  let reducers ← sparse field c.columns c.reducers
  let targets ← sparse field c.columns c.targets
  return eliminateWith field limits c.columns reducers targets provenance

end Hex.Groebner.Fixtures
