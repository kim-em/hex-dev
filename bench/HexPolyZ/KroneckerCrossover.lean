/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyZ

/-!
Kernel microbenchmark for the integer dense polynomial product: schoolbook
convolution against Kronecker substitution, by degree and coefficient width.

This is the measurement behind `Hex.ZPoly.kroneckerSizeCutoff` and
`Hex.ZPoly.kroneckerBitCutoff` (see `HexPolyZ/SPEC/hex-poly-z.md`). It is a
manual diagnostic driver, not a CI job and not a `lean-bench` registration: it
sweeps a two-dimensional grid looking for a crossover rather than fitting one
operation against a declared complexity model, so it does not belong in the
scientific harness.

Both arms run through `Hex.ZPoly.mulKroneckerAt`, with the cutoffs set to force
one path or the other, so the two arms differ only in the kernel. Emits one
JSON document on stdout; `scripts/bench/kronecker_crossover.py` pins it to a
verified-idle core and wraps the result with environment metadata.
-/

open Hex

namespace Hex.KroneckerCrossover

/-- Deterministic xorshift over `UInt64`. -/
def nextRand (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- A pseudorandom odd natural number of `bits` bits. -/
partial def randNat (bits : Nat) (s : UInt64) : Nat × UInt64 :=
  let rec go (acc : Nat) (need : Nat) (s : UInt64) : Nat × UInt64 :=
    if need == 0 then (acc, s)
    else
      let s := nextRand s
      let take := min need 32
      go (acc * 2 ^ take + (s.toNat) % (2 ^ take)) (need - take) s
  go 0 bits s

/-- `n` pseudorandom coefficients of `bits` bits each, alternating in sign when
`signed` is set. -/
def randPoly (n bits : Nat) (seed : UInt64) (signed : Bool) : ZPoly := Id.run do
  let mut out : Array Int := Array.emptyWithCapacity n
  let mut s := seed
  for i in [0:n] do
    let (v, s') := randNat bits s
    let z := Int.ofNat (v ||| 1)
    out := out.push (if signed && i % 2 == 0 then -z else z)
    s := s'
  return DensePoly.ofCoeffs out

/-- Time `reps` products at fixed cutoffs.

Each iteration selects its left operand by a branch on the running checksum,
which the checksum keeps on the same side by only ever adding an even multiple.
The product therefore depends on the previous iteration and cannot be hoisted
out of the loop — without this the compiler lifts the whole loop body and the
measured times are a flat few nanoseconds at every degree. -/
def timeProduct (reps sizeCutoff bitCutoff : Nat) (p q : ZPoly) : IO (Float × Int) := do
  let mut chk : Int := 0
  let _ := ZPoly.mulKroneckerAt sizeCutoff bitCutoff p q
  let t0 ← IO.monoNanosNow
  for _ in [0:reps] do
    let p' := if chk % 2 == 1 then q else p
    let r := ZPoly.mulKroneckerAt sizeCutoff bitCutoff p' q
    chk := chk + 2 * r.coeff 0
  let t1 ← IO.monoNanosNow
  return (Float.ofNat (t1 - t0) / Float.ofNat reps, chk)

/-- One grid cell: both arms plus their ratio, as a JSON object. -/
def cell (n bits reps : Nat) (signed : Bool) : IO String := do
  let p := randPoly n bits 0x243f6a8885a308d3 signed
  let q := randPoly n bits 0x13198a2e03707344 signed
  -- A size cutoff above `n` forces schoolbook; cutoffs of zero force Kronecker.
  let (school, cSchool) ← timeProduct reps (n + 1) 0 p q
  let (kron, cKron) ← timeProduct reps 0 0 p q
  if cSchool != cKron then
    throw <| IO.userError s!"kernel disagreement at n={n} bits={bits} signed={signed}"
  return "{\"n\": " ++ toString n ++ ", \"bits\": " ++ toString bits
    ++ ", \"signed\": " ++ (if signed then "true" else "false")
    ++ ", \"reps\": " ++ toString reps
    ++ ", \"schoolbook_nanos\": " ++ toString school
    ++ ", \"kronecker_nanos\": " ++ toString kron
    ++ ", \"ratio\": " ++ toString (school / kron) ++ "}"

/-- Repetition count chosen so each cell takes roughly the same wall time. -/
def repsFor (n bits : Nat) : Nat :=
  let work := n * n * (bits + 8)
  max 200 (min 20000 (40000000 / (work + 1)))

/-- The degree by coefficient-width grid the cutoffs are read off. -/
def grid : List (Nat × Nat) :=
  let widths := [4, 8, 12, 16, 20, 24, 32, 48, 64, 92, 128, 181, 256, 400]
  let degrees := [4, 8, 12, 16, 20, 24, 32, 48, 64, 90, 128]
  widths.flatMap fun b => degrees.map fun n => (n, b)

/-- The shapes the Hensel lift and recombination actually issue, at both signs. -/
def targets : List (Nat × Nat) :=
  [(90, 92), (90, 181), (89, 46), (60, 120), (56, 200), (178, 92), (120, 20), (105, 20)]

def main : IO Unit := do
  let mut rows : Array String := #[]
  for shape in grid do
    rows := rows.push (← cell shape.1 shape.2 (repsFor shape.1 shape.2) false)
  for shape in targets do
    rows := rows.push (← cell shape.1 shape.2 (repsFor shape.1 shape.2) false)
    rows := rows.push (← cell shape.1 shape.2 (repsFor shape.1 shape.2) true)
  IO.println ("{\"size_cutoff\": " ++ toString ZPoly.kroneckerSizeCutoff
    ++ ", \"bit_cutoff\": " ++ toString ZPoly.kroneckerBitCutoff
    ++ ", \"cells\": [" ++ String.intercalate ",\n  " rows.toList ++ "]}")

end Hex.KroneckerCrossover

def main : IO Unit := Hex.KroneckerCrossover.main
