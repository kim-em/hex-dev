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

The schoolbook and KS1 measurements run through `Hex.ZPoly.mulKroneckerAt`,
with the cutoffs set to force one path or the other; the KS2, KS3, and KS4
measurements call their forced kernels directly. Emits one JSON document on stdout;
`scripts/bench/kronecker_crossover.py` pins it to a verified-idle core and
wraps the result with environment metadata.
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

Each iteration selects its left operand by a branch on the running checksum, so
the product depends on the previous iteration and cannot be hoisted out of the
loop — without this the compiler lifts the whole loop body and the measured
times are a flat few nanoseconds at every degree.

The checksum is seeded from the clock and only ever advanced by an even amount,
so the branch is not statically decidable but always takes the same side at
runtime: every iteration multiplies the same pair, and the kernels compare
like for like. Seeding it from a literal would let a sufficiently strong
optimiser prove the branch constant and hoist the loop body again. The caller
passes one seed to all kernels so their checksums remain comparable. -/
def timeProduct (seed : Int) (reps sizeCutoff bitCutoff : Nat) (p q : ZPoly) :
    IO (Float × Int) := do
  let mut chk : Int := seed
  let _ := ZPoly.mulKroneckerAt sizeCutoff bitCutoff p q
  let t0 ← IO.monoNanosNow
  for _ in [0:reps] do
    let p' := if chk % 2 == 1 then q else p
    let r := ZPoly.mulKroneckerAt sizeCutoff bitCutoff p' q
    chk := chk + 2 * r.coeff 0
  let t1 ← IO.monoNanosNow
  return (Float.ofNat (t1 - t0) / Float.ofNat reps, chk)

/-- Time the forced two-point kernel with the same dependency chain used by
`timeProduct`.  Cost model: two packed multiplications have about half the KS1
bit width, plus linear packing and interleaving overhead. -/
def timeKronecker2 (seed : Int) (reps : Nat) (p q : ZPoly) : IO (Float × Int) := do
  let mut chk : Int := seed
  let _ := ZPoly.mulKronecker2 p q
  let t0 ← IO.monoNanosNow
  for _ in [0:reps] do
    let p' := if chk % 2 == 1 then q else p
    let r := ZPoly.mulKronecker2 p' q
    chk := chk + 2 * r.coeff 0
  let t1 ← IO.monoNanosNow
  return (Float.ofNat (t1 - t0) / Float.ofNat reps, chk)

/-- Time the forced reciprocal kernel with the same dependency chain. -/
def timeKronecker3 (seed : Int) (reps : Nat) (p q : ZPoly) : IO (Float × Int) := do
  let mut chk : Int := seed
  let _ := ZPoly.mulKronecker3 p q
  let t0 ← IO.monoNanosNow
  for _ in [0:reps] do
    let p' := if chk % 2 == 1 then q else p
    let r := ZPoly.mulKronecker3 p' q
    chk := chk + 2 * r.coeff 0
  let t1 ← IO.monoNanosNow
  return (Float.ofNat (t1 - t0) / Float.ofNat reps, chk)

/-- Time the forced four-point kernel with the same dependency chain. -/
def timeKronecker4 (seed : Int) (reps : Nat) (p q : ZPoly) : IO (Float × Int) := do
  let mut chk : Int := seed
  let _ := ZPoly.mulKronecker4 p q
  let t0 ← IO.monoNanosNow
  for _ in [0:reps] do
    let p' := if chk % 2 == 1 then q else p
    let r := ZPoly.mulKronecker4 p' q
    chk := chk + 2 * r.coeff 0
  let t1 ← IO.monoNanosNow
  return (Float.ofNat (t1 - t0) / Float.ofNat reps, chk)

/-- One grid cell: all five kernels and their ratios, as a JSON object. -/
def cell (n bits reps : Nat) (signed : Bool) : IO String := do
  let p := randPoly n bits 0x243f6a8885a308d3 signed
  let q := randPoly n bits 0x13198a2e03707344 signed
  -- A size cutoff above `n` forces schoolbook; cutoffs of zero force Kronecker.
  -- One clock-derived even seed, shared by all kernels: the branch inside the
  -- timing loop is then not statically decidable, all kernels take the same side
  -- of it at runtime, and their checksums stay directly comparable.
  let seed : Int := 2 * Int.ofNat ((← IO.monoNanosNow) % 3)
  let (school, cSchool) ← timeProduct seed reps (n + 1) 0 p q
  let (kron, cKron) ← timeProduct seed reps 0 0 p q
  let (ks2, cKs2) ← timeKronecker2 seed reps p q
  let (ks3, cKs3) ← timeKronecker3 seed reps p q
  let (ks4, cKs4) ← timeKronecker4 seed reps p q
  if cSchool != cKron || cSchool != cKs2 || cSchool != cKs3 || cSchool != cKs4 then
    throw <| IO.userError s!"kernel disagreement at n={n} bits={bits} signed={signed}"
  return "{\"n\": " ++ toString n ++ ", \"bits\": " ++ toString bits
    ++ ", \"signed\": " ++ (if signed then "true" else "false")
    ++ ", \"reps\": " ++ toString reps
    ++ ", \"schoolbook_nanos\": " ++ toString school
    ++ ", \"kronecker_nanos\": " ++ toString kron
    ++ ", \"ks2_nanos\": " ++ toString ks2
    ++ ", \"ks3_nanos\": " ++ toString ks3
    ++ ", \"ks4_nanos\": " ++ toString ks4
    ++ ", \"ratio\": " ++ toString (school / kron)
    ++ ", \"ks2_ratio\": " ++ toString (school / ks2)
    ++ ", \"ks3_ratio\": " ++ toString (school / ks3)
    ++ ", \"ks4_ratio\": " ++ toString (school / ks4) ++ "}"

/-- Repetition count chosen so each cell takes roughly the same wall time. -/
def repsFor (n bits : Nat) : Nat :=
  let work := n * n * (bits + 8)
  max 200 (min 20000 (40000000 / (work + 1)))

/-- The degree by coefficient-width grid the cutoffs are read off. -/
def grid : List (Nat × Nat) :=
  let widths := [4, 8, 12, 14, 15, 16, 17, 18, 19, 20, 22, 24, 32, 48, 64, 92,
    128, 181, 256, 400]
  let degrees := [4, 8, 12, 16, 20, 24, 28, 32, 40, 48, 64, 90, 128]
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
