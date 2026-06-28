/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPoly

/-!
Throwaway arithmetic-floor microbench (feasibility spike for the fast classical
Berlekamp-Zassenhaus rewrite). Compares the proven `DensePoly.mul` (functional
`List.range` + `Option`-indexing inner loop) against a tight `Array`-loop
`mulFast`, over `Int`, at several degrees. Measures marginal ns/op so we can see
the achievable per-op floor versus Isabelle's ~8 µs whole-factorization.

Not imported by the library; proves nothing. `mulFast` is a probe, not a
replacement for the proven `mul`.
-/

open Hex

/-- Tight schoolbook multiply over `Int`: no `List.range`, no `Option`-indexing,
in-place `set!` accumulation. Raw arrays, no normalization. -/
def mulFast (p q : Array Int) : Array Int :=
  if p.size == 0 || q.size == 0 then #[] else Id.run do
    let mut acc : Array Int := Array.replicate (p.size + q.size - 1) 0
    for i in [0:p.size] do
      let pi := p[i]!
      if pi != 0 then
        for j in [0:q.size] do
          let k := i + j
          acc := acc.set! k (acc[k]! + pi * q[j]!)
    return acc

/-- Tight schoolbook multiply over `UInt64`: machine-word arithmetic, no `Int`
extern calls. Wraps mod 2^64 (fine for a floor measurement). -/
def mulFastU64 (p q : Array UInt64) : Array UInt64 :=
  if p.size == 0 || q.size == 0 then #[] else Id.run do
    let mut acc : Array UInt64 := Array.replicate (p.size + q.size - 1) 0
    for i in [0:p.size] do
      let pi := p[i]!
      if pi != 0 then
        for j in [0:q.size] do
          let k := i + j
          acc := acc.set! k (acc[k]! + pi * q[j]!)
    return acc

def operandU64 (n : Nat) (seed : Nat) : Array UInt64 :=
  (Array.range (n + 1)).map (fun i => UInt64.ofNat (i * 7 + 3 + seed))

def csumU64 (a : Array UInt64) : UInt64 := a.foldl (· + ·) 0

/-- `(x+1)(x+2)...(x+n)`-ish dense operand of size `n+1`, perturbed by `seed` so
the optimizer cannot hoist the loop body. -/
def operand (n : Nat) (seed : Nat) : Array Int :=
  (Array.range (n + 1)).map (fun i => (Int.ofNat (i * 7 + 3) + Int.ofNat seed))

def timeIt (label : String) (iters : Nat) (act : Nat → UInt64) : IO Unit := do
  -- warmup
  let mut w : UInt64 := 0
  for s in [0:100] do
    w := w + act s
  let t0 ← IO.monoNanosNow
  let mut chk : UInt64 := w
  for s in [0:iters] do
    chk := chk + act s
  let t1 ← IO.monoNanosNow
  let total := t1 - t0
  let perOp := total.toFloat / iters.toFloat
  IO.println s!"{label}: {perOp} ns/op   (iters={iters}, total={total} ns, chk={chk})"

/-- checksum a result array into a UInt64 to force evaluation -/
def csum (a : Array Int) : UInt64 :=
  a.foldl (fun acc x => acc + (UInt64.ofNat x.toNat)) 0

def main : IO Unit := do
  for deg in [8, 16, 24, 48] do
    IO.println s!"--- degree {deg} (operand size {deg+1}) ---"
    -- DensePoly proven mul
    timeIt s!"  DensePoly.mul  deg{deg}" 200000 (fun s =>
      let p := DensePoly.ofCoeffs (operand deg s)
      let q := DensePoly.ofCoeffs (operand deg (s+1))
      csum (DensePoly.mul p q).coeffs)
    -- tight array mul (Int)
    timeIt s!"  mulFast Int    deg{deg}" 200000 (fun s =>
      csum (mulFast (operand deg s) (operand deg (s+1))))
    -- tight array mul (UInt64 machine words)
    timeIt s!"  mulFast UInt64 deg{deg}" 200000 (fun s =>
      csumU64 (mulFastU64 (operandU64 deg s) (operandU64 deg (s+1))))
