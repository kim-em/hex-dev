/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekamp

/-!
Local comparison measurement for the Strassen base kernel: default-base
`mulStrassen strassenDefault` versus delayed-reduction-base
`mulStrassen (strassenBarrett ctx)` on the prime field `ZMod64 p`.

This is a **local** measurement tool, not a CI-gated bench (it carries no
`LeanBench` registration and is not on the bench-verify list). It emits a JSON
record on stdout consumed by `scripts/plots/strassen-base-kernel-comparison.py`
to regenerate `reports/figures/strassen-base-kernel-comparison.svg`. It imports
only the Mathlib-free `HexBerlekamp` closure, so it stays off the Mathlib link
chain.

A base kernel fires only below the cutoff, so it moves the constant factor and
the crossover, never the asymptotic slope; this comparison is reported that way
(a per-dimension speedup ratio, not a scaling slope).
-/

open Hex Hex.Matrix

/-- A prime modulus near `2^31` so residue products exercise the full `~62`-bit
width of the two-word accumulator. -/
abbrev cmpPrime : Nat := 2147483647

instance : ZMod64.Bounds cmpPrime := ⟨by decide, by decide⟩

/-- The Barrett context for the delayed-reduction base kernel. -/
def cmpCtx : Hex.BarrettCtx cmpPrime := Hex.BarrettCtx.ofModulus (by decide) (by decide)

/-- Deterministic dense `n × n` matrix keyed by a runtime salt (so the timed
computation cannot be constant-folded out of the loop). -/
@[noinline]
def cmpMat (n salt : Nat) : Matrix (ZMod64 cmpPrime) n n :=
  Matrix.ofFn fun i j =>
    ZMod64.ofNat cmpPrime ((i.val * 2654435761 + j.val * 40503 + salt * 97 + 1) % cmpPrime)

/-- Sum of all entries (mod `p`) as a hashable observable of the product. -/
def cmpChecksum {n : Nat} (M : Matrix (ZMod64 cmpPrime) n n) : Nat :=
  (List.finRange n).foldl
    (fun acc i => (List.finRange n).foldl (fun a j => (a + M[(i, j)].toNat) % cmpPrime) acc) 0

/-- One product+checksum, dispatched on the base kernel and keyed by salt. -/
@[noinline]
def cmpRun (delayed : Bool) (n salt : Nat) : Nat :=
  let a := cmpMat n salt
  let b := cmpMat n (salt + 7)
  if delayed then cmpChecksum (mulStrassen (strassenBarrett cmpCtx) a b)
  else cmpChecksum (mulStrassen strassenDefault a b)

/-- Best-of-`iters` wall time in nanoseconds. The checksums are accumulated into
`sink` and printed outside the timed region, so the `cmpRun` results are live and
the timed region includes the whole computation rather than a lazy thunk. -/
def cmpBest (delayed : Bool) (n iters : Nat) : IO Nat := do
  let _ := cmpRun delayed n 5
  let mut best : Nat := 0
  let mut first := true
  let mut sink : Nat := 0
  for k in [0:iters] do
    let salt := 1000 + k * 13
    let t0 ← IO.monoNanosNow
    let r := cmpRun delayed n salt
    let t1 ← IO.monoNanosNow
    sink := sink + r
    let dt := t1 - t0
    if first || dt < best then best := dt; first := false
  IO.eprintln s!"  (checksum sink n={n} delayed={delayed}: {sink % 1000000007})"
  return best

def main : IO Unit := do
  let dims := #[64, 96, 128, 160, 192, 256]
  let mut rows : Array String := #[]
  for n in dims do
    let iters := if n ≤ 128 then 11 else 7
    let d ← cmpBest false n iters
    let b ← cmpBest true n iters
    IO.eprintln s!"n={n}  default={(d.toFloat / 1e6)}ms  delayed={(b.toFloat / 1e6)}ms  speedup(default/delayed)={d.toFloat / b.toFloat}"
    rows := rows.push
      ("    " ++ "{" ++ "\"n\": " ++ toString n ++ ", \"default_ns\": " ++ toString d ++
        ", \"delayed_ns\": " ++ toString b ++ "}")
  IO.println "{"
  IO.println ("  \"prime\": " ++ toString cmpPrime ++ ",")
  IO.println "  \"cutoff\": 64,"
  IO.println "  \"metric\": \"best_of_iters_wall_nanos\","
  IO.println "  \"results\": ["
  IO.println (String.intercalate ",\n" rows.toList)
  IO.println "  ]"
  IO.println "}"
