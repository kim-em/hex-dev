/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.Representation

/-!
Compiled-code driver for the D2 interval-representation experiment.

This is a provisional feasibility spike, not the Phase-4 `hexinterval_bench`.
It runs one candidate per process so an external harness can attribute peak RSS
to that candidate, and emits one whitespace-delimited record containing raw
nanoseconds and a checksum.  The external harness writes the structured JSON
record. Kernel replay is measured separately; it is deliberately not mixed
into a compiled-code timing.
-/

open Hex.Interval.Experiment

/-- Run a representation workload repeatedly and retain its full checksum. -/
def timeWork (variant : String) (n repeats : Nat) (work : Nat → UInt64) : IO Unit := do
  let mut warm : UInt64 := 0
  for _ in [0:4] do
    warm := warm + work n
  let start ← IO.monoNanosNow
  let mut sink := warm
  for _ in [0:repeats] do
    sink := sink + work n
  let stop ← IO.monoNanosNow
  IO.println s!"{variant} {n} {repeats} {stop - start} {sink}"

/-- Print compiled answers used as literals by the kernel-replay probes. -/
def printAnswers : IO Unit := do
  for n in [16, 433, 4096] do
    IO.println s!"{n} {bundledWork n} {checkedWork n} {bundledBoundaryWork n} {checkedBoundaryWork n} {replayBundledWork n} {replayCheckedWork n}"

def usage : String :=
  "usage: hex_interval_representation_spike answers | " ++
    "(bundled|checked|bundled-boundary|checked-boundary) N REPEATS"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["answers"] =>
      printAnswers
      return 0
  | [variant, nText, repeatsText] =>
      let some n := nText.toNat?
        | IO.eprintln usage
          return 2
      let some repeats := repeatsText.toNat?
        | IO.eprintln usage
          return 2
      if repeats = 0 then
        IO.eprintln usage
        return 2
      match variant with
      | "bundled" => timeWork variant n repeats bundledWork
      | "checked" => timeWork variant n repeats checkedWork
      | "bundled-boundary" => timeWork variant n repeats bundledBoundaryWork
      | "checked-boundary" => timeWork variant n repeats checkedBoundaryWork
      | _ =>
          IO.eprintln usage
          return 2
      return 0
  | _ =>
      IO.eprintln usage
      return 2
