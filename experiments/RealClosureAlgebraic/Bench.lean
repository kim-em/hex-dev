/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Algebraic
import LeanBench
open Hex Algebraic

structure Fixture where
  d : Descriptor
  p : DensePoly (Element d)
  q : DensePoly (Element d)
initialize fixtures : IO.Ref (Array Fixture) ← IO.mkRef #[]

/-- Preparation runs in main in every harness child, before any timed call. -/
def prepare : IO Unit := do
  let mut out := #[]
  for d in [irreducible, reducible] do
    for shared in [false,true] do
      for n in [4,8,16] do
        let p := input d n
        let q := input d n 1
        let p := if shared then DensePoly.ofCoeffs (p.toArray.map fun a => pack d (raw a*sqrt3)) else p
        let q := if shared then DensePoly.ofCoeffs (q.toArray.map fun a => pack d (raw a*sqrt3)) else q
        out := out.push ⟨d,p,q⟩
  fixtures.set out

@[noinline] def run (batch : Bool) (index : Nat) : IO UInt64 := do
  let some a := (← fixtures.get)[index]? | throw (IO.userError "missing fixture")
  let result := if batch then batchMul a.d a.p a.q else a.p*a.q
  -- Full semantic result digest, including common canonicalization cost.
  return hash (observePoly result)

-- Informational architecture comparisons, not Phase-4 complexity evidence.
def settings : LeanBench.FixedBenchmarkConfig :=
  { repeats := 1, minTotalSeconds := 0.05, maxSecondsPerCall := 10.0,
    warmupFirstIter := true }
def each0 : IO UInt64 := run false 0
setup_fixed_benchmark each0 where settings
def batch0 : IO UInt64 := run true 0
setup_fixed_benchmark batch0 where settings
def each1 : IO UInt64 := run false 1
setup_fixed_benchmark each1 where settings
def batch1 : IO UInt64 := run true 1
setup_fixed_benchmark batch1 where settings
def each2 : IO UInt64 := run false 2
setup_fixed_benchmark each2 where settings
def batch2 : IO UInt64 := run true 2
setup_fixed_benchmark batch2 where settings
def each3 : IO UInt64 := run false 3
setup_fixed_benchmark each3 where settings
def batch3 : IO UInt64 := run true 3
setup_fixed_benchmark batch3 where settings
def each4 : IO UInt64 := run false 4
setup_fixed_benchmark each4 where settings
def batch4 : IO UInt64 := run true 4
setup_fixed_benchmark batch4 where settings
def each5 : IO UInt64 := run false 5
setup_fixed_benchmark each5 where settings
def batch5 : IO UInt64 := run true 5
setup_fixed_benchmark batch5 where settings
def each6 : IO UInt64 := run false 6
setup_fixed_benchmark each6 where settings
def batch6 : IO UInt64 := run true 6
setup_fixed_benchmark batch6 where settings
def each7 : IO UInt64 := run false 7
setup_fixed_benchmark each7 where settings
def batch7 : IO UInt64 := run true 7
setup_fixed_benchmark batch7 where settings
def each8 : IO UInt64 := run false 8
setup_fixed_benchmark each8 where settings
def batch8 : IO UInt64 := run true 8
setup_fixed_benchmark batch8 where settings
def each9 : IO UInt64 := run false 9
setup_fixed_benchmark each9 where settings
def batch9 : IO UInt64 := run true 9
setup_fixed_benchmark batch9 where settings
def each10 : IO UInt64 := run false 10
setup_fixed_benchmark each10 where settings
def batch10 : IO UInt64 := run true 10
setup_fixed_benchmark batch10 where settings
def each11 : IO UInt64 := run false 11
setup_fixed_benchmark each11 where settings
def batch11 : IO UInt64 := run true 11
setup_fixed_benchmark batch11 where settings

def main (args : List String) : IO UInt32 := do
  prepare
  LeanBench.Cli.dispatch args
