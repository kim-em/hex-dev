/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Policy
import LeanBench
open Hex Policy

structure Fixture where
  mode : Nat
  a : DensePoly (Elem (base mode))
  b : DensePoly (Elem (base mode))
  c : DensePoly (Elem (upper mode))
  d : DensePoly (Elem (upper mode))
initialize fixtures : IO.Ref (Array Fixture) ← IO.mkRef #[]

def prepare : IO Unit := do
  let mut out := #[]
  for mode in [:4] do
    for n in [2,3,4,2,3] do
      out := out.push ⟨mode,input mode n 0,input mode (n-1) 1,
        nestedInput mode n 0,nestedInput mode (n-1) 1⟩
  fixtures.set out

@[noinline] def run (mode case : Nat) : IO UInt64 := do
  let some f := (← fixtures.get)[mode*5+case/2]? | throw (IO.userError "missing fixture")
  if case < 6 then
    let (q,r) := if case%2 == 0 then DensePoly.divMod f.a f.b
      else (DensePoly.monicize (DensePoly.gcd f.a f.b),0)
    return hash (q.toArray.map (observe f.mode),r.toArray.map (observe f.mode))
  else
    let (q,r) := if case%2 == 0 then DensePoly.divMod f.c f.d
      else (DensePoly.monicize (DensePoly.gcd f.c f.d),0)
    return hash (q.toArray.map (observeNested f.mode),r.toArray.map (observeNested f.mode))

-- Fixed architecture comparisons; no complexity or Phase-4 claim.
def settings : LeanBench.FixedBenchmarkConfig :=
  { repeats := 1, minTotalSeconds := 0.05, maxSecondsPerCall := 10.0,
    warmupFirstIter := true }
def policy_0_0 : IO UInt64 := run 0 0
setup_fixed_benchmark policy_0_0 where settings
def policy_0_1 : IO UInt64 := run 0 1
setup_fixed_benchmark policy_0_1 where settings
def policy_0_2 : IO UInt64 := run 0 2
setup_fixed_benchmark policy_0_2 where settings
def policy_0_3 : IO UInt64 := run 0 3
setup_fixed_benchmark policy_0_3 where settings
def policy_0_4 : IO UInt64 := run 0 4
setup_fixed_benchmark policy_0_4 where settings
def policy_0_5 : IO UInt64 := run 0 5
setup_fixed_benchmark policy_0_5 where settings
def policy_0_6 : IO UInt64 := run 0 6
setup_fixed_benchmark policy_0_6 where settings
def policy_0_7 : IO UInt64 := run 0 7
setup_fixed_benchmark policy_0_7 where settings
def policy_0_8 : IO UInt64 := run 0 8
setup_fixed_benchmark policy_0_8 where settings
def policy_0_9 : IO UInt64 := run 0 9
setup_fixed_benchmark policy_0_9 where settings
def policy_1_0 : IO UInt64 := run 1 0
setup_fixed_benchmark policy_1_0 where settings
def policy_1_1 : IO UInt64 := run 1 1
setup_fixed_benchmark policy_1_1 where settings
def policy_1_2 : IO UInt64 := run 1 2
setup_fixed_benchmark policy_1_2 where settings
def policy_1_3 : IO UInt64 := run 1 3
setup_fixed_benchmark policy_1_3 where settings
def policy_1_4 : IO UInt64 := run 1 4
setup_fixed_benchmark policy_1_4 where settings
def policy_1_5 : IO UInt64 := run 1 5
setup_fixed_benchmark policy_1_5 where settings
def policy_1_6 : IO UInt64 := run 1 6
setup_fixed_benchmark policy_1_6 where settings
def policy_1_7 : IO UInt64 := run 1 7
setup_fixed_benchmark policy_1_7 where settings
def policy_1_8 : IO UInt64 := run 1 8
setup_fixed_benchmark policy_1_8 where settings
def policy_1_9 : IO UInt64 := run 1 9
setup_fixed_benchmark policy_1_9 where settings
def policy_2_0 : IO UInt64 := run 2 0
setup_fixed_benchmark policy_2_0 where settings
def policy_2_1 : IO UInt64 := run 2 1
setup_fixed_benchmark policy_2_1 where settings
def policy_2_2 : IO UInt64 := run 2 2
setup_fixed_benchmark policy_2_2 where settings
def policy_2_3 : IO UInt64 := run 2 3
setup_fixed_benchmark policy_2_3 where settings
def policy_2_4 : IO UInt64 := run 2 4
setup_fixed_benchmark policy_2_4 where settings
def policy_2_5 : IO UInt64 := run 2 5
setup_fixed_benchmark policy_2_5 where settings
def policy_2_6 : IO UInt64 := run 2 6
setup_fixed_benchmark policy_2_6 where settings
def policy_2_7 : IO UInt64 := run 2 7
setup_fixed_benchmark policy_2_7 where settings
def policy_2_8 : IO UInt64 := run 2 8
setup_fixed_benchmark policy_2_8 where settings
def policy_2_9 : IO UInt64 := run 2 9
setup_fixed_benchmark policy_2_9 where settings
def policy_3_0 : IO UInt64 := run 3 0
setup_fixed_benchmark policy_3_0 where settings
def policy_3_1 : IO UInt64 := run 3 1
setup_fixed_benchmark policy_3_1 where settings
def policy_3_2 : IO UInt64 := run 3 2
setup_fixed_benchmark policy_3_2 where settings
def policy_3_3 : IO UInt64 := run 3 3
setup_fixed_benchmark policy_3_3 where settings
def policy_3_4 : IO UInt64 := run 3 4
setup_fixed_benchmark policy_3_4 where settings
def policy_3_5 : IO UInt64 := run 3 5
setup_fixed_benchmark policy_3_5 where settings
def policy_3_6 : IO UInt64 := run 3 6
setup_fixed_benchmark policy_3_6 where settings
def policy_3_7 : IO UInt64 := run 3 7
setup_fixed_benchmark policy_3_7 where settings
def policy_3_8 : IO UInt64 := run 3 8
setup_fixed_benchmark policy_3_8 where settings
def policy_3_9 : IO UInt64 := run 3 9
setup_fixed_benchmark policy_3_9 where settings

def main (args : List String) : IO UInt32 := do
  prepare
  LeanBench.Cli.dispatch args
