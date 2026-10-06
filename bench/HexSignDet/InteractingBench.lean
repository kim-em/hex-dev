/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet.InteractingTrace
import LeanBench

namespace Hex.SignDetBench.InteractingBench

/-- Fixed small interacting inputs, including preparation, three construction
modes, ordinary replay and subject encoding. Arithmetic observation is disabled.
No asymptotic model or general nested-field speed claim is made. -/
@[noinline, never_extract] def run (depth : Nat) : Option UInt64 := do
  let reduced ← InteractingTrace.run depth 2 (10377+10*depth+2) "reduced" false
  let direct ← InteractingTrace.run depth 2 (10377+10*depth+2) "direct" false
  let reference ← InteractingTrace.run depth 2 (10377+10*depth+2) "reference" false
  return hash (reduced.compress, direct.compress, reference.compress)

@[noinline, never_extract] def depthOne : Unit → Option UInt64 := fun () => run 1
@[noinline, never_extract] def depthTwo : Unit → Option UInt64 := fun () => run 2

-- Each executable invocation supplies one fixed observation. The paired
-- collector runs six adjacent AB/BA trials with identical registration settings.
setup_fixed_benchmark depthOne where { repeats := 1, minTotalSeconds := 0.1, maxSecondsPerCall := 10 }
setup_fixed_benchmark depthTwo where { repeats := 1, minTotalSeconds := 0.1, maxSecondsPerCall := 10 }
end Hex.SignDetBench.InteractingBench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
