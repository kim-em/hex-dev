/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexLLLBench.Inputs
import LeanBench

/-!
Focused benchmark registrations for exact Gram-row construction in HexLLL's
fixed-precision checker. Keeping these targets in a small executable avoids
charging the unrelated provider/comparator fixed-target initializers in
`hexlll_bench` to each construction probe.

The square targets exercise `rows ≈ cols`; the wide targets use
`cols = 8 * rows + 1` to exercise `rows ≪ cols`. Each isolated construction
target has a complete `lllReducedInterval` consumer on the identical fixture.
-/

namespace Hex.LLLBench

/- The square fixture performs `rows^2` integer dot products of length `rows`.
This isolates the exact Gram-row construction from the interval recurrence. -/
setup_benchmark runIntervalGramRowsSquareChecksum n =>
    intervalGramRowsSquareComplexity n
  with prep := prepIntervalSquareInput
  where {
    paramFloor := 32
    paramCeiling := 96
    paramSchedule := .custom #[32, 48, 64, 80, 96]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- The wide fixture performs `rows^2` integer dot products of length
`8 * rows + 1`, recording the `rows ≪ cols` construction separately. -/
setup_benchmark runIntervalGramRowsWideChecksum n =>
    intervalGramRowsWideComplexity n
  with prep := prepIntervalWideInput
  where {
    paramFloor := 16
    paramCeiling := 48
    paramSchedule := .custom #[16, 24, 32, 40, 48]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- The fixed-precision checker first constructs square Gram rows and then runs
its cubic interval Gram–Schmidt recurrence. The deterministic fixture exercises
the reject path after the complete interval pass; its Boolean result is a
constant checksum, so behavior discrimination comes from the paired Gram-row
target and the proved `gramRows_eq_impl`. This registration is the consumer
paired with `runIntervalGramRowsSquareChecksum` for Amdahl attribution. -/
setup_benchmark runReducedIntervalSquareChecksum n =>
    reducedIntervalSquareComplexity n
  with prep := prepIntervalSquareInput
  where {
    paramFloor := 32
    paramCeiling := 96
    paramSchedule := .custom #[32, 48, 64, 80, 96]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- The wide fixed-precision checker pairs the `rows^2 * (8 * rows + 1)` Gram
construction with the same cubic interval recurrence and reject-path Boolean
checksum described for the square target. -/
setup_benchmark runReducedIntervalWideChecksum n =>
    reducedIntervalWideComplexity n
  with prep := prepIntervalWideInput
  where {
    paramFloor := 16
    paramCeiling := 48
    paramSchedule := .custom #[16, 24, 32, 40, 48]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end Hex.LLLBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
