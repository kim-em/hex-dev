/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Bench.Cauchy
import LeanBench

namespace Hex.Groebner.Bench

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

private def mersenne : PrimeField :=
  ⟨2147483647, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩

/-- Largest-prime Cauchy input; preparation is outside the timed region. -/
def prepare31 (n : Nat) : Input := prepareOver mersenne n

/-- Identical coefficients on even columns. -/
def prepare31Strided (n : Nat) : Input := prepareStridedOver mersenne n

/-- Validation, allocation, elimination and every decoded output entry are timed. -/
def cauchy31 (input : Input) := cauchyOver mersenne input

def cauchy31Strided (input : Input) := cauchy31 input

#guard (cauchy31 (prepare31 16)).1
#guard (cauchy31Strided (prepare31Strided 16)).1

-- Full-rank dense pivot tails perform exactly (n^3-n)/3 entry updates.
-- Validation, scans, allocation and full result consumption cost O(n^2).
setup_benchmark cauchy31 n => n*n*n
  with prep := prepare31
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64,128,256,512]
    maxSecondsPerCall := 32.0
    targetInnerNanos := 4000000000
  }

-- Column remapping preserves those cubic updates and adds quadratic scans.
setup_benchmark cauchy31Strided n => n*n*n
  with prep := prepare31Strided
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64,128,256,512]
    maxSecondsPerCall := 32.0
    targetInnerNanos := 4000000000
  }

end Hex.Groebner.Bench
