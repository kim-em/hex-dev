/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor
import LeanBench

/-! Native benchmark families for integer factorization and replay. -/

namespace Hex.IntFactorBench

open Hex.Nat

def runFactor (n : Nat) : Nat :=
  match factor? n (Hex.Rand.ofSeed n) with
  | .ok (F, _) => F.raw.factors.length
  | .error f => f.attempts

def runRho (n : Nat) : Nat :=
  match rhoSplit? n (Hex.Rand.ofSeed n) 1000000 with
  | .ok (d, _) => d
  | .error f => f.attempts

def runPMinusOne (n : Nat) : Nat :=
  match pMinusOneStage1 n 2 10000 with
  | .factor d => d
  | .noFactor => 1
  | .whole => n

def runEcm (n : Nat) : Nat :=
  match ecmStage1 n 7 1000 with
  | .factor d => d
  | .noFactor => 1
  | .whole => n

def runCyclotomic (n : Nat) : Nat :=
  match cyclotomicSplit? 2 n .minus with
  | some parts => parts.foldl (fun acc part => acc + part.value % 65536) 0
  | none => 0

def replayInput (e : Nat) : Factorization :=
  ⟨2 ^ e, [⟨e, .small 2⟩]⟩

def runReplay (e : Nat) : Nat :=
  if checkFactorization (replayInput e) then 1 else 0

def runOrder (p : Nat) : Nat := orderOf 2 p

/- Generic factorization is rho-dominated on balanced semiprimes: the smaller
factor has size `sqrt n`, and rho takes its square root, giving `O(n^(1/4))`
arithmetic iterations. The returned factor-count hash is constant-size. -/
setup_benchmark runFactor n => Nat.sqrt (Nat.sqrt n)
  where {
    paramFloor := 1000
    paramCeiling := 281474641166387
    paramSchedule := .custom #[1009, 10403, 4292870399, 281474641166387]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
  }

/- Brent rho needs `O(sqrt p)` iterations for the least factor `p`; balanced
semiprimes have `p = sqrt n`, hence the declared `O(n^(1/4))` model. -/
setup_benchmark runRho n => Nat.sqrt (Nat.sqrt n)
  where {
    paramFloor := 1000
    paramCeiling := 18446744073709551615
    paramSchedule := .custom #[4292870399, 281474641166387, 18446743979220271189]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
  }

/- The smoothness bound is fixed, so the arithmetic-operation count is fixed;
operand work scales with the modulus bit length, modeled by `O(log n)`. -/
setup_benchmark runPMinusOne n => n.log2
  where {
    paramFloor := 15
    paramCeiling := 10097063
    paramSchedule := .custom #[15, 299, 1009 * 10007]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
  }

/- This stage-1 ladder fixes the curve and smoothness bound. Its scalar-step
count is fixed while modular operand work grows with `log n`. -/
setup_benchmark runEcm n => n.log2
  where {
    paramFloor := 91
    paramCeiling := 10403
    paramSchedule := .custom #[91, 589, 10403]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
  }

/- Building recursive cyclotomic values for the divisor indices through `n`
revisits prefixes whose total length has a quadratic cost bound. -/
setup_benchmark runCyclotomic n => n * n
  where {
    paramFloor := 4
    paramCeiling := 32
    paramSchedule := .custom #[4, 8, 16, 24, 32]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
  }

/- `boundedPowMul` replays the single exponent one multiplication at a time,
so a certificate with exponent `n` has linear arithmetic-operation cost. -/
setup_benchmark runReplay n => n
  where {
    paramFloor := 1
    paramCeiling := 64
    paramSchedule := .custom #[1, 2, 4, 8, 16, 32, 64]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
  }

/- `orderOf` scans candidate exponents up to the modulus and performs a bounded
modular-power check at each step, so the declared worst-case model is linear. -/
setup_benchmark runOrder n => n
  where {
    paramFloor := 7
    paramCeiling := 65537
    paramSchedule := .custom #[7, 31, 257, 65537]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
  }

end Hex.IntFactorBench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
