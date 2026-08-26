/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvGcd.Comparators
import LeanBench

/-!
Parametric handles for sampling the fixed HexMvGcd comparator cases.

The prepared inputs and core operations match the Hex arms of the fixed
comparator registrations. These handles force the result through the native
matrix checksum rather than the comparator's canonical-term encoding.
Lean-bench-samply currently drives parametric child registrations, so the
one-point constant-work handles expose those operations to its timed-region
protocol. They are profiling infrastructure, not scaling claims.
-/

namespace Hex.MvGcdBench.Profile

open Hex
open Hex.MvPoly
open Hex.MvGcdBench.Families

def prepCoprime (_ : Nat) : P 8 Int × P 8 Int :=
  sparseCoprime 8 128

def runCoprime (input : P 8 Int × P 8 Int) : UInt64 :=
  Matrix.runIntPair input

def prepDense (_ : Nat) : P 4 Int × P 4 Int :=
  denseGcd 4 5

def runDense (input : P 4 Int × P 4 Int) : UInt64 :=
  Matrix.runIntPair input

def prepSparse (_ : Nat) : P 5 Int × P 5 Int :=
  sparseGapGcd 5 16

def runSparse (input : P 5 Int × P 5 Int) : UInt64 :=
  Matrix.runIntPair input

def prepSwell (_ : Nat) : P 2 Int × P 2 Int :=
  swellGcd 5

def runSwell (input : P 2 Int × P 2 Int) : UInt64 :=
  Matrix.runIntPair input

def prepRational (_ : Nat) : P 4 Rat × P 4 Rat :=
  rationalGcd 4 5

def runRational (input : P 4 Rat × P 4 Rat) : UInt64 :=
  Matrix.runRatPair input

def prepSquarefree (_ : Nat) : P 4 Int :=
  squarefreeShape 4 [7]

def runSquarefree (input : P 4 Int) : UInt64 :=
  Matrix.runSquarefree input

def prepCofactor (_ : Nat) : P 2 Int × P 2 Int × P 2 Int :=
  cofactorHeavy 64

def runCofactor (input : P 2 Int × P 2 Int × P 2 Int) : UInt64 :=
  match divExact? input.1 input.2.1 with
  | none => 0
  | some quotient => checksum quotient

/- This is one fixed prepared computation, so the synthetic one-point
parameter has a constant cost model. -/
setup_benchmark runCoprime n => n + 1 with prep := prepCoprime where {
  paramSchedule := .custom #[0]
  tags := #[scheduledHardwareTag]
}

/- This is one fixed prepared computation, so the synthetic one-point
parameter has a constant cost model. -/
setup_benchmark runDense n => n + 1 with prep := prepDense where {
  paramSchedule := .custom #[0]
  tags := #[scheduledHardwareTag]
}

/- This is one fixed prepared computation, so the synthetic one-point
parameter has a constant cost model. -/
setup_benchmark runSparse n => n + 1 with prep := prepSparse where {
  paramSchedule := .custom #[0]
  tags := #[scheduledHardwareTag]
}

/- This is one fixed prepared computation, so the synthetic one-point
parameter has a constant cost model. -/
setup_benchmark runSwell n => n + 1 with prep := prepSwell where {
  paramSchedule := .custom #[0]
  tags := #[scheduledHardwareTag]
}

/- This is one fixed prepared computation, so the synthetic one-point
parameter has a constant cost model. -/
setup_benchmark runRational n => n + 1 with prep := prepRational where {
  paramSchedule := .custom #[0]
  tags := #[scheduledHardwareTag]
}

/- This is one fixed prepared computation, so the synthetic one-point
parameter has a constant cost model. -/
setup_benchmark runSquarefree n => n + 1 with prep := prepSquarefree where {
  paramSchedule := .custom #[0]
  tags := #[scheduledHardwareTag]
}

/- This is one fixed prepared computation, so the synthetic one-point
parameter has a constant cost model. -/
setup_benchmark runCofactor n => n + 1 with prep := prepCofactor where {
  paramSchedule := .custom #[0]
  tags := #[scheduledHardwareTag]
}

end Hex.MvGcdBench.Profile
