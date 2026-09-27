/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexOrderedFn.Infinitesimal
import LeanBench

namespace Hex.OrderedFnBench

open Hex.OrderedFn

private instance {K : Type} [Lean.Grind.Field K] [DecidableEq K] [Hashable K] :
    Hashable (RationalFn K) := ⟨fun f => hash (f.num.coeffs, f.den.coeffs)⟩

abbrev First := RationalFn Rat
abbrev Second := RationalFn First
abbrev Third := RationalFn Second

def config : LeanBench.BenchmarkConfig :=
  { paramSchedule := .custom #[128, 256, 512, 1024, 2048, 4096, 8192, 16384],
    targetInnerNanos := 100000000, maxSecondsPerCall := 10, outerTrials := 3 }

def prepScan (n : Nat) : First := RationalFn.ofPoly (DensePoly.monomial n (-1))
def scan (f : First) : Int := Infinitesimal.sign orderSign f

-- Θ(n): the numerator has n zero coefficients before its nonzero coefficient.
-- Preparation and the already-verified field arithmetic are outside the timed loop.
setup_benchmark scan n => n with prep := prepScan where config

def prepDegree (n : Nat) : First :=
  RationalFn.ofPoly (DensePoly.ofCoeffs (Array.replicate (n + 1) (1 : Rat)))
def degree (f : First) : Int := Infinitesimal.sign orderSign f

-- Θ(1): numerator and denominator have nonzero constant coefficients. The scan
-- inspects no higher coefficient, regardless of the stored polynomial degree.
setup_benchmark degree _n => 1 with prep := prepDegree where config

def prepHeight (n : Nat) : First :=
  RationalFn.C (((2^n + 1 : Nat) : Rat) / ((2^n + 3 : Nat) : Rat))
def height (f : First) : Int := Infinitesimal.sign orderSign f

-- Θ(1): equality and comparison with zero inspect the rational numerator's sign;
-- they do not traverse its limbs. Building the n-bit coefficient is preparation.
setup_benchmark height _n => 1 with prep := prepHeight where config

def prepSecond (n : Nat) : Second :=
  RationalFn.ofPoly (DensePoly.monomial n (RationalFn.X : First))
def second (f : Second) : Int := Infinitesimal.sign (Infinitesimal.sign orderSign) f

-- Θ(n): n outer zero coefficients, followed by a fixed degree-one inner fraction.
setup_benchmark second n => n with prep := prepSecond where config

def prepThird (n : Nat) : Third :=
  RationalFn.ofPoly (DensePoly.monomial n
    (RationalFn.C (RationalFn.X : First) + (RationalFn.X : Second)))
def third (f : Third) : Int :=
  Infinitesimal.sign (Infinitesimal.sign (Infinitesimal.sign orderSign)) f

-- Θ(n): another predecessor level adds bounded work at the first nonzero coefficient.
setup_benchmark third n => n with prep := prepThird where config

def prepCompare (n : Nat) : First × First :=
  (RationalFn.ofPoly (DensePoly.monomial n 1), prepScan n)
def comparison (pair : First × First) : Int :=
  match Infinitesimal.compare orderSign pair.1 pair.2 with
  | .lt => -1 | .eq => 0 | .gt => 1

-- Θ(n): subtraction and the sign scan traverse degree-n arrays with bounded
-- coefficients and constant denominators. No nonconstant gcd is encountered.
setup_benchmark comparison n => n with prep := prepCompare where config

end Hex.OrderedFnBench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
