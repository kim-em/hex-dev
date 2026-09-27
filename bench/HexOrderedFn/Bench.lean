/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexOrderedFn.Infinitesimal
import HexOrderedFn.Real
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
    targetInnerNanos := 1000000000, maxSecondsPerCall := 10, outerTrials := 3 }

def prepScan (n : Nat) : First := RationalFn.ofPoly (DensePoly.monomial n (-1))
def scan (f : First) : Int := Infinitesimal.sign orderSign f

-- Cost model: Θ(n): the numerator has n zero coefficients before its nonzero coefficient.
-- Preparation and the already-verified field arithmetic are outside the timed loop.
setup_benchmark scan n => n with prep := prepScan where config

def prepDegree (n : Nat) : First :=
  RationalFn.ofPoly (DensePoly.ofCoeffs (Array.replicate (n + 1) (1 : Rat)))
def degree (f : First) : Int := Infinitesimal.sign orderSign f

-- Cost model: Θ(1): numerator and denominator have nonzero constant coefficients. The scan
-- inspects no higher coefficient, regardless of the stored polynomial degree.
setup_benchmark degree _n => 1 with prep := prepDegree where config

def prepHeight (n : Nat) : First :=
  RationalFn.C (((2^n + 1 : Nat) : Rat) / ((2^n + 3 : Nat) : Rat))
def height (f : First) : Int := Infinitesimal.sign orderSign f

-- Cost model: Θ(1): equality and comparison with zero inspect the rational numerator's sign;
-- they do not traverse its limbs. Building the n-bit coefficient is preparation.
setup_benchmark height _n => 1 with prep := prepHeight where config

def prepSecond (n : Nat) : Second :=
  RationalFn.ofPoly (DensePoly.monomial n (RationalFn.X : First))
def second (f : Second) : Int := Infinitesimal.sign (Infinitesimal.sign orderSign) f

-- Cost model: Θ(n): n outer zero coefficients, followed by a fixed degree-one inner fraction.
setup_benchmark second n => n with prep := prepSecond where config

def prepThird (n : Nat) : Third :=
  RationalFn.ofPoly (DensePoly.monomial n
    (RationalFn.C (RationalFn.X : First) + (RationalFn.X : Second)))
def third (f : Third) : Int :=
  Infinitesimal.sign (Infinitesimal.sign (Infinitesimal.sign orderSign)) f

-- Cost model: Θ(n): another predecessor level adds bounded work at the first nonzero coefficient.
setup_benchmark third n => n with prep := prepThird where config

def prepCompare (n : Nat) : First × First :=
  (RationalFn.ofPoly (DensePoly.monomial n 1), prepScan n)
def comparison (pair : First × First) : Int :=
  match Infinitesimal.compare orderSign pair.1 pair.2 with
  | .lt => -1 | .eq => 0 | .gt => 1

-- Cost model: Θ(n): subtraction and the sign scan traverse degree-n arrays with bounded
-- coefficients and constant denominators. No nonconstant gcd is encountered.
setup_benchmark comparison n => n with prep := prepCompare where config


def compareConfig : LeanBench.BenchmarkConfig :=
  { config with paramSchedule := .custom #[16, 32, 64, 128, 256, 512, 1024, 2048] }

def prepDenominators (n : Nat) : First × First :=
  let p := prepDegree n
  (1 / p, 1 / (p + 1))

def denominators (pair : First × First) : Int := comparison pair

-- Cost model: Θ(n^log₂3): the dense product uses the default Karatsuba plan,
-- T(n)=3T(n/2)+Θ(n). The consecutive denominators have constant gcd; the
-- resulting constant numerator makes final normalization linear. Coefficient
-- heights are O(log n) and remain machine-sized on this degree ladder.
setup_benchmark denominators n => 3 ^ Nat.log2 (max n 1) with prep := prepDenominators where compareConfig

def heightConfig : LeanBench.BenchmarkConfig :=
  { config with paramSchedule := .custom #[65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] }

def prepCompareHeight (n : Nat) : First × First :=
  (RationalFn.C ((2^n + 1 : Nat) : Rat), RationalFn.C ((2^n + 2 : Nat) : Rat))

def compareHeight (pair : First × First) : Int := comparison pair

-- Cost model: Θ(n): fixed-degree subtraction traverses n-bit integer limbs before
-- cancellation leaves the constant -1. The operands have unit denominators.
setup_benchmark compareHeight n => n with prep := prepCompareHeight where heightConfig

open Oracle

private def window (q δ : Rat) : Bounds :=
  if h : 0 < δ then ⟨q - δ / 2, q + δ / 2, by grind⟩ else .singleton q

def prepProvider (n : Nat) : Rat := Real.precision n

def provider (δ : Rat) : Rat × Rat :=
  let b := window 2 δ
  (b.lower, b.upper)

-- Cost model: Θ(n): adding a fixed integer to a dyadic endpoint with n bits.
-- This isolates the test caller's interval construction from Horner and search.
setup_benchmark provider n => n with prep := prepProvider where heightConfig

/-- A finite checked witness authorizes this query, not a whole ordered field. -/
structure SignQuery where
  source : Approximation Rat
  subject : First
  progress : Acc (Next (Real.attempt source subject)) 0

private def signQuery (a : Approximation Rat) (f : First) (n : Nat) : IO SignQuery :=
  match h : Real.attempt a f n with
  | none => throw (IO.userError s!"sign preparation: no success at precision {n}")
  | some s => pure ⟨a, f, acc_of_success _ n s h 0 (by omega)⟩

def refinement (q : SignQuery) : Int := Real.sign q.source q.subject q.progress

/-- Preparation may reject a failed witness; the timed loop always runs total search
from zero. This is the ordinary lean-bench loop with an IO preparation stage. -/
private def registerSearch {α β : Type} [Hashable β] (name : Lean.Name)
    (formula : String) (cost : Nat → Nat) (cfg : LeanBench.BenchmarkConfig)
    (prepare : Nat → IO α) (run : α → β) : IO Unit := do
  LeanBench.register { name, complexityFormula := formula, hashable := true, config := cfg }
    (fun n => do
      let q ← prepare n
      return fun count => do
        if count == 0 then return (0, none)
        let mut digest := 0
        let start ← IO.monoNanosNow
        for _ in [0:count] do
          digest := hash (run q)
          LeanBench.blackBox digest
        let stop ← IO.monoNanosNow
        return (stop - start, some digest)) cost
  LeanBench.registerKernel name (fun n => do
    let q ← prepare n
    LeanBench.kernelLoop (fun () => pure (run q)) hash true)

def searchConfig : LeanBench.BenchmarkConfig :=
  { config with paramSchedule := .custom #[16, 32, 64, 128, 256, 512, 1024, 2048] }

private def prepRefinement (joint : Bool) (n : Nat) : IO SignQuery :=
  let a : Approximation Rat :=
    ⟨fun c δ => if joint then window c δ else .singleton c, window 2⟩
  let f := RationalFn.ofPoly (DensePoly.ofList [-(2 - Real.precision n), 1])
  signQuery a f (n + 3)

-- Cost model: Θ(n²) limb work: Θ(n) failed refinements on a linear polynomial,
-- with up to Θ(n) bits per rational. Dyadic denominators keep gcds simple.
initialize do
  registerSearch ``refinement "n * n" (fun n => n * n) searchConfig
    (prepRefinement false) refinement

def jointRefinement (q : SignQuery) : Int := refinement q

-- Cost model: Θ(n²), now both coefficients and the argument refine on every trial.
initialize do
  registerSearch ``jointRefinement "n * n" (fun n => n * n) searchConfig
    (prepRefinement true) jointRefinement

private def prepHorner (n : Nat) : IO SignQuery :=
  signQuery (.ofConstant (window 0)) (prepDegree n) 0

def horner (q : SignQuery) : Int := refinement q

-- Cost model: Θ(n²) bit work: n Horner steps at argument [-1/2,1/2] create
-- dyadic endpoints of increasing bit length. There is one successful trial.
initialize do
  registerSearch ``horner "n * n" (fun n => n * n) searchConfig prepHorner horner

private def prepRealHeight (n : Nat) : IO SignQuery :=
  let c : Rat := ((2^n + 1 : Nat) : Rat) / ((2^n + 3 : Nat) : Rat)
  signQuery (.ofConstant (window 0))
    (RationalFn.ofPoly (DensePoly.ofList [c, 1])) 1

def realHeight (q : SignQuery) : Int := refinement q

-- Cost model: Θ(n): one fixed-degree trial on n-bit rational coefficients;
-- denominator gcds are against powers of two of bounded height.
initialize do
  registerSearch ``realHeight "n" id heightConfig prepRealHeight realHeight

structure ApproxQuery where
  source : Approximation Rat
  subject : First
  width : Rat
  progress : Acc (Next (Real.approxAttempt source subject (Real.requestWidth width))) 0

private def prepApproximation (n : Nat) : IO ApproxQuery := do
  let a : Approximation Rat := ⟨window, window 2⟩
  let f : First := RationalFn.ofPoly (DensePoly.ofList [-1, 1])
  let δ := Real.precision n
  match h : Real.approxAttempt a f (Real.requestWidth δ) (n + 5) with
  | none => throw (IO.userError s!"approximation preparation: no success at precision {n + 5}")
  | some b => return ⟨a, f, δ, acc_of_success _ (n + 5) b h 0 (by omega)⟩

def approximation (q : ApproxQuery) : Rat × Rat :=
  let b := Real.approx q.source q.subject q.width q.progress
  (b.lower, b.upper)

-- Cost model: Θ(n²) bit work for Θ(n) joint refinement trials with Θ(n)-bit
-- dyadic inputs. Exact quotient endpoints also enter the final bound.
initialize do
  registerSearch ``approximation "n * n" (fun n => n * n) searchConfig
    prepApproximation approximation

end Hex.OrderedFnBench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
