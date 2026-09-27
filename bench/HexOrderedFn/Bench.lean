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
  { config with
    paramSchedule := .custom #[8192, 10240, 12288, 14336, 16384, 20480, 24576, 28672],
    maxSecondsPerCall := 60 }

private def prepRefinement (joint : Bool) (n : Nat) : IO SignQuery :=
  let a : Approximation Rat :=
    ⟨fun c δ => if joint then window c δ else .singleton c, window 2⟩
  let f := RationalFn.ofPoly (DensePoly.ofList [-(2 - Real.precision n), 1])
  signQuery a f (n + 3)

-- Mode 2 upper bound O(n³): O(n) trials use O(n)-bit rational operands.
-- Multiplication, division and gcd each have the published quadratic upper
-- bounds cited in the performance report. This is not a tight scaling claim;
-- GMP changes algorithms with operand size and exploits special operands.
initialize do
  registerSearch ``refinement "n * n * n" (fun n => n * n * n) searchConfig
    (prepRefinement false) refinement

def jointRefinement (q : SignQuery) : Int := refinement q

-- Mode 2 upper bound O(n³), including refinement of coefficients and argument.
initialize do
  registerSearch ``jointRefinement "n * n * n" (fun n => n * n * n) searchConfig
    (prepRefinement true) jointRefinement

private def prepHorner (n : Nat) : IO SignQuery :=
  signQuery (.ofConstant (window 0)) (prepDegree n) 0

def horner (q : SignQuery) : Int := refinement q

-- Mode 2 upper bound O(n³): n Horner steps at argument [-1/2,1/2] create
-- O(n)-bit endpoints; each rational operation costs at most O(n²).
initialize do
  registerSearch ``horner "n * n * n" (fun n => n * n * n)
    { searchConfig with targetInnerNanos := 4000000000 } prepHorner horner

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

-- Mode 2 upper bound O(n³): O(n) joint refinement trials operate on O(n)-bit
-- endpoints, including exact quotient formation, reduction and width checks.
initialize do
  registerSearch ``approximation "n * n * n" (fun n => n * n * n) searchConfig
    prepApproximation approximation

namespace Successive

open Hex.OrderedFn Hex.OrderedFn.Oracle

abbrev First := RationalFn Rat
abbrev Second := RationalFn First

private def window (q δ : Rat) : Bounds :=
  if h : 0 < δ then ⟨q - δ / 2, q + δ / 2, by grind⟩ else .singleton q

private def inner : Approximation Rat := .ofConstant (window 2)

structure Entry where
  subject : First
  width : Rat
  progress : Acc (Next (Real.approxAttempt inner subject (Real.requestWidth width))) 0

private def entry (f : First) (k : Nat) : IO Entry := do
  let δ := Real.precision k
  match h : Real.approxAttempt inner f (Real.requestWidth δ) (k + 2) with
  | none => throw (IO.userError "successive coefficient witness failed")
  | some b =>
    let value := f.num.eval 2 / f.den.eval 2
    unless b.lower ≤ value && value ≤ b.upper && b.width ≤ δ do
      throw (IO.userError "successive coefficient enclosure failed")
    return ⟨f, δ, acc_of_success _ (k + 2) b h 0 (by omega)⟩

private def execute (q : Entry) : Bounds :=
  Real.approx inner q.subject q.width q.progress

/-- The fixture covers every coefficient and request made before its outer
success witness. The exact fallback defines other requests at the same rational
subject; no global field embedding or width contract is asserted. -/
private def coefficient (entries : Array (Entry × Entry)) (c : First) (δ : Rat) : Bounds :=
  match entries[δ.den.log2]? with
  | some pair =>
    if c = pair.1.subject && δ = pair.1.width then execute pair.1
    else if c = pair.2.subject && δ = pair.2.width then execute pair.2
    else .singleton (c.num.eval 2 / c.den.eval 2)
  | none => .singleton (c.num.eval 2 / c.den.eval 2)

structure Query where
  source : Approximation First
  subject : Second
  width : Rat
  progress : Acc (Next (Real.approxAttempt source subject (Real.requestWidth width))) 0

def run (q : Query) : Rat × Rat :=
  let b := Real.approx q.source q.subject q.width q.progress
  (b.lower, b.upper)

/-- X₂ - X₁ at X₁=2, X₂=2+2⁻ⁿ; approximate it to width 2⁻ⁿ. -/
def prepare (n : Nat) : IO Query := do
  let δ := Real.precision n
  let f : Second := RationalFn.X - RationalFn.C RationalFn.X
  let negativeX : First := -RationalFn.X
  let mut entries := #[]
  for k in [:n + 4] do
    entries := entries.push (← entry negativeX k, ← entry 1 k)
  -- These are all coefficients actually requested by both Horner evaluations.
  unless f.num.coeffs == #[negativeX, 1] && f.den.coeffs == #[1] do
    throw (IO.userError "unexpected successive polynomial coefficients")
  let a : Approximation First := ⟨coefficient entries, window (2 + δ)⟩
  for k in [:n + 4] do
    let width := Real.precision k
    for c in f.num.coeffs ++ f.den.coeffs do
      unless entries[width.den.log2]?.any (fun p =>
          (c == p.1.subject && width == p.1.width) ||
          (c == p.2.subject && width == p.2.width)) do
        throw (IO.userError "successive request lacks an inner search witness")
  unless (Real.approxAttempt a f (Real.requestWidth δ) n).isNone &&
      (Real.approxAttempt a f (Real.requestWidth δ) (n + 1)).isSome do
    throw (IO.userError "unexpected successive separation precision")
  match h : Real.approxAttempt a f (Real.requestWidth δ) (n + 3) with
  | none => throw (IO.userError "successive outer witness failed")
  | some b =>
    unless b.lower ≤ δ && δ ≤ b.upper && b.width ≤ δ do
      throw (IO.userError "successive outer enclosure failed")
    let q : Query := ⟨a, f, δ, acc_of_success _ (n + 3) b h 0 (by omega)⟩
    let (lo, hi) := run q
    unless lo == δ / 2 && hi == 3 * δ / 2 do
      throw (IO.userError "successive total approximation failed")
    return q

end Successive

-- Preparation checks exact containment and width, and verifies that all requests
-- up to the outer witness have cached termination witnesses, avoiding the fallback.
#eval do
  for n in [0, 1, 4, 8, 16] do
    discard <| Hex.OrderedFnBench.Successive.prepare n

/-- The outer search executes one inner approximation search per
coefficient request; prepared witnesses never replace those searches. -/
def successiveApproximation (q : Successive.Query) : Rat × Rat := Successive.run q

-- Mode 1: count exact bound operations, including both search levels. There
-- are (n+2)(n+3)/2 negative-X trials (7 operations each), two constant-1
-- trials per outer trial (5 each), and 7 operations in each outer trial.
-- This ladder measures small operands; runtime gcd still calls GMP even
-- on scalar inputs. It does not model large-integer multiplication costs.
-- At n >= 14 comparison products exceed the 32-bit small-Int range and
-- allocate one-limb GMP integers. Each bound operation has unit model weight.
initialize do
  registerSearch ``successiveApproximation "(n + 2) * (7 * n + 55) / 2"
    (fun n => (n + 2) * (7 * n + 55) / 2)
    { config with
      paramSchedule := .custom #[4, 6, 8, 10, 12, 14, 16, 18],
      targetInnerNanos := 4000000000, maxSecondsPerCall := 60 }
    Successive.prepare successiveApproximation

end Hex.OrderedFnBench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
