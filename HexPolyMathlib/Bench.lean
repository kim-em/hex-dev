import HexPolyMathlib.Euclid
import LeanBench

/-!
Benchmark registrations for the `HexPolyMathlib` dense-polynomial bridge.

This Phase 4 slice measures the conversion surfaces that connect the executable
`Hex.DensePoly` representation to Mathlib's `Polynomial` representation, plus
the GCD and extended-GCD bridge surfaces over deterministic Euclidean fixtures.

Scientific registrations:

* `runToPolynomialChecksum`: convert a normalized dense polynomial to a Mathlib
  polynomial through the executable finite-support payload and checksum its
  coefficients, `O(n)`.
* `runOfPolynomialChecksum`: rebuild a normalized dense polynomial from a
  Mathlib polynomial and checksum its coefficients, `O(n)`.
* `runRoundTripChecksum`: perform both dense and Mathlib conversion round trips
  over bounded-degree generated inputs, `O(n)`.
* `runGcdBridgeChecksum`: compute the executable polynomial gcd and transport
  it through the Mathlib bridge on a Fibonacci quotient-chain fixture, `O(n^2)`.
* `runXGcdBridgeChecksum`: compute executable extended-gcd components and
  transport them through the same bridge fixture, `O(n^2)`.
-/

namespace HexPolyMathlib.PolyBench

open Hex

/-- Hash prepared dense-polynomial inputs by their normalized coefficient arrays. -/
instance [Hashable R] [Zero R] [DecidableEq R] : Hashable (DensePoly R) where
  hash p := hash p.toArray

/-- Hash prepared Mathlib polynomial inputs by their finite coefficient window. -/
instance [Semiring R] [Hashable R] : Hashable (Polynomial R) where
  hash p := hash <| (Array.range (p.natDegree + 1)).map p.coeff

/-- Prepared dense bridge input with degree bounded by the generated coefficients. -/
structure DenseInput where
  poly : DensePoly Int
  deriving Hashable

/-- Prepared Mathlib bridge input with degree bounded by the generated coefficients. -/
structure MathlibInput where
  poly : Polynomial Int
  deriving Hashable

/-- Prepared paired dense and Mathlib bridge inputs for round-trip checksums. -/
structure RoundTripInput where
  dense : DensePoly Int
  mathlib : Polynomial Int
  deriving Hashable

/-- Prepared executable inputs for Euclidean bridge checksums. -/
structure GcdBridgeInput where
  lhs : DensePoly Rat
  rhs : DensePoly Rat
  deriving Hashable

/-- Deterministic mixing over machine words for compact benchmark observables. -/
def mixWord (acc x : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + x + 0xBF58476D1CE4E5B9

/-- Deterministic integer coefficient generator keyed by size, index, and salt. -/
def coeffValue (n i salt : Nat) : Int :=
  let raw := ((i + 1) * (salt + 17) + (i + 3) * (i + 5) * 13 + n * 29) % 1009
  Int.ofNat raw - 504

/-- Deterministic normalized dense polynomial with `n` generated coefficients. -/
def densePoly (n salt : Nat) : DensePoly Int :=
  if n = 0 then
    0
  else
    DensePoly.ofCoeffs <| (Array.range n).map fun i =>
      let coeff := coeffValue n i salt
      if i + 1 = n ∧ coeff = 0 then 1 else coeff

/-- Exact finite-support coefficient payload for a dense polynomial. -/
def denseFinsupp [Semiring R] [DecidableEq R] (p : DensePoly R) : AddMonoidAlgebra R Nat where
  support := (Finset.range p.size).filter fun i => p.coeff i ≠ 0
  toFun := p.coeff
  mem_support_toFun := by
    intro i
    constructor
    · intro hi
      exact (Finset.mem_filter.mp hi).2
    · intro hne
      have hlt : i < p.size := by
        by_contra hlt
        exact hne (DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hlt))
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hne⟩

/-- Executable mirror of `toPolynomial`, avoiding Mathlib's noncomputable semiring wrapper. -/
def toPolynomialBench [Semiring R] [DecidableEq R] (p : DensePoly R) : Polynomial R :=
  Polynomial.ofFinsupp (denseFinsupp p)

/-- Deterministic Mathlib polynomial with `n` generated coefficients. -/
def mathlibPoly (n salt : Nat) : Polynomial Int :=
  toPolynomialBench (densePoly n salt)

/-- Stable checksum for a dense polynomial's normalized coefficient array. -/
def checksumDense (p : DensePoly Int) : UInt64 :=
  p.toArray.foldl (fun acc coeff => mixWord acc (hash coeff)) 0

/-- Stable checksum for a Mathlib polynomial's finite coefficient window. -/
def checksumMathlib [Semiring R] [Hashable R] (p : Polynomial R) : UInt64 :=
  (Array.range (p.natDegree + 1)).foldl
    (fun acc i => mixWord acc (hash (p.coeff i))) 0

/-- Stable checksum for a pair of Mathlib polynomial values. -/
def checksumMathlibPair [Semiring R] [Hashable R] (p q : Polynomial R) : UInt64 :=
  mixWord (checksumMathlib p) (checksumMathlib q)

/-- Per-parameter dense fixture for conversion to Mathlib. -/
def prepDenseInput (n : Nat) : DenseInput :=
  { poly := densePoly n 53 }

/-- Per-parameter Mathlib fixture for conversion back to dense form. -/
def prepMathlibInput (n : Nat) : MathlibInput :=
  { poly := mathlibPoly n 89 }

/-- Per-parameter paired fixture for both conversion round trips. -/
def prepRoundTripInput (n : Nat) : RoundTripInput :=
  { dense := densePoly n 131
    mathlib := mathlibPoly n 173 }

/-- Consecutive polynomial Fibonacci inputs force many Euclidean quotient steps. -/
def prepGcdBridgeInput (n : Nat) : GcdBridgeInput :=
  let x := DensePoly.monomial 1 (1 : Rat)
  let pair :=
    (List.range (n + 1)).foldl
      (fun state _ =>
        let prev := state.1
        let curr := state.2
        (curr, x * curr + prev))
      ((0 : DensePoly Rat), (1 : DensePoly Rat))
  { lhs := pair.2
    rhs := pair.1 }

/-- Benchmark target: convert one dense polynomial and checksum Mathlib coefficients. -/
def runToPolynomialChecksum (input : DenseInput) : UInt64 :=
  checksumMathlib (toPolynomialBench input.poly)

/-- Benchmark target: convert one Mathlib polynomial and checksum dense coefficients. -/
def runOfPolynomialChecksum (input : MathlibInput) : UInt64 :=
  checksumDense (ofPolynomial input.poly)

/-- Benchmark target: checksum both dense and Mathlib conversion round trips. -/
def runRoundTripChecksum (input : RoundTripInput) : UInt64 :=
  let denseRoundTrip := ofPolynomial (toPolynomialBench input.dense)
  let mathlibRoundTrip := toPolynomialBench (ofPolynomial input.mathlib)
  mixWord (checksumDense denseRoundTrip) (checksumMathlib mathlibRoundTrip)

/-- Benchmark target: compute the executable gcd and transport it across the bridge. -/
def runGcdBridgeChecksum (input : GcdBridgeInput) : UInt64 :=
  checksumMathlib (toPolynomialBench (DensePoly.gcd input.lhs input.rhs))

/-- Benchmark target: compute executable extended-gcd data and transport it across the bridge. -/
def runXGcdBridgeChecksum (input : GcdBridgeInput) : UInt64 :=
  let denseResult := DensePoly.xgcd input.lhs input.rhs
  mixWord (checksumMathlib (toPolynomialBench denseResult.gcd))
    (checksumMathlibPair (toPolynomialBench denseResult.left) (toPolynomialBench denseResult.right))

/- Cost model: the executable `toPolynomial` payload enumerates the stored dense
coefficients once, so the generated `n`-coefficient fixture performs linear
bridge work. -/
setup_benchmark runToPolynomialChecksum n => n
  with prep := prepDenseInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: `ofPolynomial` enumerates coefficients through `natDegree`,
which is bounded by the generated `n`-coefficient fixture. -/
setup_benchmark runOfPolynomialChecksum n => n
  with prep := prepMathlibInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: the round-trip target performs one conversion in each direction
for dense-origin and Mathlib-origin inputs. Each pass is linear in `n`. -/
setup_benchmark runRoundTripChecksum n => n
  with prep := prepRoundTripInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The prepared inputs are consecutive polynomial Fibonacci values. They force
Theta(n) Euclidean quotient steps. Each degree-one quotient step spends linear
work in the current degree, and the final dense-to-Mathlib transport is linear
in the output degree. The Euclidean loop dominates, so the bridge task is
quadratic in the generated degree.
-/
setup_benchmark runGcdBridgeChecksum n => n * n
  with prep := prepGcdBridgeInput
  where {
    paramFloor := 16
    paramCeiling := 96
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
This uses the same Fibonacci quotient-chain fixture as `runGcdBridgeChecksum`.
Extended gcd carries Bezout updates through the Euclidean loop. With degree-one
quotients, those updates are linear at each decreasing degree, and transporting
the three output components is linear in their output sizes. The Euclidean loop
dominates, so the bridge checksum remains Theta(n^2).
-/
setup_benchmark runXGcdBridgeChecksum n => n * n
  with prep := prepGcdBridgeInput
  where {
    paramFloor := 16
    paramCeiling := 96
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end HexPolyMathlib.PolyBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
