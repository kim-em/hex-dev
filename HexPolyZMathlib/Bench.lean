import HexPolyZMathlib.Mignotte
import LeanBench

/-!
Benchmark registrations for the `HexPolyZMathlib` integer-polynomial bridge.

This Phase 4 slice measures the executable bridge surfaces between `Hex.ZPoly`
and Mathlib's `Polynomial ℤ`, plus the Mignotte-bound bridge checksum that ties
the executable coefficient-bound helper to the Mathlib-facing `Nat.choose`
surface. Proof terms for `mignotte_bound` and `l2norm_toPolynomial_sq_le_coeffNormSq`
are erased by compiled execution, so the benchmarkable surface is the
coefficient and bound data those theorem statements connect.

Scientific registrations:

* `runToPolynomialChecksum`: convert a normalized `ZPoly` to `Polynomial ℤ` and
  checksum coefficients, `O(n)`.
* `runOfPolynomialChecksum`: rebuild a `ZPoly` from a generated
  `Polynomial ℤ` and checksum dense coefficients, `O(n)`.
* `runEquivRoundTripChecksum`: perform paired executable mirrors of
  `equiv`/`equiv.symm` round trips and checksum both results, `O(n)`.
* `runMignotteBridgeChecksum`: checksum the executable Mignotte coefficient
  bound together with the Mathlib `Nat.choose` bridge expression, `O(n)`.
-/

namespace HexPolyZMathlib.Bench

open Hex

/-- Hash prepared dense-polynomial inputs by their normalized coefficient arrays. -/
instance : Hashable ZPoly where
  hash p := hash p.toArray

/-- Hash prepared Mathlib polynomial inputs by their finite coefficient window. -/
instance : Hashable (Polynomial ℤ) where
  hash p := hash <| (Array.range (p.natDegree + 1)).map p.coeff

/-- Prepared dense bridge input with degree bounded by the generated coefficients. -/
structure DenseInput where
  poly : ZPoly
  deriving Hashable

/-- Prepared Mathlib bridge input with degree bounded by the generated coefficients. -/
structure MathlibInput where
  poly : Polynomial ℤ
  deriving Hashable

/-- Prepared paired dense and Mathlib bridge inputs for round-trip checksums. -/
structure RoundTripInput where
  dense : ZPoly
  mathlib : Polynomial ℤ
  deriving Hashable

/-- Prepared integer-polynomial bridge input for Mignotte-bound checksums. -/
structure MignotteBridgeInput where
  poly : ZPoly
  factorDegree : Nat
  coeffIndex : Nat
  deriving Hashable

/-- Deterministic mixing over machine words for compact benchmark observables. -/
def mixWord (acc x : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + x + 0xBF58476D1CE4E5B9

/-- Deterministic integer coefficient generator keyed by size, index, and salt. -/
def coeffValue (n i salt : Nat) : Int :=
  let raw := ((i + 1) * (salt + 19) + (i + 5) * (i + 11) * 17 + n * 31) % 2003
  let value := Int.ofNat raw - 1001
  if value = 0 then Int.ofNat (salt % 13 + 1) else value

/-- Deterministic normalized integer polynomial with `n` generated coefficients. -/
def denseZPoly (n salt : Nat) : ZPoly :=
  if n = 0 then
    0
  else
    DensePoly.ofCoeffs <| (Array.range n).map fun i =>
      let coeff := coeffValue n i salt
      if i + 1 = n ∧ coeff = 0 then 1 else coeff

/-- Exact finite-support coefficient payload for a dense polynomial. -/
def denseFinsupp (p : ZPoly) : AddMonoidAlgebra ℤ Nat where
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

/-- Executable mirror of `toPolynomial`, avoiding the noncomputable wrapper. -/
def toPolynomialBench (p : ZPoly) : Polynomial ℤ :=
  Polynomial.ofFinsupp (denseFinsupp p)

/-- Executable mirror of `equiv` application for benchmark timing. -/
def equivApplyBench (p : ZPoly) : Polynomial ℤ :=
  toPolynomialBench p

/-- Executable mirror of `equiv.symm` application for benchmark timing. -/
def equivSymmApplyBench (p : Polynomial ℤ) : ZPoly :=
  HexPolyMathlib.ofPolynomial p

/-- Deterministic Mathlib polynomial with `n` generated coefficients. -/
def mathlibPoly (n salt : Nat) : Polynomial ℤ :=
  toPolynomialBench (denseZPoly n salt)

/-- Stable checksum for a dense polynomial's normalized coefficient array. -/
def checksumDense (p : ZPoly) : UInt64 :=
  p.toArray.foldl (fun acc coeff => mixWord acc (hash coeff)) 0

/-- Stable checksum for a Mathlib polynomial's finite coefficient window. -/
def checksumMathlib (p : Polynomial ℤ) : UInt64 :=
  (Array.range (p.natDegree + 1)).foldl
    (fun acc i => mixWord acc (hash (p.coeff i))) 0

/-- Stable checksum for a natural-number bridge expression. -/
def checksumNat (acc n : Nat) : UInt64 :=
  mixWord (hash acc) (hash n)

/-- Per-parameter dense fixture for conversion to Mathlib. -/
def prepDenseInput (n : Nat) : DenseInput :=
  { poly := denseZPoly n 53 }

/-- Per-parameter Mathlib fixture for conversion back to dense form. -/
def prepMathlibInput (n : Nat) : MathlibInput :=
  { poly := mathlibPoly n 89 }

/-- Per-parameter paired fixture for both bridge round trips. -/
def prepRoundTripInput (n : Nat) : RoundTripInput :=
  { dense := denseZPoly n 131
    mathlib := mathlibPoly n 173 }

/-- Per-parameter fixture for the Mignotte-bound bridge checksum. -/
def prepMignotteBridgeInput (n : Nat) : MignotteBridgeInput :=
  let factorDegree := Nat.log2 (n + 1)
  { poly := denseZPoly n 211
    factorDegree := factorDegree
    coeffIndex := factorDegree / 2 }

/-- Benchmark target: convert one dense polynomial and checksum Mathlib coefficients. -/
def runToPolynomialChecksum (input : DenseInput) : UInt64 :=
  checksumMathlib (toPolynomialBench input.poly)

/-- Benchmark target: convert one Mathlib polynomial and checksum dense coefficients. -/
def runOfPolynomialChecksum (input : MathlibInput) : UInt64 :=
  checksumDense (HexPolyMathlib.ofPolynomial input.poly)

/-- Benchmark target: checksum executable mirrors of both ring-equivalence round trips. -/
def runEquivRoundTripChecksum (input : RoundTripInput) : UInt64 :=
  let denseRoundTrip := equivSymmApplyBench (equivApplyBench input.dense)
  let mathlibRoundTrip := equivApplyBench (equivSymmApplyBench input.mathlib)
  mixWord (checksumDense denseRoundTrip) (checksumMathlib mathlibRoundTrip)

/--
Benchmark target: checksum the executable Mignotte bound and the matching
Mathlib `Nat.choose` expression exposed by `binom_eq_choose`.
-/
def runMignotteBridgeChecksum (input : MignotteBridgeInput) : UInt64 :=
  let executable :=
    ZPoly.mignotteCoeffBound input.poly input.factorDegree input.coeffIndex
  let mathlibChoose :=
    Nat.choose input.factorDegree input.coeffIndex * ZPoly.coeffL2NormBound input.poly
  checksumNat executable mathlibChoose

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
setup_benchmark runEquivRoundTripChecksum n => n
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
`mignotteCoeffBound` computes `binom k j * coeffL2NormBound f`. Here `f` has
`n` coefficients and `k = log2 (n + 1)`, so the coefficient-norm scan is linear
while the `Nat.choose` bridge expression is sublinear relative to the fixture
size.
-/
setup_benchmark runMignotteBridgeChecksum n => n
  with prep := prepMignotteBridgeInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end HexPolyZMathlib.Bench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
