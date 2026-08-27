/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyFast
import LeanBench

/-!
Scientific benchmark registrations for hex-poly-fast dispatch and reusable
plans. Input preparation is excluded from timing except in explicitly cold
plan targets, and every target consumes its result through a coefficient hash.
-/

namespace Hex.PolyFastBench

open Hex Hex.DensePoly

private abbrev F2 := Fin 2

private def f2Inv (a : F2) : F2 := a
private def f2Div (a b : F2) : F2 := a * b
private def f2Zpow (a : F2) (n : Int) : F2 :=
  if n = 0 then 1 else a

local instance (priority := 2000) : Inv F2 := ⟨f2Inv⟩
local instance (priority := 2000) : Div F2 := ⟨f2Div⟩
local instance : HPow F2 Int F2 := ⟨f2Zpow⟩

private theorem f2_cases (a : F2) : a = 0 ∨ a = 1 := by
  rcases a with ⟨a, ha⟩
  have : a = 0 ∨ a = 1 := by omega
  rcases this with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

local instance : Lean.Grind.Field F2 where
  toCommRing := inferInstance
  inv := f2Inv
  div := f2Div
  zpow := ⟨f2Zpow⟩
  div_eq_mul_inv := by intros; rfl
  zero_ne_one := by decide
  inv_zero := rfl
  mul_inv_cancel := by
    intro a ha
    rcases f2_cases a with hzero | hone
    · exact False.elim (ha hzero)
    · subst a
      rfl
  zpow_zero := by intro; simp [f2Zpow]
  zpow_succ := by
    intro a n
    cases n with
    | zero =>
        change a = 1 * a
        exact (Lean.Grind.Semiring.one_mul a).symm
    | succ n =>
        have hn : (n + 1 : Int) ≠ 0 := by omega
        have hn₁ : (n + 1 : Int) + 1 ≠ 0 := by omega
        rcases f2_cases a with hzero | hone <;> subst a <;>
          simp [f2Zpow, hn, hn₁]
  zpow_neg := by
    intro a n
    by_cases hn : n = 0
    · subst n
      simp [f2Zpow, f2Inv]
    · simp [f2Zpow, hn, f2Inv]

structure Binary where
  left : DensePoly Int
  right : DensePoly Int

instance : Hashable Binary where
  hash input := mixHash (hash input.left.toArray) (hash input.right.toArray)

/-- Fixed-precision integer-series operands used to compare the retained
schoolbook `TSeries.mulUpTo` with the dependency-safe polynomial-plan path. -/
structure SeriesIntInput where
  n : Nat
  left : TSeries Int n
  right : TSeries Int n

/-- The same bounded-product campaign over rational coefficients. -/
structure SeriesRatInput where
  n : Nat
  left : TSeries Rat n
  right : TSeries Rat n

instance : Hashable SeriesIntInput where
  hash input := mixHash (hash input.n)
    (mixHash (hash input.left.coeffs.toArray) (hash input.right.coeffs.toArray))

instance : Hashable SeriesRatInput where
  hash input := mixHash (hash input.n)
    (mixHash (hash input.left.coeffs.toArray) (hash input.right.coeffs.toArray))

private def coeff (i salt : Nat) : Int :=
  Int.ofNat (((i + 3) * (salt + 11)) % 101 + 1) - 50

def prepBalanced (n : Nat) : Binary :=
  { left := ofList ((List.range n).map fun i => coeff i 3)
    right := ofList ((List.range n).map fun i => coeff i 19) }

def prepSkew (n : Nat) : Binary :=
  { left := ofList ((List.range (64 * n)).map fun i => coeff i 5)
    right := ofList ((List.range n).map fun i => coeff i 23) }

def prepSeriesInt (n : Nat) : SeriesIntInput :=
  { n
    left := TSeries.ofFn fun i => coeff i 29
    right := TSeries.ofFn fun i => coeff i 43 }

def prepSeriesRat (n : Nat) : SeriesRatInput :=
  { n
    left := TSeries.ofFn fun i => (coeff i 31 : Rat)
    right := TSeries.ofFn fun i => (coeff i 47 : Rat) }

private def checksum (p : DensePoly Int) : UInt64 :=
  p.toArray.foldl (fun acc x => mixHash acc (hash x)) 0

private def checksumSeries [Hashable R] (a : TSeries R n) : UInt64 :=
  a.coeffs.toArray.foldl (fun acc x => mixHash acc (hash x)) 0

def runSchoolbook (input : Binary) : UInt64 :=
  checksum (mulWith schoolbookPlan input.left input.right)

def runKaratsuba (input : Binary) : UInt64 :=
  checksum (mulWith (karatsubaPlan 32) input.left input.right)

def runKaratsubaSkew (input : Binary) : UInt64 :=
  checksum (mulWith (karatsubaPlan 32) input.left input.right)

def runKaratsubaSquare (input : Binary) : UInt64 :=
  checksum (squareWith (karatsubaPlan 32) input.left)

/-- Retained semiring-generic bounded series multiplication. -/
def runSeriesSchoolbookInt (input : SeriesIntInput) : UInt64 :=
  checksumSeries (TSeries.mulUpTo input.n input.left input.right)

/-- Bounded series multiplication through the generic Karatsuba plan. -/
def runSeriesKaratsubaInt (input : SeriesIntInput) : UInt64 :=
  checksumSeries
    (seriesMulUpTo (karatsubaPlan 32) input.n input.left input.right)

/-- Rational-coefficient retained bounded series multiplication. -/
def runSeriesSchoolbookRat (input : SeriesRatInput) : UInt64 :=
  checksumSeries (TSeries.mulUpTo input.n input.left input.right)

/-- Rational bounded series multiplication through the Karatsuba plan. -/
def runSeriesKaratsubaRat (input : SeriesRatInput) : UInt64 :=
  checksumSeries
    (seriesMulUpTo (karatsubaPlan 32) input.n input.left input.right)

structure DivisionInput where
  dividend : DensePoly Rat
  divisor : DensePoly Rat

instance : Hashable DivisionInput where
  hash input := mixHash (hash input.dividend.toArray) (hash input.divisor.toArray)

/-- One dividend paired with a reciprocal plan prepared outside timing. -/
structure CachedDivisionInput where
  dividend : DensePoly Rat
  plan : Option (DivPlan Rat)

/-- A fixed divisor reused across several dividends. -/
structure RepeatedDivisionInput where
  dividends : Array (DensePoly Rat)
  divisor : DensePoly Rat
  plan : Option (DivPlan Rat)

instance : Hashable CachedDivisionInput where
  hash input := mixHash (hash input.dividend.toArray) <| match input.plan with
    | none => 0
    | some plan => hash plan.divisor.toArray

instance : Hashable RepeatedDivisionInput where
  hash input := mixHash
    (input.dividends.foldl (fun acc p => mixHash acc (hash p.toArray)) 0)
    (hash input.divisor.toArray)

private def divisionDividend (n salt : Nat) : DensePoly Rat :=
  ofList ((List.range (2 * n + 1)).map fun i => (coeff i salt : Rat))

private def divisionDivisor (n : Nat) : DensePoly Rat :=
  ofList (((List.range n).map fun i => (coeff i 47 : Rat)) ++ [1])

def prepDivision (n : Nat) : DivisionInput :=
  { dividend := divisionDividend n 31
    divisor := divisionDivisor n }

private def cachedPlan? (divisor : DensePoly Rat) (capacity : Nat) :
    Option (DivPlan Rat) :=
  if h : divisor = 0 then
    none
  else
    some (DivPlan.ofNonzero (karatsubaPlan 32) divisor h capacity)

def prepCachedDivision (n : Nat) : CachedDivisionInput :=
  let input := prepDivision n
  let capacity := quotientLength input.dividend input.divisor
  { dividend := input.dividend
    plan := cachedPlan? input.divisor capacity }

def prepRepeatedDivision (n : Nat) : RepeatedDivisionInput :=
  let divisor := divisionDivisor n
  let dividends := (Array.range 8).map fun i => divisionDividend n (31 + i * 13)
  let capacity := 2 * n + 1
  { dividends
    divisor
    plan := cachedPlan? divisor capacity }

private def checksumRat (p : DensePoly Rat) : UInt64 :=
  p.toArray.foldl (fun acc x => mixHash acc (hash x)) 0

private def checksumDiv (qr : DensePoly Rat × DensePoly Rat) : UInt64 :=
  mixHash (checksumRat qr.1) (checksumRat qr.2)

def runLongDivision (input : DivisionInput) : UInt64 :=
  checksumDiv (divMod input.dividend input.divisor)

def runNewtonDivision (input : DivisionInput) : UInt64 :=
  checksumDiv (divModWith (karatsubaPlan 32) input.dividend input.divisor)

def runCachedDivision (input : CachedDivisionInput) : UInt64 :=
  match input.plan with
  | none => 0
  | some plan =>
      if hcap : quotientLength input.dividend plan.divisor ≤ plan.capacity then
        checksumDiv (plan.divMod input.dividend hcap)
      else
        0

def runRepeatedNewtonDivision (input : RepeatedDivisionInput) : UInt64 :=
  input.dividends.foldl (fun acc dividend =>
    mixHash acc <| checksumDiv
      (divModWith (karatsubaPlan 32) dividend input.divisor)) 0

def runRepeatedCachedDivision (input : RepeatedDivisionInput) : UInt64 :=
  match input.plan with
  | none => 0
  | some plan =>
      input.dividends.foldl (fun acc dividend =>
        if hcap : quotientLength dividend plan.divisor ≤ plan.capacity then
          mixHash acc (checksumDiv (plan.divMod dividend hcap))
        else
          acc) 0

structure GcdInput where
  left : DensePoly F2
  right : DensePoly F2

instance : Hashable GcdInput where
  hash input := mixHash (hash input.left.toArray) (hash input.right.toArray)

private def f2Coeff (i salt : Nat) : F2 :=
  if (mixHash (hash i) (hash salt)).toNat / 65536 % 2 = 0 then 0 else 1

def prepGcdBalanced (n : Nat) : GcdInput :=
  { left := ofList (((List.range (n + 1)).map fun i => f2Coeff i 83) ++ [1])
    right := ofList (((List.range n).map fun i => f2Coeff i 97) ++ [1]) }

def prepGcdSkew (n : Nat) : GcdInput :=
  { left := ofList (((List.range (4 * n + 1)).map fun i => f2Coeff i 89) ++ [1])
    right := ofList (((List.range n).map fun i => f2Coeff i 101) ++ [1]) }

private def checksumF2 (p : DensePoly F2) : UInt64 :=
  p.toArray.foldl (fun acc x => mixHash acc (hash x.val)) 0

private def checksumDivF2 (qr : DensePoly F2 × DensePoly F2) : UInt64 :=
  mixHash (checksumF2 qr.1) (checksumF2 qr.2)

def runSkewLongDivision (input : GcdInput) : UInt64 :=
  checksumDivF2 (divMod input.left input.right)

def runSkewNewtonDivision (input : GcdInput) : UInt64 :=
  checksumDivF2
    (divModWith (karatsubaPlan 32) input.left input.right)

private def checksumXgcd (result : XGCDResult F2) : UInt64 :=
  mixHash (checksumF2 result.gcd)
    (mixHash (checksumF2 result.left) (checksumF2 result.right))

private def checksumXgcdLeft (result : XGCDLeftResult F2) : UInt64 :=
  mixHash (checksumF2 result.gcd) (checksumF2 result.left)

def runEuclideanXgcd (input : GcdInput) : UInt64 :=
  checksumXgcd (xgcd input.left input.right)

def runHalfGcd (input : GcdInput) : UInt64 :=
  checksumXgcd (xgcdWith (karatsubaPlan 32) input.left input.right)

def runHalfGcdSkew (input : GcdInput) : UInt64 :=
  checksumXgcd (xgcdWith (karatsubaPlan 32) input.left input.right)

def runHalfGcdLeft (input : GcdInput) : UInt64 :=
  checksumXgcdLeft (xgcdLeftWith (karatsubaPlan 32) input.left input.right)

structure ProductTreeInput where
  leaves : Array (DensePoly Int)

instance : Hashable ProductTreeInput where
  hash input := input.leaves.foldl
    (fun acc p => mixHash acc (hash p.toArray)) 0

def prepProductTree (n : Nat) : ProductTreeInput :=
  { leaves := (List.range n).map (fun i => ofList [-(coeff i 59), 1]) |>.toArray }

def runProductTree (input : ProductTreeInput) : UInt64 :=
  checksum (ProductTree.build (karatsubaPlan 32) input.leaves).root

structure MultipointInput where
  plan : EvalPlan Int
  polynomial : DensePoly Int

instance : Hashable MultipointInput where
  hash input := mixHash (hash input.plan.points) (hash input.polynomial.toArray)

/-- Several polynomials sharing one point/remainder-tree plan. -/
structure MultipointBatchInput where
  plan : EvalPlan Int
  polynomials : Array (DensePoly Int)

instance : Hashable MultipointBatchInput where
  hash input := mixHash (hash input.plan.points) <|
    input.polynomials.foldl (fun acc p => mixHash acc (hash p.toArray)) 0

private def evalPointsFor (n : Nat) : Array Int :=
  (List.range n).map (fun i => Int.ofNat i - Int.ofNat (n / 2)) |>.toArray

private def evalPolynomial (n salt : Nat) : DensePoly Int :=
  ofList ((List.range n).map fun i => coeff i salt)

def prepMultipoint (n : Nat) : MultipointInput :=
  let points := evalPointsFor n
  { plan := EvalPlan.build (karatsubaPlan 32) points
    polynomial := evalPolynomial n 71 }

def prepMultipointBatch (n : Nat) : MultipointBatchInput :=
  let points := evalPointsFor n
  { plan := EvalPlan.build (karatsubaPlan 32) points
    polynomials := (Array.range 8).map fun i => evalPolynomial n (71 + i * 17) }

private def checksumValues (values : Array Int) : UInt64 :=
  values.foldl (fun acc value => mixHash acc (hash value)) 0

def runDirectEval (input : MultipointInput) : UInt64 :=
  checksumValues (input.plan.points.map (input.polynomial.eval ·))

def runMultipointEval (input : MultipointInput) : UInt64 :=
  checksumValues (input.plan.eval input.polynomial)

def runColdMultipointEval (input : MultipointInput) : UInt64 :=
  let plan := EvalPlan.build (karatsubaPlan 32) input.plan.points
  checksumValues (plan.eval input.polynomial)

def runRepeatedDirectEval (input : MultipointBatchInput) : UInt64 :=
  input.polynomials.foldl (fun acc polynomial =>
    mixHash acc <| checksumValues (input.plan.points.map (polynomial.eval ·))) 0

def runRepeatedMultipointEval (input : MultipointBatchInput) : UInt64 :=
  input.polynomials.foldl (fun acc polynomial =>
    mixHash acc <| checksumValues (input.plan.eval polynomial)) 0

structure InterpolationInput where
  points : Array Rat
  values : Array Rat
  plan : Option (InterpPlan Rat)

instance : Hashable InterpolationInput where
  hash input := mixHash (hash input.points) (hash input.values)

def prepInterpolation (n : Nat) : InterpolationInput :=
  let points := (List.range n).map (fun (i : Nat) => (i : Rat)) |>.toArray
  let values := points.map fun x => x * x * x - 7 * x + 11
  { points
    values
    plan := InterpPlan.build? (karatsubaPlan 32) points }

/-- Direct Lagrange interpolation, independently rebuilding every numerator
and denominator. This is the executable comparator for the reusable plan. -/
def directLagrange (points values : Array Rat) : DensePoly Rat :=
  let n := min points.size values.size
  (List.range n).foldl (fun sum i =>
    let ai := points.getD i 0
    let numerator := (List.range n).foldl (fun product j =>
      if i = j then product else product * pointFactor (points.getD j 0)) 1
    let denominator := (List.range n).foldl (fun product j =>
      if i = j then product else product * (ai - points.getD j 0)) 1
    sum + C (values.getD i 0 * denominator⁻¹) * numerator) 0

def runDirectInterpolation (input : InterpolationInput) : UInt64 :=
  checksumRat (directLagrange input.points input.values)

def runPlannedInterpolation (input : InterpolationInput) : UInt64 :=
  match input.plan with
  | none => 0
  | some plan =>
      match plan.interpolate? input.values with
      | none => 0
      | some p => checksumRat p

def runColdInterpolation (input : InterpolationInput) : UInt64 :=
  match InterpPlan.build? (karatsubaPlan 32) input.points with
  | none => 0
  | some plan =>
      match plan.interpolate? input.values with
      | none => 0
      | some p => checksumRat p

/- Cost model: a balanced length-`n` schoolbook convolution evaluates one
coefficient product for each input pair, hence `n²` ring multiplications. -/
setup_benchmark runSchoolbook n => n ^ 2
  with prep := prepBalanced
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "schoolbook", "balanced"]
  }

/- Cost model: balanced Karatsuba satisfies `T(n) = 3T(n/2) + O(n)`, hence
`T(n) = Θ(n^(log₂ 3))`; `n * sqrt n` is its integer-valued surrogate.
The nearby 31/32/33 rungs expose the fixed cutoff. -/
setup_benchmark runKaratsuba n => n * (Nat.sqrt n)
  with prep := prepBalanced
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "balanced"]
  }

/- Cost model: specialized squaring performs three recursive squares plus
linear combination work, so it obeys the same `Θ(n^(log₂ 3))` recurrence;
`n * sqrt n` is the integer-valued Karatsuba-range surrogate. -/
setup_benchmark runKaratsubaSquare n => n * (Nat.sqrt n)
  with prep := prepBalanced
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "square"]
  }

/- Cost model: the 64:1 dispatcher partitions the long operand into 64
length-`n` blocks.  That constant factor preserves the balanced Karatsuba
bound `Θ(n^(log₂ 3))`, represented by the `n * sqrt n` surrogate. -/
setup_benchmark runKaratsubaSkew n => n * (Nat.sqrt n)
  with prep := prepSkew
  where {
    paramFloor := 4
    paramCeiling := 256
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "ratio-64"]
  }

/- The lower library deliberately retains its weak semiring schoolbook API.
This registration measures that triangular convolution against the
commutative-ring Karatsuba plan supplied above the dependency boundary. -/
setup_benchmark runSeriesSchoolbookInt n => n ^ 2
  with prep := prepSeriesInt
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 128, 256, 512,
      1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 20.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["series-multiplication", "schoolbook", "int", "bounded"]
  }

setup_benchmark runSeriesKaratsubaInt n => n * Nat.sqrt n
  with prep := prepSeriesInt
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 128, 256, 512,
      1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 20.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["series-multiplication", "karatsuba", "int", "bounded"]
  }

setup_benchmark runSeriesSchoolbookRat n => n ^ 2
  with prep := prepSeriesRat
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 128, 256, 512,
      1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 45.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["series-multiplication", "schoolbook", "rat", "bounded"]
  }

setup_benchmark runSeriesKaratsubaRat n => n * Nat.sqrt n
  with prep := prepSeriesRat
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 128, 256, 512,
      1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 45.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["series-multiplication", "karatsuba", "rat", "bounded"]
  }

/- The long-division comparator eliminates one leading coefficient at a time
and updates a linear suffix, giving a quadratic coefficient-operation model. -/
setup_benchmark runLongDivision n => n ^ 2
  with prep := prepDivision
  where {
    paramFloor := 4
    paramCeiling := 4096
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["division", "long", "cold"]
  }

/- Cost model: a cold Newton call includes reciprocal construction and three clipped
Karatsuba products.  Doubling is geometric, so the balanced model remains
`Θ(M(n))`, represented by the Karatsuba-range integer surrogate. -/
setup_benchmark runNewtonDivision n => n * (Nat.sqrt n)
  with prep := prepDivision
  where {
    paramFloor := 4
    paramCeiling := 4096
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["division", "newton", "cold"]
  }

/- Reciprocal construction is hoisted into `prep`; the timed body performs
only the quotient low product and reconstruction product. -/
setup_benchmark runCachedDivision n => n * Nat.sqrt n
  with prep := prepCachedDivision
  where {
    paramFloor := 4
    paramCeiling := 4096
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["division", "newton", "cached-divisor", "warm-plan"]
  }

/- Eight dividends share one fixed reciprocal. This separates amortized plan
reuse from the one-shot comparison above. -/
setup_benchmark runRepeatedNewtonDivision n => 8 * n * Nat.sqrt n
  with prep := prepRepeatedDivision
  where {
    paramFloor := 4
    paramCeiling := 1024
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["division", "newton", "repeated", "cold-plan"]
  }

setup_benchmark runRepeatedCachedDivision n => 8 * n * Nat.sqrt n
  with prep := prepRepeatedDivision
  where {
    paramFloor := 4
    paramCeiling := 1024
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["division", "newton", "repeated", "warm-plan"]
  }

setup_benchmark runSkewLongDivision n => n ^ 2
  with prep := prepGcdSkew
  where {
    paramFloor := 4
    paramCeiling := 1024
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["division", "long", "ratio-4"]
  }

setup_benchmark runSkewNewtonDivision n => n * (Nat.sqrt n)
  with prep := prepGcdSkew
  where {
    paramFloor := 4
    paramCeiling := 1024
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["division", "newton", "ratio-4"]
  }

/- The established extended Euclidean loop performs a linear number of
remainder steps.  Over the fixed coefficient field, division and the Bezout
updates have total quadratic degree cost. -/
setup_benchmark runEuclideanXgcd n => n ^ 2
  with prep := prepGcdBalanced
  where {
    paramFloor := 4
    paramCeiling := 512
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["half-gcd", "euclidean", "balanced"]
  }

/- Recursive high-half transformations group the quotient sequence into a
logarithmic number of balanced matrix levels, for `O(M(n) log n)`. -/
setup_benchmark runHalfGcd n => n * (Nat.sqrt n) * (Nat.log2 n + 1)
  with prep := prepGcdBalanced
  where {
    paramFloor := 4
    paramCeiling := 2048
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["half-gcd", "matrix", "balanced"]
  }

setup_benchmark runHalfGcdSkew n => n * (Nat.sqrt n) * (Nat.log2 n + 1)
  with prep := prepGcdSkew
  where {
    paramFloor := 4
    paramCeiling := 1024
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["half-gcd", "matrix", "ratio-4"]
  }

setup_benchmark runHalfGcdLeft n => n * (Nat.sqrt n) * (Nat.log2 n + 1)
  with prep := prepGcdBalanced
  where {
    paramFloor := 4
    paramCeiling := 2048
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["half-gcd", "matrix", "one-sided"]
  }

/- A balanced product tree performs one multiplication per internal node over
geometrically growing degrees, for `O(M(n) log n)` total work. The integer
surrogate retains the logarithmic level count without assuming a particular
coefficient-kernel exponent. -/
setup_benchmark runProductTree n => n * (Nat.log2 n + 1)
  with prep := prepProductTree
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["product-tree", "karatsuba", "cold"]
  }

/- Direct Horner evaluation visits all `n` coefficients independently at all
`n` points, giving quadratic (`Θ(n²)`) coefficient operations. -/
setup_benchmark runDirectEval n => n ^ 2
  with prep := prepMultipoint
  where {
    paramFloor := 4
    paramCeiling := 4096
    paramSchedule := .custom #[4, 16, 64, 256, 1024, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multipoint", "horner", "reused-plan"]
  }

/- With products and reciprocals prepared outside the timed call, the balanced
remainder tree costs `O(M(n) log n)`. -/
setup_benchmark runMultipointEval n => n * (Nat.sqrt n) * (Nat.log2 n + 1)
  with prep := prepMultipoint
  where {
    paramFloor := 4
    paramCeiling := 4096
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multipoint", "remainder-tree", "reused-plan"]
  }

/- Product, reciprocal, and remainder trees are all constructed inside the
timed call, exposing cold reusable-plan setup cost. -/
setup_benchmark runColdMultipointEval n => n * (Nat.sqrt n) * (Nat.log2 n + 1)
  with prep := prepMultipoint
  where {
    paramFloor := 4
    paramCeiling := 2048
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multipoint", "remainder-tree", "cold-plan"]
  }

setup_benchmark runRepeatedDirectEval n => 8 * n ^ 2
  with prep := prepMultipointBatch
  where {
    paramFloor := 4
    paramCeiling := 2048
    paramSchedule := .custom #[4, 16, 32, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multipoint", "horner", "repeated", "reused-points"]
  }

setup_benchmark runRepeatedMultipointEval n =>
    8 * n * Nat.sqrt n * (Nat.log2 n + 1)
  with prep := prepMultipointBatch
  where {
    paramFloor := 4
    paramCeiling := 2048
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multipoint", "remainder-tree", "repeated", "reused-plan"]
  }

/- Direct Lagrange construction rebuilds `n` products of `n` linear factors;
schoolbook multiplication by the growing numerators gives a cubic
coefficient-operation model. -/
setup_benchmark runDirectInterpolation n => n ^ 3
  with prep := prepInterpolation
  where {
    paramFloor := 4
    paramCeiling := 1024
    paramSchedule := .custom #[4, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["interpolation", "lagrange", "direct"]
  }

/- With the distinct-point plan prepared outside the timed call, bottom-up
combination follows the balanced product shape in `O(M(n) log n)` work. -/
setup_benchmark runPlannedInterpolation n =>
    n * (Nat.sqrt n) * (Nat.log2 n + 1)
  with prep := prepInterpolation
  where {
    paramFloor := 4
    paramCeiling := 4096
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["interpolation", "product-tree", "reused-plan"]
  }

/- Distinct-point checking, derivative evaluation, inverses, and the product
tree are included in the cold planned interpolation arm. -/
setup_benchmark runColdInterpolation n =>
    n * (Nat.sqrt n) * (Nat.log2 n + 1)
  with prep := prepInterpolation
  where {
    paramFloor := 4
    paramCeiling := 2048
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["interpolation", "product-tree", "cold-plan"]
  }

end Hex.PolyFastBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
