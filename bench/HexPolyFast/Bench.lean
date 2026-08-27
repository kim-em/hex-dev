/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.BenchOracle.Flint
import HexModArith
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

instance : Nonempty Binary := ⟨{ left := 0, right := 0 }⟩

instance : Hashable Binary where
  hash input := mixHash (hash input.left.toArray) (hash input.right.toArray)

/-- Generic multiplication operands over rational coefficients. -/
structure BinaryRat where
  left : DensePoly Rat
  right : DensePoly Rat

instance : Hashable BinaryRat where
  hash input := mixHash (hash input.left.toArray) (hash input.right.toArray)

private instance boundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance boundsLarge : ZMod64.Bounds 65537 := ⟨by decide, by decide⟩

private abbrev Fp := ZMod64 65537

private instance : Inhabited Fp := ⟨0⟩

set_option maxRecDepth 8192 in
private theorem prime65537 : Hex.Nat.Prime 65537 :=
  Hex.Nat.prime_of_bounded 65537 256 (by decide) (by decide) (by decide)

private instance primeLarge : ZMod64.PrimeModulus 65537 :=
  ZMod64.primeModulusOfPrime prime65537

local instance : Div Fp where
  div a b := a * b⁻¹

private def fieldZpow (a : Fp) : Int → Fp
  | .ofNat n => a ^ n
  | .negSucc n => (a ^ (n + 1))⁻¹

local instance : HPow Fp Int Fp := ⟨fieldZpow⟩

private theorem field_inv_zero : (0 : Fp)⁻¹ = 0 := by
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  change (ZMod64.inv (0 : Fp)).toNat = (0 : Fp).toNat
  rw [ZMod64.toNat_inv_def]
  change (((HexArith.Int.extGcd 0 (Int.ofNat 65537)).2.1 % 65537).toNat % 65537 = 0)
  have hs := HexArith.Int.extGcd_zero_left_s_ofNat 65537
    (ZMod64.Bounds.pPos (p := 65537))
  rw [hs]
  simp

private theorem field_inv_ne_zero {a : Fp} (ha : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro hinv
  have hone := ZMod64.inv_mul_eq_one_of_ne_zero ha
  change ZMod64.inv a = 0 at hinv
  rw [hinv] at hone
  have hzero : (0 : Fp) * a = 0 := by grind
  rw [hzero] at hone
  exact ZMod64.one_ne_zero hone.symm

private theorem field_inv_inv (a : Fp) : (a⁻¹)⁻¹ = a := by
  by_cases ha : a = 0
  · subst a
    rw [field_inv_zero]
    exact field_inv_zero
  · have hinv_ne := field_inv_ne_zero ha
    have hleft : (a⁻¹)⁻¹ * a⁻¹ = (1 : Fp) :=
      ZMod64.inv_mul_eq_one_of_ne_zero hinv_ne
    have hright : a * a⁻¹ = (1 : Fp) :=
      ZMod64.mul_inv_eq_one_of_ne_zero ha
    have hprod : (((a⁻¹)⁻¹ - a) * a⁻¹) = (0 : Fp) := by
      rw [Lean.Grind.Ring.sub_eq_add_neg, Lean.Grind.Semiring.right_distrib, hleft]
      grind
    rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero_of_prime_modulus hprod with
      hdiff | hzero
    · grind
    · exact False.elim (hinv_ne hzero)

local instance : Lean.Grind.Field Fp where
  toCommRing := inferInstance
  inv := ZMod64.inv
  div := fun a b => a * b⁻¹
  zpow := ⟨fieldZpow⟩
  div_eq_mul_inv := by intros; rfl
  zero_ne_one := fun h => ZMod64.one_ne_zero h.symm
  inv_zero := field_inv_zero
  mul_inv_cancel := by
    intro a ha
    exact ZMod64.mul_inv_eq_one_of_ne_zero ha
  zpow_zero := by intro; simp [fieldZpow]
  zpow_succ := by
    intro a n
    change a ^ (n + 1) = a ^ n * a
    exact Lean.Grind.Semiring.pow_succ a n
  zpow_neg := by
    intro a n
    cases n with
    | ofNat m =>
        cases m with
        | zero =>
            change fieldZpow a (-Int.ofNat 0) = (fieldZpow a (Int.ofNat 0))⁻¹
            rw [show (-Int.ofNat 0) = Int.ofNat 0 by rfl]
            simp [fieldZpow]
            have h1ne : (1 : Fp) ≠ 0 := fun h => ZMod64.one_ne_zero h
            have hinvOne := ZMod64.inv_mul_eq_one_of_ne_zero h1ne
            rw [Lean.Grind.Semiring.mul_one] at hinvOne
            exact hinvOne.symm
        | succ m => rfl
    | negSucc m =>
        simp only [Int.neg_negSucc]
        change a ^ (m + 1) = ((a ^ (m + 1))⁻¹)⁻¹
        exact (field_inv_inv (a ^ (m + 1))).symm

private instance : Hashable Fp where
  hash value := hash value.toNat

/-- Generic multiplication operands over the small word field `ZMod64 5`. -/
structure BinaryMod where
  left : DensePoly (ZMod64 5)
  right : DensePoly (ZMod64 5)

instance : Nonempty BinaryMod := ⟨{ left := 0, right := 0 }⟩

private def hashModPoly (p : DensePoly (ZMod64 5)) : UInt64 :=
  p.toArray.foldl (fun acc x => mixHash acc (hash x.toNat)) 0

instance : Hashable BinaryMod where
  hash input := mixHash (hashModPoly input.left) (hashModPoly input.right)

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

def prepRatio (ratio n : Nat) : Binary :=
  { left := ofList ((List.range (ratio * n)).map fun i => coeff i (5 + ratio))
    right := ofList ((List.range n).map fun i => coeff i (23 + ratio)) }

def prepRatio2 (n : Nat) : Binary := prepRatio 2 n
def prepRatio4 (n : Nat) : Binary := prepRatio 4 n
def prepRatio16 (n : Nat) : Binary := prepRatio 16 n

/-- A ratio just below 2:1 whose top Karatsuba subproblem has a cutoff-sized
right operand and a much larger left operand. -/
def prepRatioUnder2 (n : Nat) : Binary :=
  { left := ofList ((List.range (2 * n)).map fun i => coeff i 61)
    right := ofList ((List.range (n + 16)).map fun i => coeff i 67) }

def prepSkew (n : Nat) : Binary :=
  prepRatio 64 n

def prepBalancedRat (n : Nat) : BinaryRat :=
  { left := ofList ((List.range n).map fun i => (coeff i 7 : Rat))
    right := ofList ((List.range n).map fun i => (coeff i 29 : Rat)) }

private def modCoeff (i salt : Nat) : ZMod64 5 :=
  ZMod64.ofNat 5 (((i + 3) * (salt + 11) + i * i) % 5)

private def fieldCoeff (n i salt : Nat) : Fp :=
  ZMod64.ofNat 65537 <|
    ((i + 1) * (salt + 17) + (i + 3) * (i + 5) * 13 + n * 29) % 65537

def prepBalancedMod (n : Nat) : BinaryMod :=
  { left := ofList ((List.range n).map fun i => modCoeff i 11)
    right := ofList ((List.range n).map fun i => modCoeff i 37) }

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

private def checksumRat (p : DensePoly Rat) : UInt64 :=
  p.toArray.foldl (fun acc x => mixHash acc (hash x)) 0

private def checksumMod (p : DensePoly (ZMod64 5)) : UInt64 :=
  hashModPoly p

private def checksumField (p : DensePoly Fp) : UInt64 :=
  p.toArray.foldl (fun acc x => mixHash acc (hash x.toNat)) 0

private def checksumSeries [Hashable R] (a : TSeries R n) : UInt64 :=
  a.coeffs.toArray.foldl (fun acc x => mixHash acc (hash x)) 0

def runSchoolbook (input : Binary) : UInt64 :=
  checksum (mulWith schoolbookPlan input.left input.right)

def runKaratsuba (input : Binary) : UInt64 :=
  checksum (mulWith (karatsubaPlan 32) input.left input.right)

def runKaratsubaSkew (input : Binary) : UInt64 :=
  checksum (mulWith (karatsubaPlan 32) input.left input.right)

def runKaratsubaRatio2 (input : Binary) : UInt64 :=
  checksum (mulWith (karatsubaPlan 32) input.left input.right)

def runKaratsubaRatio4 (input : Binary) : UInt64 :=
  checksum (mulWith (karatsubaPlan 32) input.left input.right)

def runKaratsubaRatio16 (input : Binary) : UInt64 :=
  checksum (mulWith (karatsubaPlan 32) input.left input.right)

def runKaratsubaRatioUnder2 (input : Binary) : UInt64 :=
  checksum (mulWith (karatsubaPlan 32) input.left input.right)

def runKaratsubaSquare (input : Binary) : UInt64 :=
  checksum (squareWith (karatsubaPlan 32) input.left)

/-- Full Karatsuba product followed by extraction of its low half. -/
def runFullThenLowInt (input : Binary) : UInt64 :=
  checksum <| coeffSlice 0 input.left.size <|
    mulWith (karatsubaPlan 32) input.left input.right

/-- Direct low-half Karatsuba product. -/
def runClippedLowInt (input : Binary) : UInt64 :=
  checksum (mulLow (karatsubaPlan 32) input.left.size input.left input.right)

def runSchoolbookRat (input : BinaryRat) : UInt64 :=
  checksumRat (mulWith schoolbookPlan input.left input.right)

def runKaratsubaRat (input : BinaryRat) : UInt64 :=
  checksumRat (mulWith (karatsubaPlan 32) input.left input.right)

def runKaratsubaSquareRat (input : BinaryRat) : UInt64 :=
  checksumRat (squareWith (karatsubaPlan 32) input.left)

def runFullThenLowRat (input : BinaryRat) : UInt64 :=
  checksumRat <| coeffSlice 0 input.left.size <|
    mulWith (karatsubaPlan 32) input.left input.right

def runClippedLowRat (input : BinaryRat) : UInt64 :=
  checksumRat (mulLow (karatsubaPlan 32) input.left.size input.left input.right)

def runSchoolbookMod (input : BinaryMod) : UInt64 :=
  checksumMod (mulWith schoolbookPlan input.left input.right)

def runKaratsubaMod (input : BinaryMod) : UInt64 :=
  checksumMod (mulWith (karatsubaPlan 32) input.left input.right)

def runKaratsubaSquareMod (input : BinaryMod) : UInt64 :=
  checksumMod (squareWith (karatsubaPlan 32) input.left)

def runFullThenLowMod (input : BinaryMod) : UInt64 :=
  checksumMod <| coeffSlice 0 input.left.size <|
    mulWith (karatsubaPlan 32) input.left input.right

def runClippedLowMod (input : BinaryMod) : UInt64 :=
  checksumMod (mulLow (karatsubaPlan 32) input.left.size input.left input.right)

/-! The external comparisons are deliberately fixed informational targets:
production dispatch remains gated by the parametric within-Lean pairs below. -/

private def intPolyJson (p : DensePoly Int) : Lean.Json :=
  Hex.BenchOracle.Flint.intsToJson p.toArray.toList

private def modPolyJson (p : DensePoly (ZMod64 5)) : Lean.Json :=
  Hex.BenchOracle.Flint.intsToJson <|
    p.toArray.toList.map fun value => Int.ofNat value.toNat

private def checksumIntList (coeffs : List Int) : UInt64 :=
  coeffs.foldl (fun acc value => mixHash acc (hash value)) 0

private def checksumModList (coeffs : List Int) : UInt64 :=
  coeffs.foldl (fun acc value => mixHash acc (hash value.toNat)) 0

/-- Informational FLINT `fmpz_poly.mul` comparator on the integer campaign. -/
def runFlintInt (input : Binary) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" "mul"
    #[("a", intPolyJson input.left), ("b", intPolyJson input.right)]
  return checksumIntList (← Hex.BenchOracle.Flint.jsonToInts result)

/-- Informational FLINT `nmod_poly.mul` comparator on the small-field campaign. -/
def runFlintMod (input : BinaryMod) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "nmod_poly" "mul"
    #[("p", (5 : Lean.Json)), ("a", modPolyJson input.left),
      ("b", modPolyJson input.right)]
  return checksumModList (← Hex.BenchOracle.Flint.jsonToInts result)

/-- Persistent FLINT process/framing overhead with no polynomial work. -/
def runFlintOverhead (_ : Unit) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" "overhead" #[]
  match result.getInt? with
  | .ok 0 => return 0
  | .ok value =>
      throw <| IO.userError s!"FLINT overhead result was {value}, expected zero"
  | .error message =>
      throw <| IO.userError s!"FLINT overhead result not integer: {message}"

initialize intInput64 : IO.Ref Binary ← IO.mkRef (prepBalanced 64)
initialize intInput256 : IO.Ref Binary ← IO.mkRef (prepBalanced 256)
initialize intInput1024 : IO.Ref Binary ← IO.mkRef (prepBalanced 1024)
initialize modInput64 : IO.Ref BinaryMod ← IO.mkRef (prepBalancedMod 64)
initialize modInput256 : IO.Ref BinaryMod ← IO.mkRef (prepBalancedMod 256)
initialize modInput1024 : IO.Ref BinaryMod ← IO.mkRef (prepBalancedMod 1024)

def runLeanInt64 (_ : Unit) : IO UInt64 := do
  let input ← intInput64.get
  return runKaratsuba input
def runFlintInt64 (_ : Unit) : IO UInt64 := do
  runFlintInt (← intInput64.get)
def runLeanInt256 (_ : Unit) : IO UInt64 := do
  let input ← intInput256.get
  return runKaratsuba input
def runFlintInt256 (_ : Unit) : IO UInt64 := do
  runFlintInt (← intInput256.get)
def runLeanInt1024 (_ : Unit) : IO UInt64 := do
  let input ← intInput1024.get
  return runKaratsuba input
def runFlintInt1024 (_ : Unit) : IO UInt64 := do
  runFlintInt (← intInput1024.get)

def runLeanMod64 (_ : Unit) : IO UInt64 := do
  let input ← modInput64.get
  return runKaratsubaMod input
def runFlintMod64 (_ : Unit) : IO UInt64 := do
  runFlintMod (← modInput64.get)
def runLeanMod256 (_ : Unit) : IO UInt64 := do
  let input ← modInput256.get
  return runKaratsubaMod input
def runFlintMod256 (_ : Unit) : IO UInt64 := do
  runFlintMod (← modInput256.get)
def runLeanMod1024 (_ : Unit) : IO UInt64 := do
  let input ← modInput1024.get
  return runKaratsubaMod input
def runFlintMod1024 (_ : Unit) : IO UInt64 := do
  runFlintMod (← modInput1024.get)

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
  dividend : DensePoly Fp
  divisor : DensePoly Fp

instance : Hashable DivisionInput where
  hash input := mixHash (hash input.dividend.toArray) (hash input.divisor.toArray)

/-- One dividend paired with a reciprocal plan prepared outside timing. -/
structure CachedDivisionInput where
  dividend : DensePoly Fp
  plan : Option (DivPlan Fp)

/-- A fixed divisor reused across several dividends. -/
structure RepeatedDivisionInput where
  dividends : Array (DensePoly Fp)
  divisor : DensePoly Fp
  plan : Option (DivPlan Fp)

instance : Hashable CachedDivisionInput where
  hash input := mixHash (hash input.dividend.toArray) <| match input.plan with
    | none => 0
    | some plan => hash plan.divisor.toArray

instance : Hashable RepeatedDivisionInput where
  hash input := mixHash
    (input.dividends.foldl (fun acc p => mixHash acc (hash p.toArray)) 0)
    (hash input.divisor.toArray)

private def divisionDividend (n salt : Nat) : DensePoly Fp :=
  ofList ((List.range (2 * n + 1)).map fun i => fieldCoeff n i salt)

private def divisionDivisor (n : Nat) : DensePoly Fp :=
  ofList (((List.range n).map fun i => fieldCoeff n i 47) ++ [1])

def prepDivision (n : Nat) : DivisionInput :=
  { dividend := divisionDividend n 31
    divisor := divisionDivisor n }

private def cachedPlan? (divisor : DensePoly Fp) (capacity : Nat) :
    Option (DivPlan Fp) :=
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

private def checksumDiv (qr : DensePoly Fp × DensePoly Fp) : UInt64 :=
  mixHash (checksumField qr.1) (checksumField qr.2)

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
  leaves : Array (DensePoly Fp)

instance : Hashable ProductTreeInput where
  hash input := input.leaves.foldl
    (fun acc p => mixHash acc (hash p.toArray)) 0

def prepProductTree (n : Nat) : ProductTreeInput :=
  { leaves := (List.range n).map
      (fun i => pointFactor (ZMod64.ofNat 65537 i)) |>.toArray }

def runProductTree (input : ProductTreeInput) : UInt64 :=
  checksumField (ProductTree.build (karatsubaPlan 32) input.leaves).root

structure RemainderTreeInput where
  points : Array Fp
  polynomial : DensePoly Fp

instance : Hashable RemainderTreeInput where
  hash input := mixHash (hash input.points) (hash input.polynomial.toArray)

def prepRemainderTree (n : Nat) : RemainderTreeInput :=
  { points := (List.range n).map (fun i => ZMod64.ofNat 65537 i) |>.toArray
    polynomial := ofList ((List.range (2 * n)).map fun i => fieldCoeff n i 73) }

/-- Construct a general cached remainder tree and traverse it once. -/
def runRemainderTree (input : RemainderTreeInput) : UInt64 :=
  let leaves : Array (MonicLeaf Fp) := input.points.map fun point =>
    { poly := pointFactor point
      monic := pointFactor_monic point
      ne := (pointFactor_monic point).neOfOneNe (by decide) }
  let tree := RemainderTree.build (karatsubaPlan 32) input.points.size leaves (by decide)
  match tree.remainders? input.polynomial with
  | none => 0
  | some remainders =>
      remainders.foldl (fun acc p => mixHash acc (checksumField p)) 0

structure MultipointInput where
  plan : EvalPlan Fp
  polynomial : DensePoly Fp

instance : Hashable MultipointInput where
  hash input := mixHash (hash input.plan.points) (hash input.polynomial.toArray)

/-- Several polynomials sharing one point/remainder-tree plan. -/
structure MultipointBatchInput where
  plan : EvalPlan Fp
  polynomials : Array (DensePoly Fp)

instance : Hashable MultipointBatchInput where
  hash input := mixHash (hash input.plan.points) <|
    input.polynomials.foldl (fun acc p => mixHash acc (hash p.toArray)) 0

private def evalPointsFor (n : Nat) : Array Fp :=
  (List.range n).map (fun i => ZMod64.ofNat 65537 i) |>.toArray

private def evalPolynomial (n salt : Nat) : DensePoly Fp :=
  ofList ((List.range n).map fun i => fieldCoeff n i salt)

def prepMultipoint (n : Nat) : MultipointInput :=
  let points := evalPointsFor n
  { plan := EvalPlan.build (karatsubaPlan 32) points
    polynomial := evalPolynomial n 71 }

def prepMultipointBatch (n : Nat) : MultipointBatchInput :=
  let points := evalPointsFor n
  { plan := EvalPlan.build (karatsubaPlan 32) points
    polynomials := (Array.range 8).map fun i => evalPolynomial n (71 + i * 17) }

private def checksumValues (values : Array Fp) : UInt64 :=
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
  points : Array Fp
  values : Array Fp
  plan : Option (InterpPlan Fp)

instance : Hashable InterpolationInput where
  hash input := mixHash (hash input.points) (hash input.values)

def prepInterpolation (n : Nat) : InterpolationInput :=
  let points := (List.range n).map (fun i => ZMod64.ofNat 65537 i) |>.toArray
  let values := points.map fun x => x * x * x - 7 * x + 11
  { points
    values
    plan := InterpPlan.build? (karatsubaPlan 32) points }

/-- Direct Lagrange interpolation, independently rebuilding every numerator
and denominator. This is the executable comparator for the reusable plan. -/
def directLagrange (points values : Array Fp) : DensePoly Fp :=
  let n := min points.size values.size
  (List.range n).foldl (fun sum i =>
    let ai := points.getD i 0
    let numerator : DensePoly Fp := (List.range n).foldl (fun (product : DensePoly Fp) j =>
      if i = j then product else DensePoly.mul product (pointFactor (points.getD j 0)))
        (1 : DensePoly Fp)
    let denominator : Fp := (List.range n).foldl (fun (product : Fp) j =>
      if i = j then product else product * (ai - points.getD j 0)) 1
    sum + C (values.getD i 0 * denominator⁻¹) * numerator) (0 : DensePoly Fp)

def runDirectInterpolation (input : InterpolationInput) : UInt64 :=
  checksumField (directLagrange input.points input.values)

def runPlannedInterpolation (input : InterpolationInput) : UInt64 :=
  match input.plan with
  | none => 0
  | some plan =>
      match plan.interpolate? input.values with
      | none => 0
      | some p => checksumField p

def runColdInterpolation (input : InterpolationInput) : UInt64 :=
  match InterpPlan.build? (karatsubaPlan 32) input.points with
  | none => 0
  | some plan =>
      match plan.interpolate? input.values with
      | none => 0
      | some p => checksumField p

/-- A diagonal `[n/n]` Padé problem over the fixed-width field `𝔽₆₅₅₃₇` at
precision `2n+1`. Reciprocal integer coefficients keep the reference Hankel
system nonsingular throughout the registered range without introducing
coefficient-bit growth into the unit-cost complexity experiment. -/
structure PadeInput where
  precision : Nat
  series : TSeries Fp precision
  bound : Nat

instance : Hashable PadeInput where
  hash input := mixHash (hash input.bound) (hash input.series.coeffs.toArray)

def prepPade (n : Nat) : PadeInput :=
  { precision := 2 * n + 1
    series := TSeries.ofFn fun i => ((i + 1 : Nat) : Fp)⁻¹
    bound := n }

/-- Gauss-Jordan elimination for a flat `n × (n+1)` augmented field matrix.
This intentionally does not use any polynomial Euclidean machinery. -/
private def solveUniqueField (n : Nat) (augmented : Array Fp) : Option (Array Fp) :=
  if augmented.size != n * (n + 1) then none else Id.run do
    let width := n + 1
    let mut a := augmented
    for col in [0:n] do
      let mut pivot := n
      for row in [col:n] do
        if a[row * width + col]! != 0 then
          pivot := row
          break
      if pivot == n then
        return none
      if pivot != col then
        for k in [0:width] do
          let x := a[col * width + k]!
          a := a.set! (col * width + k) a[pivot * width + k]!
          a := a.set! (pivot * width + k) x
      let pivotValue := a[col * width + col]!
      for k in [col:width] do
        a := a.set! (col * width + k) (a[col * width + k]! / pivotValue)
      for row in [0:n] do
        if row != col then
          let factor := a[row * width + col]!
          if factor != 0 then
            for k in [col:width] do
              a := a.set! (row * width + k)
                (a[row * width + k]! - factor * a[col * width + k]!)
    return some ((Array.range n).map fun i => a[i * width + n]!)

/-- Classical normalized Padé construction: solve the `n × n` Hankel system
for `q₁, …, qₙ` with `q₀ = 1`, then read the low product coefficients as the
numerator. This is the independent linear-algebra benchmark reference. -/
def directPade (input : PadeInput) : Option (DensePoly Fp × DensePoly Fp) :=
  let n := input.bound
  let augmented := Id.run do
    let width := n + 1
    let mut a : Array Fp := Array.replicate (n * width) 0
    for row in [0:n] do
      let k := n + 1 + row
      for col in [0:n] do
        let j := col + 1
        a := a.set! (row * width + col) (input.series.coeff (k - j))
      a := a.set! (row * width + n) (-input.series.coeff k)
    return a
  match solveUniqueField n augmented with
  | none => none
  | some qTail =>
      let q : DensePoly Fp := ofList ((1 : Fp) :: qTail.toList)
      let product := DensePoly.mul q (polyOfSeries input.series)
      let p : DensePoly Fp := ofList ((List.range (n + 1)).map product.coeff)
      some (p, q)

private def checksumPadePair (result : Option (DensePoly Fp × DensePoly Fp)) : UInt64 :=
  match result with
  | none => 0
  | some (p, q) => mixHash (checksumField p) (checksumField q)

def runLinearPade (input : PadeInput) : UInt64 :=
  checksumPadePair (directPade input)

def runHalfGcdPade (input : PadeInput) : UInt64 :=
  match pade? (karatsubaPlan 32) input.series input.bound input.bound with
  | none => 0
  | some approx => mixHash (checksumField approx.p) (checksumField approx.q)

/-- Finite-range operation-count model for the registered Karatsuba plan.
Below the cutoff the plan performs a quadratic schoolbook product; above it,
three half-sized products and linear combination work give the standard
`T(n) = 3T(⌈n/2⌉) + O(n)` recurrence. Unlike the coarser `n * sqrt n`
surrogate, this model keeps the 31/32/33 transition rows scientifically usable.
-/
private def karatsubaCost (n : Nat) : Nat :=
  if n ≤ 32 then n ^ 2
  else 3 * karatsubaCost ((n + 1) / 2) + n
termination_by n
decreasing_by omega

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
`T(n) = Θ(n^(log₂ 3))`; `karatsubaCost` records that recurrence with the
actual cutoff. The nearby 31/32/33 rungs expose the transition. -/
setup_benchmark runKaratsuba n => karatsubaCost n
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
the shared cutoff-aware model applies. -/
setup_benchmark runKaratsubaSquare n => karatsubaCost n
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
bound `Θ(n^(log₂ 3))`. The table retains the dispatcher setup regime below
64; the verdict begins at 64 and the expanded ceiling supplies five successive
recursive measurements. -/
setup_benchmark runKaratsubaSkew n => karatsubaCost n
  with prep := prepSkew
  where {
    paramFloor := 4
    paramCeiling := 1024
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 200000000
    verdictWarmupFraction := 0.45
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "ratio-64"]
  }

/- A fixed 2:1 shape performs two balanced Karatsuba blocks, preserving the
`Theta(n^(log_2 3))` model in the shorter operand size. -/
setup_benchmark runKaratsubaRatio2 n => karatsubaCost n
  with prep := prepRatio2
  where {
    paramFloor := 4
    paramCeiling := 8192
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 8192]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "ratio-2"]
  }

/- Cost model: a fixed 4:1 shape uses four shorter-size blocks, so its
Karatsuba complexity matches the balanced recurrence up to that constant. -/
setup_benchmark runKaratsubaRatio4 n => karatsubaCost n
  with prep := prepRatio4
  where {
    paramFloor := 4
    paramCeiling := 4096
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "ratio-4"]
  }

/- Cost model: a fixed 16:1 shape uses sixteen shorter-size blocks and the
same Karatsuba complexity exponent in the registered parameter. -/
setup_benchmark runKaratsubaRatio16 n => karatsubaCost n
  with prep := prepRatio16
  where {
    paramFloor := 4
    paramCeiling := 1024
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "ratio-16"]
  }

/- The just-under-2:1 shape exposes cutoff leaves with highly unequal raw
operand lengths while retaining the fixed-ratio Karatsuba cost model. -/
setup_benchmark runKaratsubaRatioUnder2 n => karatsubaCost n
  with prep := prepRatioUnder2
  where {
    paramFloor := 64
    paramCeiling := 8192
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048, 4096, 8192]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "ratio-under-2", "cutoff-skew"]
  }

/- Cost model: full-product-then-low extraction retains the full balanced
Karatsuba complexity and is the comparator for direct clipping over `Int`. -/
setup_benchmark runFullThenLowInt n => karatsubaCost n
  with prep := prepBalanced
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "int", "full-then-low"]
  }

/- Direct low clipping skips irrelevant recursive branches while retaining
the `O(M(n))` Karatsuba upper bound over `Int`. -/
setup_benchmark runClippedLowInt n => karatsubaCost n
  with prep := prepBalanced
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "int", "clipped-low"]
  }

/- Rational schoolbook convolution performs one exact coefficient product per
input pair, hence quadratic coefficient work. -/
setup_benchmark runSchoolbookRat n => (n ^ 2)
  with prep := prepBalancedRat
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 75.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "schoolbook", "rat", "balanced"]
  }

/- Cost model: balanced rational Karatsuba has the standard three-subproblem
recurrence represented by `karatsubaCost`. -/
setup_benchmark runKaratsubaRat n => karatsubaCost n
  with prep := prepBalancedRat
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 45.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "rat", "balanced"]
  }

/- Cost model: specialized rational squaring has the same recursive
complexity as rational Karatsuba multiplication. -/
setup_benchmark runKaratsubaSquareRat n => karatsubaCost n
  with prep := prepBalancedRat
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 45.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "rat", "square"]
  }

/- Cost model: full rational multiplication followed by extraction retains
the Karatsuba bound and directly compares with the clipped rational path. -/
setup_benchmark runFullThenLowRat n => karatsubaCost n
  with prep := prepBalancedRat
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 45.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "rat", "full-then-low"]
  }

/- Direct rational clipping retains the `O(M(n))` upper bound while avoiding
irrelevant high product branches. -/
setup_benchmark runClippedLowRat n => karatsubaCost n
  with prep := prepBalancedRat
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 45.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "rat", "clipped-low"]
  }

/- Small-word-field schoolbook convolution performs quadratic coefficient
work with constant-time `ZMod64 5` operations. -/
setup_benchmark runSchoolbookMod n => (n ^ 2)
  with prep := prepBalancedMod
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "schoolbook", "zmod5", "balanced"]
  }

/- Cost model: small-word-field Karatsuba follows the three-subproblem
recurrence represented by `karatsubaCost`. -/
setup_benchmark runKaratsubaMod n => karatsubaCost n
  with prep := prepBalancedMod
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "zmod5", "balanced"]
  }

/- Cost model: specialized `ZMod64 5` squaring has the same recursive
complexity as the generic Karatsuba product. -/
setup_benchmark runKaratsubaSquareMod n => karatsubaCost n
  with prep := prepBalancedMod
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "zmod5", "square"]
  }

/- Cost model: full small-word-field multiplication followed by extraction
retains the Karatsuba bound used by the direct-clipping comparator. -/
setup_benchmark runFullThenLowMod n => karatsubaCost n
  with prep := prepBalancedMod
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "zmod5", "full-then-low"]
  }

/- Direct `ZMod64 5` clipping avoids high recursive branches while retaining
the `O(M(n))` upper bound. -/
setup_benchmark runClippedLowMod n => karatsubaCost n
  with prep := prepBalancedMod
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "karatsuba", "zmod5", "clipped-low"]
  }

/- The lower library deliberately retains its weak semiring schoolbook API.
This registration measures that triangular convolution against the
commutative-ring Karatsuba plan supplied above the dependency boundary. -/
setup_benchmark runSeriesSchoolbookInt n => (n ^ 2)
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

/-
Cost model: clipped integer series multiplication follows the same
three-subproblem Karatsuba recurrence as the full product.
-/
setup_benchmark runSeriesKaratsubaInt n => karatsubaCost n
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

/-
Cost model: the retained rational series kernel forms every contributing
coefficient pair, giving quadratic work in the truncation order.
-/
setup_benchmark runSeriesSchoolbookRat n => (n ^ 2)
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

/-
Cost model: clipped rational series multiplication follows the standard
three-subproblem Karatsuba recurrence.
-/
setup_benchmark runSeriesKaratsubaRat n => karatsubaCost n
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
    tags := #["division", "long", "cold", "field-65537"]
  }

/- Cost model: a cold Newton call includes reciprocal construction and three clipped
Karatsuba products.  Doubling is geometric, so the balanced model remains
`Θ(M(n))`, represented by the cutoff-aware Karatsuba recurrence. -/
setup_benchmark runNewtonDivision n => karatsubaCost n
  with prep := prepDivision
  where {
    paramFloor := 4
    paramCeiling := 4096
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["division", "newton", "cold", "field-65537"]
  }

/- Cost model: reciprocal construction is hoisted into `prep`; the timed body
performs two `O(M(n))` products, represented by `karatsubaCost`. -/
setup_benchmark runCachedDivision n => karatsubaCost n
  with prep := prepCachedDivision
  where {
    paramFloor := 4
    paramCeiling := 4096
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["division", "newton", "cached-divisor", "warm-plan", "field-65537"]
  }

/- Eight dividends share one fixed reciprocal. This separates amortized plan
reuse from the one-shot comparison above. -/
setup_benchmark runRepeatedNewtonDivision n => 8 * karatsubaCost n
  with prep := prepRepeatedDivision
  where {
    paramFloor := 4
    paramCeiling := 1024
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["division", "newton", "repeated", "cold-plan", "field-65537"]
  }

/-
Cost model: eight dividends reuse one reciprocal, so the amortized timed work
is eight `O(M(n))` quotient-and-reconstruction products.
-/
setup_benchmark runRepeatedCachedDivision n => 8 * karatsubaCost n
  with prep := prepRepeatedDivision
  where {
    paramFloor := 4
    paramCeiling := 1024
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["division", "newton", "repeated", "warm-plan", "field-65537"]
  }

/-
Cost model: the fixed 4:1 long-division shape performs linearly many dense
suffix updates, giving a quadratic bound in the shorter degree. The first four
rungs retain the allocation-dominated small-input regime; the verdict begins
at 64, where the repeated suffix-update loop dominates, and keeps five rungs.
-/
setup_benchmark runSkewLongDivision n => (n ^ 2)
  with prep := prepGcdSkew
  where {
    paramFloor := 4
    paramCeiling := 1024
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    verdictWarmupFraction := 0.45
    signalFloorMultiplier := 1.0
    tags := #["division", "long", "ratio-4"]
  }

/-
Cost model: a fixed 4:1 shape changes Newton division by a constant number of
blocks, preserving the `O(M(n))` Karatsuba bound.
-/
setup_benchmark runSkewNewtonDivision n => karatsubaCost n
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
setup_benchmark runEuclideanXgcd n => (n ^ 2)
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
logarithmic number of sequential matrix levels, for `O(M(n) log n)`. The
verdict begins at 64, above the multiplication cutoff, while retaining the
smaller boundary-search rows. -/
setup_benchmark runHalfGcd n => karatsubaCost n * (Nat.log2 n + 1)
  with prep := prepGcdBalanced
  where {
    paramFloor := 4
    paramCeiling := 2048
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    verdictWarmupFraction := 0.4
    signalFloorMultiplier := 1.0
    tags := #["half-gcd", "matrix", "balanced"]
  }

/-
Cost model: fixed 4:1 skew changes only constants in the half-gcd recurrence,
which remains `O(M(n) log n)` in the shorter degree. Its verdict likewise
begins at 64 and retains five recursive rungs.
-/
setup_benchmark runHalfGcdSkew n => karatsubaCost n * (Nat.log2 n + 1)
  with prep := prepGcdSkew
  where {
    paramFloor := 4
    paramCeiling := 1024
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    verdictWarmupFraction := 0.45
    signalFloorMultiplier := 1.0
    tags := #["half-gcd", "matrix", "ratio-4"]
  }

/-
Cost model: the one-sided half-gcd surface uses the same logarithmic matrix
recurrence and `O(M(n) log n)` bound as the paired result. Its verdict begins
at 64 for the same cutoff reason.
-/
setup_benchmark runHalfGcdLeft n => karatsubaCost n * (Nat.log2 n + 1)
  with prep := prepGcdBalanced
  where {
    paramFloor := 4
    paramCeiling := 2048
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    verdictWarmupFraction := 0.4
    signalFloorMultiplier := 1.0
    tags := #["half-gcd", "matrix", "one-sided"]
  }

/- At level `j`, a balanced product tree performs `2^j` products of size
`n/2^j`. For the superlinear Karatsuba recurrence their costs form a geometric
sum bounded by `Θ(M(n))`; this is tighter than the generic `O(M(n) log n)`
SPEC upper bound. -/
setup_benchmark runProductTree n => karatsubaCost n
  with prep := prepProductTree
  where {
    paramFloor := 4
    paramCeiling := 16384
    paramSchedule := .custom #[4, 16, 64, 256, 1024, 4096, 16384]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["product-tree", "karatsuba", "cold", "field-65537"]
  }

/- Construction and one traversal have the same per-level geometric sum as
the product tree, hence `Θ(M(n))` for the registered Karatsuba plan and within
the generic `O(M(n) log n)` upper bound. -/
setup_benchmark runRemainderTree n => karatsubaCost n
  with prep := prepRemainderTree
  where {
    paramFloor := 4
    paramCeiling := 2048
    paramSchedule := .custom #[4, 16, 64, 256, 1024, 2048]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["remainder-tree", "karatsuba", "cold-plan", "general-monic",
      "field-65537"]
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
    tags := #["multipoint", "horner", "reused-plan", "field-65537"]
  }

/- Cost model: prepared products and reciprocals make the balanced remainder
traversal a geometric `Θ(M(n))` sum under Karatsuba. -/
setup_benchmark runMultipointEval n => karatsubaCost n
  with prep := prepMultipoint
  where {
    paramFloor := 4
    paramCeiling := 4096
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multipoint", "remainder-tree", "reused-plan", "field-65537"]
  }

/- Cost model: product, reciprocal, and remainder trees are constructed inside
the timed call. Each is a geometric `Θ(M(n))` sum under the registered
Karatsuba plan, and a constant number of such sums remains `Θ(M(n))`. -/
setup_benchmark runColdMultipointEval n => karatsubaCost n
  with prep := prepMultipoint
  where {
    paramFloor := 4
    paramCeiling := 2048
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multipoint", "remainder-tree", "cold-plan", "field-65537"]
  }

/-
Cost model: eight degree-`n` polynomials are each evaluated at `n` points by
linear Horner scans, giving eight times the quadratic direct-evaluation work.
-/
setup_benchmark runRepeatedDirectEval n => (8 * n ^ 2)
  with prep := prepMultipointBatch
  where {
    paramFloor := 4
    paramCeiling := 2048
    paramSchedule := .custom #[4, 16, 32, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multipoint", "horner", "repeated", "reused-points", "field-65537"]
  }

/- Eight polynomials reuse one point-product plan. Each remainder traversal is
a geometric `Θ(M(n))` sum under Karatsuba, so the fixed batch costs eight times
the cutoff-aware multiplication model. -/
setup_benchmark runRepeatedMultipointEval n =>
    8 * karatsubaCost n
  with prep := prepMultipointBatch
  where {
    paramFloor := 4
    paramCeiling := 2048
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multipoint", "remainder-tree", "repeated", "reused-plan",
      "field-65537"]
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
    maxSecondsPerCall := 30.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["interpolation", "lagrange", "direct", "field-65537"]
  }

/- With the distinct-point plan prepared outside the timed call, bottom-up
combination follows the same geometric `Θ(M(n))` Karatsuba tree sum. -/
setup_benchmark runPlannedInterpolation n =>
    karatsubaCost n
  with prep := prepInterpolation
  where {
    paramFloor := 4
    paramCeiling := 4096
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 256, 1024, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["interpolation", "product-tree", "reused-plan", "field-65537"]
  }

/- Distinct-point checking, derivative evaluation, inverses, and the product
tree are included in the cold arm. Their linear work plus a constant number of
geometric Karatsuba tree sums is `Θ(M(n))`. -/
setup_benchmark runColdInterpolation n =>
    karatsubaCost n
  with prep := prepInterpolation
  where {
    paramFloor := 4
    paramCeiling := 2048
    paramSchedule := .custom #[4, 16, 31, 32, 33, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["interpolation", "product-tree", "cold-plan", "field-65537"]
  }

/- Dense Gauss-Jordan elimination performs cubic fixed-field arithmetic. The
verdict excludes matrices through 32, where the quadratic allocation and pivot
scans dominate the cubic row-elimination loop, while retaining those rungs in
the table as crossover evidence. -/
setup_benchmark runLinearPade n => (n ^ 3)
  with prep := prepPade
  where {
    paramFloor := 1
    paramCeiling := 1024
    paramSchedule := .custom #[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 30.0
    targetInnerNanos := 200000000
    verdictWarmupFraction := 0.5
    signalFloorMultiplier := 1.0
    tags := #["pade", "linear-algebra", "reference", "field-65537"]
  }

/- Padé delegates its Euclidean boundary search to the half-gcd engine, with
the same `O(M(n) log n)` balanced cost model. The verdict begins at bound 32,
where the series precision is above the multiplication cutoff. -/
setup_benchmark runHalfGcdPade n => karatsubaCost n * (Nat.log2 n + 1)
  with prep := prepPade
  where {
    paramFloor := 1
    paramCeiling := 1024
    paramSchedule := .custom #[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 200000000
    verdictWarmupFraction := 0.4
    signalFloorMultiplier := 1.0
    tags := #["pade", "half-gcd", "normalized", "field-65537"]
  }

/-! # Informational external comparators

These paired rungs exercise both coefficient-specific FLINT families declared
for this library. Equal hashes check that each pair observes the same product;
their timings orient the report but never select a production cell. -/

def leanCompareConfig (expected : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { repeats := 3, maxSecondsPerCall := 5.0, minTotalSeconds := 0.1,
    expectedHash := some expected }

def flintCompareConfig (expected : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { repeats := 3, maxSecondsPerCall := 5.0, minTotalSeconds := 0.1,
    warmupFirstIter := true, expectedHash := some expected }

setup_fixed_benchmark runFlintOverhead where flintCompareConfig 0x0

setup_fixed_benchmark runLeanInt64 where leanCompareConfig 0x53782e9490aaa3dc
setup_fixed_benchmark runFlintInt64 where flintCompareConfig 0x53782e9490aaa3dc
setup_fixed_benchmark runLeanInt256 where leanCompareConfig 0xbe8b7a83febcd762
setup_fixed_benchmark runFlintInt256 where flintCompareConfig 0xbe8b7a83febcd762
setup_fixed_benchmark runLeanInt1024 where leanCompareConfig 0x6ef7aab77683b9b7
setup_fixed_benchmark runFlintInt1024 where flintCompareConfig 0x6ef7aab77683b9b7

setup_fixed_benchmark runLeanMod64 where leanCompareConfig 0xe1daeb094754a969
setup_fixed_benchmark runFlintMod64 where flintCompareConfig 0xe1daeb094754a969
setup_fixed_benchmark runLeanMod256 where leanCompareConfig 0x213a5e318bc8404d
setup_fixed_benchmark runFlintMod256 where flintCompareConfig 0x213a5e318bc8404d
setup_fixed_benchmark runLeanMod1024 where leanCompareConfig 0xff668644139f6315
setup_fixed_benchmark runFlintMod1024 where flintCompareConfig 0xff668644139f6315

end Hex.PolyFastBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
