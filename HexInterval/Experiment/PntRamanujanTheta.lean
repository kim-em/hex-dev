/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Init.Data.Nat.Log2

@[expose] public section

/-!
# Source-pinned Ramanujan theta family

The pinned Ramanujan proof uses a bounded range certificate on `[3, 599)` and
one point certificate at 599. This module authenticates both source rows, the
complete prime list through 599, its primorial, and the computations used by
the ordinary-kernel proofs.
-/

namespace Hex.Interval.Experiment.PntRamanujanTheta

structure Coordinate where
  line : Nat
  deriving DecidableEq, Repr

structure Certificate where
  coordinate : Coordinate
  input : Nat
  toleranceNumerator : Nat
  toleranceDenominator : Nat
  precision : Nat
  lowerExponent : Nat
  upperExponent : Nat
  deriving DecidableEq, Repr

structure RangeCertificate where
  coordinate : Coordinate
  start : Nat
  limit : Nat
  toleranceNumerator : Nat
  toleranceDenominator : Nat
  precision : Nat
  deriving DecidableEq, Repr

def primeList : List Nat := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
  59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
  137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
  227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311,
  313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
  419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
  509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599
]

def primeProduct : Nat :=
  31593200588075913689970182876007553570909421666260419385429299398402529944517173289900520347153350493497280131802427122599698326552878073675733671818666226970431485829830266569226518041925342790985720668473442619880541151076677539407004895703510

def checkPrime (value : Nat) : Bool :=
  decide (2 ≤ value) && (List.range value).all fun divisor =>
    decide (divisor < 2) || decide (value % divisor ≠ 0)

/-- Check the fixed point payload and its exact prime-product bracket. The
semantic theta theorem remains in the Mathlib companion. -/
def checkPointShape (value : Certificate) : Bool :=
  decide (0 < value.toleranceDenominator) &&
    decide (value.toleranceNumerator < value.toleranceDenominator) &&
    value.precision == 20 && primeList.length == 109 &&
    primeList.getLast? == some value.input &&
    primeList.all checkPrime &&
    decide (primeList.Pairwise (fun left right => left < right)) &&
    primeList.prod == primeProduct &&
    2 ^ value.lowerExponent < primeProduct &&
    primeProduct < 2 ^ value.upperExponent &&
    value.input * (value.toleranceDenominator - value.toleranceNumerator) * 100 <
      value.lowerExponent * 69 * value.toleranceDenominator &&
    value.upperExponent * 7 * value.toleranceDenominator <
      value.input * (value.toleranceDenominator + value.toleranceNumerator) * 10

def sourceRows : List Certificate := [
  ⟨⟨505⟩, 599, 65, 1000, 20, 812, 813⟩
]

/-- Product of the committed prime prefix through `n`. -/
def productThrough (n : Nat) : Nat :=
  (primeList.filter fun p => p ≤ n).prod

/-- The checked lower logarithm comparison needed on the real unit interval
with floor `n`: `0.232 * (n + 1) ≤ 0.69 * log₂(productThrough n)`. -/
def checkRangeAt (n : Nat) : Bool :=
  decide (232 * (n + 1) ≤ 690 * Nat.log2 (productThrough n))

/-- Check every floor coordinate in `[start, limit)`. -/
def checkRange (start limit : Nat) : Bool :=
  (List.range (limit - start)).all fun offset => checkRangeAt (start + offset)

def rangeRows : List RangeCertificate := [
  ⟨⟨500⟩, 3, 599, 768, 1000, 20⟩
]

def RangeCertificate.checkShape (value : RangeCertificate) : Bool :=
  value.start < value.limit && value.toleranceDenominator > 0 &&
    value.toleranceNumerator < value.toleranceDenominator && value.precision == 20

def validRangeCertificate (index : Nat) (value : RangeCertificate) : Bool :=
  rangeRows[index]? == some value && value.checkShape &&
    checkRange value.start value.limit

def validCertificate (index : Nat) (value : Certificate) : Bool :=
  sourceRows[index]? == some value && checkPointShape value

def certificates : List Certificate := sourceRows

def firstFailure? : Nat → List Certificate → Option Coordinate
  | _, [] => none
  | index, value :: values =>
      if validCertificate index value then firstFailure? (index + 1) values
      else
        match sourceRows[index]? with
        | some expected => some expected.coordinate
        | none => some value.coordinate

def firstRangeFailure? : Nat → List RangeCertificate → Option Coordinate
  | _, [] => none
  | index, value :: values =>
      if validRangeCertificate index value then
        firstRangeFailure? (index + 1) values
      else
        match rangeRows[index]? with
        | some expected => some expected.coordinate
        | none => some value.coordinate

end Hex.Interval.Experiment.PntRamanujanTheta

end
