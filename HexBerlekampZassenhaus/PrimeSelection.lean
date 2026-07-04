/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexArith.Nat.Prime
public meta import HexBerlekamp.Factor
public meta import HexBerlekamp.Irreducibility
public meta import HexHensel.Basic
public meta import HexHensel.Multifactor
public meta import HexHensel.QuadraticMultifactor
public meta import HexMatrix.Basic
public meta import HexPolyZ.Mignotte
public meta import HexLLL.Basic
public import HexArith.Nat.Prime
public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexHensel.Multifactor
public import HexHensel.QuadraticMultifactor
public import HexLLL.Basic
-- Needed so `decide`/`rfl` over `DensePoly`/`Array` equality reduces in the
-- kernel: the core `Array.instDecidableEq` delegates its nonempty case to the
-- non-`@[expose]` `Array.instDecidableEqImpl`, which is otherwise opaque under
-- the module system. Drop once that impl is exposed upstream (lean4).
import all Init.Data.Array.DecidableEq


public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
This module collects X/xPower extraction, good-prime predicates, small-prime primality certificates, prime candidates, the monic mod-p image, and prime scoring/`choosePrime`.
-/
namespace Hex

namespace ZPoly

/-- The integer polynomial `X`. -/
@[expose]
def X : ZPoly :=
  DensePoly.monomial 1 1

/-- Count the leading zero coefficients of a list, returning that count paired with the remaining tail. -/
private def splitInitialZeros : List Int → Nat × List Int
  | [] => (0, [])
  | coeff :: coeffs =>
      if coeff = 0 then
        let rest := splitInitialZeros coeffs
        (rest.1 + 1, rest.2)
      else
        (0, coeff :: coeffs)

/-- Data from extracting the largest visible power of `X` from a dense integer polynomial. -/
structure XPowerData where
  power : Nat
  core : ZPoly

/--
Remove the initial zero-coefficient run from a dense integer polynomial.

Dense coefficients are stored in ascending degree order, so the initial zero
run is exactly the executable power of `X` dividing the polynomial.
-/
def extractXPower (f : ZPoly) : XPowerData :=
  let split := splitInitialZeros f.toArray.toList
  { power := split.1, core := DensePoly.ofCoeffs split.2.toArray }

/-- The integer leading coefficient reduced to the candidate prime field. -/
@[expose]
def leadingCoeffModP (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : ZMod64 p :=
  ZMod64.ofNat p (intModNat (DensePoly.leadingCoeff f) p)

end ZPoly

/-- The candidate prime does not divide the integer leading coefficient. -/
@[expose]
def leadingCoeffAdmissible (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : Prop :=
  ZPoly.leadingCoeffModP f p ≠ 0

/--
Executable test that a field-polynomial gcd is a unit.

`DensePoly.gcd` is the raw Euclidean representative, so over a field it may be
any nonzero constant associate of `1`.  In normalized dense representation,
nonzero constants are exactly the polynomials with one stored coefficient.
-/
@[expose]
def gcdIsUnit {R : Type u} [Zero R] [DecidableEq R]
    (g : DensePoly R) : Bool :=
  g.size == 1

/-- The modular image is square-free according to the executable gcd-unit criterion. -/
@[expose]
def squareFreeModP (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : Prop :=
  let fModP := ZPoly.modP p f
  gcdIsUnit (DensePoly.gcd fModP (DensePoly.derivative fModP)) = true

/--
Executable good-prime predicate for the Berlekamp-Zassenhaus pipeline.

It checks that the modulus is at least `3`, that the integer leading coefficient
survives reduction modulo `p`, and that the modular image is square-free.
-/
def isGoodPrime (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : Bool :=
  let fModP := ZPoly.modP p f
  3 <= p &&
    ZPoly.leadingCoeffModP f p != 0 &&
    gcdIsUnit (DensePoly.gcd fModP (DensePoly.derivative fModP))

/-- The `ZMod64.Bounds` instance witness for `p = 2`. -/
private theorem bounds_two : ZMod64.Bounds 2 := by
  constructor <;> decide

/-- The `ZMod64.Bounds` instance witness for `p = 3`. -/
theorem bounds_three : ZMod64.Bounds 3 := by
  constructor <;> decide

/-- The `ZMod64.Bounds` instance witness for `p = 5`. -/
private theorem bounds_five : ZMod64.Bounds 5 := by
  constructor <;> decide

/-- The `ZMod64.Bounds` instance witness for `p = 7`. -/
private theorem bounds_seven : ZMod64.Bounds 7 := by
  constructor <;> decide

/-- The `ZMod64.Bounds` instance witness for `p = 11`. -/
private theorem bounds_eleven : ZMod64.Bounds 11 := by
  constructor <;> decide

/-- The `ZMod64.Bounds` instance witness for `p = 13`. -/
private theorem bounds_thirteen : ZMod64.Bounds 13 := by
  constructor <;> decide

/-- The `ZMod64.Bounds` instance witness for `p = 17`. -/
private theorem bounds_seventeen : ZMod64.Bounds 17 := by
  constructor <;> decide

/-- The `ZMod64.Bounds` instance witness for `p = 19`. -/
private theorem bounds_nineteen : ZMod64.Bounds 19 := by
  constructor <;> decide

/-- The `ZMod64.Bounds` instance witness for `p = 23`. -/
private theorem bounds_twenty_three : ZMod64.Bounds 23 := by
  constructor <;> decide

/-- The `ZMod64.Bounds` instance witness for `p = 31`. -/
private theorem bounds_thirty_one : ZMod64.Bounds 31 := by
  constructor <;> decide

/-- The `ZMod64.Bounds` instance witness for `p = 71`. -/
private theorem bounds_seventy_one : ZMod64.Bounds 71 := by
  constructor <;> decide

/-- The primality certificate for `p = 2`. -/
private theorem prime_two : Nat.Prime 2 := by
  refine ⟨?_, ?_⟩
  · decide
  · intro a hdvd
    have hle : a ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hdvd
    rcases hdvd with ⟨k, hk⟩
    match a with
    | 0 => omega
    | 1 => exact Or.inl rfl
    | 2 => exact Or.inr rfl
    | _ + 3 => omega

/-- The primality certificate for `p = 3`. -/
private theorem prime_three : Nat.Prime 3 := by
  refine ⟨?_, ?_⟩
  · decide
  · intro a hdvd
    have hle : a ≤ 3 := Nat.le_of_dvd (by decide : 0 < 3) hdvd
    rcases hdvd with ⟨k, hk⟩
    match a with
    | 0 => omega
    | 1 => exact Or.inl rfl
    | 2 => omega
    | 3 => exact Or.inr rfl
    | _ + 4 => omega

/-- The primality certificate for `p = 5`. -/
private theorem prime_five : Nat.Prime 5 := by
  refine ⟨?_, ?_⟩
  · decide
  · intro a hdvd
    have hle : a ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hdvd
    rcases hdvd with ⟨k, hk⟩
    match a with
    | 0 => omega
    | 1 => exact Or.inl rfl
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => exact Or.inr rfl
    | _ + 6 => omega

/-- The primality certificate for `p = 7`. -/
private theorem prime_seven : Nat.Prime 7 := by
  refine ⟨?_, ?_⟩
  · decide
  · intro a hdvd
    have hle : a ≤ 7 := Nat.le_of_dvd (by decide : 0 < 7) hdvd
    rcases hdvd with ⟨k, hk⟩
    match a with
    | 0 => omega
    | 1 => exact Or.inl rfl
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | 6 => omega
    | 7 => exact Or.inr rfl
    | _ + 8 => omega

/-- The primality certificate for `p = 11`. -/
private theorem prime_eleven : Nat.Prime 11 := by
  refine ⟨?_, ?_⟩
  · decide
  · intro a hdvd
    have hle : a ≤ 11 := Nat.le_of_dvd (by decide : 0 < 11) hdvd
    rcases hdvd with ⟨k, hk⟩
    match a with
    | 0 => omega
    | 1 => exact Or.inl rfl
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | 6 => omega
    | 7 => omega
    | 8 => omega
    | 9 => omega
    | 10 => omega
    | 11 => exact Or.inr rfl
    | _ + 12 => omega

/-- The primality certificate for `p = 13`. -/
private theorem prime_thirteen : Nat.Prime 13 := by
  refine ⟨?_, ?_⟩
  · decide
  · intro a hdvd
    have hle : a ≤ 13 := Nat.le_of_dvd (by decide : 0 < 13) hdvd
    rcases hdvd with ⟨k, hk⟩
    match a with
    | 0 => omega
    | 1 => exact Or.inl rfl
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | 6 => omega
    | 7 => omega
    | 8 => omega
    | 9 => omega
    | 10 => omega
    | 11 => omega
    | 12 => omega
    | 13 => exact Or.inr rfl
    | _ + 14 => omega

/-- The primality certificate for `p = 17`. -/
private theorem prime_seventeen : Nat.Prime 17 := by
  refine ⟨?_, ?_⟩
  · decide
  · intro a hdvd
    have hle : a ≤ 17 := Nat.le_of_dvd (by decide : 0 < 17) hdvd
    rcases hdvd with ⟨k, hk⟩
    match a with
    | 0 => omega
    | 1 => exact Or.inl rfl
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | 6 => omega
    | 7 => omega
    | 8 => omega
    | 9 => omega
    | 10 => omega
    | 11 => omega
    | 12 => omega
    | 13 => omega
    | 14 => omega
    | 15 => omega
    | 16 => omega
    | 17 => exact Or.inr rfl
    | _ + 18 => omega

/-- The primality certificate for `p = 19`. -/
private theorem prime_nineteen : Nat.Prime 19 := by
  refine ⟨?_, ?_⟩
  · decide
  · intro a hdvd
    have hle : a ≤ 19 := Nat.le_of_dvd (by decide : 0 < 19) hdvd
    rcases hdvd with ⟨k, hk⟩
    match a with
    | 0 => omega
    | 1 => exact Or.inl rfl
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | 6 => omega
    | 7 => omega
    | 8 => omega
    | 9 => omega
    | 10 => omega
    | 11 => omega
    | 12 => omega
    | 13 => omega
    | 14 => omega
    | 15 => omega
    | 16 => omega
    | 17 => omega
    | 18 => omega
    | 19 => exact Or.inr rfl
    | _ + 20 => omega

/-- The primality certificate for `p = 23`. -/
private theorem prime_twenty_three : Nat.Prime 23 := by
  refine ⟨?_, ?_⟩
  · decide
  · intro a hdvd
    have hle : a ≤ 23 := Nat.le_of_dvd (by decide : 0 < 23) hdvd
    rcases hdvd with ⟨k, hk⟩
    match a with
    | 0 => omega
    | 1 => exact Or.inl rfl
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | 6 => omega
    | 7 => omega
    | 8 => omega
    | 9 => omega
    | 10 => omega
    | 11 => omega
    | 12 => omega
    | 13 => omega
    | 14 => omega
    | 15 => omega
    | 16 => omega
    | 17 => omega
    | 18 => omega
    | 19 => omega
    | 20 => omega
    | 21 => omega
    | 22 => omega
    | 23 => exact Or.inr rfl
    | _ + 24 => omega

/-- The primality certificate for `p = 31`. -/
private theorem prime_thirty_one : Nat.Prime 31 := by
  refine ⟨?_, ?_⟩
  · decide
  · intro a hdvd
    have hle : a ≤ 31 := Nat.le_of_dvd (by decide : 0 < 31) hdvd
    rcases hdvd with ⟨k, hk⟩
    match a with
    | 0 => omega
    | 1 => exact Or.inl rfl
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | 6 => omega
    | 7 => omega
    | 8 => omega
    | 9 => omega
    | 10 => omega
    | 11 => omega
    | 12 => omega
    | 13 => omega
    | 14 => omega
    | 15 => omega
    | 16 => omega
    | 17 => omega
    | 18 => omega
    | 19 => omega
    | 20 => omega
    | 21 => omega
    | 22 => omega
    | 23 => omega
    | 24 => omega
    | 25 => omega
    | 26 => omega
    | 27 => omega
    | 28 => omega
    | 29 => omega
    | 30 => omega
    | 31 => exact Or.inr rfl
    | _ + 32 => omega

/-- The primality certificate for `p = 71`. -/
private theorem prime_seventy_one : Nat.Prime 71 := by
  refine ⟨?_, ?_⟩
  · decide
  · intro a hdvd
    have hle : a ≤ 71 := Nat.le_of_dvd (by decide : 0 < 71) hdvd
    rcases hdvd with ⟨k, hk⟩
    match a with
    | 0 => omega
    | 1 => exact Or.inl rfl
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | 6 => omega
    | 7 => omega
    | 8 => omega
    | 9 => omega
    | 10 => omega
    | 11 => omega
    | 12 => omega
    | 13 => omega
    | 14 => omega
    | 15 => omega
    | 16 => omega
    | 17 => omega
    | 18 => omega
    | 19 => omega
    | 20 => omega
    | 21 => omega
    | 22 => omega
    | 23 => omega
    | 24 => omega
    | 25 => omega
    | 26 => omega
    | 27 => omega
    | 28 => omega
    | 29 => omega
    | 30 => omega
    | 31 => omega
    | 32 => omega
    | 33 => omega
    | 34 => omega
    | 35 => omega
    | 36 => omega
    | 37 => omega
    | 38 => omega
    | 39 => omega
    | 40 => omega
    | 41 => omega
    | 42 => omega
    | 43 => omega
    | 44 => omega
    | 45 => omega
    | 46 => omega
    | 47 => omega
    | 48 => omega
    | 49 => omega
    | 50 => omega
    | 51 => omega
    | 52 => omega
    | 53 => omega
    | 54 => omega
    | 55 => omega
    | 56 => omega
    | 57 => omega
    | 58 => omega
    | 59 => omega
    | 60 => omega
    | 61 => omega
    | 62 => omega
    | 63 => omega
    | 64 => omega
    | 65 => omega
    | 66 => omega
    | 67 => omega
    | 68 => omega
    | 69 => omega
    | 70 => omega
    | 71 => exact Or.inr rfl
    | _ + 72 => omega

/-- Thin adapter promoting a `Nat.Prime p` witness to the shared
`Lean.Grind.Field (ZMod64 p)` instance via `ZMod64.primeModulusOfPrime`. -/
@[reducible]
private def fieldOfNatPrime {p : Nat} [ZMod64.Bounds p] (hp : Nat.Prime p) :
    Lean.Grind.Field (ZMod64 p) :=
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  inferInstance

/--
A small-prime candidate for the Berlekamp-Zassenhaus prime-selection hot path.

Bundles a candidate prime `p` together with the `ZMod64.Bounds p` instance and
the propositional primality witness needed to drive the modular Berlekamp
factorisation. Exposed (alongside `hotPathCandidates`) so that the SPEC D2
composition theorem
`HexBerlekampZassenhausMathlib.choosePrimeData?_none_implies_huge` can pull a
specific candidate out of the fixed hot-path list and bridge to the Mathlib
per-prime discriminant lemma.
-/
structure SmallPrimeCandidate where
  p : Nat
  [bounds : ZMod64.Bounds p]
  prime : Nat.Prime p

/-- Build a `SmallPrimeCandidate` from a trial-division primality witness and a word-size bound on `p`. -/
private def smallPrimeCandidateOfTrial (p : Nat)
    (hprime : Hex.Nat.isPrimeTrial p = true) (hbound : p ≤ UInt64.word) :
    SmallPrimeCandidate :=
  let prime := Hex.Nat.isPrimeTrial_isPrime hprime
  { p, bounds := { pPos := prime.pos, pLeR := hbound }, prime }

/-- A scored admissible small-prime candidate for default prime selection. -/
structure PrimeCandidateScore where
  /-- Candidate prime. -/
  p : Nat
  /-- Smaller scores are preferred; equal scores retain the earlier smaller prime. -/
  factorCount : Nat

/-- The default list of small primes (`3` through `71`) used for Berlekamp-Zassenhaus trial division. -/
private def smallPrimeCandidates : List SmallPrimeCandidate :=
  [ smallPrimeCandidateOfTrial 3 (by decide) (by decide),
    smallPrimeCandidateOfTrial 5 (by decide) (by decide),
    smallPrimeCandidateOfTrial 7 (by decide) (by decide),
    smallPrimeCandidateOfTrial 11 (by decide) (by decide),
    smallPrimeCandidateOfTrial 13 (by decide) (by decide),
    smallPrimeCandidateOfTrial 17 (by decide) (by decide),
    smallPrimeCandidateOfTrial 19 (by decide) (by decide),
    smallPrimeCandidateOfTrial 23 (by decide) (by decide),
    smallPrimeCandidateOfTrial 29 (by decide) (by decide),
    smallPrimeCandidateOfTrial 31 (by decide) (by decide),
    smallPrimeCandidateOfTrial 37 (by decide) (by decide),
    smallPrimeCandidateOfTrial 41 (by decide) (by decide),
    smallPrimeCandidateOfTrial 43 (by decide) (by decide),
    smallPrimeCandidateOfTrial 47 (by decide) (by decide),
    smallPrimeCandidateOfTrial 53 (by decide) (by decide),
    smallPrimeCandidateOfTrial 59 (by decide) (by decide),
    smallPrimeCandidateOfTrial 61 (by decide) (by decide),
    smallPrimeCandidateOfTrial 67 (by decide) (by decide),
    smallPrimeCandidateOfTrial 71 (by decide) (by decide) ]

set_option maxRecDepth 10000 in
/-- The extended list of larger small-prime candidates, tried when `smallPrimeCandidates` is exhausted. -/
private def extendedSmallPrimeCandidates : List SmallPrimeCandidate :=
  [ smallPrimeCandidateOfTrial 73 (by decide) (by decide),
    smallPrimeCandidateOfTrial 79 (by decide) (by decide),
    smallPrimeCandidateOfTrial 83 (by decide) (by decide),
    smallPrimeCandidateOfTrial 89 (by decide) (by decide),
    smallPrimeCandidateOfTrial 97 (by decide) (by decide),
    smallPrimeCandidateOfTrial 101 (by decide) (by decide),
    smallPrimeCandidateOfTrial 103 (by decide) (by decide),
    smallPrimeCandidateOfTrial 107 (by decide) (by decide),
    smallPrimeCandidateOfTrial 109 (by decide) (by decide),
    smallPrimeCandidateOfTrial 113 (by decide) (by decide),
    smallPrimeCandidateOfTrial 127 (by decide) (by decide),
    smallPrimeCandidateOfTrial 131 (by decide) (by decide),
    smallPrimeCandidateOfTrial 137 (by decide) (by decide),
    smallPrimeCandidateOfTrial 139 (by decide) (by decide),
    smallPrimeCandidateOfTrial 149 (by decide) (by decide),
    smallPrimeCandidateOfTrial 151 (by decide) (by decide),
    smallPrimeCandidateOfTrial 157 (by decide) (by decide),
    smallPrimeCandidateOfTrial 163 (by decide) (by decide),
    smallPrimeCandidateOfTrial 167 (by decide) (by decide),
    smallPrimeCandidateOfTrial 173 (by decide) (by decide),
    smallPrimeCandidateOfTrial 179 (by decide) (by decide),
    smallPrimeCandidateOfTrial 181 (by decide) (by decide),
    smallPrimeCandidateOfTrial 191 (by decide) (by decide),
    smallPrimeCandidateOfTrial 193 (by decide) (by decide),
    smallPrimeCandidateOfTrial 197 (by decide) (by decide),
    smallPrimeCandidateOfTrial 199 (by decide) (by decide),
    smallPrimeCandidateOfTrial 211 (by decide) (by decide),
    smallPrimeCandidateOfTrial 223 (by decide) (by decide),
    smallPrimeCandidateOfTrial 227 (by decide) (by decide),
    smallPrimeCandidateOfTrial 229 (by decide) (by decide),
    smallPrimeCandidateOfTrial 233 (by decide) (by decide),
    smallPrimeCandidateOfTrial 239 (by decide) (by decide),
    smallPrimeCandidateOfTrial 241 (by decide) (by decide),
    smallPrimeCandidateOfTrial 251 (by decide) (by decide),
    smallPrimeCandidateOfTrial 257 (by decide) (by decide),
    smallPrimeCandidateOfTrial 263 (by decide) (by decide),
    smallPrimeCandidateOfTrial 269 (by decide) (by decide),
    smallPrimeCandidateOfTrial 271 (by decide) (by decide),
    smallPrimeCandidateOfTrial 277 (by decide) (by decide),
    smallPrimeCandidateOfTrial 281 (by decide) (by decide),
    smallPrimeCandidateOfTrial 283 (by decide) (by decide),
    smallPrimeCandidateOfTrial 293 (by decide) (by decide),
    smallPrimeCandidateOfTrial 307 (by decide) (by decide),
    smallPrimeCandidateOfTrial 311 (by decide) (by decide),
    smallPrimeCandidateOfTrial 313 (by decide) (by decide),
    smallPrimeCandidateOfTrial 317 (by decide) (by decide),
    smallPrimeCandidateOfTrial 331 (by decide) (by decide),
    smallPrimeCandidateOfTrial 337 (by decide) (by decide),
    smallPrimeCandidateOfTrial 347 (by decide) (by decide),
    smallPrimeCandidateOfTrial 349 (by decide) (by decide),
    smallPrimeCandidateOfTrial 353 (by decide) (by decide),
    smallPrimeCandidateOfTrial 359 (by decide) (by decide),
    smallPrimeCandidateOfTrial 367 (by decide) (by decide),
    smallPrimeCandidateOfTrial 373 (by decide) (by decide),
    smallPrimeCandidateOfTrial 379 (by decide) (by decide),
    smallPrimeCandidateOfTrial 383 (by decide) (by decide),
    smallPrimeCandidateOfTrial 389 (by decide) (by decide),
    smallPrimeCandidateOfTrial 397 (by decide) (by decide),
    smallPrimeCandidateOfTrial 401 (by decide) (by decide),
    smallPrimeCandidateOfTrial 409 (by decide) (by decide),
    smallPrimeCandidateOfTrial 419 (by decide) (by decide),
    smallPrimeCandidateOfTrial 421 (by decide) (by decide),
    smallPrimeCandidateOfTrial 431 (by decide) (by decide),
    smallPrimeCandidateOfTrial 433 (by decide) (by decide),
    smallPrimeCandidateOfTrial 439 (by decide) (by decide),
    smallPrimeCandidateOfTrial 443 (by decide) (by decide),
    smallPrimeCandidateOfTrial 449 (by decide) (by decide),
    smallPrimeCandidateOfTrial 457 (by decide) (by decide),
    smallPrimeCandidateOfTrial 461 (by decide) (by decide),
    smallPrimeCandidateOfTrial 463 (by decide) (by decide),
    smallPrimeCandidateOfTrial 467 (by decide) (by decide),
    smallPrimeCandidateOfTrial 479 (by decide) (by decide),
    smallPrimeCandidateOfTrial 487 (by decide) (by decide),
    smallPrimeCandidateOfTrial 491 (by decide) (by decide),
    smallPrimeCandidateOfTrial 499 (by decide) (by decide) ]

/--
The SPEC hot-path prime candidate list: the deterministic small-prime prefix
followed by every prime up to `499`. Exposed so that the SPEC D2 composition
theorem can pull a specific candidate out and bridge to the Mathlib per-prime
discriminant lemma.
-/
def hotPathCandidates : List SmallPrimeCandidate :=
  smallPrimeCandidates ++ extendedSmallPrimeCandidates

#guard smallPrimeCandidates.length == 19
#guard extendedSmallPrimeCandidates.length == 75
#guard hotPathCandidates.length == 94

/--
Converse of `Hex.Nat.isPrimeTrial_isPrime`: a `Hex.Nat.Prime` witness
implies the trial-division boolean test returns `true`. Used to bridge
between the propositional prime predicate and the kernel-decidable
boolean surface needed to enumerate primes in a bounded range.
-/
private theorem isPrimeTrial_of_prime {n : Nat} (hn : Hex.Nat.Prime n) :
    Hex.Nat.isPrimeTrial n = true := by
  unfold Hex.Nat.isPrimeTrial
  rw [Bool.and_eq_true]
  refine ⟨decide_eq_true hn.two_le, ?_⟩
  rw [List.all_eq_true]
  intro k hk
  have hkn : k < n := List.mem_range.mp hk
  rw [Bool.or_eq_true]
  by_cases hk2 : k < 2
  · exact Or.inl (decide_eq_true hk2)
  · refine Or.inr (decide_eq_true ?_)
    have hk2' : 2 ≤ k := Nat.le_of_not_lt hk2
    intro hmod
    have hdvd : k ∣ n := Nat.dvd_of_mod_eq_zero hmod
    rcases hn.2 k hdvd with hk1 | hkn'
    · omega
    · omega

/--
Soundness of the hot-path prime candidate list: every entry carries a
prime in the closed range `[3, 500]`. The `Hex.Nat.Prime` conjunct is
the structure field directly; the bounds follow by a decidable check
over the 94 explicit primes in the list.
-/
theorem mem_hotPathCandidates_prime
    {c : SmallPrimeCandidate} (hc : c ∈ hotPathCandidates) :
    Hex.Nat.Prime c.p ∧ 3 ≤ c.p ∧ c.p ≤ 500 := by
  have hmem : c.p ∈ hotPathCandidates.map (fun x : SmallPrimeCandidate => x.p) :=
    List.mem_map_of_mem hc
  have hbounds :
      ∀ q ∈ hotPathCandidates.map (fun x : SmallPrimeCandidate => x.p),
        3 ≤ q ∧ q ≤ 500 := by
    decide
  exact ⟨c.prime, (hbounds c.p hmem).1, (hbounds c.p hmem).2⟩

set_option maxRecDepth 4096 in
/--
Coverage of the hot-path prime candidate list: every prime `p` with
`3 ≤ p ≤ 500` appears as the `.p` field of some candidate in
`hotPathCandidates`. Used by SPEC D2's
`choosePrimeData?_none_implies_huge` bridge to walk the executable's
candidate fold over any prime in the admissible range.
-/
theorem exists_mem_hotPathCandidates_of_prime
    {p : Nat} (hprime : Hex.Nat.Prime p) (hge : 3 ≤ p) (hle : p ≤ 500) :
    ∃ c ∈ hotPathCandidates, c.p = p := by
  have htrial : Hex.Nat.isPrimeTrial p = true := isPrimeTrial_of_prime hprime
  have key : ∀ q : Fin 501,
      3 ≤ q.val → Hex.Nat.isPrimeTrial q.val = true →
        q.val ∈ hotPathCandidates.map (fun x : SmallPrimeCandidate => x.p) := by
    decide
  have hmem :
      p ∈ hotPathCandidates.map (fun x : SmallPrimeCandidate => x.p) :=
    key ⟨p, Nat.lt_succ_of_le hle⟩ hge htrial
  obtain ⟨c, hc, hcp⟩ := List.mem_map.mp hmem
  exact ⟨c, hc, hcp⟩

/--
Coerce an admissible nonzero modular image to its monic representative by
dividing by its leading coefficient.  `monicModularImage f = scale c⁻¹ f`
where `c = leadingCoeff f`; the zero branch is a placeholder used to keep
the function total.
-/
@[expose]
def monicModularImage {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : FpPoly p :=
  if f.isZero then
    0
  else
    DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f

theorem monicModularImage_monic
    {p : Nat} [ZMod64.Bounds p] (hp : Nat.Prime p) (f : FpPoly p)
    (hgood : f.isZero = false) :
    DensePoly.Monic (monicModularImage f) := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  unfold monicModularImage
  simp only [hgood, Bool.false_eq_true, ↓reduceIte]
  have hfsize : f.size ≠ 0 := by
    intro hfsize
    have hzero : f.isZero = true := by
      simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero] using hfsize
    rw [hzero] at hgood
    contradiction
  have hfpos : 0 < f.size := Nat.pos_of_ne_zero hfsize
  have hlead_ne : DensePoly.leadingCoeff f ≠ (0 : ZMod64 p) := by
    rw [FpPoly.leadingCoeff_eq_coeff_pred f hfpos]
    exact DensePoly.coeff_last_ne_zero_of_pos_size f hfpos
  have hinv_ne : (DensePoly.leadingCoeff f)⁻¹ ≠ (0 : ZMod64 p) :=
    ZMod64.inv_ne_zero_of_prime hp hlead_ne
  unfold DensePoly.Monic
  rw [FpPoly.leadingCoeff_scale_of_ne_zero_of_nonzero (p := p) hinv_ne f hfsize]
  exact ZMod64.inv_mul_eq_one_of_prime hp hlead_ne

/-- A nonzero `FpPoly p` translates to `isZero = false`. -/
theorem isZero_false_of_ne_zero
    {p : Nat} [ZMod64.Bounds p] {f : FpPoly p} (hf : f ≠ 0) :
    f.isZero = false := by
  cases hz : f.isZero with
  | false => rfl
  | true =>
      exfalso
      apply hf
      apply DensePoly.ext_coeff
      intro n
      have hsize : f.size = 0 := by
        change f.coeffs.isEmpty = true at hz
        simpa [DensePoly.size, Array.isEmpty_iff_size_eq_zero] using hz
      rw [DensePoly.coeff_eq_zero_of_size_le f (by omega)]
      exact DensePoly.coeff_zero n

/-- `monicModularImage` of a nonzero polynomial is nonzero (it's a unit scalar of
the original). -/
theorem monicModularImage_ne_zero_of_ne_zero
    {p : Nat} [ZMod64.Bounds p] (hp : Nat.Prime p) {f : FpPoly p} (hf : f ≠ 0) :
    monicModularImage f ≠ 0 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hf_iszero : f.isZero = false := isZero_false_of_ne_zero hf
  unfold monicModularImage
  simp only [hf_iszero, Bool.false_eq_true, ↓reduceIte]
  have hf_size_pos : 0 < f.size := FpPoly.size_pos_of_ne_zero hf
  have hlead_ne : DensePoly.leadingCoeff f ≠ (0 : ZMod64 p) := by
    rw [FpPoly.leadingCoeff_eq_coeff_pred f hf_size_pos]
    exact DensePoly.coeff_last_ne_zero_of_pos_size f hf_size_pos
  have hinv_ne : (DensePoly.leadingCoeff f)⁻¹ ≠ (0 : ZMod64 p) :=
    ZMod64.inv_ne_zero_of_prime hp hlead_ne
  intro h
  have hsize_zero : (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).size = 0 := by
    rw [h]; rfl
  rw [FpPoly.scale_size_eq_of_ne_zero (p := p) hinv_ne f] at hsize_zero
  exact (Nat.pos_iff_ne_zero.mp hf_size_pos) hsize_zero

/-- `monicModularImage` is the identity on monic polynomials: dividing by a
leading coefficient of `1` is a no-op. -/
theorem monicModularImage_eq_self_of_monic
    {p : Nat} [ZMod64.Bounds p] (hp : Nat.Prime p) (f : FpPoly p)
    (hmonic : DensePoly.Monic f) :
    monicModularImage f = f := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  -- Monic forces `f` to be nonzero: otherwise `leadingCoeff f = 0` but `Monic`
  -- says `leadingCoeff f = 1`.
  have hf_ne : f ≠ 0 := by
    intro h
    subst h
    have hlead_zero : DensePoly.leadingCoeff (0 : FpPoly p) = 0 := rfl
    unfold DensePoly.Monic at hmonic
    rw [hlead_zero] at hmonic
    exact ZMod64.one_ne_zero_of_prime hp hmonic.symm
  have hf_iszero : f.isZero = false := isZero_false_of_ne_zero hf_ne
  unfold monicModularImage
  simp only [hf_iszero, Bool.false_eq_true, ↓reduceIte]
  unfold DensePoly.Monic at hmonic
  rw [hmonic]
  -- (1 : ZMod64 p)⁻¹ = 1
  have hone_ne : (1 : ZMod64 p) ≠ 0 :=
    fun h => ZMod64.one_ne_zero_of_prime hp h
  have hone_inv : (1 : ZMod64 p)⁻¹ = (1 : ZMod64 p) := by
    have hleft : (1 : ZMod64 p)⁻¹ * (1 : ZMod64 p) = 1 :=
      ZMod64.inv_mul_eq_one_of_prime hp hone_ne
    grind
  show DensePoly.scale ((1 : ZMod64 p)⁻¹) f = f
  rw [hone_inv, FpPoly.scale_one_left]

/-- Multiplicativity of `monicModularImage` on nonzero polynomials.  The leading
coefficient of a product is the product of leading coefficients (no-zero-divisors
over a prime field), so dividing both sides by their leading coefficients agrees
with dividing the product by its leading coefficient. -/
theorem monicModularImage_mul_of_nonzero
    {p : Nat} [ZMod64.Bounds p] (hp : Nat.Prime p) {a b : FpPoly p}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    monicModularImage (a * b) = monicModularImage a * monicModularImage b := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hab : a * b ≠ 0 := FpPoly.mul_ne_zero_of_ne_zero ha hb
  have ha_iszero : a.isZero = false := isZero_false_of_ne_zero ha
  have hb_iszero : b.isZero = false := isZero_false_of_ne_zero hb
  have hab_iszero : (a * b).isZero = false := isZero_false_of_ne_zero hab
  have ha_size_pos : 0 < a.size := FpPoly.size_pos_of_ne_zero ha
  have hb_size_pos : 0 < b.size := FpPoly.size_pos_of_ne_zero hb
  have hlead_a : DensePoly.leadingCoeff a ≠ (0 : ZMod64 p) := by
    rw [FpPoly.leadingCoeff_eq_coeff_pred a ha_size_pos]
    exact DensePoly.coeff_last_ne_zero_of_pos_size a ha_size_pos
  have hlead_b : DensePoly.leadingCoeff b ≠ (0 : ZMod64 p) := by
    rw [FpPoly.leadingCoeff_eq_coeff_pred b hb_size_pos]
    exact DensePoly.coeff_last_ne_zero_of_pos_size b hb_size_pos
  have hlead_ab :
      DensePoly.leadingCoeff (a * b) = DensePoly.leadingCoeff a * DensePoly.leadingCoeff b :=
    FpPoly.leadingCoeff_mul a b ha hb
  have hlead_ab_ne : DensePoly.leadingCoeff (a * b) ≠ (0 : ZMod64 p) := by
    rw [hlead_ab]
    intro h
    rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp h with h | h
    · exact hlead_a h
    · exact hlead_b h
  -- `((lc a) * (lc b))⁻¹ = (lc a)⁻¹ * (lc b)⁻¹`: standard field fact, proven
  -- via `(x⁻¹ * y⁻¹) * (x * y) = 1` plus uniqueness of inverse via cancellation.
  have hinv_distrib :
      (DensePoly.leadingCoeff a * DensePoly.leadingCoeff b)⁻¹ =
        (DensePoly.leadingCoeff a)⁻¹ * (DensePoly.leadingCoeff b)⁻¹ := by
    -- Show the candidate is a left inverse.
    have hleft :
        ((DensePoly.leadingCoeff a)⁻¹ * (DensePoly.leadingCoeff b)⁻¹) *
          (DensePoly.leadingCoeff a * DensePoly.leadingCoeff b) = 1 := by
      have ha_inv : (DensePoly.leadingCoeff a)⁻¹ * DensePoly.leadingCoeff a = 1 :=
        ZMod64.inv_mul_eq_one_of_prime hp hlead_a
      have hb_inv : (DensePoly.leadingCoeff b)⁻¹ * DensePoly.leadingCoeff b = 1 :=
        ZMod64.inv_mul_eq_one_of_prime hp hlead_b
      grind
    -- Show the canonical inverse is also a left inverse.
    have habinv_ne :
        DensePoly.leadingCoeff a * DensePoly.leadingCoeff b ≠ (0 : ZMod64 p) := by
      rw [← hlead_ab]; exact hlead_ab_ne
    have hcanon :
        (DensePoly.leadingCoeff a * DensePoly.leadingCoeff b)⁻¹ *
          (DensePoly.leadingCoeff a * DensePoly.leadingCoeff b) = 1 :=
      ZMod64.inv_mul_eq_one_of_prime hp habinv_ne
    -- Cancellation: `(c - d) * x = 0` and `x ≠ 0` ⇒ `c = d`.
    have hdiff :
        ((DensePoly.leadingCoeff a * DensePoly.leadingCoeff b)⁻¹ -
          ((DensePoly.leadingCoeff a)⁻¹ * (DensePoly.leadingCoeff b)⁻¹)) *
          (DensePoly.leadingCoeff a * DensePoly.leadingCoeff b) = 0 := by
      grind
    rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hdiff with hz | hz
    · grind
    · exact False.elim (habinv_ne hz)
  -- LHS computation.
  unfold monicModularImage
  simp only [ha_iszero, hb_iszero, hab_iszero, Bool.false_eq_true, ↓reduceIte]
  rw [hlead_ab, hinv_distrib]
  -- Goal: scale ((lc a)⁻¹ * (lc b)⁻¹) (a * b) = scale (lc a)⁻¹ a * scale (lc b)⁻¹ b
  -- Calc through scale_scale + scale_mul_left + mul_comm to align both sides.
  calc DensePoly.scale ((DensePoly.leadingCoeff a)⁻¹ * (DensePoly.leadingCoeff b)⁻¹) (a * b)
      = DensePoly.scale (DensePoly.leadingCoeff a)⁻¹
          (DensePoly.scale (DensePoly.leadingCoeff b)⁻¹ (a * b)) := by
        rw [← FpPoly.scale_scale]
    _ = DensePoly.scale (DensePoly.leadingCoeff a)⁻¹
          (DensePoly.scale (DensePoly.leadingCoeff b)⁻¹ (b * a)) := by
        rw [FpPoly.mul_comm a b]
    _ = DensePoly.scale (DensePoly.leadingCoeff a)⁻¹
          (DensePoly.scale (DensePoly.leadingCoeff b)⁻¹ b * a) := by
        rw [FpPoly.scale_mul_left]
    _ = DensePoly.scale (DensePoly.leadingCoeff a)⁻¹
          (a * DensePoly.scale (DensePoly.leadingCoeff b)⁻¹ b) := by
        rw [FpPoly.mul_comm (DensePoly.scale (DensePoly.leadingCoeff b)⁻¹ b) a]
    _ = DensePoly.scale (DensePoly.leadingCoeff a)⁻¹ a *
          DensePoly.scale (DensePoly.leadingCoeff b)⁻¹ b := by
        rw [FpPoly.scale_mul_left]

/-- The constant polynomial `1` over a prime modulus is nonzero. -/
private theorem fpPoly_one_ne_zero
    {p : Nat} [ZMod64.Bounds p] (hp : Nat.Prime p) : (1 : FpPoly p) ≠ 0 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  intro h
  have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) h
  change (1 : FpPoly p).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
  rw [DensePoly.coeff_zero] at hcoeff
  have hone_coeff : (1 : FpPoly p).coeff 0 = (1 : ZMod64 p) := by
    change (DensePoly.C (1 : ZMod64 p)).coeff 0 = (1 : ZMod64 p)
    rw [DensePoly.coeff_C]
    simp
  rw [hone_coeff] at hcoeff
  exact ZMod64.one_ne_zero_of_prime hp hcoeff

/-- The constant polynomial `1` over a prime modulus is monic. -/
private theorem fpPoly_one_monic
    {p : Nat} [ZMod64.Bounds p] (hp : Nat.Prime p) :
    DensePoly.Monic (1 : FpPoly p) := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hsize : (1 : FpPoly p).size = 1 := by
    have h_le : (1 : FpPoly p).size ≤ 1 := by
      change (DensePoly.C (1 : ZMod64 p) : FpPoly p).size ≤ 1
      exact DensePoly.size_C_le_one (1 : ZMod64 p)
    have h_ge : 1 ≤ (1 : FpPoly p).size :=
      FpPoly.size_pos_of_ne_zero (fpPoly_one_ne_zero hp)
    omega
  unfold DensePoly.Monic
  rw [DensePoly.leadingCoeff_eq_coeff_last (1 : FpPoly p) (by omega), hsize]
  change (DensePoly.C (1 : ZMod64 p)).coeff (1 - 1) = 1
  rw [DensePoly.coeff_C]
  simp

/-- `Hex.Berlekamp.factorProduct` of a list whose elements are all nonzero is
itself nonzero (over a prime field). -/
private theorem factorProduct_ne_zero_of_forall_ne_zero
    {p : Nat} [ZMod64.Bounds p] (hp : Nat.Prime p)
    (l : List (FpPoly p)) (hne : ∀ g ∈ l, g ≠ 0) :
    Hex.Berlekamp.factorProduct l ≠ 0 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  induction l with
  | nil => exact fpPoly_one_ne_zero hp
  | cons h tail ih =>
      rw [Hex.Berlekamp.factorProduct_cons]
      exact FpPoly.mul_ne_zero_of_ne_zero
        (hne h List.mem_cons_self)
        (ih (fun g hg => hne g (List.mem_cons_of_mem _ hg)))

/-- `monicModularImage` is multiplicative across `Hex.Berlekamp.factorProduct`
on lists of nonzero factors: pulling each factor through `monicModularImage`
before taking the product agrees with applying `monicModularImage` to the raw
product.  Inductive consequence of `monicModularImage_mul_of_nonzero` plus
`monicModularImage_eq_self_of_monic` at the base case `factorProduct [] = 1`. -/
theorem factorProduct_map_monicModularImage_eq_monicModularImage_factorProduct
    {p : Nat} [ZMod64.Bounds p] (hp : Nat.Prime p)
    (l : List (FpPoly p)) (hne : ∀ g ∈ l, g ≠ 0) :
    Hex.Berlekamp.factorProduct (l.map monicModularImage) =
      monicModularImage (Hex.Berlekamp.factorProduct l) := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  induction l with
  | nil =>
      simp only [List.map_nil]
      rw [Hex.Berlekamp.factorProduct_nil]
      -- Goal: 1 = monicModularImage 1
      rw [monicModularImage_eq_self_of_monic hp 1 (fpPoly_one_monic hp)]
  | cons head tail ih =>
      have hhead_ne : head ≠ 0 := hne head List.mem_cons_self
      have htail_ne : ∀ g ∈ tail, g ≠ 0 :=
        fun g hg => hne g (List.mem_cons_of_mem _ hg)
      have htail_prod_ne : Hex.Berlekamp.factorProduct tail ≠ 0 :=
        factorProduct_ne_zero_of_forall_ne_zero hp tail htail_ne
      have ih_eq := ih htail_ne
      simp only [List.map_cons]
      rw [Hex.Berlekamp.factorProduct_cons, Hex.Berlekamp.factorProduct_cons, ih_eq,
        monicModularImage_mul_of_nonzero hp hhead_ne htail_prod_ne]

private def berlekampFactorsModP (f : ZPoly) (c : SmallPrimeCandidate) :
    Array (@FpPoly c.p c.bounds) :=
  letI := c.bounds
  letI := fieldOfNatPrime c.prime
  let fModP := ZPoly.modP c.p f
  if hzero : fModP.isZero = false then
    ((Berlekamp.berlekampFactor
      (monicModularImage fModP)
      (monicModularImage_monic c.prime fModP hzero)).factors.map
        monicModularImage).toArray
  else
    #[]

/--
Defining equation for `berlekampFactorsModP` on a candidate whose modular image
is nonzero: the factor array is the executable Berlekamp factor list applied to
the candidate's monic modular image, with each factor post-processed through
`monicModularImage` to normalise it to its monic associate.  The EEA-based
`DensePoly.gcd` returns each Berlekamp split factor up to a unit scalar, so the
extraction layer applies the leading-coefficient inverse scaling here, isolating
the normalisation step to this call site without touching
`HexBerlekamp/Factor.lean`.
-/
private theorem berlekampFactorsModP_eq_of_isZero_false
    (f : ZPoly) (c : SmallPrimeCandidate) :
    letI := c.bounds
    letI := fieldOfNatPrime c.prime
    ∀ (hzero : (ZPoly.modP c.p f).isZero = false),
      berlekampFactorsModP f c =
        ((Berlekamp.berlekampFactor
          (monicModularImage (ZPoly.modP c.p f))
          (monicModularImage_monic c.prime (ZPoly.modP c.p f) hzero)).factors.map
            monicModularImage).toArray := by
  letI := c.bounds
  letI := fieldOfNatPrime c.prime
  intro hzero
  unfold berlekampFactorsModP
  rw [dif_pos hzero]

/-- Reduce an integer coefficient to its canonical natural-number residue modulo `p` for the modular Horner evaluator. -/
private def intCoeffModNat (z : Int) (p : Nat) : Nat :=
  Int.toNat (z % Int.ofNat p)

/-- Evaluate a `ZPoly` at `x` modulo `p` by Horner-folding its coefficients through `intCoeffModNat`. -/
private def evalZPolyModNat (f : ZPoly) (p x : Nat) : Nat :=
  f.toArray.toList.reverse.foldl
    (fun acc coeff => (intCoeffModNat coeff p + x * acc) % p)
    0

/-- Detect the cheap case where `f mod p` splits completely into linear factors by counting roots modulo `p`. -/
private def completeLinearDegreeSplit? (f : ZPoly) (p : Nat) [ZMod64.Bounds p] :
    Option (Array Nat) :=
  let degree := (ZPoly.modP p f).degree?.getD 0
  let roots := (List.range p).filter fun x => evalZPolyModNat f p x == 0
  if degree != 0 && roots.length == degree then
    some (Array.replicate degree 1)
  else
    none

/--
Return the sorted degrees of the Berlekamp factors of `f mod p` at an
explicit small prime supported by the executable prime-selection list.

This testing-facing surface deliberately reuses the production small-prime
pipeline. For complete linear splits, it records the explicit root-degree
evidence directly so pinned conformance checks are not sensitive to the current
Berlekamp witness splitting surface. It returns `none` if `p` is unsupported or
the leading coefficient vanishes modulo `p`; the Berlekamp branch also requires
the usual good-prime predicate.
-/
def modularFactorDegreesAt? (f : ZPoly) (p : Nat) : Option (Array Nat) :=
  hotPathCandidates.foldl
    (fun found (c : SmallPrimeCandidate) =>
      match found with
      | some degrees => some degrees
      | none =>
          if c.p == p then
            letI : ZMod64.Bounds c.p := c.bounds
            if ZPoly.leadingCoeffModP f c.p != 0 then
              match completeLinearDegreeSplit? f c.p with
              | some degrees => some degrees
              | none =>
                  if isGoodPrime f c.p then
                    some ((berlekampFactorsModP f c).map (fun factor =>
                      factor.degree?.getD 0) |>.qsort (· ≤ ·))
                  else
                    none
            else
              none
          else
            none)
    none

/-- Witness polynomial used by the nearby guard that pins the modular factor-degree query at the prime `29`. -/
private def prefixTwentyNineGuard : ZPoly :=
  DensePoly.ofCoeffs #[1, 1, 111546435]

#guard (modularFactorDegreesAt? prefixTwentyNineGuard 29).isSome

/-- Score one small-prime candidate by its Berlekamp factor count when it is admissible for `f`. -/
private def scoreCandidate (f : ZPoly) (c : SmallPrimeCandidate) : Option PrimeCandidateScore :=
  letI := c.bounds
  if isGoodPrime f c.p then
    let factors := berlekampFactorsModP f c
    some { p := c.p, factorCount := factors.size }
  else
    none

/-- Choose the lower factor-count score, keeping the incumbent score on ties for deterministic prime selection. -/
private def betterScore (old new : PrimeCandidateScore) : PrimeCandidateScore :=
  if new.factorCount < old.factorCount then
    new
  else
    old

/-- Fold one small-prime candidate into the running best score used by `choosePrimeScore?`. -/
private def choosePrimeScoreStep
    (f : ZPoly) (best : Option PrimeCandidateScore) (c : SmallPrimeCandidate) :
    Option PrimeCandidateScore :=
  match best, scoreCandidate f c with
  | none, score => score
  | some old, none => some old
  | some old, some new => some (betterScore old new)

/-- Scan the fixed hot-path prime list and return the best admissible scored candidate, if any. -/
def choosePrimeScore? (f : ZPoly) : Option PrimeCandidateScore :=
  hotPathCandidates.foldl (choosePrimeScoreStep f) none

private theorem scoreCandidate_isGoodPrime
    (f : ZPoly) (c : SmallPrimeCandidate) (score : PrimeCandidateScore)
    (hscore : scoreCandidate f c = some score) :
    ∃ hbounds : ZMod64.Bounds score.p,
      @isGoodPrime f score.p hbounds = true := by
  unfold scoreCandidate at hscore
  letI := c.bounds
  by_cases hgood : isGoodPrime f c.p
  · simp [hgood] at hscore
    cases hscore
    exact ⟨c.bounds, hgood⟩
  · simp [hgood] at hscore

private theorem betterScore_isGoodPrime
    (f : ZPoly) (old new score : PrimeCandidateScore)
    (hold : ∃ hbounds : ZMod64.Bounds old.p,
      @isGoodPrime f old.p hbounds = true)
    (hnew : ∃ hbounds : ZMod64.Bounds new.p,
      @isGoodPrime f new.p hbounds = true)
    (hscore : betterScore old new = score) :
    ∃ hbounds : ZMod64.Bounds score.p,
      @isGoodPrime f score.p hbounds = true := by
  unfold betterScore at hscore
  split at hscore
  · cases hscore
    exact hnew
  · cases hscore
    exact hold

private theorem choosePrimeScoreStep_isGoodPrime
    (f : ZPoly) (best : Option PrimeCandidateScore) (c : SmallPrimeCandidate)
    (score : PrimeCandidateScore)
    (hbest : ∀ old, best = some old →
      ∃ hbounds : ZMod64.Bounds old.p,
        @isGoodPrime f old.p hbounds = true)
    (hscore : choosePrimeScoreStep f best c = some score) :
    ∃ hbounds : ZMod64.Bounds score.p,
      @isGoodPrime f score.p hbounds = true := by
  unfold choosePrimeScoreStep at hscore
  cases hbest_eq : best with
  | none =>
      cases hc_eq : scoreCandidate f c with
      | none =>
          simp [hbest_eq, hc_eq] at hscore
      | some =>
          simp [hbest_eq, hc_eq] at hscore
          cases hscore
          exact scoreCandidate_isGoodPrime f c _ hc_eq
  | some =>
      cases hc_eq : scoreCandidate f c with
      | none =>
          simp [hbest_eq, hc_eq] at hscore
          cases hscore
          exact hbest _ hbest_eq
      | some =>
          simp [hbest_eq, hc_eq] at hscore
          exact betterScore_isGoodPrime f _ _ score
            (hbest _ hbest_eq)
            (scoreCandidate_isGoodPrime f c _ hc_eq)
            hscore

private theorem choosePrimeScore?_fold_isGoodPrime
    (f : ZPoly) (candidates : List SmallPrimeCandidate)
    (best : Option PrimeCandidateScore) (score : PrimeCandidateScore)
    (hbest : ∀ old, best = some old →
      ∃ hbounds : ZMod64.Bounds old.p,
        @isGoodPrime f old.p hbounds = true)
    (hscore : candidates.foldl (choosePrimeScoreStep f) best = some score) :
    ∃ hbounds : ZMod64.Bounds score.p,
      @isGoodPrime f score.p hbounds = true := by
  induction candidates generalizing best with
  | nil =>
      exact hbest score hscore
  | cons c candidates ih =>
      exact ih (choosePrimeScoreStep f best c)
        (fun old hold =>
          choosePrimeScoreStep_isGoodPrime f best c old hbest hold)
        hscore

/--
Choose a small admissible prime for the Berlekamp-Zassenhaus pipeline.

The search is bounded to a fixed ascending list of small primes. Candidate
scores use the currently available executable modular factor surface; strict
score improvement replaces the incumbent, so equal scores keep the smaller
earlier prime.
-/
def choosePrime (f : ZPoly) : Nat :=
  match choosePrimeScore? f with
  | some score => score.p
  | none => 3

theorem choosePrimeScore?_isGoodPrime
    (f : ZPoly) (score : PrimeCandidateScore)
    (hscore : choosePrimeScore? f = some score) :
    ∃ hbounds : ZMod64.Bounds score.p,
      @isGoodPrime f score.p hbounds = true := by
  unfold choosePrimeScore? at hscore
  exact choosePrimeScore?_fold_isGoodPrime f hotPathCandidates none score
    (by intro old hnone; cases hnone)
    hscore

theorem choosePrime_isGoodPrime_of_selected
    (f : ZPoly) (score : PrimeCandidateScore)
    (hscore : choosePrimeScore? f = some score)
    (hchoose : choosePrime f = score.p) :
    ∃ hbounds : ZMod64.Bounds (choosePrime f),
      @isGoodPrime f (choosePrime f) hbounds = true := by
  rcases choosePrimeScore?_isGoodPrime f score hscore with ⟨hbounds, hgood⟩
  simpa [hchoose] using
    (show ∃ hbounds : ZMod64.Bounds score.p,
      @isGoodPrime f score.p hbounds = true from ⟨hbounds, hgood⟩)

/-- A successful good-prime check certifies the modulus is at least three. -/
theorem isGoodPrime_ge_three
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hgood : isGoodPrime f p = true) :
    3 <= p := by
  unfold isGoodPrime at hgood
  simp only [Bool.and_eq_true] at hgood
  exact of_decide_eq_true hgood.1.1

/-- A successful good-prime check certifies leading-coefficient admissibility. -/
theorem isGoodPrime_leadingCoeffAdmissible
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hgood : isGoodPrime f p = true) :
    leadingCoeffAdmissible f p := by
  unfold isGoodPrime at hgood
  unfold leadingCoeffAdmissible
  simp only [Bool.and_eq_true] at hgood
  simpa [bne_iff_ne] using hgood.1.2

/-- A successful good-prime check certifies the modular square-free precondition. -/
theorem isGoodPrime_squareFreeModP
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hgood : isGoodPrime f p = true) :
    squareFreeModP f p := by
  unfold isGoodPrime at hgood
  unfold squareFreeModP
  simp only [Bool.and_eq_true] at hgood
  exact hgood.2

/--
A successful good-prime check rules out a vanishing modular image: the leading
coefficient survives reduction modulo `p`, so the modular image retains at
least one stored coefficient.
-/
theorem isGoodPrime_modP_isZero_false
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hgood : isGoodPrime f p = true) :
    (ZPoly.modP p f).isZero = false := by
  have hadm : leadingCoeffAdmissible f p := isGoodPrime_leadingCoeffAdmissible f p hgood
  unfold leadingCoeffAdmissible at hadm
  have hfsize : 0 < f.size := by
    rcases Nat.eq_zero_or_pos f.size with hsize_zero | hfsize
    · exfalso
      apply hadm
      have hcoeffs_zero : f.coeffs.size = 0 := by simpa [DensePoly.size] using hsize_zero
      have hlead : DensePoly.leadingCoeff f = 0 := by
        simp [DensePoly.leadingCoeff, hcoeffs_zero, Array.getD] <;> rfl
      unfold ZPoly.leadingCoeffModP
      rw [hlead]
      show (ZMod64.ofNat p (ZPoly.intModNat 0 p) : ZMod64 p) = 0
      rfl
    · exact hfsize
  have hcoeff_ne : (ZPoly.modP p f).coeff (f.size - 1) ≠ 0 := by
    rw [ZPoly.coeff_modP, ← DensePoly.leadingCoeff_eq_coeff_last f hfsize]
    exact hadm
  cases hzero : (ZPoly.modP p f).isZero with
  | false => rfl
  | true =>
      exfalso
      have hsize : (ZPoly.modP p f).size = 0 := by
        simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero] using hzero
      have hzero_coeff :=
        DensePoly.coeff_eq_zero_of_size_le (ZPoly.modP p f)
          (show (ZPoly.modP p f).size ≤ f.size - 1 by omega)
      exact hcoeff_ne hzero_coeff

/-- `leadingCoeffAdmissible` forces the source polynomial to have at least one
stored coefficient: the empty coefficient array would force
`leadingCoeffModP` to vanish. -/
theorem leadingCoeffAdmissible_size_pos
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hadm : leadingCoeffAdmissible f p) :
    0 < f.size := by
  unfold leadingCoeffAdmissible at hadm
  rcases Nat.eq_zero_or_pos f.size with hsize_zero | hfsize
  · exfalso
    apply hadm
    have hcoeffs_zero : f.coeffs.size = 0 := by simpa [DensePoly.size] using hsize_zero
    have hlead : DensePoly.leadingCoeff f = 0 := by
      simp [DensePoly.leadingCoeff, hcoeffs_zero, Array.getD] <;> rfl
    unfold ZPoly.leadingCoeffModP
    rw [hlead]
    show (ZMod64.ofNat p (ZPoly.intModNat 0 p) : ZMod64 p) = 0
    rfl
  · exact hfsize

/-- The top coefficient of `ZPoly.modP p f` matches `leadingCoeffModP` and is
nonzero precisely when admissibility holds: the modular image keeps its last
slot populated, so no trailing trim collapses below `f.size - 1`. -/
private theorem coeff_modP_top_eq_leadingCoeffModP
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hfsize : 0 < f.size) :
    (ZPoly.modP p f).coeff (f.size - 1) = ZPoly.leadingCoeffModP f p := by
  rw [ZPoly.coeff_modP, ← DensePoly.leadingCoeff_eq_coeff_last f hfsize]
  rfl

/-- Under `leadingCoeffAdmissible`, the modular image is nonzero. Companion of
`isGoodPrime_modP_isZero_false` but with the weaker admissibility hypothesis
(no square-free or `3 ≤ p` requirement). -/
theorem modP_ne_zero_of_leadingCoeffAdmissible
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hadm : leadingCoeffAdmissible f p) :
    ZPoly.modP p f ≠ 0 := by
  have hfsize := leadingCoeffAdmissible_size_pos f p hadm
  have hcoeff_ne : (ZPoly.modP p f).coeff (f.size - 1) ≠ 0 := by
    rw [coeff_modP_top_eq_leadingCoeffModP f p hfsize]
    exact hadm
  intro hzero
  apply hcoeff_ne
  rw [hzero]
  rfl

/-- Under `leadingCoeffAdmissible`, the modular image has the same size as the
input: the top coefficient survives reduction, so the trailing-zero trim does
nothing. -/
theorem size_modP_eq_of_leadingCoeffAdmissible
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hadm : leadingCoeffAdmissible f p) :
    (ZPoly.modP p f).size = f.size := by
  have hfsize := leadingCoeffAdmissible_size_pos f p hadm
  have hcoeff_ne : (ZPoly.modP p f).coeff (f.size - 1) ≠ 0 := by
    rw [coeff_modP_top_eq_leadingCoeffModP f p hfsize]
    exact hadm
  have hge : f.size ≤ (ZPoly.modP p f).size := by
    rcases Nat.lt_or_ge (ZPoly.modP p f).size f.size with hlt | hge
    · exfalso
      apply hcoeff_ne
      exact DensePoly.coeff_eq_zero_of_size_le _ (by omega)
    · exact hge
  have hle : (ZPoly.modP p f).size ≤ f.size := by
    show (ZPoly.modP p f).coeffs.size ≤ f.size
    unfold ZPoly.modP FpPoly.ofCoeffs
    have h := DensePoly.size_ofCoeffs_le
      (R := ZMod64 p)
      ((List.range f.size).map
        (fun i => ZMod64.ofNat p (ZPoly.intModNat (f.coeff i) p))).toArray
    have hlen : ((List.range f.size).map
        (fun i => ZMod64.ofNat p (ZPoly.intModNat (f.coeff i) p))).toArray.size =
          f.size := by simp
    simpa [DensePoly.size, hlen] using h
  omega

/-- Under `leadingCoeffAdmissible`, the modular image has the same `degree?` as
the input. -/
theorem degree?_modP_eq_of_leadingCoeffAdmissible
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hadm : leadingCoeffAdmissible f p) :
    (ZPoly.modP p f).degree? = f.degree? := by
  have hsize := size_modP_eq_of_leadingCoeffAdmissible f p hadm
  unfold DensePoly.degree?
  rw [hsize]

/-- Under `leadingCoeffAdmissible`, the leading coefficient of the modular
image matches `leadingCoeffModP`. -/
theorem leadingCoeff_modP_eq_leadingCoeffModP_of_admissible
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hadm : leadingCoeffAdmissible f p) :
    DensePoly.leadingCoeff (ZPoly.modP p f) = ZPoly.leadingCoeffModP f p := by
  have hfsize := leadingCoeffAdmissible_size_pos f p hadm
  have hsize := size_modP_eq_of_leadingCoeffAdmissible f p hadm
  have hmod_size_pos : 0 < (ZPoly.modP p f).size := by omega
  rw [DensePoly.leadingCoeff_eq_coeff_last _ hmod_size_pos, hsize]
  exact coeff_modP_top_eq_leadingCoeffModP f p hfsize

end Hex
