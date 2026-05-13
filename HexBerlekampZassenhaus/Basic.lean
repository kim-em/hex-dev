import HexBerlekamp.Factor
import HexBerlekamp.Irreducibility
import HexHensel.Multifactor
import HexHensel.QuadraticMultifactor
import HexLLL.Basic

/-!
Executable data records for the Berlekamp-Zassenhaus factorization pipeline.

This module contains the shared records passed between prime selection,
Hensel lifting, and LLL-based integer recombination in the `ZPoly`
factorization pipeline.
-/
namespace Hex

namespace ZPoly

private def intModNat (z : Int) (m : Nat) : Nat :=
  Int.toNat (z % Int.ofNat m)

/-- The integer polynomial `X`. -/
def X : ZPoly :=
  DensePoly.monomial 1 1

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
def leadingCoeffModP (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : ZMod64 p :=
  ZMod64.ofNat p (intModNat (DensePoly.leadingCoeff f) p)

end ZPoly

/-- The candidate prime does not divide the integer leading coefficient. -/
def leadingCoeffAdmissible (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : Prop :=
  ZPoly.leadingCoeffModP f p ≠ 0

/-- The modular image is square-free according to the executable gcd criterion. -/
def squareFreeModP (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : Prop :=
  let fModP := ZPoly.modP p f
  DensePoly.gcd fModP (DensePoly.derivative fModP) = 1

/--
Executable good-prime predicate for the Berlekamp-Zassenhaus pipeline.

It checks that the modulus is at least `3`, that the integer leading coefficient
survives reduction modulo `p`, and that the modular image is square-free.
-/
def isGoodPrime (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : Bool :=
  let fModP := ZPoly.modP p f
  3 <= p &&
    ZPoly.leadingCoeffModP f p != 0 &&
    DensePoly.gcd fModP (DensePoly.derivative fModP) == 1

private theorem bounds_two : ZMod64.Bounds 2 := by
  constructor <;> decide

private theorem bounds_three : ZMod64.Bounds 3 := by
  constructor <;> decide

private theorem bounds_five : ZMod64.Bounds 5 := by
  constructor <;> decide

private theorem bounds_seven : ZMod64.Bounds 7 := by
  constructor <;> decide

private theorem bounds_eleven : ZMod64.Bounds 11 := by
  constructor <;> decide

private theorem bounds_thirteen : ZMod64.Bounds 13 := by
  constructor <;> decide

private theorem bounds_seventeen : ZMod64.Bounds 17 := by
  constructor <;> decide

private theorem bounds_nineteen : ZMod64.Bounds 19 := by
  constructor <;> decide

private theorem bounds_twenty_three : ZMod64.Bounds 23 := by
  constructor <;> decide

private theorem bounds_thirty_one : ZMod64.Bounds 31 := by
  constructor <;> decide

private theorem bounds_seventy_one : ZMod64.Bounds 71 := by
  constructor <;> decide

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

private def zmod64ZPow {p : Nat} [ZMod64.Bounds p] (a : ZMod64 p) : Int → ZMod64 p
  | .ofNat n => a ^ n
  | .negSucc n => (a ^ (n + 1))⁻¹

private instance zmod64IntPow {p : Nat} [ZMod64.Bounds p] :
    HPow (ZMod64 p) Int (ZMod64 p) where
  hPow := zmod64ZPow

private theorem zmod64_one_ne_zero_of_prime
    {p : Nat} [ZMod64.Bounds p] (hp : Nat.Prime p) :
    (1 : ZMod64 p) ≠ 0 := by
  intro h
  have hp2 : 2 ≤ p := hp.two_le
  have htoNat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat :=
    congrArg ZMod64.toNat h
  rw [show ((1 : ZMod64 p).toNat) = 1 % p from ZMod64.toNat_one,
      show ((0 : ZMod64 p).toNat) = 0 from ZMod64.toNat_zero,
      Nat.mod_eq_of_lt (by omega : 1 < p)] at htoNat
  omega

private theorem zmod64_inv_zero {p : Nat} [ZMod64.Bounds p] :
    (0 : ZMod64 p)⁻¹ = 0 := by
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  change (ZMod64.inv (0 : ZMod64 p)).toNat = (0 : ZMod64 p).toNat
  rw [ZMod64.toNat_inv_def]
  change (((HexArith.Int.extGcd 0 (Int.ofNat p)).2.1 % Int.ofNat p).toNat % p = 0)
  have hs := HexArith.Int.extGcd_zero_left_s_ofNat p (ZMod64.Bounds.pPos (p := p))
  rw [hs]
  simp

private theorem zmod64_inv_ne_zero_of_prime
    {p : Nat} [ZMod64.Bounds p] (hp : Nat.Prime p)
    {a : ZMod64 p} (ha : a ≠ 0) :
    a⁻¹ ≠ 0 := by
  intro hinv
  have hone := ZMod64.inv_mul_eq_one_of_prime hp ha
  change ZMod64.inv a = 0 at hinv
  rw [hinv] at hone
  have hzero : (0 : ZMod64 p) * a = 0 := by grind
  rw [hzero] at hone
  exact zmod64_one_ne_zero_of_prime hp hone.symm

private theorem zmod64_inv_inv_of_prime
    {p : Nat} [ZMod64.Bounds p] (hp : Nat.Prime p) (a : ZMod64 p) :
    (a⁻¹)⁻¹ = a := by
  by_cases ha : a = 0
  · subst a
    rw [zmod64_inv_zero (p := p)]
    exact (zmod64_inv_zero (p := p))
  · have hinv_ne := zmod64_inv_ne_zero_of_prime hp ha
    have hleft : (a⁻¹)⁻¹ * a⁻¹ = (1 : ZMod64 p) :=
      ZMod64.inv_mul_eq_one_of_prime hp hinv_ne
    have hright : a * a⁻¹ = (1 : ZMod64 p) := by
      rw [Lean.Grind.CommSemiring.mul_comm]
      exact ZMod64.inv_mul_eq_one_of_prime hp ha
    have hprod : (((a⁻¹)⁻¹ - a) * a⁻¹) = (0 : ZMod64 p) := by
      rw [Lean.Grind.Ring.sub_eq_add_neg]
      rw [Lean.Grind.Semiring.right_distrib]
      rw [hleft]
      grind
    rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hprod with hdiff | hzero
    · grind
    · exact False.elim (hinv_ne hzero)

private instance zmod64FieldOfPrime
    {p : Nat} [ZMod64.Bounds p] (hp : Nat.Prime p) :
    Lean.Grind.Field (ZMod64 p) := by
  refine Lean.Grind.Field.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b
    rfl
  · intro h
    exact zmod64_one_ne_zero_of_prime hp h.symm
  · exact zmod64_inv_zero
  · intro a ha
    rw [Lean.Grind.CommSemiring.mul_comm]
    exact ZMod64.inv_mul_eq_one_of_prime hp ha
  · intro a
    exact Lean.Grind.Semiring.pow_zero a
  · intro a n
    change a ^ (n + 1) = a ^ n * a
    exact Lean.Grind.Semiring.pow_succ a n
  · intro a n
    cases n with
    | ofNat m =>
        cases m with
        | zero =>
            show zmod64ZPow a (-Int.ofNat 0) = (zmod64ZPow a (Int.ofNat 0))⁻¹
            rw [show (-Int.ofNat 0) = Int.ofNat 0 by rfl]
            simp [zmod64ZPow]
            have hpow0 : a ^ 0 = (1 : ZMod64 p) :=
              Lean.Grind.Semiring.pow_zero a
            rw [hpow0]
            have hright : (1 : ZMod64 p)⁻¹ * 1 = (1 : ZMod64 p) := by
              exact ZMod64.inv_mul_eq_one_of_prime hp (zmod64_one_ne_zero_of_prime hp)
            have hmul : (1 : ZMod64 p)⁻¹ * 1 = (1 : ZMod64 p)⁻¹ := by
              exact Lean.Grind.Semiring.mul_one ((1 : ZMod64 p)⁻¹)
            rw [hmul] at hright
            exact hright.symm
        | succ m =>
            rfl
    | negSucc m =>
        change a ^ (m + 1) = ((a ^ (m + 1))⁻¹)⁻¹
        exact (zmod64_inv_inv_of_prime hp (a ^ (m + 1))).symm

private structure SmallPrimeCandidate where
  p : Nat
  [bounds : ZMod64.Bounds p]
  prime : Nat.Prime p
  field : Lean.Grind.Field (ZMod64 p)

/-- A scored admissible small-prime candidate for default prime selection. -/
structure PrimeCandidateScore where
  /-- Candidate prime. -/
  p : Nat
  /-- Smaller scores are preferred; equal scores retain the earlier smaller prime. -/
  factorCount : Nat

private def smallPrimeCandidates : List SmallPrimeCandidate :=
  [ { p := 3, bounds := bounds_three, prime := prime_three,
      field := @zmod64FieldOfPrime 3 bounds_three prime_three },
    { p := 5, bounds := bounds_five, prime := prime_five,
      field := @zmod64FieldOfPrime 5 bounds_five prime_five },
    { p := 7, bounds := bounds_seven, prime := prime_seven,
      field := @zmod64FieldOfPrime 7 bounds_seven prime_seven },
    { p := 11, bounds := bounds_eleven, prime := prime_eleven,
      field := @zmod64FieldOfPrime 11 bounds_eleven prime_eleven },
    { p := 13, bounds := bounds_thirteen, prime := prime_thirteen,
      field := @zmod64FieldOfPrime 13 bounds_thirteen prime_thirteen },
    { p := 17, bounds := bounds_seventeen, prime := prime_seventeen,
      field := @zmod64FieldOfPrime 17 bounds_seventeen prime_seventeen },
    { p := 19, bounds := bounds_nineteen, prime := prime_nineteen,
      field := @zmod64FieldOfPrime 19 bounds_nineteen prime_nineteen },
    { p := 23, bounds := bounds_twenty_three, prime := prime_twenty_three,
      field := @zmod64FieldOfPrime 23 bounds_twenty_three prime_twenty_three },
    { p := 31, bounds := bounds_thirty_one, prime := prime_thirty_one,
      field := @zmod64FieldOfPrime 31 bounds_thirty_one prime_thirty_one },
    { p := 71, bounds := bounds_seventy_one, prime := prime_seventy_one,
      field := @zmod64FieldOfPrime 71 bounds_seventy_one prime_seventy_one } ]

private def monicModularImage {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : FpPoly p :=
  if f.isZero then
    0
  else
    DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f

private theorem monicModularImage_monic
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
    zmod64_inv_ne_zero_of_prime hp hlead_ne
  unfold DensePoly.Monic
  rw [FpPoly.leadingCoeff_scale_of_ne_zero_of_nonzero (p := p) hinv_ne f hfsize]
  exact ZMod64.inv_mul_eq_one_of_prime hp hlead_ne

private def berlekampFactorsModP (f : ZPoly) (c : SmallPrimeCandidate) :
    Array (@FpPoly c.p c.bounds) :=
  letI := c.bounds
  letI := c.field
  let fModP := ZPoly.modP c.p f
  if hzero : fModP.isZero = false then
    (Berlekamp.berlekampFactor
      (monicModularImage fModP)
      (monicModularImage_monic c.prime fModP hzero)).factors.toArray
  else
    #[]

private def intCoeffModNat (z : Int) (p : Nat) : Nat :=
  Int.toNat (z % Int.ofNat p)

private def evalZPolyModNat (f : ZPoly) (p x : Nat) : Nat :=
  f.toArray.toList.reverse.foldl
    (fun acc coeff => (intCoeffModNat coeff p + x * acc) % p)
    0

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
  smallPrimeCandidates.foldl
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

private def scoreCandidate (f : ZPoly) (c : SmallPrimeCandidate) : Option PrimeCandidateScore :=
  letI := c.bounds
  if isGoodPrime f c.p then
    let factors := berlekampFactorsModP f c
    some { p := c.p, factorCount := factors.size }
  else
    none

private def betterScore (old new : PrimeCandidateScore) : PrimeCandidateScore :=
  if new.factorCount < old.factorCount then
    new
  else
    old

private def choosePrimeScoreStep
    (f : ZPoly) (best : Option PrimeCandidateScore) (c : SmallPrimeCandidate) :
    Option PrimeCandidateScore :=
  match best, scoreCandidate f c with
  | none, score => score
  | some old, none => some old
  | some old, some new => some (betterScore old new)

/-- Scan the fixed small-prime list and return the best admissible scored candidate, if any. -/
def choosePrimeScore? (f : ZPoly) : Option PrimeCandidateScore :=
  smallPrimeCandidates.foldl (choosePrimeScoreStep f) none

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
  exact choosePrimeScore?_fold_isGoodPrime f smallPrimeCandidates none score
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
  simpa [beq_iff_eq] using hgood.2

/--
Data produced by modular prime selection: the selected prime, the image of the
input polynomial over that prime field, and its modular factors.
-/
structure PrimeChoiceData where
  p : Nat
  [bounds : ZMod64.Bounds p]
  fModP : FpPoly p
  factorsModP : Array (FpPoly p)

/--
Data produced by Hensel lifting and consumed by integer recombination: the
prime, the requested lift precision, and the lifted integer factors.
-/
structure LiftData where
  p : Nat
  p_pos : 0 < p
  k : Nat
  liftedFactors : Array ZPoly

/--
Executable normalization data for the public integer factorization API.

The public input is first split into its integer content, primitive part,
initial `X` power, and primitive square-free core. The Berlekamp-Zassenhaus
prime/lift/factorization pipeline runs on `squareFreeCore`; the other fields are
reassembled around the resulting core factors.
-/
structure FactorNormalizationData where
  content : Int
  primitive : ZPoly
  xPower : Nat
  xFreePrimitive : ZPoly
  squareFreeCore : ZPoly
  repeatedPart : ZPoly

/--
Public integer-polynomial factorization result.

The scalar carries the input's signed content: for nonzero inputs this is
`sign(lc f) * ZPoly.content f`, while zero inputs use scalar `0`. Polynomial
factors are primitive, positive-leading-coefficient factors stored with
explicit multiplicities; factor order remains operational, with the
mathematical contract expressed through `Factorization.product`.
-/
structure Factorization where
  /-- Signed scalar absorbing both sign and integer content. -/
  scalar : Int
  /-- Polynomial factors paired with explicit positive multiplicities. -/
  factors : Array (ZPoly × Nat)
deriving DecidableEq

namespace Factorization

private def polyPow (f : ZPoly) : Nat → ZPoly
  | 0 => 1
  | n + 1 => polyPow f n * f

/-- Public wrapper for the polynomial power used by `Factorization.product`. -/
def factorPower (f : ZPoly) (n : Nat) : ZPoly :=
  polyPow f n

@[simp] theorem factorPower_zero (f : ZPoly) :
    factorPower f 0 = (1 : ZPoly) := rfl

@[simp] theorem factorPower_succ (f : ZPoly) (n : Nat) :
    factorPower f (n + 1) = factorPower f n * f := rfl

/-- Expand multiplicity pairs into the ordered polynomial product. -/
def product (φ : Factorization) : ZPoly :=
  φ.factors.foldl (fun acc factor => acc * polyPow factor.1 factor.2) (DensePoly.C φ.scalar)

@[simp] theorem product_mk_empty (scalar : Int) :
    product { scalar := scalar, factors := #[] } = DensePoly.C scalar := rfl

/--
Characterize `product` using the public `factorPower` wrapper instead of the
private recursion used internally.
-/
theorem product_eq_foldl_factorPower (φ : Factorization) :
    φ.product =
      φ.factors.foldl
        (fun acc factor => acc * factorPower factor.1 factor.2)
        (DensePoly.C φ.scalar) := by
  rfl

end Factorization

/-- Compute the normalization data required before the square-free pipeline. -/
def normalizeForFactor (f : ZPoly) : FactorNormalizationData :=
  let primitive := ZPoly.primitivePart f
  let xData := ZPoly.extractXPower primitive
  let sqData := ZPoly.primitiveSquareFreeDecomposition xData.core
  { content := ZPoly.content f
    primitive
    xPower := xData.power
    xFreePrimitive := xData.core
    squareFreeCore := sqData.squareFreeCore
    repeatedPart := sqData.repeatedPart }

private def contentFactorArray (content : Int) : Array ZPoly :=
  if content = 1 then
    #[]
  else
    #[DensePoly.C content]

private def xPowerFactorArray (power : Nat) : Array ZPoly :=
  (List.replicate power ZPoly.X).toArray

private def repeatedPartFactorArray (repeatedPart : ZPoly) : Array ZPoly :=
  if repeatedPart = 1 then
    #[]
  else
    #[repeatedPart]

private def signedContentScalar (f : ZPoly) : Int :=
  if f = 0 then
    0
  else if DensePoly.leadingCoeff f < 0 then
    -ZPoly.content f
  else
    ZPoly.content f

private def normalizeFactorSign (f : ZPoly) : ZPoly :=
  if DensePoly.leadingCoeff f < 0 then
    DensePoly.scale (-1 : Int) f
  else
    f

private def shouldRecordPolynomialFactor (f : ZPoly) : Bool :=
  f ≠ 0 && f ≠ 1 && f ≠ DensePoly.C (-1)

private def bumpFactorMultiplicity (f : ZPoly) : List (ZPoly × Nat) → List (ZPoly × Nat)
  | [] => [(f, 1)]
  | entry :: entries =>
      if entry.1 = f then
        (entry.1, entry.2 + 1) :: entries
      else
        entry :: bumpFactorMultiplicity f entries

private def collectFactorMultiplicities (factors : Array ZPoly) : Array (ZPoly × Nat) :=
  factors.toList.foldl
    (fun acc factor =>
      let factor := normalizeFactorSign factor
      if shouldRecordPolynomialFactor factor then
        bumpFactorMultiplicity factor acc
      else
        acc)
    []
  |>.reverse.toArray

private def polynomialNormalizationPrefixFactors (d : FactorNormalizationData) : Array ZPoly :=
  xPowerFactorArray d.xPower ++ repeatedPartFactorArray d.repeatedPart

/-- Factors that come from normalization before the square-free core is factored. -/
def normalizationPrefixFactors (d : FactorNormalizationData) : Array ZPoly :=
  contentFactorArray d.content ++
    xPowerFactorArray d.xPower ++
    repeatedPartFactorArray d.repeatedPart

/-- Reassemble normalization factors around the factors of the square-free core. -/
def reassembleNormalizedFactors
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) : Array ZPoly :=
  normalizationPrefixFactors d ++ coreFactors

private def reassemblePolynomialFactors
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) : Array ZPoly :=
  polynomialNormalizationPrefixFactors d ++ coreFactors

private def factorizationOfFactors (f : ZPoly) (factors : Array ZPoly) : Factorization :=
  { scalar := signedContentScalar f
    factors := collectFactorMultiplicities factors }

private def normalizedConstantFactors (d : FactorNormalizationData) : Array ZPoly :=
  let coreFactor :=
    if d.squareFreeCore = 1 then
      #[]
    else
      #[d.squareFreeCore]
  normalizationPrefixFactors d ++ coreFactor

/--
Per-prime modular irreducibility evidence for integer irreducibility
certificates.

The factor array records the modular factors observed at this prime. The degree
list and Rabin certificates are zipped with those concrete factors so the
checker can validate certificate metadata and the executable Rabin witness
against the polynomial it is meant to certify.
-/
structure PrimeFactorData where
  p : Nat
  [bounds : ZMod64.Bounds p]
  factorDegrees : Array Nat
  factorPolys : Array (FpPoly p)
  factorCerts : Array Berlekamp.IrreducibilityCertificate

/--
Evidence that a candidate integer factor degree is impossible for one recorded
prime block.

If an integer factor has degree `targetDegree`, then reducing modulo any good
prime gives a product of modular irreducible factors whose degrees sum to
`targetDegree`. The checker validates an obstruction by confirming that the
referenced prime block has no subset of recorded factor degrees with this sum.
-/
structure DegreeObstruction where
  targetDegree : Nat
  primeIndex : Nat

/--
Checker-first certificate data for irreducibility over `Z[x]`.

Each entry groups all modular degree and irreducibility-certificate data for a
single prime so the checker can validate the prime and degree metadata before
the later proof layer interprets the degree obstruction mathematically.
-/
structure ZPolyIrreducibilityCertificate where
  perPrime : Array PrimeFactorData
  degreeObstructions : Array DegreeObstruction

namespace PrimeFactorData

/-- Sum the recorded modular factor degrees for one prime. -/
def degreeSum (d : PrimeFactorData) : Nat :=
  d.factorDegrees.toList.foldl (fun acc n => acc + n) 0

/-- Ordered product of the recorded modular factors for one prime. -/
def factorProduct (d : PrimeFactorData) : @FpPoly d.p d.bounds :=
  letI := d.bounds
  d.factorPolys.foldl (· * ·) 1

/-- Does the recorded degree multiset contain `n`? -/
def containsDegree (d : PrimeFactorData) (n : Nat) : Bool :=
  d.factorDegrees.toList.any fun degree => degree == n

private def hasSubsetDegreeAux : List Nat → Nat → Bool
  | [], target => target == 0
  | degree :: degrees, target =>
      hasSubsetDegreeAux degrees target ||
        (degree ≤ target && hasSubsetDegreeAux degrees (target - degree))

/--
Does some subset of this prime block's modular factor degrees sum to `target`?
-/
def hasSubsetDegree (d : PrimeFactorData) (target : Nat) : Bool :=
  hasSubsetDegreeAux d.factorDegrees.toList target

/--
Check one nested finite-field irreducibility certificate against its degree slot
and the concrete modular factor occupying that slot.
-/
def checkCertAtFactor
    (d : PrimeFactorData) (degree : Nat) (factor : @FpPoly d.p d.bounds)
    (cert : Berlekamp.IrreducibilityCertificate) : Bool :=
  letI := d.bounds
  decide (cert.p = d.p) &&
    decide (cert.n = degree) &&
    d.containsDegree cert.n &&
    factor.degree? == some degree &&
    if hmonic : factor.leadingCoeff = 1 then
      Berlekamp.checkIrreducibilityCertificate factor (by exact hmonic) cert
    else
      false

/--
Check that nested certificates match the enclosing prime, degree array, and
concrete modular factor array.
-/
def checkFactorCerts (d : PrimeFactorData) : Bool :=
  d.factorDegrees.size == d.factorCerts.size &&
    d.factorDegrees.size == d.factorPolys.size &&
    (d.factorDegrees.toList.zip (d.factorPolys.toList.zip d.factorCerts.toList)).all fun pair =>
      checkCertAtFactor d pair.1 pair.2.1 pair.2.2

/-- Check one prime block against the integer polynomial being certified. -/
def checkForPolynomial (f : ZPoly) (d : PrimeFactorData) : Bool :=
  letI := d.bounds
  isGoodPrime f d.p &&
    d.factorDegrees.all (fun degree => 0 < degree) &&
    d.degreeSum == (ZPoly.modP d.p f).degree?.getD 0 &&
    d.factorProduct == ZPoly.modP d.p f &&
    d.checkFactorCerts

end PrimeFactorData

namespace ZPolyIrreducibilityCertificate

/-- Nontrivial integer factor degrees that must be ruled out for `f`. -/
def candidateFactorDegrees (f : ZPoly) : List Nat :=
  (List.range ((f.degree?.getD 0) / 2)).map fun i => i + 1

/-- Look up a per-prime block by the index stored in an obstruction. -/
def primeDataAt? (cert : ZPolyIrreducibilityCertificate) (idx : Nat) :
    Option PrimeFactorData :=
  match cert.perPrime.toList.drop idx with
  | [] => none
  | primeData :: _ => some primeData

end ZPolyIrreducibilityCertificate

namespace DegreeObstruction

/--
Check one degree obstruction against the certificate's per-prime degree data.

The target must be one of the nontrivial candidate degrees for `f`, and the
referenced prime block must have no subset of modular factor degrees summing to
that target.
-/
def checkForCertificate
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (obs : DegreeObstruction) : Bool :=
  decide (obs.targetDegree ∈ ZPolyIrreducibilityCertificate.candidateFactorDegrees f) &&
    match cert.primeDataAt? obs.primeIndex with
    | none => false
    | some primeData => !primeData.hasSubsetDegree obs.targetDegree

end DegreeObstruction

namespace ZPolyIrreducibilityCertificate

/-- Does the obstruction array contain a valid obstruction for `targetDegree`? -/
def hasObstructionFor (f : ZPoly)
    (cert : ZPolyIrreducibilityCertificate) (targetDegree : Nat) : Bool :=
  cert.degreeObstructions.toList.any fun obs =>
    obs.targetDegree == targetDegree && obs.checkForCertificate f cert

/-- Check that every candidate nontrivial factor degree is ruled out. -/
def checkDegreeObstructions (f : ZPoly)
    (cert : ZPolyIrreducibilityCertificate) : Bool :=
  (cert.degreeObstructions.all fun obs => obs.checkForCertificate f cert) &&
    (candidateFactorDegrees f).all fun targetDegree =>
      cert.hasObstructionFor f targetDegree

end ZPolyIrreducibilityCertificate

/--
Executable surface checker for integer-polynomial irreducibility certificates.

This validates all computational alignment data available at this layer: every
prime block must use an admissible prime for `f`, its recorded modular factors
must multiply back to the modular image, each nested finite-field certificate
must match the enclosing prime and its concrete factor, and every nontrivial
integer factor degree must be excluded by explicit per-prime degree data.
-/
def checkIrreducibleCert
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate) : Bool :=
  cert.perPrime.all (fun primeData => primeData.checkForPolynomial f) &&
    cert.checkDegreeObstructions f

private structure PrimeChoiceDataScore where
  data : PrimeChoiceData
  factorCount : Nat

private def primeChoiceDataScore (f : ZPoly) (c : SmallPrimeCandidate) :
    Option PrimeChoiceDataScore :=
  letI := c.bounds
  if isGoodPrime f c.p then
    let fModP := ZPoly.modP c.p f
    let factorsModP := berlekampFactorsModP f c
    some
      { data := { p := c.p, fModP, factorsModP }
        factorCount := factorsModP.size }
  else
    none

private def betterPrimeChoiceDataScore
    (old new : PrimeChoiceDataScore) : PrimeChoiceDataScore :=
  if new.factorCount < old.factorCount then
    new
  else
    old

private def choosePrimeData? (f : ZPoly) : Option PrimeChoiceData :=
  smallPrimeCandidates.foldl
    (fun best c =>
      match best, primeChoiceDataScore f c with
      | none, score => score
      | some old, none => some old
      | some old, some new => some (betterPrimeChoiceDataScore old new))
    none
  |>.map (fun score => score.data)

private def fallbackPrimeChoiceData (f : ZPoly) : PrimeChoiceData :=
  letI := bounds_three
  let c : SmallPrimeCandidate :=
    { p := 3, bounds := bounds_three, prime := prime_three,
      field := @zmod64FieldOfPrime 3 bounds_three prime_three }
  let fModP := ZPoly.modP 3 f
  let factorsModP := berlekampFactorsModP f c
  { p := 3, fModP, factorsModP }

/--
Choose an admissible small prime and package the modular image together with
its Berlekamp irreducible factor data for the rest of the pipeline.

The returned record stores the selected prime's `ZMod64.Bounds` instance, so
callers can consume `fModP` and `factorsModP` directly without re-running the
prime search or reconstructing typeclass evidence.
-/
def choosePrimeData (f : ZPoly) : PrimeChoiceData :=
  match choosePrimeData? f with
  | some data => data
  | none => fallbackPrimeChoiceData f

/--
Lift the chosen modular factors to the requested precision for integer
recombination.
-/
def henselLiftData (f : ZPoly) (B : Nat) (d : PrimeChoiceData) : LiftData :=
  letI := d.bounds
  let factors := d.factorsModP.map (fun factor => FpPoly.liftToZ factor)
  { p := d.p
    p_pos := ZMod64.Bounds.pPos (p := d.p)
    k := B
    liftedFactors := ZPoly.multifactorLiftQuadratic d.p B f factors }

@[simp] theorem henselLiftData_p (f : ZPoly) (B : Nat) (d : PrimeChoiceData) :
    (henselLiftData f B d).p = d.p := rfl

@[simp] theorem henselLiftData_k (f : ZPoly) (B : Nat) (d : PrimeChoiceData) :
    (henselLiftData f B d).k = B := rfl

/--
Integer upper bound for the BHKS fast-recombination precision schedule.

This is the conservative all-integer cap from the `hex-berlekamp-zassenhaus`
SPEC: `1 + n * 4^(n^2) * (sumSquared + 1)^n * log2(sumSquared + 1)^n`, where
`n` is the executable degree bound and `sumSquared` is the squared coefficient
norm.
-/
def bhksBound (f : ZPoly) : Nat :=
  let n := f.degree?.getD 0
  let sumSquared := ZPoly.coeffNormSq f
  1 + n * 4 ^ (n * n) * (sumSquared + 1) ^ n * (Nat.log2 (sumSquared + 1)) ^ n

/-- Integer coefficient bound `B_j` used by the BHKS all-coefficients CLD lattice. -/
def bhksCoeffBound (f : ZPoly) (j : Nat) : Nat :=
  let n := f.degree?.getD 0
  Nat.choose (n - 1) j * n * ZPoly.coeffL2NormBound f

private def ceilLogPAux (p target : Nat) : Nat → Nat → Nat → Nat
  | 0, ell, _ => ell
  | fuel + 1, ell, power =>
      if target ≤ power then
        ell
      else
        ceilLogPAux p target fuel (ell + 1) (power * p)

/--
Small executable `ceil_log_p` helper.

For `1 < p`, `ceilLogP p target` searches for the least visible exponent
whose `p`-power is at least `target`. The degenerate `p ≤ 1` case returns
zero because the BHKS fast path is only used with admissible primes.
-/
def ceilLogP (p target : Nat) : Nat :=
  if p ≤ 1 then
    0
  else
    ceilLogPAux p target (target + 1) 0 1

/-- Per-coordinate BHKS precision threshold `ell_j := ceil_log_p (2 * B_j + 1)`. -/
def bhksCoeffCutThreshold (p : Nat) (f : ZPoly) (j : Nat) : Nat :=
  ceilLogP p (2 * bhksCoeffBound f j + 1)

/--
Hensel precision exponent for a Mignotte coefficient bound.

For the Mignotte criterion `p^a > 2·B`, returns the smallest exponent
`a` with `p^a ≥ 2·B + 1` (equivalently `p^a > 2·B`). The two quantities
are different — `B` is a magnitude on integer coefficients, `a` is the
small exponent on the Hensel modulus `p^a` — and must not be conflated.
See SPEC/Libraries/hex-berlekamp-zassenhaus.md §"Slow path".
-/
def precisionForCoeffBound (B p : Nat) : Nat :=
  ceilLogP p (2 * B + 1)

private def subsetSplits : List ZPoly → List (List ZPoly × List ZPoly)
  | [] => [([], [])]
  | factor :: factors =>
      let rest := subsetSplits factors
      rest.map (fun split => (split.1, factor :: split.2)) ++
        rest.map (fun split => (factor :: split.1, split.2))

private def subsetSplitsWithFirst : List ZPoly → List (List ZPoly × List ZPoly)
  | [] => []
  | factor :: factors =>
      (subsetSplits factors).map fun split => (factor :: split.1, split.2)

private def firstSome {α β : Type} : List α → (α → Option β) → Option β
  | [], _ => none
  | x :: xs, f =>
      match f x with
      | some y => some y
      | none => firstSome xs f

def exactQuotient? (target candidate : ZPoly) : Option ZPoly :=
  if candidate.isZero || candidate = 1 then
    none
  else
    let qr := DensePoly.divMod target candidate
    if qr.2 = 0 && qr.1 * candidate == target then
      some qr.1
    else
      none

private theorem one_mul_zpoly (g : ZPoly) :
    (1 : ZPoly) * g = g := by
  rw [DensePoly.mul_comm_poly (S := Int), DensePoly.mul_one_right_poly]

private theorem list_foldl_mul_eq_mul_foldl_one (g : ZPoly) (xs : List ZPoly) :
    xs.foldl (fun acc factor => acc * factor) g =
      g * xs.foldl (fun acc factor => acc * factor) 1 := by
  induction xs generalizing g with
  | nil =>
      simpa using (DensePoly.mul_one_right_poly (S := Int) g).symm
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [one_mul_zpoly]
      calc
        xs.foldl (fun acc factor => acc * factor) (g * x) =
            (g * x) * xs.foldl (fun acc factor => acc * factor) 1 := ih (g * x)
        _ = g * (x * xs.foldl (fun acc factor => acc * factor) 1) := by
            rw [DensePoly.mul_assoc_poly (S := Int)]
        _ = g * xs.foldl (fun acc factor => acc * factor) x := by
            rw [ih x]

private theorem polyProduct_cons_toArray (g : ZPoly) (rest : List ZPoly) :
    Array.polyProduct (g :: rest).toArray = g * Array.polyProduct rest.toArray := by
  simpa [Array.polyProduct, one_mul_zpoly] using
    (list_foldl_mul_eq_mul_foldl_one g rest)

private theorem polyProduct_singleton (g : ZPoly) :
    Array.polyProduct #[g] = g := by
  simpa [Array.polyProduct] using one_mul_zpoly g

private theorem polyProduct_empty :
    Array.polyProduct (#[] : Array ZPoly) = 1 := by
  rfl

private theorem polyProduct_append (xs ys : Array ZPoly) :
    Array.polyProduct (xs ++ ys) = Array.polyProduct xs * Array.polyProduct ys := by
  rw [Array.polyProduct, Array.foldl_append]
  cases ys with
  | mk ylist =>
      simpa [Array.polyProduct] using list_foldl_mul_eq_mul_foldl_one
        (Array.foldl (fun acc factor => acc * factor) 1 xs) ylist

private theorem polyProduct_contentFactorArray (content : Int) :
    Array.polyProduct (contentFactorArray content) =
      if content = 1 then 1 else DensePoly.C content := by
  unfold contentFactorArray
  by_cases hcontent : content = 1
  · simp [hcontent, polyProduct_empty]
  · simp [hcontent, polyProduct_singleton]

private theorem polyProduct_repeatedPartFactorArray (repeatedPart : ZPoly) :
    Array.polyProduct (repeatedPartFactorArray repeatedPart) =
      if repeatedPart = 1 then 1 else repeatedPart := by
  unfold repeatedPartFactorArray
  by_cases hrepeated : repeatedPart = 1
  · simp [hrepeated, polyProduct_empty]
  · simp [hrepeated, polyProduct_singleton]

private theorem polyProduct_replicate_X_zero :
    Array.polyProduct ((List.replicate 0 ZPoly.X).toArray) = 1 := by
  rfl

private theorem polyProduct_replicate_X_succ (power : Nat) :
    Array.polyProduct ((List.replicate (power + 1) ZPoly.X).toArray) =
      ZPoly.X * Array.polyProduct ((List.replicate power ZPoly.X).toArray) := by
  simpa [List.replicate] using polyProduct_cons_toArray ZPoly.X (List.replicate power ZPoly.X)

private theorem polyProduct_xPowerFactorArray_zero :
    Array.polyProduct (xPowerFactorArray 0) = 1 := by
  simpa [xPowerFactorArray] using polyProduct_replicate_X_zero

private theorem polyProduct_xPowerFactorArray_succ (power : Nat) :
    Array.polyProduct (xPowerFactorArray (power + 1)) =
      ZPoly.X * Array.polyProduct (xPowerFactorArray power) := by
  simpa [xPowerFactorArray] using polyProduct_replicate_X_succ power

private theorem shift_zero (f : ZPoly) :
    DensePoly.shift 0 f = f := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_shift]
  simp

private theorem ofCoeffs_toArray (f : ZPoly) :
    DensePoly.ofCoeffs f.toArray = f := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_ofCoeffs]
  rfl

private theorem shift_shift_one (power : Nat) (f : ZPoly) :
    DensePoly.shift 1 (DensePoly.shift power f) = DensePoly.shift (power + 1) f := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_shift (power + 1) f n]
  rw [DensePoly.coeff_shift 1 (DensePoly.shift power f) n]
  cases n with
  | zero =>
      simp
  | succ n =>
      have hsub_one : n + 1 - 1 = n := by omega
      rw [hsub_one]
      rw [DensePoly.coeff_shift power f n]
      by_cases hn : n < power
      · have hsucc : n + 1 < power + 1 := by omega
        simp [hn, hsucc]
      · have hsucc : ¬ n + 1 < power + 1 := by omega
        simp [hn, hsucc, Nat.succ_sub_succ_eq_sub]

private theorem X_mul_shift (power : Nat) (f : ZPoly) :
    ZPoly.X * DensePoly.shift power f = DensePoly.shift (power + 1) f := by
  unfold ZPoly.X
  rw [DensePoly.monomial_one_mul_poly_eq_shift]
  exact shift_shift_one power f

private theorem polyProduct_xPowerFactorArray_mul (power : Nat) (f : ZPoly) :
    Array.polyProduct (xPowerFactorArray power) * f = DensePoly.shift power f := by
  induction power with
  | zero =>
      rw [polyProduct_xPowerFactorArray_zero]
      rw [one_mul_zpoly, shift_zero]
  | succ power ih =>
      rw [polyProduct_xPowerFactorArray_succ]
      rw [DensePoly.mul_assoc_poly (S := Int)]
      rw [ih]
      exact X_mul_shift power f

private theorem splitInitialZeros_reassembles (coeffs : List Int) :
    let split := ZPoly.splitInitialZeros coeffs
    DensePoly.shift split.1 (DensePoly.ofCoeffs split.2.toArray) =
      DensePoly.ofCoeffs coeffs.toArray := by
  induction coeffs with
  | nil =>
      rfl
  | cons coeff coeffs ih =>
      unfold ZPoly.splitInitialZeros
      by_cases hcoeff : coeff = 0
      · simp [hcoeff]
        cases split : ZPoly.splitInitialZeros coeffs with
        | mk power core =>
            have hcore :
                DensePoly.shift power (DensePoly.ofCoeffs core.toArray) =
                  DensePoly.ofCoeffs coeffs.toArray := by
              simpa [split] using ih
            simp
            apply DensePoly.ext_coeff
            intro n
            cases n with
            | zero =>
                rw [DensePoly.coeff_shift (power + 1) (DensePoly.ofCoeffs core.toArray) 0]
                rw [DensePoly.coeff_ofCoeffs_list (0 :: coeffs) 0]
                simp
                rfl
            | succ n =>
                have hcoeff_n := congrArg (fun p : ZPoly => p.coeff n) hcore
                change (DensePoly.shift power (DensePoly.ofCoeffs core.toArray)).coeff n =
                  (DensePoly.ofCoeffs coeffs.toArray).coeff n at hcoeff_n
                rw [DensePoly.coeff_shift power (DensePoly.ofCoeffs core.toArray) n] at hcoeff_n
                rw [DensePoly.coeff_ofCoeffs_list coeffs n] at hcoeff_n
                rw [DensePoly.coeff_shift (power + 1) (DensePoly.ofCoeffs core.toArray) (n + 1)]
                rw [DensePoly.coeff_ofCoeffs_list (0 :: coeffs) (n + 1)]
                by_cases hn : n < power
                · have hsucc : n + 1 < power + 1 := by omega
                  simpa [hsucc, hn] using hcoeff_n
                · have hsucc : ¬ n + 1 < power + 1 := by omega
                  have hvalue :
                      (DensePoly.ofCoeffs core.toArray).coeff (n - power) =
                        coeffs.getD n 0 := by
                    simpa [hn] using hcoeff_n
                  simpa [hsucc, Nat.succ_sub_succ_eq_sub] using hvalue
      · simp [hcoeff]
        exact shift_zero (DensePoly.ofCoeffs (coeff :: coeffs).toArray)

private theorem extractXPower_product (f : ZPoly) :
    let xData := ZPoly.extractXPower f
    Array.polyProduct (xPowerFactorArray xData.power ++ #[xData.core]) = f := by
  unfold ZPoly.extractXPower
  generalize hsplit : ZPoly.splitInitialZeros f.toArray.toList = split
  cases split with
  | mk power core =>
      simp only
      rw [polyProduct_append, polyProduct_singleton]
      rw [polyProduct_xPowerFactorArray_mul]
      have hreassemble := splitInitialZeros_reassembles f.toArray.toList
      rw [hsplit] at hreassemble
      rw [← ofCoeffs_toArray f]
      simpa [DensePoly.toArray] using hreassemble

private theorem polyProduct_polynomialNormalizationPrefixFactors
    (d : FactorNormalizationData) :
    Array.polyProduct (polynomialNormalizationPrefixFactors d) =
      Array.polyProduct (xPowerFactorArray d.xPower) *
        Array.polyProduct (repeatedPartFactorArray d.repeatedPart) := by
  unfold polynomialNormalizationPrefixFactors
  rw [polyProduct_append]

private theorem polyProduct_normalizationPrefixFactors (d : FactorNormalizationData) :
    Array.polyProduct (normalizationPrefixFactors d) =
      Array.polyProduct (contentFactorArray d.content) *
        (Array.polyProduct (xPowerFactorArray d.xPower) *
          Array.polyProduct (repeatedPartFactorArray d.repeatedPart)) := by
  unfold normalizationPrefixFactors
  rw [polyProduct_append, polyProduct_append]
  rw [DensePoly.mul_assoc_poly (S := Int)]

private theorem polyPow_zero (g : ZPoly) :
    Factorization.polyPow g 0 = (1 : ZPoly) := rfl

private theorem polyPow_succ (g : ZPoly) (n : Nat) :
    Factorization.polyPow g (n + 1) = Factorization.polyPow g n * g := rfl

private theorem polyPow_one (g : ZPoly) :
    Factorization.polyPow g 1 = g := by
  rw [polyPow_succ, polyPow_zero, one_mul_zpoly]

private def multListProduct (mults : List (ZPoly × Nat)) : ZPoly :=
  mults.foldl (fun acc m => acc * Factorization.polyPow m.1 m.2) 1

private theorem multListProduct_nil :
    multListProduct [] = 1 := rfl

private theorem multListFoldl_eq_mul_foldl_one (acc : ZPoly) (mults : List (ZPoly × Nat)) :
    mults.foldl (fun acc m => acc * Factorization.polyPow m.1 m.2) acc =
      acc * mults.foldl (fun acc m => acc * Factorization.polyPow m.1 m.2) 1 := by
  induction mults generalizing acc with
  | nil =>
      simpa using (DensePoly.mul_one_right_poly (S := Int) acc).symm
  | cons m ms ih =>
      simp only [List.foldl_cons]
      rw [one_mul_zpoly]
      calc
        ms.foldl (fun acc m => acc * Factorization.polyPow m.1 m.2)
            (acc * Factorization.polyPow m.1 m.2) =
              (acc * Factorization.polyPow m.1 m.2) *
                ms.foldl (fun acc m => acc * Factorization.polyPow m.1 m.2) 1 :=
            ih (acc * Factorization.polyPow m.1 m.2)
        _ = acc * (Factorization.polyPow m.1 m.2 *
              ms.foldl (fun acc m => acc * Factorization.polyPow m.1 m.2) 1) := by
              rw [DensePoly.mul_assoc_poly (S := Int)]
        _ = acc * ms.foldl (fun acc m => acc * Factorization.polyPow m.1 m.2)
              (Factorization.polyPow m.1 m.2) := by
              rw [ih (Factorization.polyPow m.1 m.2)]

private theorem multListProduct_cons (m : ZPoly × Nat) (ms : List (ZPoly × Nat)) :
    multListProduct (m :: ms) =
      Factorization.polyPow m.1 m.2 * multListProduct ms := by
  simp only [multListProduct, List.foldl_cons]
  rw [one_mul_zpoly]
  exact multListFoldl_eq_mul_foldl_one (Factorization.polyPow m.1 m.2) ms

private theorem multListProduct_singleton (m : ZPoly × Nat) :
    multListProduct [m] = Factorization.polyPow m.1 m.2 := by
  rw [multListProduct_cons, multListProduct_nil]
  rw [DensePoly.mul_one_right_poly]

private theorem multListProduct_append (xs ys : List (ZPoly × Nat)) :
    multListProduct (xs ++ ys) = multListProduct xs * multListProduct ys := by
  induction xs with
  | nil =>
      rw [List.nil_append, multListProduct_nil]
      rw [one_mul_zpoly]
  | cons m ms ih =>
      rw [List.cons_append]
      rw [multListProduct_cons, multListProduct_cons, ih]
      rw [DensePoly.mul_assoc_poly (S := Int)]

private theorem multListProduct_reverse (mults : List (ZPoly × Nat)) :
    multListProduct mults.reverse = multListProduct mults := by
  induction mults with
  | nil => rfl
  | cons m ms ih =>
      rw [List.reverse_cons]
      rw [multListProduct_append, multListProduct_singleton]
      rw [ih, multListProduct_cons]
      exact DensePoly.mul_comm_poly (S := Int) _ _

private theorem multListProduct_bumpFactorMultiplicity
    (g : ZPoly) (mults : List (ZPoly × Nat)) :
    multListProduct (bumpFactorMultiplicity g mults) = g * multListProduct mults := by
  induction mults with
  | nil =>
      rw [bumpFactorMultiplicity, multListProduct_singleton, multListProduct_nil]
      rw [polyPow_one]
      rw [DensePoly.mul_one_right_poly]
  | cons entry entries ih =>
      unfold bumpFactorMultiplicity
      by_cases heq : entry.1 = g
      · simp only [heq, if_true]
        rw [multListProduct_cons]
        show Factorization.polyPow g (entry.2 + 1) * multListProduct entries =
          g * multListProduct (entry :: entries)
        rw [polyPow_succ, multListProduct_cons, heq]
        rw [DensePoly.mul_comm_poly (S := Int)
              (Factorization.polyPow g entry.2) g]
        rw [DensePoly.mul_assoc_poly (S := Int)]
      · simp only [heq, if_false]
        rw [multListProduct_cons, multListProduct_cons, ih]
        rw [← DensePoly.mul_assoc_poly (S := Int)]
        rw [DensePoly.mul_comm_poly (S := Int)
              (Factorization.polyPow entry.1 entry.2) g]
        rw [DensePoly.mul_assoc_poly (S := Int)]

private def collectFactorStep
    (acc : List (ZPoly × Nat)) (f : ZPoly) : List (ZPoly × Nat) :=
  let f := normalizeFactorSign f
  if shouldRecordPolynomialFactor f then
    bumpFactorMultiplicity f acc
  else
    acc

private theorem collectFactorMultiplicities_eq_foldl (factors : Array ZPoly) :
    collectFactorMultiplicities factors =
      (factors.toList.foldl collectFactorStep []).reverse.toArray := rfl

private def filteredNormalizedFactors (factors : List ZPoly) : List ZPoly :=
  factors.filterMap fun f =>
    let f := normalizeFactorSign f
    if shouldRecordPolynomialFactor f then some f else none

private theorem filteredNormalizedFactors_nil :
    filteredNormalizedFactors [] = [] := rfl

private theorem filteredNormalizedFactors_cons_keep
    {f : ZPoly} (fs : List ZPoly)
    (hkeep : shouldRecordPolynomialFactor (normalizeFactorSign f) = true) :
    filteredNormalizedFactors (f :: fs) =
      normalizeFactorSign f :: filteredNormalizedFactors fs := by
  unfold filteredNormalizedFactors
  simp [hkeep]

private theorem filteredNormalizedFactors_cons_drop
    {f : ZPoly} (fs : List ZPoly)
    (hdrop : shouldRecordPolynomialFactor (normalizeFactorSign f) = false) :
    filteredNormalizedFactors (f :: fs) = filteredNormalizedFactors fs := by
  unfold filteredNormalizedFactors
  simp [hdrop]

private theorem multListProduct_collectAux
    (acc : List (ZPoly × Nat)) (factors : List ZPoly) :
    multListProduct (factors.foldl collectFactorStep acc) =
      multListProduct acc *
        Array.polyProduct (filteredNormalizedFactors factors).toArray := by
  induction factors generalizing acc with
  | nil =>
      rw [filteredNormalizedFactors_nil, List.foldl_nil]
      show multListProduct acc = _
      simp [Array.polyProduct]
      rw [DensePoly.mul_one_right_poly]
  | cons f fs ih =>
      rw [List.foldl_cons]
      by_cases hrec :
          shouldRecordPolynomialFactor (normalizeFactorSign f) = true
      · rw [filteredNormalizedFactors_cons_keep fs hrec]
        rw [show collectFactorStep acc f =
              bumpFactorMultiplicity (normalizeFactorSign f) acc from by
              unfold collectFactorStep
              simp [hrec]]
        rw [ih (bumpFactorMultiplicity (normalizeFactorSign f) acc)]
        rw [multListProduct_bumpFactorMultiplicity]
        rw [polyProduct_cons_toArray]
        rw [DensePoly.mul_comm_poly (S := Int) (normalizeFactorSign f)
              (multListProduct acc)]
        rw [DensePoly.mul_assoc_poly (S := Int)]
      · have hdrop : shouldRecordPolynomialFactor (normalizeFactorSign f) = false := by
          cases hcase :
              shouldRecordPolynomialFactor (normalizeFactorSign f) with
          | true => exact (hrec hcase).elim
          | false => rfl
        rw [filteredNormalizedFactors_cons_drop fs hdrop]
        rw [show collectFactorStep acc f = acc from by
              unfold collectFactorStep
              simp [hdrop]]
        exact ih acc

private theorem multListProduct_collectFactorMultiplicities
    (factors : Array ZPoly) :
    multListProduct (collectFactorMultiplicities factors).toList =
      Array.polyProduct (filteredNormalizedFactors factors.toList).toArray := by
  rw [collectFactorMultiplicities_eq_foldl]
  show multListProduct (factors.toList.foldl collectFactorStep []).reverse = _
  rw [multListProduct_reverse]
  have hcol := multListProduct_collectAux [] factors.toList
  rw [multListProduct_nil, one_mul_zpoly] at hcol
  exact hcol

private theorem factorizationOfFactors_product
    (f : ZPoly) (factors : Array ZPoly) :
    Factorization.product (factorizationOfFactors f factors) =
      DensePoly.C (signedContentScalar f) *
        Array.polyProduct (filteredNormalizedFactors factors.toList).toArray := by
  show
    (collectFactorMultiplicities factors).foldl
        (fun acc m => acc * Factorization.polyPow m.1 m.2)
        (DensePoly.C (signedContentScalar f)) =
      _
  rw [← Array.foldl_toList]
  rw [multListFoldl_eq_mul_foldl_one]
  show
    DensePoly.C (signedContentScalar f) *
        multListProduct (collectFactorMultiplicities factors).toList =
      _
  rw [multListProduct_collectFactorMultiplicities]

private theorem rat_scale_scale (u v : Rat) (p : DensePoly Rat) :
    DensePoly.scale u (DensePoly.scale v p) = DensePoly.scale (u * v) p := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Rat) u (DensePoly.scale v p) n (Rat.mul_zero u)]
  rw [DensePoly.coeff_scale (R := Rat) v p n (Rat.mul_zero v)]
  rw [DensePoly.coeff_scale (R := Rat) (u * v) p n (Rat.mul_zero (u * v))]
  rw [Rat.mul_assoc]

private theorem toRatPoly_mul_product (f g : ZPoly) :
    ZPoly.toRatPoly (f * g) = ZPoly.toRatPoly f * ZPoly.toRatPoly g := by
  exact ZPoly.toRatPoly_mul f g

private theorem primitiveSquareFreeDecomposition_reassembles_xfree_over_rat
    (xFree : ZPoly) :
    let sqData := ZPoly.primitiveSquareFreeDecomposition xFree
    ∃ unit : Rat,
      ZPoly.toRatPoly xFree =
        DensePoly.scale unit (ZPoly.toRatPoly (sqData.squareFreeCore * sqData.repeatedPart)) := by
  simp only
  rcases ZPoly.primitiveSquareFreeDecomposition_reassembly_over_rat xFree with
    ⟨unit, hunit⟩
  refine ⟨(ZPoly.content xFree : Rat) * unit, ?_⟩
  have hprimitive :
      (ZPoly.primitiveSquareFreeDecomposition xFree).primitive =
        ZPoly.primitivePart xFree :=
    ZPoly.primitiveSquareFreeDecomposition_primitive xFree
  rw [hprimitive] at hunit
  have hcontent :
      ZPoly.toRatPoly xFree =
        DensePoly.scale (ZPoly.content xFree : Rat)
          (ZPoly.toRatPoly (ZPoly.primitivePart xFree)) := by
    rw [← ZPoly.toRatPoly_scale_int]
    rw [ZPoly.content_mul_primitivePart]
  rw [hcontent, hunit, rat_scale_scale]
  rw [toRatPoly_mul_product]

private theorem exactQuotient?_product
    {target candidate quotient : ZPoly}
    (hquot : exactQuotient? target candidate = some quotient) :
    quotient * candidate = target := by
  unfold exactQuotient? at hquot
  split at hquot
  · contradiction
  · rename_i hnontrivial
    generalize hqr : DensePoly.divMod target candidate = qr at hquot
    cases qr with
    | mk q r =>
        simp only at hquot
        split at hquot
        · rename_i hcheck
          cases hquot
          exact (by
            simpa [Bool.and_eq_true, beq_iff_eq] using hcheck : r = 0 ∧ quotient * candidate = target).2
        · contradiction

/-- Converse to `exactQuotient?_product`: if `candidate` is monic with positive
degree and `quotient * candidate = target`, then `exactQuotient? target candidate`
returns `some quotient`. -/
theorem exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree
    {target candidate quotient : ZPoly}
    (hmonic : DensePoly.Monic candidate)
    (hdegree : 0 < candidate.degree?.getD 0)
    (hmul : quotient * candidate = target) :
    exactQuotient? target candidate = some quotient := by
  have hcandidate_ne : candidate ≠ 0 := by
    intro hzero
    have hdeg : candidate.degree?.getD 0 = 0 := by
      rw [hzero]
      simp [DensePoly.degree?]
    omega
  have hcandidate_ne_one : candidate ≠ 1 := by
    intro hone
    have hdeg : candidate.degree?.getD 0 = 0 := by
      rw [hone]
      change (DensePoly.C (1 : Int)).degree?.getD 0 = 0
      exact DensePoly.degree?_C_getD 1
    omega
  have hsize_pos : 0 < candidate.size := by
    rcases Nat.lt_or_ge 0 candidate.size with h | h
    · exact h
    · exfalso
      apply hcandidate_ne
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le candidate (by omega)
  have hisZero_false : candidate.isZero = false := by
    unfold DensePoly.isZero
    have hne : candidate.coeffs ≠ #[] := by
      intro hempty
      have : candidate.size = 0 := by
        change candidate.coeffs.size = 0
        rw [hempty]
        rfl
      omega
    simpa using hne
  have hdivMod_eq : DensePoly.divMod target candidate = (quotient, 0) :=
    ZPoly.divMod_eq_of_monic_mul_eq target candidate quotient hmonic hdegree hmul
  unfold exactQuotient?
  rw [hisZero_false]
  simp only [Bool.false_or, decide_eq_true_eq]
  rw [if_neg hcandidate_ne_one]
  rw [hdivMod_eq]
  simp [hmul]

private def positiveDivisors (n : Nat) : List Nat :=
  (List.range (n + 1)).filter fun d => d != 0 && n % d == 0

private def integerRootCandidates (f : ZPoly) : List Int :=
  (positiveDivisors (f.coeff 0).natAbs).flatMap fun d =>
    let r : Int := Int.ofNat d
    [r, -r]

private def linearFactorForRoot (r : Int) : ZPoly :=
  DensePoly.ofCoeffs #[-r, 1]

private def splitIntegerRootFactorsAux :
    ZPoly → List Int → Nat → Array ZPoly × ZPoly
  | target, _roots, 0 => (#[], target)
  | target, [], _fuel + 1 => (#[], target)
  | target, root :: roots, fuel + 1 =>
      let factor := linearFactorForRoot root
      match exactQuotient? target factor with
      | some quotient =>
          let rest := splitIntegerRootFactorsAux quotient roots fuel
          (#[factor] ++ rest.1, rest.2)
      | none => splitIntegerRootFactorsAux target roots fuel

private def quadraticIntegerRootFactors? (core : ZPoly) : Option (Array ZPoly) :=
  if core.degree?.getD 0 = 2 then
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    if split.1.size = 0 then
      none
    else if split.2 = 1 then
      some split.1
    else if split.2.degree?.getD 0 ≤ 1 then
      some (split.1.push split.2)
    else
      none
  else
    none

def centeredModNat (z : Int) (m : Nat) : Int :=
  if m = 0 then
    z
  else
    let r := z % Int.ofNat m
    if 2 * r.natAbs ≤ m then
      r
    else if r < 0 then
      r + Int.ofNat m
    else
      r - Int.ofNat m

theorem centeredModNat_zero (m : Nat) :
    centeredModNat 0 m = 0 := by
  unfold centeredModNat
  by_cases hm : m = 0 <;> simp [hm]

theorem centeredModNat_emod_eq_of_natAbs_le
    (z : Int) (m B : Nat)
    (hbound : z.natAbs ≤ B) (hsep : 2 * B < m) :
    centeredModNat (z % (m : Int)) m = z := by
  have hmpos : 0 < m := by omega
  have hmne : m ≠ 0 := Nat.ne_of_gt hmpos
  rcases Int.natAbs_eq z with hz | hz
  · rw [hz]
    have hltNat : z.natAbs < m := by omega
    have hlt : (z.natAbs : Int) < (m : Int) := by exact_mod_cast hltNat
    have hnonneg : 0 ≤ (z.natAbs : Int) := by exact_mod_cast Nat.zero_le z.natAbs
    have hmod : ((z.natAbs : Int) % (m : Int)) = (z.natAbs : Int) :=
      Int.emod_eq_of_lt hnonneg hlt
    unfold centeredModNat
    simp [hmne, hmod]
    intro hbad
    omega
  · rw [hz]
    by_cases hzero : z.natAbs = 0
    · simp [hzero, centeredModNat, hmne]
    · have ha_lt : z.natAbs < m := by omega
      have hrem : (-(z.natAbs : Int)) % (m : Int) = (m : Int) - (z.natAbs : Int) := by
        have hnonneg : 0 ≤ (m : Int) - (z.natAbs : Int) := by omega
        have hlt : (m : Int) - (z.natAbs : Int) < (m : Int) := by omega
        have hcongr :
            (((m : Int) - (z.natAbs : Int)) - (-(z.natAbs : Int))) % (m : Int) = 0 := by
          have hsimp :
              ((m : Int) - (z.natAbs : Int)) - (-(z.natAbs : Int)) = (m : Int) := by
            omega
          rw [hsimp]
          exact Int.emod_eq_zero_of_dvd ⟨1, by omega⟩
        have hmod_eq := (Int.emod_eq_emod_iff_emod_sub_eq_zero).2 hcongr
        rw [Int.emod_eq_of_lt hnonneg hlt] at hmod_eq
        exact hmod_eq.symm
      have hinner :
          (((m : Int) - (z.natAbs : Int)) % (m : Int)) =
            (m : Int) - (z.natAbs : Int) := by
        apply Int.emod_eq_of_lt <;> omega
      unfold centeredModNat
      simp [hmne, hrem, hinner]
      have hsub_cast : (m : Int) - (z.natAbs : Int) = (m - z.natAbs : Nat) := by
        omega
      have hnatAbs : (((m : Int) - (z.natAbs : Int)).natAbs) = m - z.natAbs := by
        rw [hsub_cast, Int.natAbs_natCast]
      rw [hnatAbs]
      have hnot : ¬ 2 * (m - z.natAbs) ≤ m := by omega
      simp [hnot]
      have hnotneg : ¬ (m : Int) - (z.natAbs : Int) < 0 := by omega
      simp [hnotneg]
      omega

/-- Centred residue modulo `p^b`, the `mod^±` operation in the BHKS cut. -/
def centeredResiduePow (p b : Nat) (x : Int) : Int :=
  centeredModNat x (p ^ b)

/--
BHKS two-sided cut `Psi^a_b(x) = (x - (x mod^± p^b)) / p^b`.

The precision parameter `a` records the ambient modulus `p^a`; the executable
cut only needs the lower threshold `b`.
-/
def psiCut (p _a b : Nat) (x : Int) : Int :=
  let modulus := p ^ b
  if modulus = 0 then
    0
  else
    (x - centeredResiduePow p b x) / Int.ofNat modulus

private def cldQuotientMod (f g : ZPoly) (p a : Nat) : ZPoly :=
  let numerator := ZPoly.reduceModPow (f * DensePoly.derivative g) p a
  let quotient := (DensePoly.divMod numerator g).1
  ZPoly.reduceModPow quotient p a

/--
Centred high-bit CLD coefficients for one lifted local factor.

The returned array has one entry for each coefficient index
`0, ..., deg(f)-1`; entry `j` is
`Psi^a_{ell_j}([x^j] (f * g.derivative / g mod p^a))`.
-/
def cldCoeffs (f : ZPoly) (p a : Nat) (g : ZPoly) : Array Int :=
  let quotient := cldQuotientMod f g p a
  let n := f.degree?.getD 0
  (List.range n).map
    (fun j => psiCut p a (bhksCoeffCutThreshold p f j) (quotient.coeff j))
    |>.toArray

/-- Per-coordinate BHKS cut thresholds for the all-coefficients CLD lattice. -/
def bhksCutThresholds (f : ZPoly) (p : Nat) : Array Nat :=
  let n := f.degree?.getD 0
  (List.range n).map (fun j => bhksCoeffCutThreshold p f j) |>.toArray

/--
Executable row-basis data for the BHKS all-coefficients CLD lattice.

The basis has row and column dimension `factorCount + coeffWidth`. Its first
`factorCount` columns are indicator coordinates, and its remaining
`coeffWidth` columns are CLD high-bit coordinates.
-/
structure BhksLatticeBasis where
  p : Nat
  precision : Nat
  factorCount : Nat
  coeffWidth : Nat
  liftedFactors : Array ZPoly
  cutThresholds : Array Nat
  cldRows : Array (Array Int)
  basis : Matrix Int (factorCount + coeffWidth) (factorCount + coeffWidth)

/--
Projected BHKS rows after LLL reduction and the Gram-Schmidt cut.

`cutRadiusSq4` stores `4 * B'^2 = 4r + n*r^2`, avoiding square-root or
floating-point arithmetic for the BHKS cut radius.
-/
structure BhksProjectedRows where
  factorCount : Nat
  coeffWidth : Nat
  cutRadiusSq4 : Nat
  reducedRowCount : Nat
  projectedRows : Array (Array Int)

private def bhksLatticeEntry
    (r n p a : Nat) (thresholds : Array Nat) (cldRows : Array (Array Int))
    (i j : Fin (r + n)) : Int :=
  if _hi : i.val < r then
    if _hj : j.val < r then
      if i.val = j.val then 1 else 0
    else
      (cldRows.getD i.val #[]).getD (j.val - r) 0
  else if _hj : j.val < r then
    0
  else
    let coord := i.val - r
    if j.val - r = coord then
      Int.ofNat (p ^ (a - thresholds.getD coord 0))
    else
      0

/--
Build the BHKS all-coefficients CLD row-basis matrix
`[ I_r | A_tilde ; 0 | diag(p^(a-l_j)) ]`.

The diagonal exponent uses natural subtraction; callers that need the exact
BHKS hypotheses should lift to a precision `a` satisfying every `l_j ≤ a`.
-/
def bhksLatticeBasis (f : ZPoly) (p a : Nat) (liftedFactors : Array ZPoly) :
    BhksLatticeBasis :=
  let r := liftedFactors.size
  let n := f.degree?.getD 0
  let thresholds := bhksCutThresholds f p
  let cldRows := liftedFactors.map (fun g => cldCoeffs f p a g)
  let basis : Matrix Int (r + n) (r + n) :=
    Matrix.ofFn (bhksLatticeEntry r n p a thresholds cldRows)
  { p
    precision := a
    factorCount := r
    coeffWidth := n
    liftedFactors
    cutThresholds := thresholds
    cldRows
    basis }

private theorem bhksLatticeBasis_factorCount_eq
    (f : ZPoly) (p a : Nat) (liftedFactors : Array ZPoly) :
    (bhksLatticeBasis f p a liftedFactors).factorCount = liftedFactors.size := by
  rfl

private theorem bhksLatticeBasis_coeffWidth_eq
    (f : ZPoly) (p a : Nat) (liftedFactors : Array ZPoly) :
    (bhksLatticeBasis f p a liftedFactors).coeffWidth = f.degree?.getD 0 := by
  rfl

private theorem bhksLatticeEntry_topLeft
    (r n p a : Nat) (thresholds : Array Nat) (cldRows : Array (Array Int))
    (i j : Fin (r + n)) (hi : i.val < r) (hj : j.val < r) :
    bhksLatticeEntry r n p a thresholds cldRows i j =
      if i.val = j.val then 1 else 0 := by
  simp [bhksLatticeEntry, hi, hj]

private theorem bhksLatticeEntry_bottomLeft
    (r n p a : Nat) (thresholds : Array Nat) (cldRows : Array (Array Int))
    (i j : Fin (r + n)) (hi : r ≤ i.val) (hj : j.val < r) :
    bhksLatticeEntry r n p a thresholds cldRows i j = 0 := by
  have hnot : ¬i.val < r := by
    omega
  simp [bhksLatticeEntry, hnot, hj]

private theorem bhksLatticeEntry_bottomRight
    (r n p a : Nat) (thresholds : Array Nat) (cldRows : Array (Array Int))
    (i j : Fin (r + n)) (hi : r ≤ i.val) (hj : r ≤ j.val) :
    bhksLatticeEntry r n p a thresholds cldRows i j =
      let coord := i.val - r
      if j.val - r = coord then
        Int.ofNat (p ^ (a - thresholds.getD coord 0))
      else
        0 := by
  have hnot_i : ¬i.val < r := by
    omega
  have hnot_j : ¬j.val < r := by
    omega
  simp [bhksLatticeEntry, hnot_i, hnot_j]

private theorem bhksLatticeEntry_bottomRight_offDiag
    (r n p a : Nat) (thresholds : Array Nat) (cldRows : Array (Array Int))
    (i j : Fin (r + n)) (hi : r ≤ i.val) (hj : r ≤ j.val)
    (hneq : j.val - r ≠ i.val - r) :
    bhksLatticeEntry r n p a thresholds cldRows i j = 0 := by
  rw [bhksLatticeEntry_bottomRight r n p a thresholds cldRows i j hi hj]
  simp [hneq]

private theorem bhksLatticeEntry_bottomRight_diag
    (r n p a : Nat) (thresholds : Array Nat) (cldRows : Array (Array Int))
    (i : Fin (r + n)) (hi : r ≤ i.val) :
    bhksLatticeEntry r n p a thresholds cldRows i i =
      Int.ofNat (p ^ (a - thresholds.getD (i.val - r) 0)) := by
  rw [bhksLatticeEntry_bottomRight r n p a thresholds cldRows i i hi hi]
  simp

private theorem bhksLatticeEntry_bottomRight_diag_pos
    (r n p a : Nat) (thresholds : Array Nat) (cldRows : Array (Array Int))
    (hp : 0 < p) (i : Fin (r + n)) (hi : r ≤ i.val)
    (_hthreshold : thresholds.getD (i.val - r) 0 ≤ a) :
    0 < bhksLatticeEntry r n p a thresholds cldRows i i := by
  rw [bhksLatticeEntry_bottomRight_diag r n p a thresholds cldRows i hi]
  have hpos : 0 < p ^ (a - thresholds.getD (i.val - r) 0) :=
    Nat.pow_pos hp
  exact Int.ofNat_lt.mpr hpos

/-- Four times the squared BHKS cut radius, `4 * (r + n * (r / 2)^2)`. -/
def bhksCutRadiusSq4 (L : BhksLatticeBasis) : Nat :=
  4 * L.factorCount + L.coeffWidth * L.factorCount * L.factorCount

private def bhksWithinGramSchmidtCut (L : BhksLatticeBasis)
    (dets : Vector Nat (L.factorCount + L.coeffWidth + 1))
    (i : Fin (L.factorCount + L.coeffWidth)) : Bool :=
  let d0 := dets.get ⟨i.val,
    Nat.lt_trans i.isLt (Nat.lt_succ_self (L.factorCount + L.coeffWidth))⟩
  let d1 := dets.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  if d0 = 0 then
    false
  else
    4 * ((d1 : Rat) / (d0 : Rat)) ≤ (bhksCutRadiusSq4 L : Rat)

private def bhksProjectIndicator (r n : Nat) (v : Vector Int (r + n)) : Array Int :=
  (List.range r).map
    (fun j =>
      if h : j < r + n then
        v.get ⟨j, h⟩
      else
        0)
    |>.toArray

private def bhksRowsArrayToMatrix {m : Nat} (n : Nat) (rows : Array (Vector Int m)) :
    Matrix Int n m :=
  Matrix.ofFn fun i j => (rows.getD i.val (Vector.ofFn fun _ => 0))[j]

private theorem lll_delta_lower : (1 / 4 : Rat) < 3 / 4 := by
  grind

private theorem lll_delta_upper : (3 / 4 : Rat) ≤ 1 := by
  grind

private def bhksCutProjectReducedRows
    (L : BhksLatticeBasis)
    (reduced : Matrix Int (L.factorCount + L.coeffWidth)
        (L.factorCount + L.coeffWidth)) :
    Array (Array Int) :=
  let dets := GramSchmidt.Int.gramDetVec reduced
  (List.finRange (L.factorCount + L.coeffWidth)).foldl
    (fun acc i =>
      if bhksWithinGramSchmidtCut L dets i then
        acc.push (bhksProjectIndicator L.factorCount L.coeffWidth (reduced.row i))
      else
        acc)
    #[]

/--
Run LLL on a BHKS row-basis lattice, discard rows whose Gram-Schmidt squared
length exceeds the BHKS radius, and project survivors to the first `r`
indicator coordinates. The squared Gram-Schmidt lengths are computed from the
integer leading Gram determinant vector as `d_{i+1}/d_i`.

The result is the executable `L'` row data consumed by the later RREF /
equivalence-class recovery stage.
-/
def bhksProjectedRows (L : BhksLatticeBasis)
    (hrows : 1 ≤ L.factorCount + L.coeffWidth)
    (hind : L.basis.independent) : BhksProjectedRows :=
  let reducedRows :=
    lll.shortVectors L.basis (3 / 4) lll_delta_lower lll_delta_upper hrows hind
  let reducedBasis :=
    bhksRowsArrayToMatrix (L.factorCount + L.coeffWidth) reducedRows
  { factorCount := L.factorCount
    coeffWidth := L.coeffWidth
    cutRadiusSq4 := bhksCutRadiusSq4 L
    reducedRowCount := reducedRows.size
    projectedRows := bhksCutProjectReducedRows L reducedBasis }

/-- Constructor-produced BHKS `[ I_r | A_tilde ; 0 | diag(p^(a-l_j)) ]`
lattice bases are linearly independent over `Int` for positive `p`. -/
theorem bhksLatticeBasis_independent
    (f : ZPoly) (p a : Nat) (liftedFactors : Array ZPoly) (hp : 0 < p) :
    (bhksLatticeBasis f p a liftedFactors).basis.independent := by
  change
    (Matrix.ofFn
      (bhksLatticeEntry liftedFactors.size (f.degree?.getD 0) p a
        (bhksCutThresholds f p)
        (liftedFactors.map (fun g => cldCoeffs f p a g)))).independent
  apply Matrix.independent_of_upperTriangular_pos_diag
  · intro i j hji
    by_cases hi : i.val < liftedFactors.size
    · have hj : j.val < liftedFactors.size := by omega
      simp [Matrix.ofFn, bhksLatticeEntry, hi, hj]
      omega
    · have hi' : liftedFactors.size ≤ i.val := by omega
      by_cases hj : j.val < liftedFactors.size
      · simp [Matrix.ofFn, bhksLatticeEntry, hi, hj]
      · have hj' : liftedFactors.size ≤ j.val := by omega
        have hneq : j.val - liftedFactors.size ≠ i.val - liftedFactors.size := by omega
        simp [Matrix.ofFn, bhksLatticeEntry, hi, hj, hneq]
  · intro i
    by_cases hi : i.val < liftedFactors.size
    · simp [Matrix.ofFn, bhksLatticeEntry, hi]
    · have hi' : liftedFactors.size ≤ i.val := by omega
      have hpos : 0 < p ^ (a - (bhksCutThresholds f p).getD (i.val - liftedFactors.size) 0) :=
        Nat.pow_pos hp
      simpa [Matrix.ofFn, bhksLatticeEntry, hi] using Int.ofNat_lt.mpr hpos

private theorem bhksLiftData_latticeBasis_independent (f : ZPoly) (d : LiftData) :
    (bhksLatticeBasis f d.p d.k d.liftedFactors).basis.independent :=
  bhksLatticeBasis_independent f d.p d.k d.liftedFactors d.p_pos

#guard psiCut 5 4 1 3 = 1
#guard psiCut 5 4 1 3 ≠ 3 / (5 : Int)
#guard centeredResiduePow 5 1 (-3) = 2
#guard psiCut 5 4 1 (-3) = -1
#guard centeredResiduePow 5 1 (-2) = -2
#guard psiCut 5 4 1 (-2) = 0
#guard psiCut 5 4 1 (-2) ≠ (-2) / (5 : Int)

private def cldGuardF : ZPoly :=
  DensePoly.ofCoeffs #[6, -5, 1]

private def cldGuardG : ZPoly :=
  DensePoly.ofCoeffs #[-2, 1]

#guard cldQuotientMod cldGuardF cldGuardG 5 2 = DensePoly.ofCoeffs #[22, 1]
#guard (cldCoeffs cldGuardF 5 2 cldGuardG).size = cldGuardF.degree?.getD 0

private def bhksGuardFactors : Array ZPoly :=
  #[DensePoly.ofCoeffs #[-2, 1], DensePoly.ofCoeffs #[-3, 1]]

private def bhksGuardBasis : BhksLatticeBasis :=
  bhksLatticeBasis cldGuardF 5 2 bhksGuardFactors

#guard bhksGuardBasis.factorCount = 2
#guard bhksGuardBasis.coeffWidth = 2
#guard bhksGuardBasis.basis[0][0] = 1
#guard bhksGuardBasis.basis[0][1] = 0
#guard bhksGuardBasis.basis[0][2] = (bhksGuardBasis.cldRows.getD 0 #[]).getD 0 0
#guard bhksGuardBasis.basis[0][3] = (bhksGuardBasis.cldRows.getD 0 #[]).getD 1 0
#guard bhksGuardBasis.basis[0][2] ≠ bhksGuardFactors[0].coeff 0
#guard bhksGuardBasis.basis[1][0] = 0
#guard bhksGuardBasis.basis[1][1] = 1
#guard bhksGuardBasis.basis[2][0] = 0
#guard bhksGuardBasis.basis[2][2] =
  Int.ofNat (5 ^ (2 - bhksGuardBasis.cutThresholds.getD 0 0))
#guard bhksGuardBasis.basis[3][3] =
  Int.ofNat (5 ^ (2 - bhksGuardBasis.cutThresholds.getD 1 0))
#guard bhksCutRadiusSq4 bhksGuardBasis = 16
#guard bhksProjectIndicator 2 2 bhksGuardBasis.basis[0] = #[1, 0]
#guard (bhksProjectIndicator 2 2 bhksGuardBasis.basis[0]).size = bhksGuardBasis.factorCount

/--
Lift the projected integer rows of `L` into a rational row-basis matrix
sized `n × r`, with `n := L.projectedRows.size` and `r := L.factorCount`.
The matrix is the input to BHKS Lemma 3.3 RREF-based equivalence-class
identification.
-/
def bhksProjectedRowsAsRatMatrix
    (rows : Array (Array Int)) (n r : Nat) : Matrix Rat n r :=
  Matrix.ofFn fun i j =>
    ((rows.getD i.val #[]).getD j.val (0 : Int) : Rat)

private def bhksColumnSignature
    (echelonRows : Array (Array Rat)) (j : Nat) : Array Rat :=
  echelonRows.map (·.getD j 0)

private def bhksInsertSignatureClass
    (sig : Array Rat) (j : Nat) :
    List (Array Rat × List Nat) → List (Array Rat × List Nat)
  | [] => [(sig, [j])]
  | (s, members) :: rest =>
      if s = sig then (s, members ++ [j]) :: rest
      else (s, members) :: bhksInsertSignatureClass sig j rest

private def bhksClassIndicator (r : Nat) (members : List Nat) : Array Int :=
  ((List.range r).map (fun i => if i ∈ members then (1 : Int) else 0)).toArray

/--
BHKS equivalence-class indicator vectors over the projected lattice rows
of `L`.

Lifts the projected integer rows into a rational row-basis matrix, runs
`Matrix.rref` over `Q`, and groups column indices `0, …, r - 1` by their
echelon-column signature: indices `i` and `j` are equivalent iff every
echelon row agrees at positions `i` and `j` (BHKS Lemma 3.3 / FLINT
Algorithm 8). Each equivalence class produces one compact `0/1` indicator
of length `r`. Classes are emitted in the order they are first observed by
ascending column index.
-/
def bhksEquivalenceClassIndicators (L : BhksProjectedRows) : Array (Array Int) :=
  let n := L.projectedRows.size
  let r := L.factorCount
  let M : Matrix Rat n r := bhksProjectedRowsAsRatMatrix L.projectedRows n r
  let D := Matrix.rref M
  let echelonRows : Array (Array Rat) := D.echelon.toArray.map (·.toArray)
  let groups : List (List Nat) :=
    ((List.range r).foldl
        (fun acc j =>
          bhksInsertSignatureClass (bhksColumnSignature echelonRows j) j acc)
        []).map Prod.snd
  (groups.map (fun cls => bhksClassIndicator r cls)).toArray

private def bhksTwoClassProjectedRows : BhksProjectedRows :=
  { factorCount := 4
    coeffWidth := 0
    cutRadiusSq4 := 0
    reducedRowCount := 1
    projectedRows := #[#[1, 1, 0, 0]] }

#guard bhksEquivalenceClassIndicators bhksTwoClassProjectedRows =
  #[#[1, 1, 0, 0], #[0, 0, 1, 1]]

private def bhksSingletonClassProjectedRows : BhksProjectedRows :=
  { factorCount := 3
    coeffWidth := 0
    cutRadiusSq4 := 0
    reducedRowCount := 0
    projectedRows := #[] }

#guard bhksEquivalenceClassIndicators bhksSingletonClassProjectedRows =
  #[#[1, 1, 1]]

private def bhksNoProgressProjectedRows : BhksProjectedRows :=
  { factorCount := 3
    coeffWidth := 0
    cutRadiusSq4 := 0
    reducedRowCount := 3
    projectedRows := #[#[1, 0, 0], #[0, 1, 0], #[0, 0, 1]] }

#guard bhksEquivalenceClassIndicators bhksNoProgressProjectedRows =
  #[#[1, 0, 0], #[0, 1, 0], #[0, 0, 1]]

private def liftModulus (d : LiftData) : Nat :=
  d.p ^ d.k

def centeredLiftPoly (f : ZPoly) (m : Nat) : ZPoly :=
  DensePoly.ofCoeffs <| f.toArray.map fun coeff => centeredModNat coeff m

private theorem coeff_centeredLiftPoly (f : ZPoly) (m i : Nat) :
    (centeredLiftPoly f m).coeff i = centeredModNat (f.coeff i) m := by
  have hzero : centeredModNat (0 : Int) m = 0 := centeredModNat_zero m
  unfold centeredLiftPoly
  rw [DensePoly.coeff_ofCoeffs]
  unfold DensePoly.toArray DensePoly.coeff Array.getD
  by_cases hi : i < f.coeffs.size
  · simp [hi, Array.getElem_map]
  · simp [hi]
    change (0 : Int) = centeredModNat 0 m
    exact hzero.symm

theorem centeredLiftPoly_reduceModPow_eq_of_coeff_natAbs_le
    (g : ZPoly) (p k B : Nat)
    (hbound : ∀ i, (g.coeff i).natAbs ≤ B)
    (hsep : 2 * B < p ^ k) :
    centeredLiftPoly (ZPoly.reduceModPow g p k) (p ^ k) = g := by
  apply DensePoly.ext_coeff
  intro i
  rw [coeff_centeredLiftPoly]
  have hpk : 0 < p ^ k := by omega
  rw [ZPoly.coeff_reduceModPow_eq_emod_of_pos _ _ _ _ hpk]
  exact centeredModNat_emod_eq_of_natAbs_le (g.coeff i) (p ^ k) B (hbound i) hsep

theorem centeredLiftPoly_eq_of_reduceModPow_eq
    (g h : ZPoly) (p k B : Nat)
    (hbound : ∀ i, (g.coeff i).natAbs ≤ B)
    (hsep : 2 * B < p ^ k)
    (hreduce : ZPoly.reduceModPow h p k = ZPoly.reduceModPow g p k) :
    centeredLiftPoly (ZPoly.reduceModPow h p k) (p ^ k) = g := by
  rw [hreduce]
  exact centeredLiftPoly_reduceModPow_eq_of_coeff_natAbs_le g p k B hbound hsep

/-- Normalize a candidate integer factor by extracting its primitive part and
flipping sign so the leading coefficient is non-negative.  Used by
`bhksIndicatorCandidate?` to produce a canonical witness from the centred
lift of a scaled lifted-factor product. -/
def normalizeCandidateFactor (candidate : ZPoly) : ZPoly :=
  let primitive := ZPoly.primitivePart candidate
  if DensePoly.leadingCoeff primitive < 0 then
    DensePoly.scale (-1 : Int) primitive
  else
    primitive

/--
`normalizeCandidateFactor g = g` when `g` is already primitive (content `1`)
and has non-negative leading coefficient.  This is the A2 reconstruction step
that asserts the canonical witness produced by `bhksIndicatorCandidate?`
agrees with the expected true factor under those normalization assumptions.
-/
theorem normalizeCandidateFactor_eq_of_primitive_nonneg_leading
    (g : ZPoly) (hprim : ZPoly.Primitive g)
    (hsign : 0 ≤ DensePoly.leadingCoeff g) :
    normalizeCandidateFactor g = g := by
  unfold normalizeCandidateFactor
  have hpart : ZPoly.primitivePart g = g :=
    ZPoly.primitivePart_eq_self_of_primitive g hprim
  rw [hpart]
  have hnot_neg : ¬ DensePoly.leadingCoeff g < 0 := Int.not_lt.mpr hsign
  rw [if_neg hnot_neg]

def bhksIndicatorSelectedFactors
    (liftedFactors : Array ZPoly) (indicator : Array Int) : Option (Array ZPoly) :=
  if indicator.size != liftedFactors.size then
    none
  else
    let indices := List.range indicator.size
    if indices.all (fun i => indicator.getD i 0 == 0 || indicator.getD i 0 == 1) &&
        indices.any (fun i => indicator.getD i 0 == 1) then
      some <| indices.foldl
        (fun selected i =>
          if indicator.getD i 0 == 1 then
            selected.push (liftedFactors.getD i 0)
          else
            selected)
        #[]
    else
      none

/--
Reconstruct and verify one BHKS equivalence-class indicator.

The indicator row is supplied by the later RREF recovery stage. This helper
only checks that the row is a nonempty `0/1` vector over the lifted factors,
forms `lc(f) * product selected g_i` modulo the Hensel modulus, applies the
centred integer lift, normalizes content and sign, and accepts the candidate
only when exact division of `f` succeeds.
-/
def bhksIndicatorCandidate?
    (f : ZPoly) (d : LiftData) (indicator : Array Int) : Option (ZPoly × ZPoly) :=
  match bhksIndicatorSelectedFactors d.liftedFactors indicator with
  | none => none
  | some selected =>
      let modulus := liftModulus d
      let raw := DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected)
      let candidate := normalizeCandidateFactor <|
        centeredLiftPoly (ZPoly.reduceModPow raw d.p d.k) modulus
      match exactQuotient? f candidate with
      | some quotient => some (candidate, quotient)
      | none => none

/--
A2 reconstruction surface for a single BHKS indicator, stated at the
Mathlib-free executable layer. If the indicator selects `selected`, the
scaled selected product is congruent to the expected factor modulo the Hensel
precision, the expected factor is within the Mignotte bound, already
canonical under primitive/sign normalization, and it divides `f` as a monic
positive-degree factor, then `bhksIndicatorCandidate?` returns that expected
factor with some quotient.
-/
theorem bhksIndicatorCandidate?_eq_some_of_mignottePrecision
    (f : ZPoly) (d : LiftData) (indicator : Array Int)
    (selected : Array ZPoly) (expectedFactor : ZPoly)
    (hselected :
      bhksIndicatorSelectedFactors d.liftedFactors indicator = some selected)
    (hdvd : expectedFactor ∣ f)
    (hbound :
      ∀ i, (expectedFactor.coeff i).natAbs ≤ ZPoly.defaultFactorCoeffBound f)
    (hexpected_prim : ZPoly.Primitive expectedFactor)
    (hexpected_sign : 0 ≤ DensePoly.leadingCoeff expectedFactor)
    (hexpected_monic : DensePoly.Monic expectedFactor)
    (hexpected_degree : 0 < expectedFactor.degree?.getD 0)
    (hprecision : 2 * ZPoly.defaultFactorCoeffBound f < d.p ^ d.k)
    (hindicator_product :
      ZPoly.reduceModPow
          (DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected))
          d.p d.k =
        ZPoly.reduceModPow expectedFactor d.p d.k) :
    ∃ quotient,
      bhksIndicatorCandidate? f d indicator = some (expectedFactor, quotient) := by
  let raw :=
    DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected)
  have hlift :
      centeredLiftPoly (ZPoly.reduceModPow raw d.p d.k) (d.p ^ d.k) =
        expectedFactor := by
    exact
      centeredLiftPoly_eq_of_reduceModPow_eq
        expectedFactor raw d.p d.k (ZPoly.defaultFactorCoeffBound f)
        hbound hprecision hindicator_product
  have hnormalize :
      normalizeCandidateFactor
          (centeredLiftPoly (ZPoly.reduceModPow raw d.p d.k) (d.p ^ d.k)) =
        expectedFactor := by
    rw [hlift]
    exact normalizeCandidateFactor_eq_of_primitive_nonneg_leading
      expectedFactor hexpected_prim hexpected_sign
  rcases hdvd with ⟨quotient, hquotient_mul⟩
  have hmul : quotient * expectedFactor = f := by
    rw [DensePoly.mul_comm_poly (S := Int)]
    exact hquotient_mul.symm
  have hquotient :
      exactQuotient? f expectedFactor = some quotient :=
    exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree
      hexpected_monic hexpected_degree hmul
  refine ⟨quotient, ?_⟩
  unfold bhksIndicatorCandidate?
  rw [hselected]
  change
    (let modulus := liftModulus d
     let raw :=
       DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected)
     let candidate :=
       normalizeCandidateFactor
         (centeredLiftPoly (ZPoly.reduceModPow raw d.p d.k) modulus)
     match exactQuotient? f candidate with
     | some quotient => some (candidate, quotient)
     | none => none) = some (expectedFactor, quotient)
  simp [raw, liftModulus, hnormalize, hquotient]

def bhksIndicatorOneCount (r : Nat) (indicator : Array Int) : Nat :=
  (List.range r).foldl
    (fun count i => if indicator.getD i 0 == 1 then count + 1 else count)
    0

def bhksIndicatorAllOnes (r : Nat) (indicator : Array Int) : Bool :=
  indicator.size == r && bhksIndicatorOneCount r indicator == r

/-- The recovery early-bailout predicate: the projected lattice is empty, the
indicator partition is empty, or the indicator partition is the trivial
all-ones single class. -/
def bhksDegenerateIndicatorPartition
    (L : BhksProjectedRows) (indicators : Array (Array Int)) : Bool :=
  indicators.isEmpty ||
    L.projectedRows.isEmpty ||
    (indicators.size == 1 &&
      bhksIndicatorAllOnes L.factorCount (indicators.getD 0 #[]))

private def bhksIndicatorCandidatesStep
    (f : ZPoly) (d : LiftData) :
    Option (Array ZPoly) → Array Int → Option (Array ZPoly)
  | none, _ => none
  | some candidates, indicator =>
      match bhksIndicatorCandidate? f d indicator with
      | some candidate => some (candidates.push candidate.1)
      | none => none

/-- Reconstruct and verify every BHKS equivalence-class indicator candidate.

Folds `bhksIndicatorCandidate?` over the list of indicator vectors, pushing the
verified candidate factor onto the accumulator on success and short-circuiting
to `none` on the first reconstruction failure. -/
def bhksIndicatorCandidates?
    (f : ZPoly) (d : LiftData) (indicators : Array (Array Int)) :
    Option (Array ZPoly) :=
  indicators.foldl (bhksIndicatorCandidatesStep f d) (some #[])

private theorem array_toList_getD {α : Type}
    (xs : Array α) (i : Nat) (fallback : α) :
    xs.toList.getD i fallback = xs.getD i fallback := by
  cases xs with
  | mk data =>
      rw [List.getD_eq_getElem?_getD]
      unfold Array.getD Array.size Array.getInternal
      by_cases hlt : i < data.length
      · rw [dif_pos hlt]
        simp [List.getElem?_eq_getElem hlt]
      · rw [dif_neg hlt]
        simp [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hlt)]

private theorem bhksIndicatorCandidatesStep_fold_eq_some
    (f : ZPoly) (d : LiftData)
    (pref : List ZPoly) (indicators : List (Array Int)) (candidates quotients : List ZPoly)
    (hsize : candidates.length = indicators.length)
    (hcandidate :
      ∀ i, i < indicators.length →
        bhksIndicatorCandidate? f d (indicators.getD i #[]) =
          some (candidates.getD i 0, quotients.getD i 0)) :
    indicators.foldl (bhksIndicatorCandidatesStep f d) (some pref.toArray) =
      some ((pref ++ candidates).toArray) := by
  induction indicators generalizing pref candidates quotients with
  | nil =>
      cases candidates with
      | nil => simp
      | cons candidate candidates => simp at hsize
  | cons indicator indicators ih =>
      cases candidates with
      | nil => simp at hsize
      | cons candidate candidates =>
          have hhead :
              bhksIndicatorCandidate? f d indicator =
                some (candidate, quotients.getD 0 0) := by
            simpa using hcandidate 0 (by simp)
          have htail_size : candidates.length = indicators.length := by
            simpa using hsize
          have htail :
              ∀ i, i < indicators.length →
                bhksIndicatorCandidate? f d (indicators.getD i #[]) =
                  some (candidates.getD i 0, (quotients.drop 1).getD i 0) := by
            intro i hi
            have h := hcandidate (i + 1) (by simp [hi])
            simpa [List.getD_cons_succ] using h
          rw [List.foldl_cons]
          simp [bhksIndicatorCandidatesStep, hhead]
          simpa [List.append_assoc] using
            ih (pref := pref ++ [candidate]) (candidates := candidates)
              (quotients := quotients.drop 1) htail_size htail

/--
If each BHKS equivalence-class indicator reconstructs and verifies to the
corresponding candidate factor, the executable candidate fold returns the
whole candidate array.

The `quotients` array records the exact-division witnesses returned by
`bhksIndicatorCandidate?`; only the first component is accumulated by
`bhksIndicatorCandidates?`.
-/
theorem bhksIndicatorCandidates?_eq_some_of_forall_candidate
    (f : ZPoly) (d : LiftData)
    (indicators : Array (Array Int)) (candidates quotients : Array ZPoly)
    (hsize : candidates.size = indicators.size)
    (hcandidate :
      ∀ i, i < indicators.size →
        bhksIndicatorCandidate? f d (indicators.getD i #[]) =
          some (candidates.getD i 0, quotients.getD i 0)) :
    bhksIndicatorCandidates? f d indicators = some candidates := by
  unfold bhksIndicatorCandidates?
  rw [← Array.foldl_toList]
  have hlist :
      indicators.toList.foldl (bhksIndicatorCandidatesStep f d) (some #[]) =
        some ([].append candidates.toList).toArray := by
    apply bhksIndicatorCandidatesStep_fold_eq_some
      (quotients := quotients.toList)
    · simpa using hsize
    · intro i hi
      have h := hcandidate i (by simpa using hi)
      have hindicator :
          indicators.toList.getD i #[] = indicators.getD i #[] := by
        exact array_toList_getD indicators i #[]
      have hcand :
          candidates.toList.getD i 0 = candidates.getD i 0 := by
        exact array_toList_getD candidates i 0
      have hquot :
          quotients.toList.getD i 0 = quotients.getD i 0 := by
        exact array_toList_getD quotients i 0
      simpa [hindicator, hcand, hquot] using h
  simpa using hlist

private theorem bhksIndicatorCandidates?_foldl_eq_some_append
    (f : ZPoly) (d : LiftData) :
    ∀ (indicators : List (Array Int)) (candidates : List ZPoly) (acc : Array ZPoly),
      (hlength : candidates.length = indicators.length) →
      (∀ i (hi : i < indicators.length),
        ∃ quotient,
          bhksIndicatorCandidate? f d indicators[i] =
            some (candidates[i]'(by rw [hlength]; exact hi), quotient)) →
      List.foldl (bhksIndicatorCandidatesStep f d) (some acc) indicators =
        some (acc ++ candidates.toArray)
  | [], candidates, acc, hlength, _ => by
      have hcandidates : candidates = [] := List.eq_nil_of_length_eq_zero hlength
      subst hcandidates
      apply congrArg some
      rw [← Array.toList_inj]
      simp
  | indicator :: indicators, candidates, acc, hlength, hcandidate => by
      cases candidates with
      | nil => simp at hlength
      | cons candidate candidates =>
          have hhead :
              ∃ quotient,
                bhksIndicatorCandidate? f d indicator = some (candidate, quotient) := by
            simpa using hcandidate 0 (Nat.succ_pos _)
          rcases hhead with ⟨quotient, hhead⟩
          have hlength_tail : candidates.length = indicators.length := by
            simpa using Nat.succ.inj hlength
          have htail :
              ∀ i (hi : i < indicators.length),
                ∃ quotient,
                  bhksIndicatorCandidate? f d indicators[i] =
                    some (candidates[i]'(by rw [hlength_tail]; exact hi), quotient) := by
            intro i hi
            simpa using hcandidate (i + 1) (Nat.succ_lt_succ hi)
          calc
            List.foldl (bhksIndicatorCandidatesStep f d) (some acc)
                (indicator :: indicators)
                =
              List.foldl (bhksIndicatorCandidatesStep f d)
                (some (acc.push candidate)) indicators := by
                  simp [bhksIndicatorCandidatesStep, hhead]
            _ = some (acc.push candidate ++ candidates.toArray) := by
                  exact bhksIndicatorCandidates?_foldl_eq_some_append
                    f d indicators candidates (acc.push candidate) hlength_tail htail
            _ = some (acc ++ (candidate :: candidates).toArray) := by
                  apply congrArg some
                  rw [← Array.toList_inj]
                  simp [Array.toList_append]

/--
Assemble the BHKS candidate fold from per-indicator reconstruction facts.

This is the proof-facing surface for callers that know every indicator row
reconstructs and exactly divides `f`: with a size agreement and one quotient
witness for each row, the executable fold returns the requested candidate
array.
-/
theorem bhksIndicatorCandidates?_eq_some_of_getD
    (f : ZPoly) (d : LiftData)
    (indicators : Array (Array Int)) (candidates : Array ZPoly)
    (hsize : candidates.size = indicators.size)
    (hcandidate :
      ∀ i, i < indicators.size →
        ∃ quotient,
          bhksIndicatorCandidate? f d (indicators.getD i #[]) =
            some (candidates.getD i 0, quotient)) :
    bhksIndicatorCandidates? f d indicators = some candidates := by
  unfold bhksIndicatorCandidates?
  rw [← Array.foldl_toList]
  have hlength : candidates.toList.length = indicators.toList.length := by
    simpa [Array.length_toList] using hsize
  have hcandidate_list :
      ∀ i (hi : i < indicators.toList.length),
        ∃ quotient,
          bhksIndicatorCandidate? f d indicators.toList[i] =
            some (candidates.toList[i]'(by rw [hlength]; exact hi), quotient) := by
    intro i hi
    have hi_array : i < indicators.size := by
      simpa [Array.length_toList] using hi
    have hi_candidates : i < candidates.size := by
      simpa [hsize] using hi_array
    rcases hcandidate i hi_array with ⟨quotient, hquotient⟩
    refine ⟨quotient, ?_⟩
    have hind :
        indicators.toList[i] = indicators.getD i #[] := by
      simp [Array.getD, Array.getElem_toList, hi_array]
    have hcand :
        candidates.toList[i] = candidates.getD i 0 := by
      simp [Array.getD, Array.getElem_toList, hi_candidates]
    rw [hind, hcand]
    exact hquotient
  have hfold :=
    bhksIndicatorCandidates?_foldl_eq_some_append f d
      indicators.toList candidates.toList #[] hlength hcandidate_list
  rw [hfold]
  apply congrArg some
  rw [← Array.toList_inj]
  simp

private inductive BhksRecoveryResult where
  | success (candidates : Array ZPoly)
  | degenerate
  | candidateFailure
  | productMismatch (candidates : Array ZPoly)
deriving DecidableEq

private def BhksRecoveryResult.toOption : BhksRecoveryResult → Option (Array ZPoly)
  | .success candidates => some candidates
  | .degenerate => none
  | .candidateFailure => none
  | .productMismatch _ => none

private def BhksRecoveryResult.isReconstructionFailure : BhksRecoveryResult → Bool
  | .success _ => false
  | .degenerate => false
  | .candidateFailure => true
  | .productMismatch _ => true

private def BhksRecoveryResult.isLatticeFailure : BhksRecoveryResult → Bool
  | .success _ => false
  | .degenerate => true
  | .candidateFailure => false
  | .productMismatch _ => false

/--
Run the fixed-precision BHKS recovery pipeline.

This executable glue builds the CLD lattice for the lifted factors, runs LLL
plus the Gram-Schmidt cut, extracts BHKS Lemma 3.3 equivalence-class
indicators by RREF, reconstructs every indicated candidate by centred lifting,
and accepts only when the verified candidates multiply back to `f`.
-/
private def bhksRecoverClassified (f : ZPoly) (d : LiftData) : BhksRecoveryResult :=
  let L := bhksLatticeBasis f d.p d.k d.liftedFactors
  if hrows : 1 ≤ L.factorCount + L.coeffWidth then
    let projected := bhksProjectedRows L hrows (bhksLiftData_latticeBasis_independent f d)
    let indicators := bhksEquivalenceClassIndicators projected
    if bhksDegenerateIndicatorPartition projected indicators then
      .degenerate
    else
      match bhksIndicatorCandidates? f d indicators with
      | none => .candidateFailure
      | some candidates =>
          if Array.polyProduct candidates == f then
            .success candidates
          else
            .productMismatch candidates
  else
    .degenerate

def bhksRecover? (f : ZPoly) (d : LiftData) : Option (Array ZPoly) :=
  (bhksRecoverClassified f d).toOption

/--
If the executable BHKS recovery guards all pass, `bhksRecover?` returns the
verified candidate array.

This lemma is the public proof-facing surface for callers that should not
unfold the private failure classifier used by the executable.
-/
theorem bhksRecover?_eq_some_of_checks
    (f : ZPoly) (d : LiftData) {candidates : Array ZPoly}
    (hrows : 1 ≤ (bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount +
      (bhksLatticeBasis f d.p d.k d.liftedFactors).coeffWidth)
    (hnondeg :
      bhksDegenerateIndicatorPartition
          (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors)
            hrows (bhksLiftData_latticeBasis_independent f d))
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows
              (bhksLatticeBasis f d.p d.k d.liftedFactors)
              hrows (bhksLiftData_latticeBasis_independent f d))) = false)
    (hcand :
      bhksIndicatorCandidates? f d
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows
              (bhksLatticeBasis f d.p d.k d.liftedFactors)
              hrows (bhksLiftData_latticeBasis_independent f d))) =
        some candidates)
    (hprod : Array.polyProduct candidates = f) :
    bhksRecover? f d = some candidates := by
  unfold bhksRecover?
  rw [bhksRecoverClassified]
  have hproductCheck : (Array.polyProduct candidates == f) = true := by
    simpa [beq_iff_eq] using hprod
  simp only [dif_pos hrows, hnondeg, Bool.false_eq_true, if_false, hcand,
    hproductCheck, if_true, BhksRecoveryResult.toOption]

private def bhksIndicatorGuardLift : LiftData :=
  { p := 5
    p_pos := by decide
    k := 2
    liftedFactors := bhksGuardFactors }

#guard bhksIndicatorCandidate? cldGuardF bhksIndicatorGuardLift #[1, 0] =
  some (DensePoly.ofCoeffs #[-2, 1], DensePoly.ofCoeffs #[-3, 1])
#guard bhksIndicatorCandidate? cldGuardF bhksIndicatorGuardLift #[0, 0] = none
#guard bhksIndicatorCandidate? cldGuardF bhksIndicatorGuardLift #[2, 0] = none
#guard (bhksIndicatorCandidate? cldGuardF bhksIndicatorGuardLift #[0, 1]).map Prod.snd =
  some (DensePoly.ofCoeffs #[-2, 1])

#guard bhksRecover? cldGuardF bhksIndicatorGuardLift =
  some bhksGuardFactors
#guard bhksRecoverClassified cldGuardF bhksIndicatorGuardLift =
  .success bhksGuardFactors

private def bhksDegenerateRecoverLift : LiftData :=
  { p := 5
    p_pos := by decide
    k := 2
    liftedFactors := #[DensePoly.ofCoeffs #[1]] }

#guard bhksRecover? cldGuardF bhksDegenerateRecoverLift = none
#guard bhksRecoverClassified cldGuardF bhksDegenerateRecoverLift =
  .degenerate
#guard (bhksRecoverClassified cldGuardF bhksDegenerateRecoverLift).isLatticeFailure
#guard !(bhksRecoverClassified cldGuardF bhksDegenerateRecoverLift).isReconstructionFailure

private def bhksFailedDivisionRecoverLift : LiftData :=
  { p := 5
    p_pos := by decide
    k := 2
    liftedFactors := #[DensePoly.ofCoeffs #[-2, 1], DensePoly.ofCoeffs #[-4, 1]] }

#guard bhksIndicatorCandidate? cldGuardF bhksFailedDivisionRecoverLift #[0, 1] = none
#guard bhksRecover? cldGuardF bhksFailedDivisionRecoverLift = none
#guard bhksRecoverClassified cldGuardF bhksFailedDivisionRecoverLift =
  .candidateFailure
#guard (bhksRecoverClassified cldGuardF bhksFailedDivisionRecoverLift).isReconstructionFailure
#guard !(bhksRecoverClassified cldGuardF bhksFailedDivisionRecoverLift).isLatticeFailure

private def bhksProductMismatchRecoverLift : LiftData :=
  { p := 5
    k := 2
    liftedFactors := #[DensePoly.ofCoeffs #[-2, 1]]
    p_pos := by decide }

#guard bhksIndicatorCandidate? cldGuardF bhksProductMismatchRecoverLift #[1] =
  some (DensePoly.ofCoeffs #[-2, 1], DensePoly.ofCoeffs #[-3, 1])
#guard BhksRecoveryResult.toOption
    (.productMismatch #[DensePoly.ofCoeffs #[-2, 1]]) = none

private def recombinationSearchAux
    (target : ZPoly) (localFactors : List ZPoly) : Nat → Option (List ZPoly)
  | 0 => none
  | fuel + 1 =>
      if target = 1 then
        some []
      else
        firstSome (subsetSplitsWithFirst localFactors) fun split =>
          let candidate := Array.polyProduct split.1.toArray
          match exactQuotient? target candidate with
          | none => none
          | some quotient =>
              match recombinationSearchAux quotient split.2 fuel with
              | none => none
              | some rest => some (candidate :: rest)

/--
Search for an integer-factor recombination of the lifted local factors.

The search enumerates subsets containing the first remaining local factor,
accepts a subset only when its product exactly divides the current target, and
then recurses on the quotient and unused local factors.
-/
def recombinationSearch (f : ZPoly) (localFactors : List ZPoly) : Option (List ZPoly) :=
  recombinationSearchAux f localFactors (localFactors.length + 1)

private def recombinationSearchModAux
    (target : ZPoly) (modulus : Nat) (localFactors : List ZPoly) :
    Nat → Option (List ZPoly)
  | 0 => none
  | fuel + 1 =>
      if target = 1 then
        some []
      else
        firstSome (subsetSplitsWithFirst localFactors) fun split =>
          let candidate :=
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
          match exactQuotient? target candidate with
          | none => none
          | some quotient =>
              match recombinationSearchModAux quotient modulus split.2 fuel with
              | none => none
              | some rest => some (candidate :: rest)

private def recombinationSearchMod
    (f : ZPoly) (modulus : Nat) (localFactors : List ZPoly) : Option (List ZPoly) :=
  recombinationSearchModAux f modulus localFactors (localFactors.length + 1)

private def recombineExhaustive (f : ZPoly) (d : LiftData) : Array ZPoly :=
  match recombinationSearchMod f (liftModulus d) d.liftedFactors.toList with
  | some factors => factors.toArray
  | none => #[]

/-- Initial Hensel precision used by the fast BHKS doubling schedule. -/
def initialHenselPrecision (B : Nat) : Nat :=
  if B ≤ 4 then B else 4

/-- Successor precision used by the fast BHKS doubling schedule. -/
def nextHenselPrecision (k B : Nat) : Nat :=
  if 2 * k < B then
    2 * k
  else
    B

private def factorFastCoreWithBound
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) : Nat → Nat → Option (Array ZPoly)
  | _k, 0 => none
  | k, fuel + 1 =>
      let liftData := henselLiftData core k primeData
      match bhksRecoverClassified core liftData with
      | .success factors => some factors
      | .candidateFailure =>
        if k ≥ B then
          none
        else
          factorFastCoreWithBound core B primeData (nextHenselPrecision k B) fuel
      | .productMismatch _ =>
        if k ≥ B then
          none
        else
          factorFastCoreWithBound core B primeData (nextHenselPrecision k B) fuel
      | .degenerate =>
        if k ≥ B then
          none
        else
          factorFastCoreWithBound core B primeData (nextHenselPrecision k B) fuel

/-- Finite list of Hensel precisions inspected by the fast BHKS core loop. -/
def henselPrecisionSchedule (B : Nat) : Nat → Nat → List Nat
  | _k, 0 => []
  | k, fuel + 1 =>
      k :: if k ≥ B then [] else henselPrecisionSchedule B (nextHenselPrecision k B) fuel

private theorem initialHenselPrecision_le (B : Nat) :
    initialHenselPrecision B ≤ B := by
  unfold initialHenselPrecision
  by_cases hB : B ≤ 4
  · simp [hB]
  · simp [hB]
    omega

private theorem nextHenselPrecision_le (k B : Nat) :
    nextHenselPrecision k B ≤ B := by
  unfold nextHenselPrecision
  by_cases h : 2 * k < B
  · simp [h]
    omega
  · simp [h]

private theorem nextHenselPrecision_eq_B_of_cap_reached {k B : Nat}
    (h : B ≤ 2 * k) :
    nextHenselPrecision k B = B := by
  unfold nextHenselPrecision
  have hnot : ¬ 2 * k < B := by omega
  simp [hnot]

private theorem initialHenselPrecision_mem_schedule (B fuel : Nat) :
    initialHenselPrecision B ∈
      henselPrecisionSchedule B (initialHenselPrecision B) (fuel + 1) := by
  simp [henselPrecisionSchedule]

private theorem nextHenselPrecision_mem_schedule {B k fuel : Nat}
    (hk : ¬ k ≥ B) :
    nextHenselPrecision k B ∈
      henselPrecisionSchedule B k (fuel + 2) := by
  simp [henselPrecisionSchedule, hk]

/-- Helper: when the doubling fuel `fuel` is large enough that the geometric
progression starting from `k` reaches the cap `B`, the cap appears in the
finite Hensel precision schedule.  The geometric bound `B ≤ k * 2 ^ fuel`
is what we will discharge for the canonical executable choice
`k = initialHenselPrecision B`, `fuel = quadraticDoublingSteps B + 1`. -/
private theorem henselPrecisionSchedule_mem_cap
    {B : Nat} :
    ∀ (k fuel : Nat), 0 < k → k ≤ B → B ≤ k * 2 ^ fuel →
      B ∈ henselPrecisionSchedule B k (fuel + 1) := by
  intro k fuel
  induction fuel generalizing k with
  | zero =>
      intro _ hk_le hfuel
      have hkB : k = B := by
        have : k * 2 ^ 0 = k := by simp
        omega
      subst hkB
      simp [henselPrecisionSchedule]
  | succ fuel ih =>
      intro hk_pos hk_le hfuel
      by_cases hk_eq : k = B
      · subst hk_eq
        simp [henselPrecisionSchedule]
      · have hk_lt : k < B := Nat.lt_of_le_of_ne hk_le hk_eq
        rw [henselPrecisionSchedule]
        simp only [List.mem_cons]
        right
        rw [if_neg (by omega : ¬ k ≥ B)]
        unfold nextHenselPrecision
        have hpow : k * 2 ^ (fuel + 1) = 2 * k * 2 ^ fuel := by
          rw [Nat.pow_succ']
          rw [← Nat.mul_assoc, Nat.mul_comm k 2]
        by_cases h2 : 2 * k < B
        · rw [if_pos h2]
          refine ih (2 * k) (by omega) (by omega) ?_
          omega
        · rw [if_neg h2]
          refine ih B (by omega) (Nat.le_refl _) ?_
          have hge1 : 1 ≤ 2 ^ fuel := Nat.one_le_two_pow
          calc B = B * 1 := (Nat.mul_one B).symm
            _ ≤ B * 2 ^ fuel := Nat.mul_le_mul_left B hge1

/--
The fast-path cap `B` is itself a member of the canonical Hensel precision
schedule the executable loop walks: `henselPrecisionSchedule B
(initialHenselPrecision B) (quadraticDoublingSteps B + 2)`.

This is the connective bridge consumed by the Mathlib-facing Group D
forward-recovery wrapper: callers who supply `ForwardRecoveryInputs` at the
canonical terminal precision no longer need to re-prove the executable
doubling-schedule membership obligation.
-/
theorem cap_mem_henselPrecisionSchedule (B : Nat) :
    B ∈ henselPrecisionSchedule B (initialHenselPrecision B)
      (ZPoly.quadraticDoublingSteps B + 2) := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB
    simp [henselPrecisionSchedule, initialHenselPrecision]
  · -- B ≥ 1.  Reduce to the geometric-bound helper.
    have hinit_pos : 0 < initialHenselPrecision B := by
      unfold initialHenselPrecision
      by_cases hle : B ≤ 4
      · simp [hle]; omega
      · simp [hle]
    have hinit_le : initialHenselPrecision B ≤ B := initialHenselPrecision_le B
    have hbound :
        B ≤ initialHenselPrecision B * 2 ^ (ZPoly.quadraticDoublingSteps B + 1) := by
      by_cases hsmall : B ≤ 4
      · have hinit : initialHenselPrecision B = B := by
          unfold initialHenselPrecision; simp [hsmall]
        rw [hinit]
        have hpow : 1 ≤ 2 ^ (ZPoly.quadraticDoublingSteps B + 1) :=
          Nat.one_le_two_pow
        calc B = B * 1 := (Nat.mul_one B).symm
          _ ≤ B * 2 ^ (ZPoly.quadraticDoublingSteps B + 1) :=
              Nat.mul_le_mul_left B hpow
      · have hinit : initialHenselPrecision B = 4 := by
          unfold initialHenselPrecision
          simp [hsmall]
        rw [hinit]
        have hquad :
            ZPoly.quadraticDoublingSteps B = (B - 1).log2 + 1 := by
          unfold ZPoly.quadraticDoublingSteps
          have : ¬ B ≤ 1 := by omega
          simp [this]
        rw [hquad]
        -- Goal: B ≤ 4 * 2 ^ ((B - 1).log2 + 1 + 1)
        have hlog : B - 1 < 2 ^ ((B - 1).log2 + 1) := Nat.lt_log2_self
        have hB_le : B ≤ 2 ^ ((B - 1).log2 + 1) := by omega
        have hexp :
            2 ^ ((B - 1).log2 + 1 + 1) = 2 * 2 ^ ((B - 1).log2 + 1) := by
          rw [Nat.pow_succ, Nat.mul_comm]
        calc B ≤ 2 ^ ((B - 1).log2 + 1) := hB_le
          _ ≤ 4 * 2 ^ ((B - 1).log2 + 1 + 1) := by
              rw [hexp]
              -- 2^(x+1) ≤ 4 * (2 * 2^(x+1)) = 8 * 2^(x+1)
              have hle : 2 ^ ((B - 1).log2 + 1) ≤ 8 * 2 ^ ((B - 1).log2 + 1) := by
                have : 1 ≤ 8 := by decide
                calc 2 ^ ((B - 1).log2 + 1)
                    = 1 * 2 ^ ((B - 1).log2 + 1) := (Nat.one_mul _).symm
                  _ ≤ 8 * 2 ^ ((B - 1).log2 + 1) := Nat.mul_le_mul_right _ this
              have h8eq : 4 * (2 * 2 ^ ((B - 1).log2 + 1)) =
                  8 * 2 ^ ((B - 1).log2 + 1) := by
                rw [← Nat.mul_assoc]
              omega
    exact henselPrecisionSchedule_mem_cap _ _ hinit_pos hinit_le hbound

private theorem factorFastCoreWithBound_isSome_of_recovery_on_schedule
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    {start fuel target : Nat} {factors : Array ZPoly}
    (hmem : target ∈ henselPrecisionSchedule B start fuel)
    (hrecover :
      bhksRecover? core (henselLiftData core target primeData) = some factors) :
    (factorFastCoreWithBound core B primeData start fuel).isSome := by
  induction fuel generalizing start with
  | zero =>
      simp [henselPrecisionSchedule] at hmem
  | succ fuel ih =>
      rw [factorFastCoreWithBound]
      cases hclass : bhksRecoverClassified core (henselLiftData core start primeData) with
      | success xs =>
          simp
      | degenerate =>
          by_cases hk : start ≥ B
          · simp [hk]
            have hmem' : target = start := by
              simpa [henselPrecisionSchedule, hk] using hmem
            subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
          · simp [hk]
            have hmem' :
                target ∈
                  henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
              have hmem_tail :
                  target = start ∨
                    target ∈
                      henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                simpa [henselPrecisionSchedule, hk] using hmem
              cases hmem_tail with
              | inl htarget =>
                  subst target
                  rw [bhksRecover?] at hrecover
                  simp [hclass, BhksRecoveryResult.toOption] at hrecover
              | inr htail =>
                  exact htail
            exact ih hmem'
      | candidateFailure =>
          by_cases hk : start ≥ B
          · simp [hk]
            have hmem' : target = start := by
              simpa [henselPrecisionSchedule, hk] using hmem
            subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
          · simp [hk]
            have hmem' :
                target ∈
                  henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
              have hmem_tail :
                  target = start ∨
                    target ∈
                      henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                simpa [henselPrecisionSchedule, hk] using hmem
              cases hmem_tail with
              | inl htarget =>
                  subst target
                  rw [bhksRecover?] at hrecover
                  simp [hclass, BhksRecoveryResult.toOption] at hrecover
              | inr htail =>
                  exact htail
            exact ih hmem'
      | productMismatch cands =>
          by_cases hk : start ≥ B
          · simp [hk]
            have hmem' : target = start := by
              simpa [henselPrecisionSchedule, hk] using hmem
            subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
          · simp [hk]
            have hmem' :
                target ∈
                  henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
              have hmem_tail :
                  target = start ∨
                    target ∈
                      henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                simpa [henselPrecisionSchedule, hk] using hmem
              cases hmem_tail with
              | inl htarget =>
                  subst target
                  rw [bhksRecover?] at hrecover
                  simp [hclass, BhksRecoveryResult.toOption] at hrecover
              | inr htail =>
                  exact htail
            exact ih hmem'

private theorem factorFastCoreWithBound_ne_none_of_recovery_on_schedule
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    {start fuel target : Nat} {factors : Array ZPoly}
    (hmem : target ∈ henselPrecisionSchedule B start fuel)
    (hrecover :
      bhksRecover? core (henselLiftData core target primeData) = some factors) :
    factorFastCoreWithBound core B primeData start fuel ≠ none := by
  intro hnone
  have hsome :=
    factorFastCoreWithBound_isSome_of_recovery_on_schedule
      core B primeData hmem hrecover
  rw [hnone] at hsome
  simp at hsome

private def factorFastCoreGuardPrimeData : PrimeChoiceData :=
  choosePrimeData cldGuardF

#guard factorFastCoreWithBound cldGuardF 1 factorFastCoreGuardPrimeData
    (initialHenselPrecision 1) (ZPoly.quadraticDoublingSteps 1 + 2) =
  none

#guard factorFastCoreWithBound cldGuardF 4 factorFastCoreGuardPrimeData
    (initialHenselPrecision 4) (ZPoly.quadraticDoublingSteps 4 + 2) =
  some bhksGuardFactors

private def exhaustiveCoreFactorsWithBound
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) : Array ZPoly :=
  if B = 0 then
    #[core]
  else
    let liftData :=
      henselLiftData core (precisionForCoeffBound B primeData.p) primeData
    let factors := recombineExhaustive core liftData
    if factors.isEmpty then
      #[core]
    else
      factors

private def factorSlowFactorsWithBound (f : ZPoly) (B : Nat) : Array ZPoly :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    reassemblePolynomialFactors normalized #[]
  else
    match quadraticIntegerRootFactors? normalized.squareFreeCore with
    | some coreFactors => reassemblePolynomialFactors normalized coreFactors
    | none =>
        let primeData := choosePrimeData normalized.squareFreeCore
        let coreFactors :=
          exhaustiveCoreFactorsWithBound normalized.squareFreeCore B primeData
        reassemblePolynomialFactors normalized coreFactors

private def factorSlowWithBound (f : ZPoly) (B : Nat) : Factorization :=
  factorizationOfFactors f (factorSlowFactorsWithBound f B)

/--
Factor using the exhaustive recombination path at the default Mignotte
coefficient bound. This is the public slow-path backstop for the two-tier BZ
API.
-/
def factorSlow (f : ZPoly) : Factorization :=
  factorSlowWithBound f (ZPoly.defaultFactorCoeffBound f)

private def factorFastFactorsWithBound (f : ZPoly) (B : Nat) : Option (Array ZPoly) :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    some (reassemblePolynomialFactors normalized #[])
  else if B = 0 then
    none
  else
    if B = 1 then
      let primeData := choosePrimeData normalized.squareFreeCore
      let a := precisionForCoeffBound B primeData.p
      if primeData.factorsModP.size ≤ 1 then
        some (reassemblePolynomialFactors normalized #[normalized.squareFreeCore])
      else
        match factorFastCoreWithBound normalized.squareFreeCore a primeData
            (initialHenselPrecision a) (ZPoly.quadraticDoublingSteps a + 2) with
        | some coreFactors => some (reassemblePolynomialFactors normalized coreFactors)
        | none => none
    else
      match quadraticIntegerRootFactors? normalized.squareFreeCore with
      | some coreFactors => some (reassemblePolynomialFactors normalized coreFactors)
      | none =>
        let primeData := choosePrimeData normalized.squareFreeCore
        let a := precisionForCoeffBound B primeData.p
        if primeData.factorsModP.size ≤ 1 then
          some (reassemblePolynomialFactors normalized #[normalized.squareFreeCore])
        else
          match factorFastCoreWithBound normalized.squareFreeCore a primeData
              (initialHenselPrecision a) (ZPoly.quadraticDoublingSteps a + 2) with
          | some coreFactors => some (reassemblePolynomialFactors normalized coreFactors)
          | none => none

#guard factorFastFactorsWithBound cldGuardF 1 = none

#guard factorFastFactorsWithBound cldGuardF 4 =
  some bhksGuardFactors

/-- Lift a successful `factorFastCoreWithBound` call to a `factorFastFactorsWithBound`
success conclusion. The hypotheses pin down the wrapper's branch dispatch: the
input is not zero-degree (`hdeg`), the recombination budget is at least one
(`hB_pos`), the chosen prime produces more than one mod-`p` factor (`hmulti`),
and (when `B ≠ 1`) the quadratic-root short-circuit does not apply
(`hquadratic`). -/
private theorem factorFastFactorsWithBound_eq_some_of_core_success
    (f : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    (coreFactors : Array ZPoly)
    (hB_pos : 1 ≤ B)
    (hnormalized : primeData = choosePrimeData
      (normalizeForFactor f).squareFreeCore)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hmulti : 1 < primeData.factorsModP.size)
    (hquadratic : B = 1 ∨
      quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none)
    (hcore :
      let a := precisionForCoeffBound B primeData.p
      factorFastCoreWithBound (normalizeForFactor f).squareFreeCore a
        primeData (initialHenselPrecision a)
        (ZPoly.quadraticDoublingSteps a + 2) = some coreFactors) :
    factorFastFactorsWithBound f B =
      some (reassemblePolynomialFactors (normalizeForFactor f) coreFactors) := by
  unfold factorFastFactorsWithBound
  rw [if_neg hdeg, if_neg (by omega : B ≠ 0)]
  by_cases hB1 : B = 1
  · rw [if_pos hB1]
    rw [← hnormalized]
    rw [if_neg (by omega : ¬ primeData.factorsModP.size ≤ 1)]
    rw [hcore]
  · rw [if_neg hB1]
    have hq : quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none := by
      cases hquadratic with
      | inl heq => exact absurd heq hB1
      | inr hnone => exact hnone
    rw [hq]
    rw [← hnormalized]
    rw [if_neg (by omega : ¬ primeData.factorsModP.size ≤ 1)]
    rw [hcore]

/--
Precision cap used by the public fast path.

The cap is the larger of the BHKS separation threshold bound and the
Mignotte coefficient bound, so later termination proofs can use the same
precision for both lattice separation and exact integer reconstruction.
-/
def factorFastPrecisionCap (f : ZPoly) : Nat :=
  max (bhksBound f) (ZPoly.defaultFactorCoeffBound f)

theorem bhksBound_le_factorFastPrecisionCap (f : ZPoly) :
    bhksBound f ≤ factorFastPrecisionCap f := by
  unfold factorFastPrecisionCap
  exact Nat.le_max_left _ _

theorem defaultFactorCoeffBound_le_factorFastPrecisionCap (f : ZPoly) :
    ZPoly.defaultFactorCoeffBound f ≤ factorFastPrecisionCap f := by
  unfold factorFastPrecisionCap
  exact Nat.le_max_right _ _

private def factorFastWithBound (f : ZPoly) (B : Nat) : Option Factorization :=
  (factorFastFactorsWithBound f B).map (factorizationOfFactors f)

/--
Public van Hoeij CLD fast path with a combined BHKS/Mignotte precision cap.

The bounded core loop only accepts candidates certified by the fixed-precision
BHKS recovery pipeline; if every precision up to the cap misses, this reports
`none` so the public `factor` combinator can use the slow backstop.
-/
def factorFast (f : ZPoly) : Option Factorization :=
  factorFastWithBound f (factorFastPrecisionCap f)

#guard (factorFast (DensePoly.ofCoeffs #[1, 1, 1, 1, 1])).map Factorization.product =
  some (DensePoly.ofCoeffs #[1, 1, 1, 1, 1])

#guard factorFastWithBound (DensePoly.ofCoeffs #[1, 0, 0, 0, 1]) 4 = none
#guard factorFastWithBound cldGuardF 1 = none

/-- Lift a `factorFastFactorsWithBound` success through the `.map` layer that
defines `factorFastWithBound`. -/
private theorem factorFastWithBound_eq_some_of_factors_some
    (f : ZPoly) (B : Nat) {factors : Array ZPoly}
    (h : factorFastFactorsWithBound f B = some factors) :
    factorFastWithBound f B = some (factorizationOfFactors f factors) := by
  unfold factorFastWithBound
  rw [h]
  rfl

/-- Forward a `factorFastFactorsWithBound ≠ none` through the `.map` layer that
defines `factorFastWithBound`. -/
private theorem factorFastWithBound_ne_none_of_factors_ne_none
    (f : ZPoly) (B : Nat)
    (h : factorFastFactorsWithBound f B ≠ none) :
    factorFastWithBound f B ≠ none := by
  match hex : factorFastFactorsWithBound f B with
  | some factors =>
    rw [factorFastWithBound_eq_some_of_factors_some f B hex]
    exact Option.some_ne_none _
  | none => exact absurd hex h

/-- Lift a successful `factorFastWithBound` call at the precision cap to a
`factorFast` success conclusion. Immediate from the definition of `factorFast`. -/
theorem factorFast_eq_some_of_factorFastWithBound_cap_eq_some
    (f : ZPoly) {result : Factorization}
    (h : factorFastWithBound f (factorFastPrecisionCap f) = some result) :
    factorFast f = some result := h

/-- Forward `factorFastWithBound ≠ none` at the precision cap to `factorFast ≠ none`.
Immediate from the definition of `factorFast`. -/
theorem factorFast_ne_none_of_factorFastWithBound_cap_ne_none
    (f : ZPoly)
    (h : factorFastWithBound f (factorFastPrecisionCap f) ≠ none) :
    factorFast f ≠ none := h

/--
Expose the proof-facing fast-path bridge used by the BHKS termination layer.
If a precision on `factorFast`'s scheduled search recovers a core
factorization for the normalized square-free core, then the public fast path
returns `some _`.
-/
theorem factorFast_ne_none_of_core_recovery_on_schedule
    (f : ZPoly) (primeData : PrimeChoiceData)
    {target : Nat} {coreFactors : Array ZPoly}
    (hB_pos : 1 ≤ factorFastPrecisionCap f)
    (hnormalized :
      primeData = choosePrimeData (normalizeForFactor f).squareFreeCore)
    (hmem :
      let a := precisionForCoeffBound (factorFastPrecisionCap f) primeData.p
      target ∈
        henselPrecisionSchedule a
          (initialHenselPrecision a)
          (ZPoly.quadraticDoublingSteps a + 2))
    (hrecover :
      bhksRecover? (normalizeForFactor f).squareFreeCore
        (henselLiftData (normalizeForFactor f).squareFreeCore target primeData) =
          some coreFactors) :
    factorFast f ≠ none := by
  let B := factorFastPrecisionCap f
  let a := precisionForCoeffBound B primeData.p
  have hB_pos' : 1 ≤ B := by
    simpa [B] using hB_pos
  have hcore_ne :
      factorFastCoreWithBound (normalizeForFactor f).squareFreeCore a primeData
          (initialHenselPrecision a) (ZPoly.quadraticDoublingSteps a + 2) ≠ none := by
    exact
      factorFastCoreWithBound_ne_none_of_recovery_on_schedule
        (normalizeForFactor f).squareFreeCore a primeData
        (by simpa [a, B] using hmem) hrecover
  have hfactors_ne :
      factorFastFactorsWithBound f B ≠ none := by
    unfold factorFastFactorsWithBound
    by_cases hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
    · rw [if_pos hdeg]
      exact Option.some_ne_none _
    · rw [if_neg hdeg]
      rw [if_neg (by omega : B ≠ 0)]
      by_cases hB1 : B = 1
      · rw [if_pos hB1]
        rw [← hnormalized]
        by_cases hsmall : primeData.factorsModP.size ≤ 1
        · rw [if_pos hsmall]
          exact Option.some_ne_none _
        · rw [if_neg hsmall]
          cases hcore :
              factorFastCoreWithBound (normalizeForFactor f).squareFreeCore
                (precisionForCoeffBound B primeData.p) primeData
                (initialHenselPrecision (precisionForCoeffBound B primeData.p))
                (ZPoly.quadraticDoublingSteps (precisionForCoeffBound B primeData.p) + 2) with
          | none => exact absurd hcore hcore_ne
          | some factors =>
              simp
      · rw [if_neg hB1]
        cases hquad :
            quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore with
        | some factors =>
            simp
        | none =>
            rw [← hnormalized]
            by_cases hsmall : primeData.factorsModP.size ≤ 1
            · rw [if_pos hsmall]
              exact Option.some_ne_none _
            · rw [if_neg hsmall]
              cases hcore :
                  factorFastCoreWithBound (normalizeForFactor f).squareFreeCore
                    (precisionForCoeffBound B primeData.p) primeData
                    (initialHenselPrecision (precisionForCoeffBound B primeData.p))
                    (ZPoly.quadraticDoublingSteps
                      (precisionForCoeffBound B primeData.p) + 2) with
              | none => exact absurd hcore hcore_ne
              | some factors =>
                  simp
  have hbounded :
      factorFastWithBound f B ≠ none :=
    factorFastWithBound_ne_none_of_factors_ne_none f B hfactors_ne
  exact
    factorFast_ne_none_of_factorFastWithBound_cap_ne_none f
      (by simpa [B] using hbounded)

/--
Factor with an explicit coefficient bound for the recombination stage.

The bounded fast path is tried first at this precision. If it cannot certify a
factorization at the requested bound, the exhaustive slow path at the same
bound supplies the returned `Factorization`.
-/
def factorWithBound (f : ZPoly) (B : Nat) : Factorization :=
  (factorFastWithBound f B).getD (factorSlowWithBound f B)

#guard Factorization.product (factorWithBound cldGuardF 1) = cldGuardF

/--
Factor using the Mignotte-bounded fast attempt with exhaustive slow fallback.

The standalone `factorFast` entry point exposes the proof-facing combined
BHKS/Mignotte cap. The default total factorization combinator keeps the
runtime-oriented coefficient bound before falling back to exhaustive
recombination, so irreducible inputs that split modulo the chosen prime do not
force the full BHKS threshold search.
-/
def factor (f : ZPoly) : Factorization :=
  factorWithBound f (ZPoly.defaultFactorCoeffBound f)

@[simp] theorem factor_eq_factorWithBound_default (f : ZPoly) :
    factor f = factorWithBound f (ZPoly.defaultFactorCoeffBound f) := rfl

namespace ZPoly

/--
Mathlib-free irreducibility predicate for integer polynomials.

The class form lets downstream Mathlib-free APIs request irreducibility through
typeclass inference. The predicate remains the usual nonzero, non-unit, no
proper factorization condition.
-/
class Irreducible (f : ZPoly) : Prop where
  /-- The zero polynomial is not irreducible. -/
  not_zero : f ≠ 0
  /-- Units are excluded from irreducibility. -/
  not_unit : ¬ ZPoly.IsUnit f
  /-- Every product decomposition has a unit factor. -/
  no_factors :
    ∀ a b : ZPoly, f = a * b → ZPoly.IsUnit a ∨ ZPoly.IsUnit b

private def isNatPrime (n : Nat) : Bool :=
  2 ≤ n && !((List.range n).any fun d => 2 ≤ d && d * d ≤ n && n % d == 0)

/--
Computational irreducibility checker backed by the public factorization API.

Constants are checked by integer primality. Positive-degree polynomials are
checked from the returned `Factorization`: the scalar must be a unit and there
must be exactly one polynomial factor with multiplicity one.
-/
def isIrreducible (f : ZPoly) : Bool :=
  if f = 0 then
    false
  else if f.degree?.getD 0 = 0 then
    let k := (f.coeff 0).natAbs
    isNatPrime k
  else
    let φ := factor f
    decide (φ.scalar.natAbs = 1) &&
      φ.factors.size == 1 &&
      match φ.factors.toList with
      | [entry] => decide (entry.2 = 1)
      | _ => false

theorem isIrreducible_iff (f : ZPoly) :
    isIrreducible f = true ↔ Irreducible f := by
  sorry

instance instDecidableIrreducible (f : ZPoly) : Decidable (Irreducible f) :=
  decidable_of_iff _ (isIrreducible_iff f)

end ZPoly

/--
Conditional product contract for the bounded factorization entry point.
The bound hypothesis is the computational correctness assumption supplied by
the later proof layer.
-/
theorem factor_product_of_bound (f : ZPoly) (B : Nat)
    (hB : ∀ g : ZPoly, g ∣ f → ∀ i, (g.coeff i).natAbs ≤ B) :
    Factorization.product (factorWithBound f B) = f := by
  sorry

/--
The primitive square-free layer in normalization reassembles the extracted
`X`-free primitive core up to the rational unit introduced by clearing
denominators.
-/
theorem normalizeForFactor_reassembles (f : ZPoly) :
    let normalized := normalizeForFactor f
    ∃ unit : Rat,
      ZPoly.toRatPoly normalized.xFreePrimitive =
        DensePoly.scale unit
          (ZPoly.toRatPoly (normalized.squareFreeCore * normalized.repeatedPart)) := by
  unfold normalizeForFactor
  simp only
  exact primitiveSquareFreeDecomposition_reassembles_xfree_over_rat
    (ZPoly.extractXPower (ZPoly.primitivePart f)).core

/--
Replacing the square-free core by a product-equivalent factor array preserves
the rational-associate normalization invariant for the extracted primitive core.
-/
theorem reassembleNormalizedFactors_product
    (f : ZPoly) (normalized : FactorNormalizationData) (coreFactors : Array ZPoly)
    (hnormalized : normalizeForFactor f = normalized)
    (hcore : Array.polyProduct coreFactors = normalized.squareFreeCore) :
    ∃ unit : Rat,
      ZPoly.toRatPoly normalized.xFreePrimitive =
        DensePoly.scale unit
          (ZPoly.toRatPoly (Array.polyProduct coreFactors * normalized.repeatedPart)) := by
  subst normalized
  have hnormalized := normalizeForFactor_reassembles f
  change
    ∃ unit : Rat,
      ZPoly.toRatPoly (normalizeForFactor f).xFreePrimitive =
        DensePoly.scale unit
          (ZPoly.toRatPoly
            ((normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart)) at hnormalized
  simpa [hcore] using hnormalized

/--
For constant square-free cores, the normalization-only factor array preserves the
rational-associate normalization invariant for the extracted primitive core.
-/
theorem normalizedConstantFactors_product
    (f : ZPoly) (normalized : FactorNormalizationData)
    (hnormalized : normalizeForFactor f = normalized)
    (hconst : normalized.squareFreeCore.degree?.getD 0 = 0) :
    ∃ unit : Rat,
      ZPoly.toRatPoly normalized.xFreePrimitive =
        DensePoly.scale unit
          (ZPoly.toRatPoly (normalized.squareFreeCore * normalized.repeatedPart)) := by
  subst normalized
  by_cases hcore : (normalizeForFactor f).squareFreeCore = 1
  · simpa [normalizedConstantFactors, hcore] using normalizeForFactor_reassembles f
  · simpa [normalizedConstantFactors, hcore] using normalizeForFactor_reassembles f

/--
The `X`-free part of the primitive part of a nonzero integer polynomial is itself
primitive. Stripping initial zero coefficients does not introduce a common factor
because the original primitive part already has unit content.
-/
private theorem extractXPower_core_primitive_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0) :
    ZPoly.Primitive (ZPoly.extractXPower (ZPoly.primitivePart f)).core := by
  -- Step 1: shift xData.power xData.core = primitivePart f.
  have hshift :
      DensePoly.shift (ZPoly.extractXPower (ZPoly.primitivePart f)).power
        (ZPoly.extractXPower (ZPoly.primitivePart f)).core =
        ZPoly.primitivePart f := by
    have hex :
        Array.polyProduct
          (xPowerFactorArray (ZPoly.extractXPower (ZPoly.primitivePart f)).power ++
            #[(ZPoly.extractXPower (ZPoly.primitivePart f)).core]) =
          ZPoly.primitivePart f :=
      extractXPower_product (ZPoly.primitivePart f)
    rw [polyProduct_append, polyProduct_singleton, polyProduct_xPowerFactorArray_mul] at hex
    exact hex
  -- Step 2: f ≠ 0 → content f ≠ 0.
  have hcontent_f_ne : ZPoly.content f ≠ 0 := by
    intro hcontent
    apply hf
    have hreconstruct := ZPoly.content_mul_primitivePart f
    rw [hcontent] at hreconstruct
    have hzero : DensePoly.scale (0 : Int) (ZPoly.primitivePart f) = 0 := by
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_scale (R := Int) (0 : Int) (ZPoly.primitivePart f) n
        (Int.zero_mul 0)]
      rw [DensePoly.coeff_zero]
      exact Int.zero_mul _
    rw [hzero] at hreconstruct
    exact hreconstruct.symm
  -- Step 3: content (primitivePart f) = 1.
  have hcontent_pf : ZPoly.content (ZPoly.primitivePart f) = 1 :=
    ZPoly.primitivePart_primitive f hcontent_f_ne
  -- Step 4: every coefficient of primitivePart f is divisible by content xData.core.
  have hdvd : ∀ n,
      ZPoly.content (ZPoly.extractXPower (ZPoly.primitivePart f)).core ∣
        (ZPoly.primitivePart f).coeff n := by
    intro n
    have hcoeff_eq :
        (ZPoly.primitivePart f).coeff n =
          (DensePoly.shift (ZPoly.extractXPower (ZPoly.primitivePart f)).power
            (ZPoly.extractXPower (ZPoly.primitivePart f)).core).coeff n :=
      congrArg (fun p : ZPoly => p.coeff n) hshift.symm
    rw [hcoeff_eq, DensePoly.coeff_shift]
    by_cases hn : n < (ZPoly.extractXPower (ZPoly.primitivePart f)).power
    · rw [if_pos hn]
      exact ⟨0, by show (0 : Int) = _ * 0; rw [Int.mul_zero]⟩
    · rw [if_neg hn]
      exact DensePoly.content_dvd_coeff
        (ZPoly.extractXPower (ZPoly.primitivePart f)).core
        (n - (ZPoly.extractXPower (ZPoly.primitivePart f)).power)
  -- Step 5: content xData.core is non-negative.
  have hcontent_nonneg :
      0 ≤ ZPoly.content (ZPoly.extractXPower (ZPoly.primitivePart f)).core := by
    show 0 ≤ DensePoly.content _
    rw [DensePoly.content]
    exact Int.natCast_nonneg _
  have hd_int :
      ((ZPoly.content (ZPoly.extractXPower (ZPoly.primitivePart f)).core).toNat : Int) =
        ZPoly.content (ZPoly.extractXPower (ZPoly.primitivePart f)).core :=
    Int.toNat_of_nonneg hcontent_nonneg
  have hdvd_d :
      ∀ n,
        ((ZPoly.content
            (ZPoly.extractXPower (ZPoly.primitivePart f)).core).toNat : Int) ∣
          (ZPoly.primitivePart f).coeff n := by
    intro n
    rw [hd_int]
    exact hdvd n
  -- Step 6: apply the nat_eq_one helper.
  have hd_eq :
      (ZPoly.content (ZPoly.extractXPower (ZPoly.primitivePart f)).core).toNat = 1 :=
    DensePoly.nat_eq_one_of_content_eq_one_of_nat_dvd_coeff
      (ZPoly.primitivePart f) _
      (by simpa [ZPoly.content] using hcontent_pf)
      hdvd_d
  show ZPoly.content (ZPoly.extractXPower (ZPoly.primitivePart f)).core = 1
  have hcast :
      ((ZPoly.content (ZPoly.extractXPower (ZPoly.primitivePart f)).core).toNat : Int) =
        (1 : Int) := by exact_mod_cast hd_eq
  rw [hd_int] at hcast
  exact hcast

private theorem firstSome_some
    {α β : Type} {xs : List α} {f : α → Option β} {y : β}
    (h : firstSome xs f = some y) :
    ∃ x, f x = some y := by
  induction xs with
  | nil =>
      simp [firstSome] at h
  | cons x xs ih =>
      unfold firstSome at h
      cases hx : f x with
      | none =>
          simp [hx] at h
          exact ih h
      | some y' =>
          simp [hx] at h
          cases h
          exact ⟨x, hx⟩

private theorem recombinationSearchAux_product
    (target : ZPoly) (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch : recombinationSearchAux target localFactors fuel = some factors) :
    Array.polyProduct factors.toArray = target := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [recombinationSearchAux] at hsearch
  | succ fuel ih =>
      unfold recombinationSearchAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simpa [Array.polyProduct] using htarget.symm
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        cases hquot : exactQuotient? target (Array.polyProduct split.1.toArray) with
        | none =>
            simp [hquot] at hsplit
        | some quotient =>
            simp [hquot] at hsplit
            cases hrec : recombinationSearchAux quotient split.2 fuel with
            | none =>
                simp [hrec] at hsplit
            | some rest =>
                simp [hrec] at hsplit
                cases hsplit
                have hrest :
                    Array.polyProduct rest.toArray = quotient :=
                  ih quotient split.2 rest hrec
                have hquot_prod :
                    quotient * Array.polyProduct split.1.toArray = target :=
                  exactQuotient?_product hquot
                calc
                  Array.polyProduct (Array.polyProduct split.1.toArray :: rest).toArray =
                      Array.polyProduct split.1.toArray * Array.polyProduct rest.toArray := by
                    exact polyProduct_cons_toArray (Array.polyProduct split.1.toArray) rest
                  _ = Array.polyProduct split.1.toArray * quotient := by
                    rw [hrest]
                  _ = quotient * Array.polyProduct split.1.toArray := by
                    rw [DensePoly.mul_comm_poly (S := Int)]
                  _ = target := hquot_prod

/-- A successful exhaustive recombination search preserves the target product. -/
theorem recombinationSearch_product
    (f : ZPoly) (localFactors factors : List ZPoly)
    (hsearch : recombinationSearch f localFactors = some factors) :
    Array.polyProduct factors.toArray = f := by
  exact recombinationSearchAux_product f localFactors factors (localFactors.length + 1) hsearch

private theorem recombinationSearchModAux_product
    (target : ZPoly) (modulus : Nat) (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch : recombinationSearchModAux target modulus localFactors fuel = some factors) :
    Array.polyProduct factors.toArray = target := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [recombinationSearchModAux] at hsearch
  | succ fuel ih =>
      unfold recombinationSearchModAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simpa [Array.polyProduct] using htarget.symm
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        let candidate :=
          ZPoly.primitivePart <|
            centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        cases hquot : exactQuotient? target candidate with
        | none =>
            simp [candidate, hquot] at hsplit
        | some quotient =>
            simp [candidate, hquot] at hsplit
            cases hrec : recombinationSearchModAux quotient modulus split.2 fuel with
            | none =>
                simp [hrec] at hsplit
            | some rest =>
                simp [hrec] at hsplit
                cases hsplit
                have hrest :
                    Array.polyProduct rest.toArray = quotient :=
                  ih quotient split.2 rest hrec
                have hquot_prod : quotient * candidate = target :=
                  exactQuotient?_product hquot
                calc
                  Array.polyProduct (candidate :: rest).toArray =
                      candidate * Array.polyProduct rest.toArray := by
                    exact polyProduct_cons_toArray candidate rest
                  _ = candidate * quotient := by
                    rw [hrest]
                  _ = quotient * candidate := by
                    rw [DensePoly.mul_comm_poly (S := Int)]
                  _ = target := hquot_prod

private theorem recombinationSearchMod_product
    (f : ZPoly) (modulus : Nat) (localFactors factors : List ZPoly)
    (hsearch : recombinationSearchMod f modulus localFactors = some factors) :
    Array.polyProduct factors.toArray = f := by
  exact recombinationSearchModAux_product
    f modulus localFactors factors (localFactors.length + 1) hsearch

private theorem recombineExhaustive_product
    (f : ZPoly) (d : LiftData) (factors : List ZPoly)
    (hsearch :
      recombinationSearchMod f (liftModulus d) d.liftedFactors.toList =
        some factors) :
    Array.polyProduct (recombineExhaustive f d) = f := by
  unfold recombineExhaustive
  simp [hsearch, recombinationSearchMod_product f (liftModulus d)
    d.liftedFactors.toList factors hsearch]

private theorem bhksRecoverClassified_success_product
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (hrecover : bhksRecoverClassified f d = .success candidates) :
    Array.polyProduct candidates = f := by
  rw [bhksRecoverClassified] at hrecover
  by_cases hrows : 1 ≤ (bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount +
      (bhksLatticeBasis f d.p d.k d.liftedFactors).coeffWidth
  · rw [dif_pos hrows] at hrecover
    by_cases hdeg :
        bhksDegenerateIndicatorPartition
          (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows
            (bhksLiftData_latticeBasis_independent f d))
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors)
              hrows (bhksLiftData_latticeBasis_independent f d))) = true
    · simp [hdeg] at hrecover
    · simp only [hdeg, Bool.false_eq_true, if_false] at hrecover
      cases hcand : bhksIndicatorCandidates? f d
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors)
              hrows (bhksLiftData_latticeBasis_independent f d))) with
      | none => simp [hcand] at hrecover
      | some cands =>
          simp only [hcand] at hrecover
          by_cases hprod : Array.polyProduct cands == f
          · simp only [hprod, if_true] at hrecover
            cases hrecover
            simpa [beq_iff_eq] using hprod
          · simp [hprod] at hrecover
  · rw [dif_neg hrows] at hrecover
    simp at hrecover

/-- A successful BHKS recovery call preserves the polynomial product: when
`bhksRecover? f d` returns `some candidates`, the candidates multiply back
to `f` because the executable runs a final `Array.polyProduct candidates == f`
check before reporting success. -/
private theorem bhksRecover?_product
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (hrecover : bhksRecover? f d = some candidates) :
    Array.polyProduct candidates = f := by
  rw [bhksRecover?] at hrecover
  cases hclass : bhksRecoverClassified f d with
  | success cands =>
      simp [BhksRecoveryResult.toOption, hclass] at hrecover
      cases hrecover
      exact bhksRecoverClassified_success_product hclass
  | degenerate =>
      simp [BhksRecoveryResult.toOption, hclass] at hrecover
  | candidateFailure =>
      simp [BhksRecoveryResult.toOption, hclass] at hrecover
  | productMismatch cands =>
      simp [BhksRecoveryResult.toOption, hclass] at hrecover

/-- A successful fixed-precision BHKS fast-recombination loop preserves the
polynomial product: every success branch comes from the classified BHKS
recovery success case, which already certifies `Array.polyProduct = core`. -/
private theorem factorFastCoreWithBound_product
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) :
    ∀ k fuel coreFactors,
      factorFastCoreWithBound core B primeData k fuel = some coreFactors →
        Array.polyProduct coreFactors = core := by
  intro k fuel
  induction fuel generalizing k with
  | zero =>
      intro coreFactors hfast
      simp [factorFastCoreWithBound] at hfast
  | succ fuel ih =>
      intro coreFactors hfast
      rw [factorFastCoreWithBound] at hfast
      cases hclass : bhksRecoverClassified core (henselLiftData core k primeData) with
      | success xs =>
          simp [hclass] at hfast
          cases hfast
          exact bhksRecoverClassified_success_product hclass
      | degenerate =>
          by_cases hk : k ≥ B
          · simp [hclass, hk] at hfast
          · simp [hclass, hk] at hfast
            exact ih _ coreFactors hfast
      | candidateFailure =>
          by_cases hk : k ≥ B
          · simp [hclass, hk] at hfast
          · simp [hclass, hk] at hfast
            exact ih _ coreFactors hfast
      | productMismatch cands =>
          by_cases hk : k ≥ B
          · simp [hclass, hk] at hfast
          · simp [hclass, hk] at hfast
            exact ih _ coreFactors hfast

/-- The exhaustive recombination wrapper preserves the polynomial product
unconditionally: every branch returns either `#[core]` (singleton, trivially
multiplying to `core`) or the result of a successful `recombinationSearchMod`
call (`recombineExhaustive_product`). -/
private theorem exhaustiveCoreFactorsWithBound_product
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) :
    Array.polyProduct (exhaustiveCoreFactorsWithBound core B primeData) = core := by
  rw [exhaustiveCoreFactorsWithBound]
  by_cases hB : B = 0
  · simp [hB, polyProduct_singleton]
  · simp only [hB, if_false]
    by_cases hempty :
        (recombineExhaustive core
            (henselLiftData core (precisionForCoeffBound B primeData.p) primeData)).isEmpty
    · simp [hempty, polyProduct_singleton]
    · simp only [hempty]
      cases hsearch : recombinationSearchMod core
          (liftModulus
            (henselLiftData core (precisionForCoeffBound B primeData.p) primeData))
          (henselLiftData core (precisionForCoeffBound B primeData.p)
            primeData).liftedFactors.toList with
      | none =>
          have hnil :
              recombineExhaustive core
                (henselLiftData core (precisionForCoeffBound B primeData.p)
                  primeData) = #[] := by
            rw [recombineExhaustive]
            simp [hsearch]
          rw [hnil] at hempty
          simp at hempty
      | some xs =>
          exact recombineExhaustive_product core
            (henselLiftData core (precisionForCoeffBound B primeData.p) primeData)
            xs hsearch

/--
A successful integer certificate exposes the per-prime polynomial check fact:
every recorded `PrimeFactorData` block satisfies `checkForPolynomial f` —
admissible prime, positive recorded factor degrees, modular degree-sum and
factor-product alignment, and aligned nested Rabin certificates. Consumers
extract individual conjuncts via the dedicated helpers below.
-/
theorem checkIrreducibleCert_prime_data
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ primeData ∈ cert.perPrime.toList,
      primeData.checkForPolynomial f = true := by
  simp [checkIrreducibleCert] at hcert
  intro primeData hmem
  rw [List.mem_iff_getElem] at hmem
  rcases hmem with ⟨i, hi, hget⟩
  have hiArray : i < cert.perPrime.size := by
    simpa using hi
  have hgetArray : cert.perPrime[i] = primeData := by
    simpa [Array.getElem_toList] using hget
  simpa [hgetArray] using hcert.1 i hiArray

/--
A successful integer certificate exposes the per-prime good-prime fact: every
recorded `PrimeFactorData` uses an admissible prime for `f` (size, leading
coefficient, and modular square-freeness all satisfied).
-/
theorem checkIrreducibleCert_isGoodPrime
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ primeData ∈ cert.perPrime.toList,
      letI := primeData.bounds
      isGoodPrime f primeData.p = true := by
  intro primeData hmem
  have hcheck := checkIrreducibleCert_prime_data f cert hcert primeData hmem
  simp [PrimeFactorData.checkForPolynomial] at hcheck
  exact hcheck.1.1.1.1

/--
A successful integer certificate exposes positivity of every recorded modular
factor degree: each per-prime block's `factorDegrees` array contains only
positive entries.
-/
theorem checkIrreducibleCert_factorDegrees_positive
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ primeData ∈ cert.perPrime.toList,
      ∀ (i : Nat) (hi : i < primeData.factorDegrees.size),
        0 < primeData.factorDegrees[i] := by
  intro primeData hmem
  have hcheck := checkIrreducibleCert_prime_data f cert hcert primeData hmem
  simp [PrimeFactorData.checkForPolynomial] at hcheck
  exact hcheck.1.1.1.2

/--
A successful integer certificate exposes the per-prime modular degree-sum
alignment: each block's recorded `degreeSum` equals the degree of the
polynomial's modular image.
-/
theorem checkIrreducibleCert_degreeSum_eq
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ primeData ∈ cert.perPrime.toList,
      letI := primeData.bounds
      primeData.degreeSum = (ZPoly.modP primeData.p f).degree?.getD 0 := by
  intro primeData hmem
  have hcheck := checkIrreducibleCert_prime_data f cert hcert primeData hmem
  simp [PrimeFactorData.checkForPolynomial] at hcheck
  exact hcheck.1.1.2

/--
A successful integer certificate exposes the per-prime modular factor product
alignment: each block's recorded `factorProduct` equals the polynomial's
modular image.
-/
theorem checkIrreducibleCert_factorProduct_eq
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ primeData ∈ cert.perPrime.toList,
      letI := primeData.bounds
      primeData.factorProduct = ZPoly.modP primeData.p f := by
  intro primeData hmem
  have hcheck := checkIrreducibleCert_prime_data f cert hcert primeData hmem
  simp [PrimeFactorData.checkForPolynomial] at hcheck
  exact hcheck.1.2

/--
A successful integer certificate exposes the per-prime nested Rabin checks:
`checkFactorCerts` validates the concrete modular factor array, the recorded
degrees, and the upstream `Berlekamp.checkIrreducibilityCertificate` result for
each aligned entry.
-/
theorem checkIrreducibleCert_certificate_alignment
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ primeData ∈ cert.perPrime.toList,
      primeData.checkFactorCerts = true := by
  intro primeData hmem
  have hcheck := checkIrreducibleCert_prime_data f cert hcert primeData hmem
  simp [PrimeFactorData.checkForPolynomial] at hcheck
  exact hcheck.2

/--
A successful integer certificate satisfies the top-level degree-obstruction
check: every recorded `DegreeObstruction` is valid for the certificate, and
every nontrivial candidate factor degree of `f` has at least one obstruction.
-/
theorem checkIrreducibleCert_degree_obstructions
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    cert.checkDegreeObstructions f = true := by
  simp [checkIrreducibleCert] at hcert
  exact hcert.2

/--
A successful integer certificate provides a valid obstruction for every
nontrivial candidate factor degree of `f` (the degrees `1, …, (deg f) / 2`),
ruling out an integer factorization at any of those degrees.
-/
theorem checkIrreducibleCert_obstructs_candidate_degrees
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ targetDegree ∈ ZPolyIrreducibilityCertificate.candidateFactorDegrees f,
      cert.hasObstructionFor f targetDegree = true := by
  intro targetDegree hmem
  have hobs := checkIrreducibleCert_degree_obstructions f cert hcert
  simp [ZPolyIrreducibilityCertificate.checkDegreeObstructions] at hobs
  exact hobs.2 targetDegree hmem

/--
A valid `DegreeObstruction` exposes the underlying no-subset-sum fact: the
referenced per-prime block has no subset of its modular factor degrees summing
to the obstruction's `targetDegree`.
-/
theorem degreeObstruction_no_subset_degree
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (obs : DegreeObstruction) (primeData : PrimeFactorData)
    (hobs : obs.checkForCertificate f cert = true)
    (hprime : cert.primeDataAt? obs.primeIndex = some primeData) :
    primeData.hasSubsetDegree obs.targetDegree = false := by
  simp [DegreeObstruction.checkForCertificate, hprime] at hobs
  exact hobs.2

end Hex
