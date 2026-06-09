import HexArith.Nat.Prime
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

/--
Executable test that a field-polynomial gcd is a unit.

`DensePoly.gcd` is the raw Euclidean representative, so over a field it may be
any nonzero constant associate of `1`.  In normalized dense representation,
nonzero constants are exactly the polynomials with one stored coefficient.
-/
def gcdIsUnit {R : Type u} [Zero R] [DecidableEq R]
    (g : DensePoly R) : Bool :=
  g.size == 1

/-- The modular image is square-free according to the executable gcd-unit criterion. -/
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

/-- Thin adapter promoting a `Nat.Prime p` witness to the shared
`Lean.Grind.Field (ZMod64 p)` instance via `ZMod64.primeModulusOfPrime`. -/
@[reducible]
private def fieldOfNatPrime {p : Nat} [ZMod64.Bounds p] (hp : Nat.Prime p) :
    Lean.Grind.Field (ZMod64 p) :=
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  inferInstance

private structure SmallPrimeCandidate where
  p : Nat
  [bounds : ZMod64.Bounds p]
  prime : Nat.Prime p

/-- A scored admissible small-prime candidate for default prime selection. -/
structure PrimeCandidateScore where
  /-- Candidate prime. -/
  p : Nat
  /-- Smaller scores are preferred; equal scores retain the earlier smaller prime. -/
  factorCount : Nat

private def smallPrimeCandidates : List SmallPrimeCandidate :=
  [ { p := 3, bounds := bounds_three, prime := prime_three },
    { p := 5, bounds := bounds_five, prime := prime_five },
    { p := 7, bounds := bounds_seven, prime := prime_seven },
    { p := 11, bounds := bounds_eleven, prime := prime_eleven },
    { p := 13, bounds := bounds_thirteen, prime := prime_thirteen },
    { p := 17, bounds := bounds_seventeen, prime := prime_seventeen },
    { p := 19, bounds := bounds_nineteen, prime := prime_nineteen },
    { p := 23, bounds := bounds_twenty_three, prime := prime_twenty_three },
    { p := 31, bounds := bounds_thirty_one, prime := prime_thirty_one },
    { p := 71, bounds := bounds_seventy_one, prime := prime_seventy_one } ]

/--
Coerce an admissible nonzero modular image to its monic representative by
dividing by its leading coefficient.  `monicModularImage f = scale c⁻¹ f`
where `c = leadingCoeff f`; the zero branch is a placeholder used to keep
the function total.
-/
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
  rw [DensePoly.leadingCoeff_eq_coeff_last (1 : FpPoly p) (by omega)]
  rw [hsize]
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
      rw [Hex.Berlekamp.factorProduct_cons, Hex.Berlekamp.factorProduct_cons]
      rw [ih_eq]
      rw [monicModularImage_mul_of_nonzero hp hhead_ne htail_prod_ne]

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
        unfold DensePoly.leadingCoeff
        rw [Array.back?_eq_getElem?]
        simp [hcoeffs_zero]
      unfold ZPoly.leadingCoeffModP
      rw [hlead]
      show (ZMod64.ofNat p (ZPoly.intModNat 0 p) : ZMod64 p) = 0
      rfl
    · exact hfsize
  have hcoeff_ne : (ZPoly.modP p f).coeff (f.size - 1) ≠ 0 := by
    rw [ZPoly.coeff_modP]
    rw [← DensePoly.leadingCoeff_eq_coeff_last f hfsize]
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
      unfold DensePoly.leadingCoeff
      rw [Array.back?_eq_getElem?]
      simp [hcoeffs_zero]
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
  rw [ZPoly.coeff_modP]
  rw [← DensePoly.leadingCoeff_eq_coeff_last f hfsize]
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
  rw [DensePoly.leadingCoeff_eq_coeff_last _ hmod_size_pos]
  rw [hsize]
  exact coeff_modP_top_eq_leadingCoeffModP f p hfsize

/-- `ZPoly.modP p` never increases the executable dense size: the
coefficientwise reduction maps into a length-`f.size` coefficient list, which
`FpPoly.ofCoeffs` then trims of trailing zeros. -/
private theorem size_modP_le (p : Nat) [ZMod64.Bounds p] (f : ZPoly) :
    (ZPoly.modP p f).size ≤ f.size := by
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

/--
Data produced by modular prime selection: the selected prime, the image of the
input polynomial over that prime field, and its modular factors.
-/
structure PrimeChoiceData where
  p : Nat
  [bounds : ZMod64.Bounds p]
  fModP : FpPoly p
  factorsModP : Array (FpPoly p)

instance : Inhabited PrimeChoiceData where
  default :=
    { p := 3
      bounds := bounds_three
      fModP := 0
      factorsModP := #[] }

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

namespace ZPoly

/--
Executable data for the integer scaling transform that sends a primitive
positive-leading core to a monic integer polynomial with the same roots
(scaled by the leading coefficient).

If `core` has degree `n` and leading coefficient `c`, `monic` is the
coefficientwise integer polynomial `c^(n-1) * core (X / c)`: lower coefficient
`a_i` becomes `a_i * c^(n-1-i)` and the leading coefficient is normalised to
`1`.
-/
structure ToMonicData where
  core : ZPoly
  leadingCoeff : Int
  degree : Nat
  monic : ZPoly

namespace ToMonicData

private def transformedCoeffs (core : ZPoly) (degree : Nat) : Array Int :=
  ((List.range degree).map fun i =>
      core.coeff i * (DensePoly.leadingCoeff core) ^ (degree - 1 - i)).toArray.push 1

private def transformedCore (core : ZPoly) (degree : Nat) : ZPoly :=
  { coeffs := transformedCoeffs core degree
    normalized := by
      right
      change (transformedCoeffs core degree).back? ≠ some (0 : Int)
      simp [transformedCoeffs] }

@[simp] theorem transformedCoeffs_size (core : ZPoly) (degree : Nat) :
    (transformedCoeffs core degree).size = degree + 1 := by
  simp [transformedCoeffs]

@[simp] theorem transformedCoeffs_getD_top (core : ZPoly) (degree : Nat) :
    (transformedCoeffs core degree).getD degree 0 = 1 := by
  simp [transformedCoeffs]

@[simp] theorem transformedCore_size (core : ZPoly) (degree : Nat) :
    (transformedCore core degree).size = degree + 1 := by
  simp [transformedCore, DensePoly.size]

theorem transformedCore_coeff_top (core : ZPoly) (degree : Nat) :
    (transformedCore core degree).coeff degree = 1 := by
  change (transformedCoeffs core degree).getD degree (0 : Int) = 1
  exact transformedCoeffs_getD_top core degree

theorem transformedCore_monic (core : ZPoly) (degree : Nat) :
    DensePoly.Monic (transformedCore core degree) := by
  unfold DensePoly.Monic DensePoly.leadingCoeff transformedCore
  simp [transformedCoeffs]

@[simp] theorem transformedCore_degree_getD (core : ZPoly) (degree : Nat) :
    (transformedCore core degree).degree?.getD 0 = degree := by
  unfold DensePoly.degree? transformedCore DensePoly.size
  simp [transformedCoeffs]

end ToMonicData

/-- Build the `ToMonicData` packet for a core by the integer scaling transform. -/
def toMonic (core : ZPoly) : ToMonicData :=
  let degree := core.degree?.getD 0
  { core
    leadingCoeff := DensePoly.leadingCoeff core
    degree
    monic :=
      if DensePoly.leadingCoeff core = 1 then
        core
      else
        ToMonicData.transformedCore core degree }

@[simp] theorem toMonic_core (core : ZPoly) :
    (toMonic core).core = core := rfl

@[simp] theorem toMonic_leadingCoeff (core : ZPoly) :
    (toMonic core).leadingCoeff = DensePoly.leadingCoeff core := rfl

@[simp] theorem toMonic_degree (core : ZPoly) :
    (toMonic core).degree = core.degree?.getD 0 := rfl

/-- The `monic` field of `toMonic core` is monic once the source has positive
degree. -/
theorem toMonic_monic_isMonic_of_pos_degree
    (core : ZPoly) (_hpos_lc : 0 < DensePoly.leadingCoeff core)
    (_hdegree : 0 < (toMonic core).degree) :
    DensePoly.Monic (toMonic core).monic := by
  unfold toMonic
  by_cases hmonic : DensePoly.leadingCoeff core = 1
  · simp [hmonic, DensePoly.Monic]
  · simp [hmonic, ToMonicData.transformedCore_monic]

/-- The `monic` field preserves the recorded degree in nonconstant cases. -/
theorem toMonic_monic_degree_eq_of_pos_degree
    (core : ZPoly) (_hpos_lc : 0 < DensePoly.leadingCoeff core)
    (_hdegree : 0 < (toMonic core).degree) :
    (toMonic core).monic.degree?.getD 0 = (toMonic core).degree := by
  unfold toMonic
  by_cases hmonic : DensePoly.leadingCoeff core = 1
  · simp [hmonic]
  · simp [hmonic]

/-- Applying `toMonic` to an already-monic core leaves its `monic` field equal
to the original. -/
theorem toMonic_monic_eq_core_of_leadingCoeff_eq_one
    (core : ZPoly) (hmonic : DensePoly.leadingCoeff core = 1) :
    (toMonic core).monic = core := by
  simp [toMonic, hmonic]

private def toMonicGuardMonic : ToMonicData :=
  toMonic (DensePoly.ofCoeffs #[1, 3, 1])

#guard toMonicGuardMonic.monic = toMonicGuardMonic.core

private def toMonicGuardQuadratic : ToMonicData :=
  toMonic (DensePoly.ofCoeffs #[1, 3, 2])

#guard toMonicGuardQuadratic.degree = 2
#guard toMonicGuardQuadratic.leadingCoeff = 2
#guard toMonicGuardQuadratic.monic = DensePoly.ofCoeffs #[2, 3, 1]

private def toMonicGuardZero : ToMonicData :=
  toMonic 0

#guard toMonicGuardZero.degree = 0
#guard toMonicGuardZero.monic = DensePoly.ofCoeffs #[1]

end ZPoly

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

/-- Normalize a polynomial factor's sign by negating it whenever the leading
coefficient is negative.  The result has nonnegative leading coefficient and is
associated to the input over `ℤ`. -/
def normalizeFactorSign (f : ZPoly) : ZPoly :=
  if DensePoly.leadingCoeff f < 0 then
    DensePoly.scale (-1 : Int) f
  else
    f

/-- A polynomial factor is recorded by the factorization routines only
when it is not zero and not a unit (`±1`).  Exposed publicly so that
Mathlib-side lemmas can transport the predicate into `¬ IsUnit` over
`Polynomial ℤ`. -/
def shouldRecordPolynomialFactor (f : ZPoly) : Bool :=
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

/--
Exact-division check on integer polynomials: returns the quotient when
`quot * candidate = target` exactly, and rejects unit candidates so iterated
calls cannot loop forever on `±1`.
-/
def exactQuotient? (target candidate : ZPoly) : Option ZPoly :=
  if candidate.isZero || candidate = 1 then
    none
  else
    let qr := DensePoly.divMod target candidate
    if qr.2 = 0 && qr.1 * candidate == target then
      some qr.1
    else
      none

/-- Successful exact-division extracts a multiplication witness:
`exactQuotient? target candidate = some quotient` implies
`quotient * candidate = target`. Forward companion of
`exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree`. -/
theorem exactQuotient?_product
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

/--
Greedy peel of `candidate^?` out of `target` via repeated exact division.
Returns `(residual, multiplicity)` with the invariant
`candidate ^ multiplicity * residual = target`. The recursion is bounded by
`fuel`, which the caller chooses based on the source degree.
-/
private def consumeExactPower (target candidate : ZPoly) : Nat → ZPoly × Nat
  | 0 => (target, 0)
  | fuel + 1 =>
      match exactQuotient? target candidate with
      | some quot =>
          let (residual, m) := consumeExactPower quot candidate fuel
          (residual, m + 1)
      | none => (target, 0)

/--
Fold `consumeExactPower` over a list of candidate factors, accumulating
emitted copies and tracking the residual that has not yet been factored.
Invariant: `polyProduct emitted * residual = initialRepeatedPart`.
-/
private def expandRepeatedPartFactorsAux : List ZPoly → ZPoly → Nat → Array ZPoly × ZPoly
  | [], rp, _ => (#[], rp)
  | q :: qs, rp, fuel =>
      let (rp', m) := consumeExactPower rp q fuel
      let (rest, residual) := expandRepeatedPartFactorsAux qs rp' fuel
      ((List.replicate m q).toArray ++ rest, residual)

/--
Compute `(emitted, residual)` where each candidate factor `q` from
`coreFactors` appears in `emitted` to the maximum multiplicity such that
`q^k` exactly divides the running repeated-part. The fuel is the source
size, which dominates any irreducible's multiplicity in `repeatedPart`.
-/
private def expandRepeatedPartFactorArray (rp : ZPoly) (coreFactors : Array ZPoly) :
    Array ZPoly × ZPoly :=
  expandRepeatedPartFactorsAux coreFactors.toList rp (rp.size + 1)

/--
Reassemble normalization-prefix and square-free factors around the supplied
core factors, expanding each core factor `q` to its multiplicity in
`d.repeatedPart` so the recorded `Factorization` carries the right exponents
for higher-multiplicity inputs. Falls back to the un-expanded
`polynomialNormalizationPrefixFactors` shape when the expansion does not
fully consume `repeatedPart` (e.g. when the BZ pipeline emitted the raw
square-free core as a single core factor).
-/
private def reassemblePolynomialFactors
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) : Array ZPoly :=
  let (expanded, residual) := expandRepeatedPartFactorArray d.repeatedPart coreFactors
  if residual = 1 then
    xPowerFactorArray d.xPower ++ expanded ++ coreFactors
  else
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

def hasSubsetDegreeAux : List Nat → Nat → Bool
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

private def choosePrimeDataScoreStep
    (f : ZPoly) (best : Option PrimeChoiceDataScore) (c : SmallPrimeCandidate) :
    Option PrimeChoiceDataScore :=
  match best, primeChoiceDataScore f c with
  | none, score => score
  | some old, none => some old
  | some old, some new => some (betterPrimeChoiceDataScore old new)

private theorem primeChoiceDataScore_prime
    (f : ZPoly) (c : SmallPrimeCandidate) (score : PrimeChoiceDataScore)
    (hscore : primeChoiceDataScore f c = some score) :
    Nat.Prime score.data.p := by
  unfold primeChoiceDataScore at hscore
  letI := c.bounds
  by_cases hgood : isGoodPrime f c.p
  · simp [hgood] at hscore
    cases hscore
    exact c.prime
  · simp [hgood] at hscore

private theorem primeChoiceDataScore_fModP_eq
    (f : ZPoly) (c : SmallPrimeCandidate) (score : PrimeChoiceDataScore)
    (hscore : primeChoiceDataScore f c = some score) :
    score.data.fModP =
      @ZPoly.modP score.data.p score.data.bounds f := by
  unfold primeChoiceDataScore at hscore
  letI := c.bounds
  by_cases hgood : isGoodPrime f c.p
  · simp [hgood] at hscore
    cases hscore
    rfl
  · simp [hgood] at hscore

private theorem betterPrimeChoiceDataScore_prime
    (old new score : PrimeChoiceDataScore)
    (hold : Nat.Prime old.data.p)
    (hnew : Nat.Prime new.data.p)
    (hscore : betterPrimeChoiceDataScore old new = score) :
    Nat.Prime score.data.p := by
  unfold betterPrimeChoiceDataScore at hscore
  split at hscore
  · cases hscore
    exact hnew
  · cases hscore
    exact hold

private theorem betterPrimeChoiceDataScore_fModP_eq
    (f : ZPoly) (old new score : PrimeChoiceDataScore)
    (hold :
      old.data.fModP =
        @ZPoly.modP old.data.p old.data.bounds f)
    (hnew :
      new.data.fModP =
        @ZPoly.modP new.data.p new.data.bounds f)
    (hscore : betterPrimeChoiceDataScore old new = score) :
    score.data.fModP =
      @ZPoly.modP score.data.p score.data.bounds f := by
  unfold betterPrimeChoiceDataScore at hscore
  split at hscore
  · cases hscore
    exact hnew
  · cases hscore
    exact hold

private theorem choosePrimeDataScoreStep_prime
    (f : ZPoly) (best : Option PrimeChoiceDataScore) (c : SmallPrimeCandidate)
    (score : PrimeChoiceDataScore)
    (hbest : ∀ old, best = some old → Nat.Prime old.data.p)
    (hscore : choosePrimeDataScoreStep f best c = some score) :
    Nat.Prime score.data.p := by
  unfold choosePrimeDataScoreStep at hscore
  cases hbest_eq : best with
  | none =>
      cases hc_eq : primeChoiceDataScore f c with
      | none =>
          simp [hbest_eq, hc_eq] at hscore
      | some new =>
          simp [hbest_eq, hc_eq] at hscore
          have hnew := primeChoiceDataScore_prime f c new hc_eq
          simpa [hscore] using hnew
  | some old =>
      cases hc_eq : primeChoiceDataScore f c with
      | none =>
          simp [hbest_eq, hc_eq] at hscore
          have hold := hbest old hbest_eq
          simpa [hscore] using hold
      | some new =>
          simp [hbest_eq, hc_eq] at hscore
          exact betterPrimeChoiceDataScore_prime old new score
            (hbest old hbest_eq)
            (primeChoiceDataScore_prime f c new hc_eq)
            hscore

private theorem choosePrimeDataScoreStep_fModP_eq
    (f : ZPoly) (best : Option PrimeChoiceDataScore) (c : SmallPrimeCandidate)
    (score : PrimeChoiceDataScore)
    (hbest : ∀ old, best = some old →
      old.data.fModP =
        @ZPoly.modP old.data.p old.data.bounds f)
    (hscore : choosePrimeDataScoreStep f best c = some score) :
    score.data.fModP =
      @ZPoly.modP score.data.p score.data.bounds f := by
  unfold choosePrimeDataScoreStep at hscore
  cases hbest_eq : best with
  | none =>
      cases hc_eq : primeChoiceDataScore f c with
      | none =>
          simp [hbest_eq, hc_eq] at hscore
      | some new =>
          simp [hbest_eq, hc_eq] at hscore
          have hnew := primeChoiceDataScore_fModP_eq f c new hc_eq
          subst score
          exact hnew
  | some old =>
      cases hc_eq : primeChoiceDataScore f c with
      | none =>
          simp [hbest_eq, hc_eq] at hscore
          have hold := hbest old hbest_eq
          subst score
          exact hold
      | some new =>
          simp [hbest_eq, hc_eq] at hscore
          exact betterPrimeChoiceDataScore_fModP_eq f old new score
            (hbest old hbest_eq)
            (primeChoiceDataScore_fModP_eq f c new hc_eq)
            hscore

private theorem choosePrimeDataScore_fold_prime
    (f : ZPoly) (candidates : List SmallPrimeCandidate)
    (best : Option PrimeChoiceDataScore) (score : PrimeChoiceDataScore)
    (hbest : ∀ old, best = some old → Nat.Prime old.data.p)
    (hscore :
      candidates.foldl (choosePrimeDataScoreStep f) best = some score) :
    Nat.Prime score.data.p := by
  induction candidates generalizing best with
  | nil =>
      exact hbest score hscore
  | cons c candidates ih =>
      exact ih (choosePrimeDataScoreStep f best c)
        (fun old hold =>
          choosePrimeDataScoreStep_prime f best c old hbest hold)
        hscore

private theorem choosePrimeDataScore_fold_fModP_eq
    (f : ZPoly) (candidates : List SmallPrimeCandidate)
    (best : Option PrimeChoiceDataScore) (score : PrimeChoiceDataScore)
    (hbest : ∀ old, best = some old →
      old.data.fModP =
        @ZPoly.modP old.data.p old.data.bounds f)
    (hscore :
      candidates.foldl (choosePrimeDataScoreStep f) best = some score) :
    score.data.fModP =
      @ZPoly.modP score.data.p score.data.bounds f := by
  induction candidates generalizing best with
  | nil =>
      exact hbest score hscore
  | cons c candidates ih =>
      exact ih (choosePrimeDataScoreStep f best c)
        (fun old hold =>
          choosePrimeDataScoreStep_fModP_eq f best c old hbest hold)
        hscore

private theorem primeChoiceDataScore_isGoodPrime
    (f : ZPoly) (c : SmallPrimeCandidate) (score : PrimeChoiceDataScore)
    (hscore : primeChoiceDataScore f c = some score) :
    @isGoodPrime f score.data.p score.data.bounds = true := by
  unfold primeChoiceDataScore at hscore
  letI := c.bounds
  by_cases hgood : isGoodPrime f c.p
  · simp [hgood] at hscore
    cases hscore
    exact hgood
  · simp [hgood] at hscore

private theorem betterPrimeChoiceDataScore_isGoodPrime
    (f : ZPoly) (old new score : PrimeChoiceDataScore)
    (hold : @isGoodPrime f old.data.p old.data.bounds = true)
    (hnew : @isGoodPrime f new.data.p new.data.bounds = true)
    (hscore : betterPrimeChoiceDataScore old new = score) :
    @isGoodPrime f score.data.p score.data.bounds = true := by
  unfold betterPrimeChoiceDataScore at hscore
  split at hscore
  · cases hscore
    exact hnew
  · cases hscore
    exact hold

private theorem choosePrimeDataScoreStep_isGoodPrime
    (f : ZPoly) (best : Option PrimeChoiceDataScore) (c : SmallPrimeCandidate)
    (score : PrimeChoiceDataScore)
    (hbest : ∀ old, best = some old →
      @isGoodPrime f old.data.p old.data.bounds = true)
    (hscore : choosePrimeDataScoreStep f best c = some score) :
    @isGoodPrime f score.data.p score.data.bounds = true := by
  unfold choosePrimeDataScoreStep at hscore
  cases hbest_eq : best with
  | none =>
      cases hc_eq : primeChoiceDataScore f c with
      | none =>
          simp [hbest_eq, hc_eq] at hscore
      | some new =>
          simp [hbest_eq, hc_eq] at hscore
          have hnew := primeChoiceDataScore_isGoodPrime f c new hc_eq
          simpa [hscore] using hnew
  | some old =>
      cases hc_eq : primeChoiceDataScore f c with
      | none =>
          simp [hbest_eq, hc_eq] at hscore
          have hold := hbest old hbest_eq
          simpa [hscore] using hold
      | some new =>
          simp [hbest_eq, hc_eq] at hscore
          exact betterPrimeChoiceDataScore_isGoodPrime f old new score
            (hbest old hbest_eq)
            (primeChoiceDataScore_isGoodPrime f c new hc_eq)
            hscore

private theorem choosePrimeDataScore_fold_isGoodPrime
    (f : ZPoly) (candidates : List SmallPrimeCandidate)
    (best : Option PrimeChoiceDataScore) (score : PrimeChoiceDataScore)
    (hbest : ∀ old, best = some old →
      @isGoodPrime f old.data.p old.data.bounds = true)
    (hscore :
      candidates.foldl (choosePrimeDataScoreStep f) best = some score) :
    @isGoodPrime f score.data.p score.data.bounds = true := by
  induction candidates generalizing best with
  | nil =>
      exact hbest score hscore
  | cons c candidates ih =>
      exact ih (choosePrimeDataScoreStep f best c)
        (fun old hold =>
          choosePrimeDataScoreStep_isGoodPrime f best c old hbest hold)
        hscore

/--
Build a `SmallPrimeCandidate` from an arbitrary natural number `p` if
`p` passes the executable trial-division primality test and fits in one
machine word. Used by the post-prefix prime walk to produce candidates beyond
the fixed `smallPrimeCandidates` list with explicit primality and
`ZMod64.Bounds` evidence.
-/
private def mkExtendedSmallPrimeCandidate? (p : Nat) :
    Option SmallPrimeCandidate :=
  if hprime : Hex.Nat.isPrimeTrial p = true then
    if hbound : p ≤ UInt64.word then
      let prime := Hex.Nat.isPrimeTrial_isPrime hprime
      let bounds : ZMod64.Bounds p := { pPos := prime.pos, pLeR := hbound }
      some { p, bounds, prime }
    else
      none
  else
    none

/--
Input-dependent fuel for the post-prefix prime walk.

The small-prime prefix remains fixed for stable tie-breaking, but the fallback
walk is no longer a closed candidate set: larger coefficients give the trial
walk more room before the `Option` boundary reports `none`. The Mathlib-side D2
leaf theorem will prove this fuel is sufficient on primitive square-free inputs;
at this executable layer it is just the structurally recursive bound.
-/
private def choosePrimeDataWalkFuel (f : ZPoly) : Nat :=
  max 256 <| f.toArray.foldl (fun acc coeff => acc + coeff.natAbs) (2 * f.size + 1)

/--
Walk odd natural candidates starting at `start`, using `isPrimeTrial` to build
candidate records and stopping at the first good prime. The `fuel` argument is
only the Lean termination measure; callers choose it as a function of the input
polynomial.
-/
private def choosePrimeDataWalk? (f : ZPoly) : Nat → Nat → Option PrimeChoiceDataScore
  | _, 0 => none
  | start, fuel + 1 =>
      match mkExtendedSmallPrimeCandidate? start with
      | some c =>
          match primeChoiceDataScore f c with
          | some score => some score
          | none => choosePrimeDataWalk? f (start + 2) fuel
      | none => choosePrimeDataWalk? f (start + 2) fuel

private theorem choosePrimeDataWalk?_prime
    (f : ZPoly) (start fuel : Nat) (score : PrimeChoiceDataScore)
    (hscore : choosePrimeDataWalk? f start fuel = some score) :
    Nat.Prime score.data.p := by
  induction fuel generalizing start with
  | zero =>
      simp [choosePrimeDataWalk?] at hscore
  | succ fuel ih =>
      unfold choosePrimeDataWalk? at hscore
      cases hc : mkExtendedSmallPrimeCandidate? start with
      | none =>
          simp [hc] at hscore
          exact ih (start + 2) hscore
      | some c =>
          cases hs : primeChoiceDataScore f c with
          | none =>
              simp [hc, hs] at hscore
              exact ih (start + 2) hscore
          | some currentScore =>
              simp [hc, hs] at hscore
              cases hscore
              exact primeChoiceDataScore_prime f c score hs

private theorem choosePrimeDataWalk?_fModP_eq
    (f : ZPoly) (start fuel : Nat) (score : PrimeChoiceDataScore)
    (hscore : choosePrimeDataWalk? f start fuel = some score) :
    score.data.fModP =
      @ZPoly.modP score.data.p score.data.bounds f := by
  induction fuel generalizing start with
  | zero =>
      simp [choosePrimeDataWalk?] at hscore
  | succ fuel ih =>
      unfold choosePrimeDataWalk? at hscore
      cases hc : mkExtendedSmallPrimeCandidate? start with
      | none =>
          simp [hc] at hscore
          exact ih (start + 2) hscore
      | some c =>
          cases hs : primeChoiceDataScore f c with
          | none =>
              simp [hc, hs] at hscore
              exact ih (start + 2) hscore
          | some currentScore =>
              simp [hc, hs] at hscore
              cases hscore
              exact primeChoiceDataScore_fModP_eq f c score hs

private theorem choosePrimeDataWalk?_isGoodPrime
    (f : ZPoly) (start fuel : Nat) (score : PrimeChoiceDataScore)
    (hscore : choosePrimeDataWalk? f start fuel = some score) :
    @isGoodPrime f score.data.p score.data.bounds = true := by
  induction fuel generalizing start with
  | zero =>
      simp [choosePrimeDataWalk?] at hscore
  | succ fuel ih =>
      unfold choosePrimeDataWalk? at hscore
      cases hc : mkExtendedSmallPrimeCandidate? start with
      | none =>
          simp [hc] at hscore
          exact ih (start + 2) hscore
      | some c =>
          cases hs : primeChoiceDataScore f c with
          | none =>
              simp [hc, hs] at hscore
              exact ih (start + 2) hscore
          | some currentScore =>
              simp [hc, hs] at hscore
              cases hscore
              exact primeChoiceDataScore_isGoodPrime f c score hs

/--
Optional prime selection: returns `some` with the chosen `PrimeChoiceData` when
the executable walk finds a good prime for `f`, and `none` otherwise.

The search first folds `choosePrimeDataScoreStep` over the deterministic
small-prime prefix. If that prefix selects an admissible prime, the original
tie-breaking is preserved. If the prefix exhausts without selecting any prime,
the search continues with a `Nat`-indexed odd-candidate walk using
`Hex.Nat.isPrimeTrial`; the walk fuel is derived from `f`, so the runtime
candidate set is not the old closed fixed list.
-/
def choosePrimeData? (f : ZPoly) : Option PrimeChoiceData :=
  match smallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
  | some score => some score.data
  | none =>
      choosePrimeDataWalk? f 73 (choosePrimeDataWalkFuel f)
      |>.map (fun score => score.data)

/--
Choose an admissible small prime and package the modular image together with
its Berlekamp irreducible factor data for the rest of the pipeline.

The returned record stores the selected prime's `ZMod64.Bounds` instance, so
callers can consume `fModP` and `factorsModP` directly without re-running the
prime search or reconstructing typeclass evidence.

This total wrapper is retained for compatibility with existing total slow-path
statements. It fails through `Option.get!` when no admissible prime is selected;
new call sites that require an actual selected prime should use
`choosePrimeData?` directly and carry the local `some` witness.
-/
def choosePrimeData (f : ZPoly) : PrimeChoiceData :=
  (choosePrimeData? f).get!

theorem choosePrimeData_eq_of_choosePrimeData?_some
    {f : ZPoly} {data : PrimeChoiceData}
    (hdata : choosePrimeData? f = some data) :
    choosePrimeData f = data := by
  simp [choosePrimeData, hdata]

theorem choosePrimeData?_prime
    (f : ZPoly) (data : PrimeChoiceData)
    (hdata : choosePrimeData? f = some data) :
    Nat.Prime data.p := by
  unfold choosePrimeData? at hdata
  cases hscore :
      smallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
  | some score =>
      simp [hscore] at hdata
      cases hdata
      exact choosePrimeDataScore_fold_prime f smallPrimeCandidates none score
        (by intro old hnone; cases hnone)
        hscore
  | none =>
      simp [hscore] at hdata
      cases hext :
          choosePrimeDataWalk? f 73 (choosePrimeDataWalkFuel f) with
      | none =>
          simp [hext] at hdata
      | some escore =>
          simp [hext] at hdata
          cases hdata
          exact choosePrimeDataWalk?_prime f 73 (choosePrimeDataWalkFuel f)
            escore hext

theorem choosePrimeData?_fModP_eq
    (f : ZPoly) (data : PrimeChoiceData)
    (hdata : choosePrimeData? f = some data) :
    data.fModP = @ZPoly.modP data.p data.bounds f := by
  unfold choosePrimeData? at hdata
  cases hscore :
      smallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
  | some score =>
      simp [hscore] at hdata
      cases hdata
      exact choosePrimeDataScore_fold_fModP_eq f smallPrimeCandidates none score
        (by intro old hnone; cases hnone)
        hscore
  | none =>
      simp [hscore] at hdata
      cases hext :
          choosePrimeDataWalk? f 73 (choosePrimeDataWalkFuel f) with
      | none =>
          simp [hext] at hdata
      | some escore =>
          simp [hext] at hdata
          cases hdata
          exact choosePrimeDataWalk?_fModP_eq f 73 (choosePrimeDataWalkFuel f)
            escore hext

/--
When `choosePrimeData? f` succeeds, the selected prime is a good prime for `f`
in the executable sense (modulus at least three, leading coefficient survives
reduction, modular image is square-free).
-/
theorem choosePrimeData?_isGoodPrime
    (f : ZPoly) (data : PrimeChoiceData)
    (hdata : choosePrimeData? f = some data) :
    @isGoodPrime f data.p data.bounds = true := by
  unfold choosePrimeData? at hdata
  cases hscore :
      smallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
  | some score =>
      simp [hscore] at hdata
      cases hdata
      exact choosePrimeDataScore_fold_isGoodPrime f smallPrimeCandidates none score
        (by intro old hnone; cases hnone)
        hscore
  | none =>
      simp [hscore] at hdata
      cases hext :
          choosePrimeDataWalk? f 73 (choosePrimeDataWalkFuel f) with
      | none =>
          simp [hext] at hdata
      | some escore =>
          simp [hext] at hdata
          cases hdata
          exact choosePrimeDataWalk?_isGoodPrime f 73 (choosePrimeDataWalkFuel f)
            escore hext

/--
Invariant capturing that `data.factorsModP` is exactly the Berlekamp factor
output for the monic modular image used by prime selection.  Phrased as an
existential bundling the prime witness and the nonzero-image proof so that
it threads through the executable prime-selection fold; the `Lean.Grind.Field`
instance required by `Berlekamp.berlekampFactor` is constructed explicitly
from `hprime`, so callers can match it against any field instance built from
the same prime witness via proof irrelevance of `ZMod64.PrimeModulus`.
-/
def factorsModPBerlekampForm
    (f : ZPoly) (data : PrimeChoiceData) : Prop :=
  letI := data.bounds
  ∃ (hprime : Nat.Prime data.p)
    (hzero : (ZPoly.modP data.p f).isZero = false),
    data.factorsModP =
      ((@Berlekamp.berlekampFactor data.p data.bounds
        (monicModularImage (ZPoly.modP data.p f))
        (monicModularImage_monic hprime (ZPoly.modP data.p f) hzero)
        (@zmod64FieldOfPrime data.p data.bounds
          (ZMod64.primeModulusOfPrime hprime))).factors.map monicModularImage).toArray

set_option maxHeartbeats 800000 in
private theorem primeChoiceDataScore_factorsModPBerlekampForm
    (f : ZPoly) (c : SmallPrimeCandidate) (score : PrimeChoiceDataScore)
    (hscore : primeChoiceDataScore f c = some score) :
    factorsModPBerlekampForm f score.data := by
  unfold primeChoiceDataScore at hscore
  letI := c.bounds
  by_cases hgood : isGoodPrime f c.p
  · simp [hgood] at hscore
    cases hscore
    have hzero : (ZPoly.modP c.p f).isZero = false :=
      isGoodPrime_modP_isZero_false f c.p hgood
    refine ⟨c.prime, hzero, ?_⟩
    show berlekampFactorsModP f c = _
    exact berlekampFactorsModP_eq_of_isZero_false f c hzero
  · simp [hgood] at hscore

set_option maxHeartbeats 800000 in
private theorem betterPrimeChoiceDataScore_factorsModPBerlekampForm
    (f : ZPoly) (old new score : PrimeChoiceDataScore)
    (hold : factorsModPBerlekampForm f old.data)
    (hnew : factorsModPBerlekampForm f new.data)
    (hscore : betterPrimeChoiceDataScore old new = score) :
    factorsModPBerlekampForm f score.data := by
  unfold betterPrimeChoiceDataScore at hscore
  split at hscore
  · cases hscore
    exact hnew
  · cases hscore
    exact hold

private theorem choosePrimeDataScoreStep_factorsModPBerlekampForm
    (f : ZPoly) (best : Option PrimeChoiceDataScore) (c : SmallPrimeCandidate)
    (score : PrimeChoiceDataScore)
    (hbest : ∀ old, best = some old → factorsModPBerlekampForm f old.data)
    (hscore : choosePrimeDataScoreStep f best c = some score) :
    factorsModPBerlekampForm f score.data := by
  unfold choosePrimeDataScoreStep at hscore
  cases hbest_eq : best with
  | none =>
      cases hc_eq : primeChoiceDataScore f c with
      | none =>
          simp [hbest_eq, hc_eq] at hscore
      | some new =>
          simp [hbest_eq, hc_eq] at hscore
          have hnew := primeChoiceDataScore_factorsModPBerlekampForm f c new hc_eq
          subst score
          exact hnew
  | some old =>
      cases hc_eq : primeChoiceDataScore f c with
      | none =>
          simp [hbest_eq, hc_eq] at hscore
          have hold := hbest old hbest_eq
          subst score
          exact hold
      | some new =>
          simp [hbest_eq, hc_eq] at hscore
          exact betterPrimeChoiceDataScore_factorsModPBerlekampForm f old new score
            (hbest old hbest_eq)
            (primeChoiceDataScore_factorsModPBerlekampForm f c new hc_eq)
            hscore

private theorem choosePrimeDataScore_fold_factorsModPBerlekampForm
    (f : ZPoly) (candidates : List SmallPrimeCandidate)
    (best : Option PrimeChoiceDataScore) (score : PrimeChoiceDataScore)
    (hbest : ∀ old, best = some old → factorsModPBerlekampForm f old.data)
    (hscore :
      candidates.foldl (choosePrimeDataScoreStep f) best = some score) :
    factorsModPBerlekampForm f score.data := by
  induction candidates generalizing best with
  | nil =>
      exact hbest score hscore
  | cons c candidates ih =>
      exact ih (choosePrimeDataScoreStep f best c)
        (fun old hold =>
          choosePrimeDataScoreStep_factorsModPBerlekampForm f best c old hbest hold)
        hscore

private theorem choosePrimeDataWalk?_factorsModPBerlekampForm
    (f : ZPoly) (start fuel : Nat) (score : PrimeChoiceDataScore)
    (hscore : choosePrimeDataWalk? f start fuel = some score) :
    factorsModPBerlekampForm f score.data := by
  induction fuel generalizing start with
  | zero =>
      simp [choosePrimeDataWalk?] at hscore
  | succ fuel ih =>
      unfold choosePrimeDataWalk? at hscore
      cases hc : mkExtendedSmallPrimeCandidate? start with
      | none =>
          simp [hc] at hscore
          exact ih (start + 2) hscore
      | some c =>
          cases hs : primeChoiceDataScore f c with
          | none =>
              simp [hc, hs] at hscore
              exact ih (start + 2) hscore
          | some currentScore =>
              simp [hc, hs] at hscore
              cases hscore
              exact primeChoiceDataScore_factorsModPBerlekampForm f c score hs

/--
When `choosePrimeData? f` succeeds, the stored modular factor array is exactly
the Berlekamp factor output for the monic modular image of the selected
candidate.  Mirrors the `_prime` / `_fModP_eq` / `_isGoodPrime` provenance
chains, exposing the executable surface used by the small-mod singleton
irreducibility composition.
-/
theorem choosePrimeData?_factorsModP_berlekamp_form
    (f : ZPoly) (data : PrimeChoiceData)
    (hdata : choosePrimeData? f = some data) :
    letI := data.bounds
    ∃ (hzero : (ZPoly.modP data.p f).isZero = false),
      data.factorsModP =
        ((@Berlekamp.berlekampFactor data.p data.bounds
          (monicModularImage (ZPoly.modP data.p f))
          (monicModularImage_monic
            (choosePrimeData?_prime f data hdata)
            (ZPoly.modP data.p f) hzero)
          (@zmod64FieldOfPrime data.p data.bounds
            (ZMod64.primeModulusOfPrime
              (choosePrimeData?_prime f data hdata)))).factors.map
                monicModularImage).toArray := by
  unfold choosePrimeData? at hdata
  cases hscore :
      smallPrimeCandidates.foldl (choosePrimeDataScoreStep f) none with
  | some score =>
      simp [hscore] at hdata
      cases hdata
      have hform :=
        choosePrimeDataScore_fold_factorsModPBerlekampForm f smallPrimeCandidates none
          score (by intro old hnone; cases hnone) hscore
      obtain ⟨_, hzero, heq⟩ := hform
      exact ⟨hzero, heq⟩
  | none =>
      simp [hscore] at hdata
      cases hext :
          choosePrimeDataWalk? f 73 (choosePrimeDataWalkFuel f) with
      | none =>
          simp [hext] at hdata
      | some escore =>
          simp [hext] at hdata
          cases hdata
          have hform :=
            choosePrimeDataWalk?_factorsModPBerlekampForm f 73
              (choosePrimeDataWalkFuel f) escore hext
          obtain ⟨_, hzero, heq⟩ := hform
          exact ⟨hzero, heq⟩

/--
Small-mod singleton executable branch fact for the selected monic modular
image.

When `choosePrimeData?` succeeds and the public `factorsModP` field has size at
most one, the underlying Berlekamp factor list for
`monicModularImage (ZPoly.modP data.p f)` also has length at most one.  This is
the Mathlib-free shape fact needed before applying Berlekamp soundness in a
caller that already imports the heavier Rabin proof module.
-/
theorem choosePrimeData?_berlekampFactor_factors_length_le_one_of_small
    (f : ZPoly) (data : PrimeChoiceData)
    (hdata : choosePrimeData? f = some data)
    (hsmall : data.factorsModP.size ≤ 1) :
    letI := data.bounds
    ∃ (hzero : (@ZPoly.modP data.p data.bounds f).isZero = false),
      (@Berlekamp.berlekampFactor data.p data.bounds
        (@monicModularImage data.p data.bounds
          (@ZPoly.modP data.p data.bounds f))
        (monicModularImage_monic
          (choosePrimeData?_prime f data hdata)
          (@ZPoly.modP data.p data.bounds f) hzero)
        (@zmod64FieldOfPrime data.p data.bounds
          (ZMod64.primeModulusOfPrime
            (choosePrimeData?_prime f data hdata)))).factors.length ≤ 1 := by
  letI := data.bounds
  obtain ⟨hzero, hform⟩ :=
    choosePrimeData?_factorsModP_berlekamp_form f data hdata
  refine ⟨hzero, ?_⟩
  have hlen :
      (@Berlekamp.berlekampFactor data.p data.bounds
        (@monicModularImage data.p data.bounds
          (@ZPoly.modP data.p data.bounds f))
        (monicModularImage_monic
          (choosePrimeData?_prime f data hdata)
          (@ZPoly.modP data.p data.bounds f) hzero)
        (@zmod64FieldOfPrime data.p data.bounds
          (ZMod64.primeModulusOfPrime
            (choosePrimeData?_prime f data hdata)))).factors.length ≤ 1 := by
    simpa [hform] using hsmall
  exact hlen

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

namespace ZPoly

/--
`PrimeChoiceData`-shaped wrapper around
`Hex.ZPoly.quadraticMultifactorLiftInvariant_of_factorsModP`.

Given monic `core`, an admissible `1 ≤ B`, and the minimal modular boundary
facts about `primeData.factorsModP` -- per-factor monicness, product
congruence modulo `primeData.p`, sequential split coprimality, and a
nonempty witness -- this produces the recursive quadratic multifactor lift
invariant on the lifted modular factors that `henselLiftData` consumes.

The Mathlib-free downstream theorem
`HexBerlekampZassenhausMathlib.henselLiftData_liftedFactor_monic` already
feeds this invariant into `Hex.ZPoly.multifactorLiftQuadratic_each_monic`.
-/
theorem QuadraticMultifactorLiftInvariant_of_choosePrimeData
    (core : ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hp_prime : Nat.Prime primeData.p)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B)
    (hcore_monic : DensePoly.Monic core)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map FpPoly.liftToZ))
        core primeData.p)
    (hcoprime :
      letI := primeData.bounds
      QuadraticMultifactorCoprimeSplits primeData.p
        primeData.factorsModP.toList)
    (hnonempty : primeData.factorsModP.toList ≠ []) :
    letI := primeData.bounds
    QuadraticMultifactorLiftInvariant primeData.p B core
      (primeData.factorsModP.map FpPoly.liftToZ).toList := by
  letI := primeData.bounds
  haveI : ZMod64.PrimeModulus primeData.p :=
    ZMod64.primeModulusOfPrime hp_prime
  have hfactors_monic_list :
      ∀ g ∈ primeData.factorsModP.toList, DensePoly.Monic g := by
    intro g hg
    exact hfactors_monic g (by simpa using hg)
  have hproduct_mod_p_list :
      ZPoly.congr
        (Array.polyProduct
          ((primeData.factorsModP.toList.map FpPoly.liftToZ).toArray))
        core primeData.p := by
    have hmap_eq :
        (primeData.factorsModP.toList.map FpPoly.liftToZ).toArray
          = primeData.factorsModP.map FpPoly.liftToZ := by
      rw [← Array.toList_map]
    rw [hmap_eq]; exact hproduct_mod_p
  have hkey :=
    Hex.ZPoly.quadraticMultifactorLiftInvariant_of_factorsModP
      primeData.p B core primeData.factorsModP.toList
      hp hB hcore_monic hfactors_monic_list hproduct_mod_p_list
      hcoprime hnonempty
  have hmap_list :
      (primeData.factorsModP.map FpPoly.liftToZ).toList
        = primeData.factorsModP.toList.map FpPoly.liftToZ := by simp
  rw [hmap_list]
  exact hkey

end ZPoly

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

private theorem ceilLogPAux_ge_ell (p target : Nat) :
    ∀ (fuel ell power : Nat),
      ell ≤ ceilLogPAux p target fuel ell power := by
  intro fuel
  induction fuel with
  | zero =>
    intro ell power
    simp [ceilLogPAux]
  | succ fuel ih =>
    intro ell power
    unfold ceilLogPAux
    split
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ ell) (ih (ell + 1) (power * p))

private theorem ceilLogPAux_pow_bound (p : Nat) :
    ∀ (fuel target ell power : Nat),
      target ≤ power * p ^ fuel →
      target ≤ power * p ^ (ceilLogPAux p target fuel ell power - ell) := by
  intro fuel
  induction fuel with
  | zero =>
    intro target ell power h
    simp only [ceilLogPAux, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    simpa [Nat.pow_zero, Nat.mul_one] using h
  | succ fuel ih =>
    intro target ell power h
    unfold ceilLogPAux
    split
    · rename_i h_le
      simpa [Nat.sub_self, Nat.pow_zero, Nat.mul_one] using h_le
    · have h_step : target ≤ (power * p) * p ^ fuel := by
        have hrw : power * p ^ (fuel + 1) = (power * p) * p ^ fuel := by
          rw [Nat.pow_succ, Nat.mul_comm (p ^ fuel) p, ← Nat.mul_assoc]
        rw [hrw] at h
        exact h
      have ih_app := ih target (ell + 1) (power * p) h_step
      have hge : ell + 1 ≤ ceilLogPAux p target fuel (ell + 1) (power * p) :=
        ceilLogPAux_ge_ell p target fuel (ell + 1) (power * p)
      have hk :
          ceilLogPAux p target fuel (ell + 1) (power * p) - ell =
            (ceilLogPAux p target fuel (ell + 1) (power * p) - (ell + 1)) + 1 := by
        omega
      rw [hk, Nat.pow_succ]
      have hrw2 :
          power *
              (p ^ (ceilLogPAux p target fuel (ell + 1) (power * p) - (ell + 1)) *
                p) =
            (power * p) *
              p ^ (ceilLogPAux p target fuel (ell + 1) (power * p) - (ell + 1)) := by
        rw [Nat.mul_comm (p ^ _) p, ← Nat.mul_assoc]
      rw [hrw2]
      exact ih_app

/--
Correctness of `ceilLogP`: when `2 ≤ p`, the returned exponent satisfies
`target ≤ p ^ ceilLogP p target`.

This is the small spec consumed by `precisionForCoeffBound_spec` below; the
strict-inequality Mignotte side condition `2 * B < p ^ precisionForCoeffBound B p`
follows by chaining this with the target `target = 2 * B + 1`.
-/
theorem le_pow_ceilLogP {p : Nat} (hp : 2 ≤ p) (target : Nat) :
    target ≤ p ^ ceilLogP p target := by
  unfold ceilLogP
  rw [if_neg (by omega : ¬ p ≤ 1)]
  have hlt2 : target < 2 ^ target := Nat.lt_two_pow_self
  have hle2 : (2 : Nat) ^ target ≤ 2 ^ (target + 1) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
  have hpow_p : (2 : Nat) ^ (target + 1) ≤ p ^ (target + 1) :=
    Nat.pow_le_pow_left hp (target + 1)
  have h_init : target ≤ 1 * p ^ (target + 1) := by
    rw [Nat.one_mul]; omega
  have h_spec := ceilLogPAux_pow_bound p (target + 1) target 0 1 h_init
  simpa [Nat.sub_zero, Nat.one_mul] using h_spec

/--
The executable Mignotte precision exponent satisfies the Mignotte side
condition `2 * B < p ^ precisionForCoeffBound B p` whenever the modulus is at
least `2`.

This is the reusable spec consumed by `ForwardRecoveryInputs` constructors that
need to discharge the `mignotte_precision` field at the actual executable
precision returned by `henselLiftData f (precisionForCoeffBound B p)`.
-/
theorem precisionForCoeffBound_spec {p : Nat} (hp : 2 ≤ p) (B : Nat) :
    2 * B < p ^ precisionForCoeffBound B p := by
  unfold precisionForCoeffBound
  have h := le_pow_ceilLogP hp (2 * B + 1)
  omega

/-- Enumerate every way to partition a list of polynomials into a `(selected,
unselected)` pair while preserving the original order in each component.  Used
by the exhaustive recombination search to drive the slow path. -/
def subsetSplits : List ZPoly → List (List ZPoly × List ZPoly)
  | [] => [([], [])]
  | factor :: factors =>
      let rest := subsetSplits factors
      rest.map (fun split => (split.1, factor :: split.2)) ++
        rest.map (fun split => (factor :: split.1, split.2))

/-- Variant of `subsetSplits` that forces the first element of the input list
into the `selected` component.  This is what the recombination search actually
iterates over, since the head of the remaining local factors must end up in
some recovered factor and tracking that explicitly avoids enumerating the same
subset twice through different traversal orders. -/
def subsetSplitsWithFirst : List ZPoly → List (List ZPoly × List ZPoly)
  | [] => []
  | factor :: factors =>
      (subsetSplits factors).map fun split => (factor :: split.1, split.2)

/-- Return the first `some` produced by applying `f` to elements of `xs` in
order, or `none` if every application is `none`. -/
def firstSome {α β : Type} : List α → (α → Option β) → Option β
  | [], _ => none
  | x :: xs, f =>
      match f x with
      | some y => some y
      | none => firstSome xs f

private theorem polyProduct_contentFactorArray (content : Int) :
    Array.polyProduct (contentFactorArray content) =
      if content = 1 then 1 else DensePoly.C content := by
  unfold contentFactorArray
  by_cases hcontent : content = 1
  · simp [hcontent, ZPoly.polyProduct_empty]
  · simp [hcontent, Array.polyProduct]

private theorem polyProduct_repeatedPartFactorArray (repeatedPart : ZPoly) :
    Array.polyProduct (repeatedPartFactorArray repeatedPart) =
      if repeatedPart = 1 then 1 else repeatedPart := by
  unfold repeatedPartFactorArray
  by_cases hrepeated : repeatedPart = 1
  · simp [hrepeated, ZPoly.polyProduct_empty]
  · simp [hrepeated, Array.polyProduct]

private theorem polyProduct_replicate_X_zero :
    Array.polyProduct ((List.replicate 0 ZPoly.X).toArray) = 1 := by
  rfl

private theorem polyProduct_replicate_X_succ (power : Nat) :
    Array.polyProduct ((List.replicate (power + 1) ZPoly.X).toArray) =
      ZPoly.X * Array.polyProduct ((List.replicate power ZPoly.X).toArray) := by
  simpa [List.replicate] using ZPoly.polyProduct_cons_toArray ZPoly.X (List.replicate power ZPoly.X)

private theorem polyProduct_xPowerFactorArray_zero :
    Array.polyProduct (xPowerFactorArray 0) = 1 := by
  simp [xPowerFactorArray]

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
      rw [ZPoly.one_mul_zpoly, shift_zero]
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

private theorem extractXPower_product (f : ZPoly) :
    let xData := ZPoly.extractXPower f
    Array.polyProduct (xPowerFactorArray xData.power ++ #[xData.core]) = f := by
  unfold ZPoly.extractXPower
  generalize hsplit : ZPoly.splitInitialZeros f.toArray.toList = split
  cases split with
  | mk power core =>
      simp only
      rw [ZPoly.polyProduct_append, ZPoly.polyProduct_singleton]
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
  rw [ZPoly.polyProduct_append]

private theorem polyPow_zero_lemma (g : ZPoly) :
    Factorization.polyPow g 0 = (1 : ZPoly) := rfl

private theorem polyPow_succ_lemma (g : ZPoly) (n : Nat) :
    Factorization.polyPow g (n + 1) = Factorization.polyPow g n * g := rfl

private theorem polyProduct_replicate_toArray (q : ZPoly) (m : Nat) :
    Array.polyProduct (List.replicate m q).toArray = Factorization.polyPow q m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [List.replicate_succ]
      rw [ZPoly.polyProduct_cons_toArray]
      rw [ih]
      rw [polyPow_succ_lemma]
      rw [DensePoly.mul_comm_poly (S := Int)]

private theorem consumeExactPower_invariant
    (target candidate : ZPoly) (fuel : Nat) :
    Factorization.polyPow candidate (consumeExactPower target candidate fuel).2 *
        (consumeExactPower target candidate fuel).1 = target := by
  induction fuel generalizing target with
  | zero =>
      show Factorization.polyPow candidate 0 * target = target
      rw [polyPow_zero_lemma, ZPoly.one_mul_zpoly]
  | succ fuel ih =>
      unfold consumeExactPower
      cases hex : exactQuotient? target candidate with
      | none =>
          simp only
          rw [polyPow_zero_lemma, ZPoly.one_mul_zpoly]
      | some quot =>
          have hquot : quot * candidate = target := exactQuotient?_product hex
          have hih := ih quot
          simp only
          rw [polyPow_succ_lemma]
          rw [DensePoly.mul_assoc_poly (S := Int)]
          rw [DensePoly.mul_comm_poly (S := Int) candidate
            (consumeExactPower quot candidate fuel).1]
          rw [← DensePoly.mul_assoc_poly (S := Int)]
          rw [hih]
          exact hquot

private theorem expandRepeatedPartFactorsAux_invariant
    (coreFactors : List ZPoly) (rp : ZPoly) (fuel : Nat) :
    Array.polyProduct (expandRepeatedPartFactorsAux coreFactors rp fuel).1 *
        (expandRepeatedPartFactorsAux coreFactors rp fuel).2 = rp := by
  induction coreFactors generalizing rp with
  | nil =>
      show Array.polyProduct #[] * rp = rp
      rw [ZPoly.polyProduct_empty, ZPoly.one_mul_zpoly]
  | cons q qs ih =>
      unfold expandRepeatedPartFactorsAux
      have hcep := consumeExactPower_invariant rp q fuel
      have hih := ih (consumeExactPower rp q fuel).1
      simp only
      rw [ZPoly.polyProduct_append]
      rw [polyProduct_replicate_toArray]
      rw [DensePoly.mul_assoc_poly (S := Int)]
      rw [hih]
      exact hcep

private theorem expandRepeatedPartFactorArray_invariant
    (rp : ZPoly) (coreFactors : Array ZPoly) :
    Array.polyProduct (expandRepeatedPartFactorArray rp coreFactors).1 *
        (expandRepeatedPartFactorArray rp coreFactors).2 = rp := by
  unfold expandRepeatedPartFactorArray
  exact expandRepeatedPartFactorsAux_invariant _ _ _

private theorem expandRepeatedPartFactorsAux_mem
    (coreFactors : List ZPoly) (rp : ZPoly) (fuel : Nat) (factor : ZPoly)
    (hmem : factor ∈ (expandRepeatedPartFactorsAux coreFactors rp fuel).1.toList) :
    factor ∈ coreFactors := by
  induction coreFactors generalizing rp with
  | nil =>
      simp [expandRepeatedPartFactorsAux] at hmem
  | cons q qs ih =>
      unfold expandRepeatedPartFactorsAux at hmem
      simp only at hmem
      rw [Array.toList_append] at hmem
      rcases List.mem_append.mp hmem with hreplicate | hrest
      · have hreplicate_list :
            factor ∈ List.replicate (consumeExactPower rp q fuel).2 q := by
          simpa using hreplicate
        rw [List.eq_of_mem_replicate hreplicate_list]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem q (ih _ hrest)

private theorem expandRepeatedPartFactorArray_mem
    (rp : ZPoly) (coreFactors : Array ZPoly) (factor : ZPoly)
    (hmem : factor ∈ (expandRepeatedPartFactorArray rp coreFactors).1.toList) :
    factor ∈ coreFactors.toList := by
  unfold expandRepeatedPartFactorArray at hmem
  exact expandRepeatedPartFactorsAux_mem _ _ _ _ hmem

private theorem reassemblePolynomialFactors_mem
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) (factor : ZPoly)
    (hmem : factor ∈ (reassemblePolynomialFactors d coreFactors).toList) :
    factor ∈ (polynomialNormalizationPrefixFactors d).toList ∨
      factor ∈ coreFactors.toList := by
  unfold reassemblePolynomialFactors at hmem
  generalize hexp : expandRepeatedPartFactorArray d.repeatedPart coreFactors = exp at hmem
  cases exp with
  | mk expanded residual =>
      simp only at hmem
      by_cases hres : residual = 1
      · rw [if_pos hres] at hmem
        rw [Array.toList_append, Array.toList_append] at hmem
        rcases List.mem_append.mp hmem with hxe | hcf
        · rcases List.mem_append.mp hxe with hx | hexp_mem
          · left
            unfold polynomialNormalizationPrefixFactors
            rw [Array.toList_append]
            exact List.mem_append.mpr (Or.inl hx)
          · right
            have hexp_mem' : factor ∈
                (expandRepeatedPartFactorArray d.repeatedPart coreFactors).1.toList := by
              rw [hexp]
              exact hexp_mem
            exact expandRepeatedPartFactorArray_mem _ _ _ hexp_mem'
        · right
          exact hcf
      · rw [if_neg hres] at hmem
        rw [Array.toList_append] at hmem
        rcases List.mem_append.mp hmem with hprefix | hcf
        · exact Or.inl hprefix
        · exact Or.inr hcf

/-- Public wrapper for the reassembly membership split used by downstream
factor-output classifiers. -/
theorem reassemblePolynomialFactors_mem_normalization_or_core
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) (factor : ZPoly)
    (hmem : factor ∈ (reassemblePolynomialFactors d coreFactors).toList) :
    factor ∈ (polynomialNormalizationPrefixFactors d).toList ∨
      factor ∈ coreFactors.toList :=
  reassemblePolynomialFactors_mem d coreFactors factor hmem

/--
The repeated-part expansion fully consumed the normalization residual, so
`reassemblePolynomialFactors` uses its expanded branch rather than the
non-decomposed repeated-part fallback.
-/
def reassemblyExpansionComplete
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) : Prop :=
  (expandRepeatedPartFactorArray d.repeatedPart coreFactors).2 = 1

/--
Sharp membership split for the complete-expansion branch of reassembly.

When the repeated part has been completely expanded by the supplied core
factors, a reassembled raw factor is either an extracted `X`-power factor or one
of the supplied core factors. In particular, it cannot be the non-decomposed
`repeatedPartFactorArray` fallback.
-/
theorem reassemblePolynomialFactors_mem_xPower_or_core_of_expansionComplete
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) (factor : ZPoly)
    (hcomplete : reassemblyExpansionComplete d coreFactors)
    (hmem : factor ∈ (reassemblePolynomialFactors d coreFactors).toList) :
    factor ∈ (xPowerFactorArray d.xPower).toList ∨
      factor ∈ coreFactors.toList := by
  unfold reassemblyExpansionComplete at hcomplete
  unfold reassemblePolynomialFactors at hmem
  generalize hexp : expandRepeatedPartFactorArray d.repeatedPart coreFactors = exp at hmem hcomplete
  cases exp with
  | mk expanded residual =>
      simp only at hmem hcomplete
      rw [if_pos hcomplete] at hmem
      rw [Array.toList_append, Array.toList_append] at hmem
      rcases List.mem_append.mp hmem with hxe | hcore
      · rcases List.mem_append.mp hxe with hx | hexp_mem
        · exact Or.inl hx
        · right
          have hexp_mem' :
              factor ∈ (expandRepeatedPartFactorArray d.repeatedPart coreFactors).1.toList := by
            rw [hexp]
            exact hexp_mem
          exact expandRepeatedPartFactorArray_mem _ _ _ hexp_mem'
      · exact Or.inr hcore

private theorem polyProduct_repeatedPartFactorArray_eq (repeatedPart : ZPoly) :
    Array.polyProduct (repeatedPartFactorArray repeatedPart) = repeatedPart := by
  rw [polyProduct_repeatedPartFactorArray]
  split <;> simp_all

private theorem polyProduct_reassemblePolynomialFactors
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) :
    Array.polyProduct (reassemblePolynomialFactors d coreFactors) =
      DensePoly.shift d.xPower d.repeatedPart * Array.polyProduct coreFactors := by
  unfold reassemblePolynomialFactors
  have hinv := expandRepeatedPartFactorArray_invariant d.repeatedPart coreFactors
  generalize hexp : expandRepeatedPartFactorArray d.repeatedPart coreFactors = exp at hinv
  cases exp with
  | mk expanded residual =>
      simp only at hinv ⊢
      by_cases hres : residual = 1
      · rw [if_pos hres]
        rw [hres] at hinv
        rw [DensePoly.mul_one_right_poly (S := Int)] at hinv
        rw [ZPoly.polyProduct_append, ZPoly.polyProduct_append]
        rw [polyProduct_xPowerFactorArray_mul]
        rw [hinv]
      · rw [if_neg hres]
        rw [ZPoly.polyProduct_append, polyProduct_polynomialNormalizationPrefixFactors]
        rw [polyProduct_xPowerFactorArray_mul]
        rw [polyProduct_repeatedPartFactorArray_eq]

private theorem polyProduct_normalizationPrefixFactors (d : FactorNormalizationData) :
    Array.polyProduct (normalizationPrefixFactors d) =
      Array.polyProduct (contentFactorArray d.content) *
        (Array.polyProduct (xPowerFactorArray d.xPower) *
          Array.polyProduct (repeatedPartFactorArray d.repeatedPart)) := by
  unfold normalizationPrefixFactors
  rw [ZPoly.polyProduct_append, ZPoly.polyProduct_append]
  rw [DensePoly.mul_assoc_poly (S := Int)]

private theorem polyPow_zero (g : ZPoly) :
    Factorization.polyPow g 0 = (1 : ZPoly) := rfl

private theorem polyPow_succ (g : ZPoly) (n : Nat) :
    Factorization.polyPow g (n + 1) = Factorization.polyPow g n * g := rfl

private theorem polyPow_one (g : ZPoly) :
    Factorization.polyPow g 1 = g := by
  rw [polyPow_succ, polyPow_zero, ZPoly.one_mul_zpoly]

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
      rw [ZPoly.one_mul_zpoly]
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
  rw [ZPoly.one_mul_zpoly]
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
      rw [ZPoly.one_mul_zpoly]
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

private theorem shouldRecordPolynomialFactor_eq_true_of_ne
    {f : ZPoly}
    (hzero : f ≠ 0)
    (hone : f ≠ 1)
    (hneg_one : f ≠ DensePoly.C (-1 : Int)) :
    shouldRecordPolynomialFactor f = true := by
  unfold shouldRecordPolynomialFactor
  simp [hzero, hone, hneg_one]

private theorem normalizeFactorSign_ne_zero_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0) :
    normalizeFactorSign f ≠ 0 := by
  unfold normalizeFactorSign
  by_cases hlead : DensePoly.leadingCoeff f < 0
  · rw [if_pos hlead]
    intro hzero
    apply hf
    apply DensePoly.ext_coeff
    intro n
    have hcoeff := congrArg (fun p : ZPoly => p.coeff n) hzero
    change (DensePoly.scale (-1 : Int) f).coeff n = (0 : ZPoly).coeff n at hcoeff
    rw [DensePoly.coeff_scale (R := Int) (-1 : Int) f n
      (Int.mul_zero (-1 : Int))] at hcoeff
    rw [DensePoly.coeff_zero] at hcoeff
    rw [DensePoly.coeff_zero]
    omega
  · rw [if_neg hlead]
    exact hf

private theorem filteredNormalizedFactors_eq_map_normalizeFactorSign_of_no_units
    (factors : List ZPoly)
    (h_no_zero : ∀ factor ∈ factors, factor ≠ 0)
    (h_no_unit :
      ∀ factor ∈ factors,
        normalizeFactorSign factor ≠ 1 ∧
          normalizeFactorSign factor ≠ DensePoly.C (-1 : Int)) :
    filteredNormalizedFactors factors = factors.map normalizeFactorSign := by
  induction factors with
  | nil => rfl
  | cons factor factors ih =>
      have hkeep :
          shouldRecordPolynomialFactor (normalizeFactorSign factor) = true :=
        shouldRecordPolynomialFactor_eq_true_of_ne
          (normalizeFactorSign_ne_zero_of_ne_zero factor
            (h_no_zero factor (by simp)))
          (h_no_unit factor (by simp)).1
          (h_no_unit factor (by simp)).2
      rw [filteredNormalizedFactors_cons_keep factors hkeep]
      rw [ih
        (fun factor hmem => h_no_zero factor (by simp [hmem]))
        (fun factor hmem => h_no_unit factor (by simp [hmem]))]
      simp

private theorem polyProduct_filteredNormalizedFactors_eq_of_normalized_product
    (factors : Array ZPoly)
    (h_no_zero : ∀ factor ∈ factors.toList, factor ≠ 0)
    (h_no_unit :
      ∀ factor ∈ factors.toList,
        normalizeFactorSign factor ≠ 1 ∧
          normalizeFactorSign factor ≠ DensePoly.C (-1 : Int))
    (hnormalized_product :
      Array.polyProduct (factors.toList.map normalizeFactorSign).toArray =
        Array.polyProduct factors) :
    Array.polyProduct (filteredNormalizedFactors factors.toList).toArray =
      Array.polyProduct factors := by
  rw [filteredNormalizedFactors_eq_map_normalizeFactorSign_of_no_units
    factors.toList h_no_zero h_no_unit]
  exact hnormalized_product

private theorem filteredNormalizedFactors_eq_self_of_all_recorded_normalized
    (factors : List ZPoly)
    (hnormalized :
      ∀ factor ∈ factors, normalizeFactorSign factor = factor)
    (hrecorded :
      ∀ factor ∈ factors, shouldRecordPolynomialFactor factor = true) :
    filteredNormalizedFactors factors = factors := by
  induction factors with
  | nil => rfl
  | cons factor factors ih =>
      have hfactor_normalized :
          normalizeFactorSign factor = factor :=
        hnormalized factor (by simp)
      have hfactor_recorded :
          shouldRecordPolynomialFactor factor = true :=
        hrecorded factor (by simp)
      have hkeep :
          shouldRecordPolynomialFactor (normalizeFactorSign factor) = true := by
        rw [hfactor_normalized]
        exact hfactor_recorded
      rw [filteredNormalizedFactors_cons_keep factors hkeep, hfactor_normalized]
      rw [ih
        (fun factor hmem => hnormalized factor (by simp [hmem]))
        (fun factor hmem => hrecorded factor (by simp [hmem]))]

private theorem polyProduct_filteredNormalizedFactors_eq_self_of_all_recorded_normalized
    (factors : Array ZPoly)
    (hnormalized :
      ∀ factor ∈ factors.toList, normalizeFactorSign factor = factor)
    (hrecorded :
      ∀ factor ∈ factors.toList, shouldRecordPolynomialFactor factor = true) :
    Array.polyProduct (filteredNormalizedFactors factors.toList).toArray =
      Array.polyProduct factors := by
  rw [filteredNormalizedFactors_eq_self_of_all_recorded_normalized
    factors.toList hnormalized hrecorded]

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
        rw [ZPoly.polyProduct_cons_toArray]
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
  rw [multListProduct_nil, ZPoly.one_mul_zpoly] at hcol
  exact hcol

private theorem bumpFactorMultiplicity_mem_normalized_or_old
    (g : ZPoly) (acc : List (ZPoly × Nat)) (entry : ZPoly × Nat)
    (hmem : entry ∈ bumpFactorMultiplicity g acc) :
    entry.1 = g ∨ entry ∈ acc := by
  induction acc with
  | nil =>
      simp [bumpFactorMultiplicity] at hmem
      left
      rw [hmem]
  | cons head tail ih =>
      unfold bumpFactorMultiplicity at hmem
      by_cases heq : head.1 = g
      · simp [heq] at hmem
        rcases hmem with hentry | htail
        · left
          rw [hentry]
        · right
          exact List.mem_cons_of_mem head htail
      · simp [heq] at hmem
        rcases hmem with hhead | htail
        · right
          rw [hhead]
          simp
        · rcases ih htail with hnorm | hold
          · left
            exact hnorm
          · right
            exact List.mem_cons_of_mem head hold

private theorem collectFactorStep_mem_normalized_or_old
    (acc : List (ZPoly × Nat)) (factor : ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ collectFactorStep acc factor) :
    entry.1 = normalizeFactorSign factor ∨ entry ∈ acc := by
  unfold collectFactorStep at hmem
  by_cases hrec : shouldRecordPolynomialFactor (normalizeFactorSign factor) = true
  · simp [hrec] at hmem
    exact bumpFactorMultiplicity_mem_normalized_or_old
      (normalizeFactorSign factor) acc entry hmem
  · simp [hrec] at hmem
    exact Or.inr hmem

private theorem foldl_collectFactorStep_mem_normalized_or_old
    (factors : List ZPoly) (acc : List (ZPoly × Nat)) (entry : ZPoly × Nat)
    (hmem : entry ∈ factors.foldl collectFactorStep acc) :
    entry ∈ acc ∨ ∃ factor ∈ factors, entry.1 = normalizeFactorSign factor := by
  induction factors generalizing acc with
  | nil =>
      simp at hmem
      exact Or.inl hmem
  | cons factor factors ih =>
      simp only [List.foldl_cons] at hmem
      rcases ih (collectFactorStep acc factor) hmem with hstep | htail
      · rcases collectFactorStep_mem_normalized_or_old acc factor entry hstep with hnorm | hold
        · right
          exact ⟨factor, by simp, hnorm⟩
        · left
          exact hold
      · rcases htail with ⟨raw, hraw, hnorm⟩
        right
        exact ⟨raw, by simp [hraw], hnorm⟩

private theorem bumpFactorMultiplicity_entries_positive
    (g : ZPoly) (acc : List (ZPoly × Nat))
    (hpos : ∀ entry ∈ acc, 0 < entry.2) :
    ∀ entry ∈ bumpFactorMultiplicity g acc, 0 < entry.2 := by
  induction acc with
  | nil =>
      intro entry hmem
      simp [bumpFactorMultiplicity] at hmem
      rw [hmem]
      simp
  | cons head tail ih =>
      intro entry hmem
      unfold bumpFactorMultiplicity at hmem
      by_cases heq : head.1 = g
      · simp [heq] at hmem
        rcases hmem with hentry | htail
        · rw [hentry]
          simp
        · exact hpos entry (by simp [htail])
      · simp [heq] at hmem
        rcases hmem with hentry | htail
        · rw [hentry]
          exact hpos head (by simp)
        · exact ih (fun entry hentry => hpos entry (by simp [hentry])) entry htail

private theorem collectFactorStep_entries_positive
    (acc : List (ZPoly × Nat)) (factor : ZPoly)
    (hpos : ∀ entry ∈ acc, 0 < entry.2) :
    ∀ entry ∈ collectFactorStep acc factor, 0 < entry.2 := by
  unfold collectFactorStep
  by_cases hrec : shouldRecordPolynomialFactor (normalizeFactorSign factor) = true
  · intro entry hmem
    simp [hrec] at hmem
    exact
      bumpFactorMultiplicity_entries_positive
        (normalizeFactorSign factor) acc hpos entry hmem
  · intro entry hmem
    simp [hrec] at hmem
    exact hpos entry hmem

private theorem foldl_collectFactorStep_entries_positive
    (factors : List ZPoly) (acc : List (ZPoly × Nat))
    (hpos : ∀ entry ∈ acc, 0 < entry.2) :
    ∀ entry ∈ factors.foldl collectFactorStep acc, 0 < entry.2 := by
  induction factors generalizing acc with
  | nil =>
      simpa using hpos
  | cons factor factors ih =>
      simp only [List.foldl_cons]
      exact ih (collectFactorStep acc factor)
        (collectFactorStep_entries_positive acc factor hpos)

private theorem bumpFactorMultiplicity_entries_recorded
    (g : ZPoly) (acc : List (ZPoly × Nat))
    (hrec : shouldRecordPolynomialFactor g = true)
    (hacc : ∀ entry ∈ acc, shouldRecordPolynomialFactor entry.1 = true) :
    ∀ entry ∈ bumpFactorMultiplicity g acc,
      shouldRecordPolynomialFactor entry.1 = true := by
  intro entry hmem
  rcases bumpFactorMultiplicity_mem_normalized_or_old g acc entry hmem with hnorm | hold
  · rw [hnorm]
    exact hrec
  · exact hacc entry hold

private theorem collectFactorStep_entries_recorded
    (acc : List (ZPoly × Nat)) (factor : ZPoly)
    (hacc : ∀ entry ∈ acc, shouldRecordPolynomialFactor entry.1 = true) :
    ∀ entry ∈ collectFactorStep acc factor,
      shouldRecordPolynomialFactor entry.1 = true := by
  unfold collectFactorStep
  by_cases hrec : shouldRecordPolynomialFactor (normalizeFactorSign factor) = true
  · intro entry hmem
    simp [hrec] at hmem
    exact bumpFactorMultiplicity_entries_recorded
      (normalizeFactorSign factor) acc hrec hacc entry hmem
  · intro entry hmem
    simp [hrec] at hmem
    exact hacc entry hmem

private theorem foldl_collectFactorStep_entries_recorded
    (factors : List ZPoly) (acc : List (ZPoly × Nat))
    (hacc : ∀ entry ∈ acc, shouldRecordPolynomialFactor entry.1 = true) :
    ∀ entry ∈ factors.foldl collectFactorStep acc,
      shouldRecordPolynomialFactor entry.1 = true := by
  induction factors generalizing acc with
  | nil =>
      simpa using hacc
  | cons factor factors ih =>
      simp only [List.foldl_cons]
      exact ih (collectFactorStep acc factor)
        (collectFactorStep_entries_recorded acc factor hacc)

private theorem bumpFactorMultiplicity_pairwise_first
    (g : ZPoly) (acc : List (ZPoly × Nat))
    (hpair : List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1) acc) :
    List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1)
      (bumpFactorMultiplicity g acc) := by
  induction acc with
  | nil =>
      simp [bumpFactorMultiplicity]
  | cons head tail ih =>
      unfold bumpFactorMultiplicity
      by_cases heq : head.1 = g
      · cases hpair with
        | cons hhead htail =>
            simp [heq]
            constructor
            · intro a m hmem
              simpa [heq] using hhead (a, m) hmem
            · exact htail
      · cases hpair with
        | cons hhead htail =>
            simp [heq]
            constructor
            · intro a m hmem hfirst
              rcases bumpFactorMultiplicity_mem_normalized_or_old g tail (a, m) hmem with
                hnorm | hold
              · exact heq (hfirst.trans hnorm)
              · exact hhead (a, m) hold hfirst
            · exact ih htail

private theorem collectFactorStep_pairwise_first
    (acc : List (ZPoly × Nat)) (factor : ZPoly)
    (hpair : List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1) acc) :
    List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1)
      (collectFactorStep acc factor) := by
  unfold collectFactorStep
  by_cases hrec : shouldRecordPolynomialFactor (normalizeFactorSign factor) = true
  · simp [hrec]
    exact bumpFactorMultiplicity_pairwise_first
      (normalizeFactorSign factor) acc hpair
  · simp [hrec]
    exact hpair

private theorem foldl_collectFactorStep_pairwise_first
    (factors : List ZPoly) (acc : List (ZPoly × Nat))
    (hpair : List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1) acc) :
    List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1)
      (factors.foldl collectFactorStep acc) := by
  induction factors generalizing acc with
  | nil =>
      simpa using hpair
  | cons factor factors ih =>
      simp only [List.foldl_cons]
      exact ih (collectFactorStep acc factor)
        (collectFactorStep_pairwise_first acc factor hpair)

/-- Every collected `(factor, multiplicity)` entry comes from some raw factor
after sign normalization. This is the theorem-level wrapper for the
`collectFactorMultiplicities` step. -/
theorem collectFactorMultiplicities_entry_mem_normalized_raw
    (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (collectFactorMultiplicities factors).toList) :
    ∃ raw ∈ factors.toList, entry.1 = normalizeFactorSign raw := by
  rw [collectFactorMultiplicities_eq_foldl] at hmem
  have hmem_fold : entry ∈ factors.toList.foldl collectFactorStep [] := by
    simpa using hmem
  rcases foldl_collectFactorStep_mem_normalized_or_old factors.toList [] entry hmem_fold with
    hold | hraw
  · simp at hold
  · exact hraw

/-- Every collected factorization entry has positive multiplicity. -/
theorem collectFactorMultiplicities_entry_multiplicity_pos
    (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (collectFactorMultiplicities factors).toList) :
    0 < entry.2 := by
  rw [collectFactorMultiplicities_eq_foldl] at hmem
  have hmem_fold : entry ∈ factors.toList.foldl collectFactorStep [] := by
    simpa using hmem
  exact
    foldl_collectFactorStep_entries_positive factors.toList []
      (by simp) entry hmem_fold

/-- Every collected factorization entry passed the recorded-factor filter. -/
theorem collectFactorMultiplicities_entry_shouldRecord
    (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (collectFactorMultiplicities factors).toList) :
    shouldRecordPolynomialFactor entry.1 = true := by
  rw [collectFactorMultiplicities_eq_foldl] at hmem
  have hmem_fold : entry ∈ factors.toList.foldl collectFactorStep [] := by
    simpa using hmem
  exact
    foldl_collectFactorStep_entries_recorded factors.toList []
      (by simp) entry hmem_fold

/-- The collector emits no duplicate polynomial keys. -/
theorem collectFactorMultiplicities_pairwise_first
    (factors : Array ZPoly) :
    List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1)
      (collectFactorMultiplicities factors).toList := by
  rw [collectFactorMultiplicities_eq_foldl]
  have hpair :
      List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1)
        (factors.toList.foldl collectFactorStep []) :=
    foldl_collectFactorStep_pairwise_first factors.toList [] (by simp)
  rw [List.pairwise_reverse]
  exact hpair.imp (fun hne h => hne h.symm)

/-- Membership in a `Factorization` built from a raw factor array descends to
membership in that raw array, up to sign normalization. -/
theorem factorizationOfFactors_entry_mem_normalized_raw
    (f : ZPoly) (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factorizationOfFactors f factors).factors.toList) :
    ∃ raw ∈ factors.toList, entry.1 = normalizeFactorSign raw := by
  unfold factorizationOfFactors at hmem
  exact collectFactorMultiplicities_entry_mem_normalized_raw factors entry hmem

/-- Entries in a `Factorization` built from raw factors have positive multiplicity. -/
theorem factorizationOfFactors_entry_multiplicity_pos
    (f : ZPoly) (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factorizationOfFactors f factors).factors.toList) :
    0 < entry.2 := by
  unfold factorizationOfFactors at hmem
  exact collectFactorMultiplicities_entry_multiplicity_pos factors entry hmem

/-- A `Factorization` built from raw factors has no duplicate polynomial keys. -/
theorem factorizationOfFactors_pairwise_first
    (f : ZPoly) (factors : Array ZPoly) :
    List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1)
      (factorizationOfFactors f factors).factors.toList := by
  unfold factorizationOfFactors
  exact collectFactorMultiplicities_pairwise_first factors

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

private theorem factorizationOfFactors_product_of_filtered_product
    (f : ZPoly) (factors : Array ZPoly)
    (hraw : DensePoly.C (signedContentScalar f) *
      Array.polyProduct factors = f)
    (hfiltered :
      Array.polyProduct (filteredNormalizedFactors factors.toList).toArray =
        Array.polyProduct factors) :
    Factorization.product (factorizationOfFactors f factors) = f := by
  rw [factorizationOfFactors_product, hfiltered]
  exact hraw

private theorem factorizationOfFactors_product_of_raw_product_of_all_recorded_normalized
    (f : ZPoly) (factors : Array ZPoly)
    (hraw : DensePoly.C (signedContentScalar f) *
      Array.polyProduct factors = f)
    (hnormalized :
      ∀ factor ∈ factors.toList, normalizeFactorSign factor = factor)
    (hrecorded :
      ∀ factor ∈ factors.toList, shouldRecordPolynomialFactor factor = true) :
    Factorization.product (factorizationOfFactors f factors) = f :=
  factorizationOfFactors_product_of_filtered_product f factors hraw
    (polyProduct_filteredNormalizedFactors_eq_self_of_all_recorded_normalized
      factors hnormalized hrecorded)

private theorem signedContentScalar_zero :
    signedContentScalar 0 = 0 := by
  unfold signedContentScalar
  simp

private theorem factorizationOfFactors_product_of_zero (factors : Array ZPoly) :
    Factorization.product (factorizationOfFactors 0 factors) = 0 := by
  rw [factorizationOfFactors_product]
  rw [signedContentScalar_zero]
  change DensePoly.C (0 : Int) *
      Array.polyProduct (filteredNormalizedFactors factors.toList).toArray = 0
  rw [show (DensePoly.C (0 : Int) : ZPoly) = (0 : ZPoly) from rfl]
  exact DensePoly.zero_mul
    (Array.polyProduct (filteredNormalizedFactors factors.toList).toArray)

private theorem leadingCoeff_X :
    DensePoly.leadingCoeff ZPoly.X = (1 : Int) := by
  rfl

private theorem X_ne_zero : ZPoly.X ≠ (0 : ZPoly) := by
  decide

private theorem X_ne_one : ZPoly.X ≠ (1 : ZPoly) := by
  decide

private theorem X_ne_C_neg_one : ZPoly.X ≠ DensePoly.C (-1 : Int) := by
  decide

private theorem normalizeFactorSign_X :
    normalizeFactorSign ZPoly.X = ZPoly.X := by
  unfold normalizeFactorSign
  rw [leadingCoeff_X]
  simp

private theorem shouldRecordPolynomialFactor_X :
    shouldRecordPolynomialFactor ZPoly.X = true := by
  unfold shouldRecordPolynomialFactor
  simp [X_ne_zero, X_ne_one, X_ne_C_neg_one]

/-- The sign-normalisation of `1` is `1`.  Exposed publicly so Mathlib-side
per-branch umbrellas (in particular the fast-path constant arm, where the
singleton square-free core collapses to `1`) can normalise the unit core
without re-deriving the leading-coefficient computation inline. -/
theorem normalizeFactorSign_one :
    normalizeFactorSign (1 : ZPoly) = 1 := by
  unfold normalizeFactorSign
  have hnot : ¬ DensePoly.leadingCoeff (1 : ZPoly) < 0 := by
    change ¬ DensePoly.leadingCoeff (DensePoly.C (1 : Int)) < 0
    simp [DensePoly.leadingCoeff,
      DensePoly.coeffs_C_of_ne_zero (by decide : (1 : Int) ≠ 0)]
  rw [if_neg hnot]

/-- The `shouldRecordPolynomialFactor` filter rejects the unit `1`.  Exposed
publicly so Mathlib-side per-branch umbrellas can contradict
`factorWithBound_entry_shouldRecord` directly when an entry collapses to a
unit (in particular the fast-path constant arm, where the singleton
square-free core is `1`). -/
theorem shouldRecordPolynomialFactor_one :
    shouldRecordPolynomialFactor (1 : ZPoly) = false := by
  unfold shouldRecordPolynomialFactor
  simp

private theorem mem_xPowerFactorArray_eq_X (power : Nat) (factor : ZPoly)
    (h : factor ∈ (xPowerFactorArray power).toList) :
    factor = ZPoly.X := by
  unfold xPowerFactorArray at h
  simp [List.mem_replicate] at h
  exact h.2

private theorem xPowerFactorArray_normalizeFactorSign
    (power : Nat) (factor : ZPoly)
    (h : factor ∈ (xPowerFactorArray power).toList) :
    normalizeFactorSign factor = factor := by
  rw [mem_xPowerFactorArray_eq_X power factor h]
  exact normalizeFactorSign_X

private theorem xPowerFactorArray_shouldRecord
    (power : Nat) (factor : ZPoly)
    (h : factor ∈ (xPowerFactorArray power).toList) :
    shouldRecordPolynomialFactor factor = true := by
  rw [mem_xPowerFactorArray_eq_X power factor h]
  exact shouldRecordPolynomialFactor_X

private theorem mem_repeatedPartFactorArray_eq (rep : ZPoly) (factor : ZPoly)
    (h : factor ∈ (repeatedPartFactorArray rep).toList) :
    factor = rep := by
  unfold repeatedPartFactorArray at h
  by_cases hone : rep = 1
  · simp [hone] at h
  · simp [hone] at h
    exact h

private theorem mem_repeatedPartFactorArray_ne_one
    (rep : ZPoly) (factor : ZPoly)
    (h : factor ∈ (repeatedPartFactorArray rep).toList) :
    rep ≠ 1 := by
  unfold repeatedPartFactorArray at h
  by_cases hone : rep = 1
  · simp [hone] at h
  · exact hone

private theorem normalizeFactorSign_eq_self_of_leadingCoeff_nonneg (g : ZPoly)
    (h : 0 ≤ DensePoly.leadingCoeff g) :
    normalizeFactorSign g = g := by
  unfold normalizeFactorSign
  have hnot : ¬ DensePoly.leadingCoeff g < 0 := by omega
  rw [if_neg hnot]

private theorem normalizeFactorSign_leadingCoeff_nonneg (g : ZPoly) :
    0 ≤ DensePoly.leadingCoeff (normalizeFactorSign g) := by
  unfold normalizeFactorSign
  by_cases hlead : DensePoly.leadingCoeff g < 0
  · rw [if_pos hlead]
    have hg_ne : g ≠ 0 := by
      intro hzero
      rw [hzero] at hlead
      change (0 : Int) < 0 at hlead
      omega
    rw [ZPoly.leadingCoeff_scale_of_nonzero (-1 : Int) g (by decide)]
    omega
  · rw [if_neg hlead]
    omega

private theorem normalizeFactorSign_idem (g : ZPoly) :
    normalizeFactorSign (normalizeFactorSign g) = normalizeFactorSign g :=
  normalizeFactorSign_eq_self_of_leadingCoeff_nonneg
    (normalizeFactorSign g) (normalizeFactorSign_leadingCoeff_nonneg g)

/-- Sign normalisation preserves primitivity: the `if_neg` branch is the
identity, and the `if_pos` branch scales by `-1`, which preserves content
by `DensePoly.content_scale_neg_one`. -/
private theorem normalizeFactorSign_primitive (f : ZPoly)
    (h : ZPoly.Primitive f) :
    ZPoly.Primitive (normalizeFactorSign f) := by
  unfold normalizeFactorSign
  by_cases hlead : DensePoly.leadingCoeff f < 0
  · rw [if_pos hlead]
    show ZPoly.content (DensePoly.scale (-1 : Int) f) = 1
    rw [show ZPoly.content (DensePoly.scale (-1 : Int) f)
          = DensePoly.content (DensePoly.scale (-1 : Int) f) from rfl,
        DensePoly.content_scale_neg_one f]
    exact h
  · rw [if_neg hlead]
    exact h

/-- Collected factor entries are fixed points of `normalizeFactorSign`. -/
theorem collectFactorMultiplicities_entry_normalizeFactorSign_id
    (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (collectFactorMultiplicities factors).toList) :
    normalizeFactorSign entry.1 = entry.1 := by
  rcases collectFactorMultiplicities_entry_mem_normalized_raw factors entry hmem with
    ⟨raw, _hraw_mem, hraw⟩
  rw [hraw]
  exact normalizeFactorSign_idem raw

/-- Collected factor entries have positive leading coefficient. -/
theorem collectFactorMultiplicities_entry_leadingCoeff_pos
    (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (collectFactorMultiplicities factors).toList) :
    0 < DensePoly.leadingCoeff entry.1 := by
  have hnorm :=
    collectFactorMultiplicities_entry_normalizeFactorSign_id factors entry hmem
  have hnonneg : 0 ≤ DensePoly.leadingCoeff entry.1 := by
    have h := normalizeFactorSign_leadingCoeff_nonneg entry.1
    rwa [hnorm] at h
  have hrecord :=
    collectFactorMultiplicities_entry_shouldRecord factors entry hmem
  have hne : entry.1 ≠ 0 := by
    unfold shouldRecordPolynomialFactor at hrecord
    simp at hrecord
    exact hrecord.1.1
  have hlead_ne : DensePoly.leadingCoeff entry.1 ≠ 0 :=
    ZPoly.leadingCoeff_ne_zero_of_ne_zero entry.1 hne
  omega

/-- Entries in a `Factorization` built from raw factors are fixed points of
`normalizeFactorSign`. -/
theorem factorizationOfFactors_entry_normalizeFactorSign_id
    (f : ZPoly) (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factorizationOfFactors f factors).factors.toList) :
    normalizeFactorSign entry.1 = entry.1 := by
  unfold factorizationOfFactors at hmem
  exact collectFactorMultiplicities_entry_normalizeFactorSign_id factors entry hmem

/-- Entries in a `Factorization` built from raw factors have positive leading
coefficient. -/
theorem factorizationOfFactors_entry_leadingCoeff_pos
    (f : ZPoly) (factors : Array ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factorizationOfFactors f factors).factors.toList) :
    0 < DensePoly.leadingCoeff entry.1 := by
  unfold factorizationOfFactors at hmem
  exact collectFactorMultiplicities_entry_leadingCoeff_pos factors entry hmem

private theorem rat_scale_scale (u v : Rat) (p : DensePoly Rat) :
    DensePoly.scale u (DensePoly.scale v p) = DensePoly.scale (u * v) p := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Rat) u (DensePoly.scale v p) n (Rat.mul_zero u)]
  rw [DensePoly.coeff_scale (R := Rat) v p n (Rat.mul_zero v)]
  rw [DensePoly.coeff_scale (R := Rat) (u * v) p n (Rat.mul_zero (u * v))]
  rw [Rat.mul_assoc]

private theorem int_scale_scale (u v : Int) (p : ZPoly) :
    DensePoly.scale u (DensePoly.scale v p) = DensePoly.scale (u * v) p := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Int) u (DensePoly.scale v p) n (Int.mul_zero u)]
  rw [DensePoly.coeff_scale (R := Int) v p n (Int.mul_zero v)]
  rw [DensePoly.coeff_scale (R := Int) (u * v) p n (Int.mul_zero (u * v))]
  rw [Int.mul_assoc]

private theorem shift_scale_int (k : Nat) (c : Int) (p : ZPoly) :
    DensePoly.shift k (DensePoly.scale c p) =
      DensePoly.scale c (DensePoly.shift k p) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_shift, DensePoly.coeff_scale (R := Int) c (DensePoly.shift k p) n
    (Int.mul_zero c)]
  rw [DensePoly.coeff_shift]
  by_cases hn : n < k
  · rw [if_pos hn]
    rw [if_pos hn]
    change (0 : Int) = c * 0
    rw [Int.mul_zero]
  · rw [if_neg hn]
    rw [if_neg hn]
    rw [DensePoly.coeff_scale (R := Int) c p (n - k) (Int.mul_zero c)]

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

/--
Non-monic packaging companion for `exactQuotient?_product`.

For non-monic integer polynomials, an exact product equation alone does not
identify the executable quotient: `DensePoly.divMod` performs coefficient
division in `ℤ`, so downstream proofs must also supply the concrete
`divMod` result.  This lemma records the remaining wrapper logic of
`exactQuotient?`: a recorded non-unit candidate with zero executable
remainder and the checked product equation is accepted with the witnessed
quotient.
-/
theorem exactQuotient?_eq_some_of_divMod_eq_of_shouldRecord
    {target candidate quotient : ZPoly}
    (hrecord : shouldRecordPolynomialFactor candidate = true)
    (hdivMod : DensePoly.divMod target candidate = (quotient, 0))
    (hmul : quotient * candidate = target) :
    exactQuotient? target candidate = some quotient := by
  have hrecord_props :
      (candidate ≠ 0 ∧ candidate ≠ 1) ∧
        candidate ≠ DensePoly.C (-1 : Int) := by
    simpa [shouldRecordPolynomialFactor] using hrecord
  have hcandidate_ne : candidate ≠ 0 := by
    exact hrecord_props.1.1
  have hcandidate_ne_one : candidate ≠ 1 := by
    exact hrecord_props.1.2
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
  unfold exactQuotient?
  rw [hisZero_false]
  simp only [Bool.false_or, decide_eq_true_eq]
  rw [if_neg hcandidate_ne_one]
  rw [hdivMod]
  simp [hmul]

/-- Non-monic converse to `exactQuotient?_product` for divisors with positive
leading coefficient.  Drops the `Monic` hypothesis from
`exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree` in favour of
`0 < leadingCoeff candidate`, routing the executable division through
`divMod_eq_of_pos_lc_pos_degree_mul_eq` and packaging the result with
`exactQuotient?_eq_some_of_divMod_eq_of_shouldRecord`.  Positive degree alone
discharges `shouldRecordPolynomialFactor`, since `0`, `C 1`, and `C (-1)` all
have `degree?.getD 0 = 0`. -/
theorem exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq
    {target candidate quotient : ZPoly}
    (hpos_lc : 0 < DensePoly.leadingCoeff candidate)
    (hdegree : 0 < candidate.degree?.getD 0)
    (hmul : quotient * candidate = target) :
    exactQuotient? target candidate = some quotient := by
  have hrecord : shouldRecordPolynomialFactor candidate = true := by
    have hne_zero : candidate ≠ 0 := by
      intro hzero
      have hdeg : candidate.degree?.getD 0 = 0 := by
        rw [hzero]; simp [DensePoly.degree?]
      omega
    have hne_one : candidate ≠ 1 := by
      intro hone
      have hdeg : candidate.degree?.getD 0 = 0 := by
        rw [hone]
        change (DensePoly.C (1 : Int)).degree?.getD 0 = 0
        exact DensePoly.degree?_C_getD 1
      omega
    have hne_neg_one : candidate ≠ DensePoly.C (-1 : Int) := by
      intro hneg
      have hdeg : candidate.degree?.getD 0 = 0 := by
        rw [hneg]
        exact DensePoly.degree?_C_getD (-1)
      omega
    unfold shouldRecordPolynomialFactor
    simp [hne_zero, hne_one, hne_neg_one]
  have hdivMod_eq : DensePoly.divMod target candidate = (quotient, 0) :=
    ZPoly.divMod_eq_of_pos_lc_pos_degree_mul_eq target candidate quotient
      hpos_lc hdegree hmul
  exact exactQuotient?_eq_some_of_divMod_eq_of_shouldRecord hrecord hdivMod_eq hmul

private def positiveDivisors (n : Nat) : List Nat :=
  (List.range (n + 1)).filter fun d => d != 0 && n % d == 0

private def integerRootCandidates (f : ZPoly) : List Int :=
  (positiveDivisors (f.coeff 0).natAbs).flatMap fun d =>
    let r : Int := Int.ofNat d
    [r, -r]

private def linearFactorForRoot (r : Int) : ZPoly :=
  DensePoly.ofCoeffs #[-r, 1]

private theorem leadingCoeff_linearFactorForRoot (r : Int) :
    DensePoly.leadingCoeff (linearFactorForRoot r) = (1 : Int) := by
  unfold linearFactorForRoot
  rfl

private theorem linearFactorForRoot_size_eq_two (r : Int) :
    (linearFactorForRoot r).size = 2 := by
  unfold linearFactorForRoot
  rfl

private theorem linearFactorForRoot_degree_pos (r : Int) :
    0 < (linearFactorForRoot r).degree?.getD 0 := by
  unfold DensePoly.degree?
  rw [linearFactorForRoot_size_eq_two r]
  simp

private theorem linearFactorForRoot_ne_zero (r : Int) :
    linearFactorForRoot r ≠ (0 : ZPoly) := by
  intro h
  have hsize := linearFactorForRoot_size_eq_two r
  rw [h] at hsize
  change (0 : ZPoly).size = 2 at hsize
  have hzero : (0 : ZPoly).size = 0 := rfl
  omega

private theorem linearFactorForRoot_ne_one (r : Int) :
    linearFactorForRoot r ≠ (1 : ZPoly) := by
  intro h
  have hsize := linearFactorForRoot_size_eq_two r
  rw [h] at hsize
  have hone : (1 : ZPoly).size = 1 := rfl
  omega

private theorem linearFactorForRoot_ne_C_neg_one (r : Int) :
    linearFactorForRoot r ≠ DensePoly.C (-1 : Int) := by
  intro h
  have hsize := linearFactorForRoot_size_eq_two r
  rw [h] at hsize
  have hcsize : (DensePoly.C (-1 : Int)).size = 1 := rfl
  omega

private theorem normalizeFactorSign_linearFactorForRoot (r : Int) :
    normalizeFactorSign (linearFactorForRoot r) = linearFactorForRoot r := by
  unfold normalizeFactorSign
  rw [leadingCoeff_linearFactorForRoot]
  simp

private theorem shouldRecordPolynomialFactor_linearFactorForRoot (r : Int) :
    shouldRecordPolynomialFactor (linearFactorForRoot r) = true := by
  unfold shouldRecordPolynomialFactor
  simp [linearFactorForRoot_ne_zero, linearFactorForRoot_ne_one,
    linearFactorForRoot_ne_C_neg_one]

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

def quadraticIntegerRootFactors? (core : ZPoly) : Option (Array ZPoly) :=
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

/-- Integer values in `[-B, B]`, listed in increasing order. -/
private def boundedIntegerList (B : Nat) : List Int :=
  (List.range (2 * B + 1)).map fun i => (Int.ofNat i) - (Int.ofNat B)

/-- All length-`len` integer coefficient lists with each entry in `[-B, B]`. -/
private def boundedCoefficientVectors (B : Nat) : Nat → List (List Int)
  | 0 => [[]]
  | len + 1 =>
      (boundedCoefficientVectors B len).flatMap fun rest =>
        (boundedIntegerList B).map fun c => c :: rest

/-- Bounded-coefficient candidate divisors of degree exactly `d`. Each
emitted polynomial has positive leading coefficient (so
`normalizeFactorSign` is the identity on it) and passes
`shouldRecordPolynomialFactor`. -/
private def trialDivisionCandidatesOfDegree (B d : Nat) : List ZPoly :=
  (boundedCoefficientVectors B (d + 1)).filterMap fun coeffs =>
    let p := DensePoly.ofCoeffs coeffs.toArray
    if p.degree?.getD 0 = d ∧ 0 < DensePoly.leadingCoeff p ∧
        shouldRecordPolynomialFactor p = true then
      some p
    else
      none

/-- Bounded-coefficient candidate divisors of degrees `1..maxDeg`, in order
of increasing degree. -/
private def trialDivisionCandidatesUpTo (B maxDeg : Nat) : List ZPoly :=
  (List.range maxDeg).flatMap fun d => trialDivisionCandidatesOfDegree B (d + 1)

/-- Peel candidate divisors off the running target via `exactQuotient?`. Each
candidate in the input list is tried at most once. Returns
`(emittedFactors, residual)` with the invariant
`residual * polyProduct emittedFactors = target`. -/
private def trialDivisionPeelAux :
    ZPoly → List ZPoly → Array ZPoly × ZPoly
  | target, [] => (#[], target)
  | target, candidate :: candidates =>
      match exactQuotient? target candidate with
      | some quotient =>
          let rest := trialDivisionPeelAux quotient candidates
          (#[candidate] ++ rest.1, rest.2)
      | none => trialDivisionPeelAux target candidates

/--
Standalone integer trial-division core for the slow factorization path.

First peels monic linear integer-root factors `(x - r)` off `core` via
`splitIntegerRootFactorsAux`, then enumerates non-unit polynomial candidates
of degrees `1..deg(afterLinear)/2` with coefficients in `[-B, B]`, dividing
each in turn into the running residual. The returned array consists of the
linear factors, the bounded-coefficient factors that exactly divided the
residual, and the final residual (omitted when it collapses to `1`).

The companion theorems `exhaustiveIntegerTrialCoreFactorsWithBound_polyProduct`,
`exhaustiveIntegerTrialCoreFactorsWithBound_normalizeFactorSign`, and
`exhaustiveIntegerTrialCoreFactorsWithBound_shouldRecord` record the
local executable invariants needed by the eventual `factorSlow`
reassembly callers.
-/
def exhaustiveIntegerTrialCoreFactorsWithBound
    (core : ZPoly) (B : Nat) : Array ZPoly :=
  let split :=
    splitIntegerRootFactorsAux core (integerRootCandidates core)
      (integerRootCandidates core).length
  let peel :=
    trialDivisionPeelAux split.2
      (trialDivisionCandidatesUpTo B (split.2.degree?.getD 0 / 2))
  if peel.2 = 1 then
    split.1 ++ peel.1
  else
    (split.1 ++ peel.1).push peel.2

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
BHKS two-sided cut `Psi^a_b(x) = (x_amb - (x_amb mod^± p^b)) / p^b`, where
`x_amb := x mod^± p^a` is the centered ambient representative.

Centering at the ambient modulus `p^a` before taking the lower-precision cut
is required to match the SPEC semantics: a CLD coefficient passed in as a
nonnegative `p^a`-residue `(p^a - c)` of a negative exact value `-c` must be
recentered to `-c` before applying the `p^b` cut. Without this step the cut
produces an oversized output for negative exact coefficients — see #6217 for
the `f = x^2 - 5*x + 6`, `g = x - 2`, `p = 5`, `a = 6` counterexample to the
old uncentered formulation.
-/
def psiCut (p a b : Nat) (x : Int) : Int :=
  let modulus := p ^ b
  if modulus = 0 then
    0
  else
    let xCentered := centeredResiduePow p a x
    (xCentered - centeredResiduePow p b xCentered) / Int.ofNat modulus

/--
Mod-`p^a` representative of `f * g.derivative / g`, the polynomial whose
`x^j` coefficient is the integer CLD coefficient `[x^j] Phi(g)` reduced
modulo `p^a`.

Exposed (rather than private) so the BHKS bridge layer can state the
congruence linking the executable quotient to the exact integer CLD
coefficient.
-/
def cldQuotientMod (f g : ZPoly) (p a : Nat) : ZPoly :=
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

/-- `centeredModNat` depends only on its argument modulo `m`. -/
theorem centeredModNat_emod_self (z : Int) (m : Nat) :
    centeredModNat (z % (m : Int)) m = centeredModNat z m := by
  by_cases hm : m = 0
  · subst hm
    show centeredModNat (z % ((0 : Nat) : Int)) 0 = centeredModNat z 0
    simp [Int.emod_zero]
  · have hmod : (z % (m : Int)) % Int.ofNat m = z % Int.ofNat m := by
      show z % Int.ofNat m % Int.ofNat m = z % Int.ofNat m
      exact Int.emod_emod _ _
    unfold centeredModNat
    rw [if_neg hm, if_neg hm, hmod]

/--
If `y` is an exact integer with `|y| ≤ B`, `y ≡ z (mod p^a)`, and the ambient
modulus `p^a` is large enough to separate the centered residue (`2*B < p^a`),
then `centeredResiduePow p a z = y`.
-/
theorem centeredResiduePow_eq_of_natAbs_le
    (p a : Nat) (y z : Int) (B : Nat)
    (hbound : y.natAbs ≤ B)
    (hsep : 2 * B < p ^ a)
    (hcongr : y % ((p ^ a : Nat) : Int) = z % ((p ^ a : Nat) : Int)) :
    centeredResiduePow p a z = y := by
  unfold centeredResiduePow
  rw [← centeredModNat_emod_self z, ← hcongr]
  exact centeredModNat_emod_eq_of_natAbs_le y (p ^ a) B hbound hsep

/--
If an exact integer `y` with `|y| ≤ B` is congruent to `z` modulo `p^a`, and
both the ambient modulus `p^a` and the lower cut modulus `p^b` separate `B`
(`2*B < p^a` and `2*B < p^b`), then the BHKS two-sided cut `psiCut p a b z`
vanishes.
-/
theorem psiCut_eq_zero_of_natAbs_le
    (p a b : Nat) (y z : Int) (B : Nat)
    (hbound : y.natAbs ≤ B)
    (hsep_a : 2 * B < p ^ a)
    (hsep_b : 2 * B < p ^ b)
    (hcongr : y % ((p ^ a : Nat) : Int) = z % ((p ^ a : Nat) : Int)) :
    psiCut p a b z = 0 := by
  unfold psiCut
  have hbpos : 0 < p ^ b := by omega
  have hbne : (p ^ b : Nat) ≠ 0 := Nat.ne_of_gt hbpos
  have hcentered_amb : centeredResiduePow p a z = y :=
    centeredResiduePow_eq_of_natAbs_le p a y z B hbound hsep_a hcongr
  rw [if_neg hbne]
  show (centeredResiduePow p a z - centeredResiduePow p b (centeredResiduePow p a z))
      / Int.ofNat (p ^ b) = 0
  rw [hcentered_amb]
  have hcentered_b : centeredResiduePow p b y = y := by
    unfold centeredResiduePow
    rw [← centeredModNat_emod_self y]
    exact centeredModNat_emod_eq_of_natAbs_le y (p ^ b) B hbound hsep_b
  rw [hcentered_b, Int.sub_self, Int.zero_ediv]

/--
Absolute-value form of `psiCut_eq_zero_of_natAbs_le`: under the same
hypotheses, `|psiCut p a b z| ≤ B`. Useful when callers carry the BHKS
column bound `B = bhksCoeffBound f j` and just need an upper bound on the
executable cut output.
-/
theorem abs_psiCut_le_of_natAbs_le
    (p a b : Nat) (y z : Int) (B : Nat)
    (hbound : y.natAbs ≤ B)
    (hsep_a : 2 * B < p ^ a)
    (hsep_b : 2 * B < p ^ b)
    (hcongr : y % ((p ^ a : Nat) : Int) = z % ((p ^ a : Nat) : Int)) :
    (psiCut p a b z).natAbs ≤ B := by
  rw [psiCut_eq_zero_of_natAbs_le p a b y z B hbound hsep_a hsep_b hcongr]
  exact Nat.zero_le _

/--
In-range coordinate of `cldCoeffs`: for `j < deg(f)`, the executable
`cldCoeffs` array entry is exactly `psiCut` applied to the corresponding
quotient coefficient.
-/
theorem cldCoeffs_getD_of_lt
    (f : ZPoly) (p a : Nat) (g : ZPoly) (j : Nat)
    (h : j < f.degree?.getD 0) :
    (cldCoeffs f p a g).getD j 0 =
      psiCut p a (bhksCoeffCutThreshold p f j) ((cldQuotientMod f g p a).coeff j) := by
  unfold cldCoeffs
  rw [Array.getD_eq_getD_getElem?]
  have hlen :
      ((List.range (f.degree?.getD 0)).map (fun j =>
        psiCut p a (bhksCoeffCutThreshold p f j)
          ((cldQuotientMod f g p a).coeff j))).length = f.degree?.getD 0 := by
    simp
  have hsize :
      ((List.range (f.degree?.getD 0)).map (fun j =>
        psiCut p a (bhksCoeffCutThreshold p f j)
          ((cldQuotientMod f g p a).coeff j))).toArray.size = f.degree?.getD 0 := by
    simp [hlen]
  rw [Array.getElem?_eq_getElem (by simpa [hsize] using h)]
  simp [List.getElem_toArray, List.getElem_map, List.getElem_range]

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

def bhksLatticeEntry
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
    (hrows : 1 ≤ L.factorCount + L.coeffWidth) : BhksProjectedRows :=
  let reducedRows :=
    lll.shortVectorsUnchecked L.basis (3 / 4) lll_delta_lower lll_delta_upper hrows
  let reducedBasis :=
    bhksRowsArrayToMatrix (L.factorCount + L.coeffWidth) reducedRows
  { factorCount := L.factorCount
    coeffWidth := L.coeffWidth
    cutRadiusSq4 := bhksCutRadiusSq4 L
    reducedRowCount := reducedRows.size
    projectedRows := bhksCutProjectReducedRows L reducedBasis }

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

/-
Regression guard for #6217. The exact integer CLD coefficient of
`cldGuardF = x^2 - 5x + 6` against the true factor `g = x - 2` at index 0 is
`-3`, so under the centered cut the executable `cldCoeffs` at this index is
`0`. Without ambient centering the result was `125`, which exceeded
`bhksCoeffBound cldGuardF 0 = 16`.
-/
#guard (cldCoeffs cldGuardF 5 6 cldGuardG).getD 0 0 = 0
#guard (cldCoeffs cldGuardF 5 6 cldGuardG).getD 1 0 = 0

namespace BHKS

/--
BHKS Lemma 5.1 column bound for the executable `cldCoeffs`.

If there exists an exact integer `y` (morally `[x^j] (f * g'.derivative / g')`
for a true integer factor `g'` of `f` that Hensel-lifts to `g`) congruent to
`(cldQuotientMod f g p a).coeff j` modulo `p^a` and satisfying
`|y| ≤ bhksCoeffBound f j`, then under the Hensel precision hypothesis
`2 * bhksCoeffBound f j < p^a` and `p ≥ 2`, the executable `cldCoeffs` entry
at index `j` is bounded by `bhksCoeffBound f j`.

This replaces the original unconditional `#5224` target — the
counterexample of `#6217` showed the executable cut had to be re-centered at
the ambient modulus before this column bound could hold. The recentering
landed in `Hex.psiCut`; the bound is then a direct consequence of
`abs_psiCut_le_of_natAbs_le` plus `precisionForCoeffBound_spec` for the
lower cut threshold.
-/
theorem abs_cldCoeffs_le_bhksCoeffBound
    (f g : ZPoly) (p a j : Nat) (y : Int)
    (hp : 2 ≤ p)
    (hbound : y.natAbs ≤ bhksCoeffBound f j)
    (hsep_a : 2 * bhksCoeffBound f j < p ^ a)
    (hcongr : y % ((p ^ a : Nat) : Int) =
              (cldQuotientMod f g p a).coeff j % ((p ^ a : Nat) : Int)) :
    ((cldCoeffs f p a g).getD j 0).natAbs ≤ bhksCoeffBound f j := by
  have hsep_b : 2 * bhksCoeffBound f j < p ^ bhksCoeffCutThreshold p f j := by
    unfold bhksCoeffCutThreshold
    have := le_pow_ceilLogP hp (2 * bhksCoeffBound f j + 1)
    omega
  by_cases hlt : j < f.degree?.getD 0
  · rw [cldCoeffs_getD_of_lt f p a g j hlt]
    exact abs_psiCut_le_of_natAbs_le p a (bhksCoeffCutThreshold p f j)
      y ((cldQuotientMod f g p a).coeff j) (bhksCoeffBound f j)
      hbound hsep_a hsep_b hcongr
  · -- Out-of-range index: `cldCoeffs` returns 0 by `Array.getD` default.
    have hsize :
        (cldCoeffs f p a g).size = f.degree?.getD 0 := by
      unfold cldCoeffs
      simp
    have hge : (cldCoeffs f p a g).size ≤ j := by
      simpa [hsize] using Nat.le_of_not_lt hlt
    rw [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none hge]
    simp

end BHKS

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

def bhksInsertSignatureClass
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

/-- Coefficientwise description of `centeredLiftPoly`. -/
theorem coeff_centeredLiftPoly (f : ZPoly) (m i : Nat) :
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

/-- The array selected by a `0/1` BHKS indicator row. -/
def bhksIndicatorSelectedFactorsArray
    (liftedFactors : Array ZPoly) (indicator : Array Int) : Array ZPoly :=
  (List.range indicator.size).foldl
    (fun selected i =>
      if indicator.getD i 0 == 1 then
        selected.push (liftedFactors.getD i 0)
      else
        selected)
    #[]

/--
Successful branch of `bhksIndicatorSelectedFactors` for well-formed `0/1`
indicator rows, returning the canonical selected-factor array.
-/
theorem bhksIndicatorSelectedFactors_eq_some_selectedArray_of_getD
    (liftedFactors : Array ZPoly) (indicator : Array Int)
    (hsize : indicator.size = liftedFactors.size)
    (hbits : ∀ i, i < indicator.size →
      indicator.getD i 0 = 0 ∨ indicator.getD i 0 = 1)
    (hnonempty : ∃ i, i < indicator.size ∧ indicator.getD i 0 = 1) :
    bhksIndicatorSelectedFactors liftedFactors indicator =
      some (bhksIndicatorSelectedFactorsArray liftedFactors indicator) := by
  unfold bhksIndicatorSelectedFactors bhksIndicatorSelectedFactorsArray
  have hsizeBool : (indicator.size != liftedFactors.size) = false := by
    simp [hsize]
  rw [hsizeBool]
  simp only [Bool.false_eq_true, if_false]
  have hall :
      (List.range indicator.size).all
          (fun i => indicator.getD i 0 == 0 || indicator.getD i 0 == 1) = true := by
    rw [List.all_eq_true]
    intro i hi
    have hi_size : i < indicator.size := List.mem_range.mp hi
    rcases hbits i hi_size with hzero | hone
    · simp [hzero]
    · simp [hone]
  have hany :
      (List.range indicator.size).any
          (fun i => indicator.getD i 0 == 1) = true := by
    rw [List.any_eq_true]
    rcases hnonempty with ⟨i, hi_size, hone⟩
    exact ⟨i, List.mem_range.mpr hi_size, by simp [hone]⟩
  change
    (if
        ((List.range indicator.size).all
            (fun i => indicator.getD i 0 == 0 || indicator.getD i 0 == 1) &&
          (List.range indicator.size).any
            (fun i => indicator.getD i 0 == 1)) = true then
      some
        ((List.range indicator.size).foldl
          (fun selected i =>
            if (indicator.getD i 0 == 1) = true then
              selected.push (liftedFactors.getD i 0)
            else
              selected)
          #[])
    else
      none) =
      some
        ((List.range indicator.size).foldl
          (fun selected i =>
            if (indicator.getD i 0 == 1) = true then
              selected.push (liftedFactors.getD i 0)
            else
              selected)
          #[])
  rw [hall, hany]
  rfl

/--
Successful branch of `bhksIndicatorSelectedFactors`, stated with an explicit
name for the selected-factor array chosen by the caller.
-/
theorem bhksIndicatorSelectedFactors_eq_some_of_getD
    (liftedFactors : Array ZPoly) (indicator : Array Int)
    (selected : Array ZPoly)
    (hsize : indicator.size = liftedFactors.size)
    (hbits : ∀ i, i < indicator.size →
      indicator.getD i 0 = 0 ∨ indicator.getD i 0 = 1)
    (hnonempty : ∃ i, i < indicator.size ∧ indicator.getD i 0 = 1)
    (hselected :
      selected = bhksIndicatorSelectedFactorsArray liftedFactors indicator) :
    bhksIndicatorSelectedFactors liftedFactors indicator = some selected := by
  rw [hselected]
  exact
    bhksIndicatorSelectedFactors_eq_some_selectedArray_of_getD
      liftedFactors indicator hsize hbits hnonempty

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
      let candidate := normalizeFactorSign <| normalizeCandidateFactor <|
        centeredLiftPoly (ZPoly.reduceModPow raw d.p d.k) modulus
      if shouldRecordPolynomialFactor candidate then
        match exactQuotient? f candidate with
        | some quotient => some (candidate, quotient)
        | none => none
      else
        none

private theorem bhksIndicatorCandidate?_normalizeFactorSign
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidate? f d indicator = some (candidate, quotient)) :
    normalizeFactorSign candidate = candidate := by
  unfold bhksIndicatorCandidate? at h
  cases hselected : bhksIndicatorSelectedFactors d.liftedFactors indicator with
  | none =>
      simp [hselected] at h
  | some selected =>
      simp only [hselected] at h
      let modulus := liftModulus d
      let raw := DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected)
      let candidate0 :=
        normalizeCandidateFactor
          (centeredLiftPoly (ZPoly.reduceModPow raw d.p d.k) modulus)
      let candidate' := normalizeFactorSign candidate0
      change
        (if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? f candidate' with
          | some quotient => some (candidate', quotient)
          | none => none
        else
          none) = some (candidate, quotient) at h
      by_cases hrecord : shouldRecordPolynomialFactor candidate'
      · rw [if_pos hrecord] at h
        cases hquot : exactQuotient? f candidate' with
        | none =>
            simp [hquot] at h
        | some quotient' =>
            simp [hquot] at h
            rcases h with ⟨hcandidate, _hquotient⟩
            subst candidate
            exact normalizeFactorSign_idem candidate0
      · rw [if_neg hrecord] at h
        simp at h

private theorem bhksIndicatorCandidate?_shouldRecord
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidate? f d indicator = some (candidate, quotient)) :
    shouldRecordPolynomialFactor candidate = true := by
  unfold bhksIndicatorCandidate? at h
  cases hselected : bhksIndicatorSelectedFactors d.liftedFactors indicator with
  | none =>
      simp [hselected] at h
  | some selected =>
      simp only [hselected] at h
      let modulus := liftModulus d
      let raw := DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected)
      let candidate0 :=
        normalizeCandidateFactor
          (centeredLiftPoly (ZPoly.reduceModPow raw d.p d.k) modulus)
      let candidate' := normalizeFactorSign candidate0
      change
        (if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? f candidate' with
          | some quotient => some (candidate', quotient)
          | none => none
        else
          none) = some (candidate, quotient) at h
      by_cases hrecord : shouldRecordPolynomialFactor candidate'
      · rw [if_pos hrecord] at h
        cases hquot : exactQuotient? f candidate' with
        | none =>
            simp [hquot] at h
        | some quotient' =>
            simp [hquot] at h
            rcases h with ⟨hcandidate, _hquotient⟩
            subst candidate
            exact hrecord
      · rw [if_neg hrecord] at h
        simp at h

/--
A successful BHKS indicator candidate divides `f`. The executable
`bhksIndicatorCandidate?` only returns `some (candidate, _)` after
`exactQuotient? f candidate` succeeds, so the candidate is a verified
integer divisor of `f`.
-/
private theorem bhksIndicatorCandidate?_dvd
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidate? f d indicator = some (candidate, quotient)) :
    candidate ∣ f := by
  unfold bhksIndicatorCandidate? at h
  cases hselected : bhksIndicatorSelectedFactors d.liftedFactors indicator with
  | none =>
      simp [hselected] at h
  | some selected =>
      simp only [hselected] at h
      let modulus := liftModulus d
      let raw := DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected)
      let candidate0 :=
        normalizeCandidateFactor
          (centeredLiftPoly (ZPoly.reduceModPow raw d.p d.k) modulus)
      let candidate' := normalizeFactorSign candidate0
      change
        (if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? f candidate' with
          | some quotient => some (candidate', quotient)
          | none => none
        else
          none) = some (candidate, quotient) at h
      by_cases hrecord : shouldRecordPolynomialFactor candidate'
      · rw [if_pos hrecord] at h
        cases hquot : exactQuotient? f candidate' with
        | none =>
            simp [hquot] at h
        | some quotient' =>
            simp [hquot] at h
            rcases h with ⟨hcandidate, hquotient⟩
            subst candidate
            subst quotient
            have hmul : quotient' * candidate' = f := exactQuotient?_product hquot
            refine ⟨quotient', ?_⟩
            rw [DensePoly.mul_comm_poly (S := Int)]
            exact hmul.symm
      · rw [if_neg hrecord] at h
        simp at h

/-- If `normalizeCandidateFactor g` is nonzero, it is primitive: the inner
`primitivePart g` must then be nonzero, hence `content g ≠ 0`, hence
`content (primitivePart g) = 1` (and `scale (-1)` preserves content). -/
private theorem normalizeCandidateFactor_primitive
    {g : ZPoly} (hne : normalizeCandidateFactor g ≠ 0) :
    ZPoly.Primitive (normalizeCandidateFactor g) := by
  unfold normalizeCandidateFactor at hne ⊢
  by_cases hlead :
      DensePoly.leadingCoeff (ZPoly.primitivePart g) < 0
  · rw [if_pos hlead] at hne ⊢
    have hprim_ne :
        (ZPoly.primitivePart g : ZPoly) ≠ 0 := by
      intro hzero
      apply hne
      show DensePoly.scale (-1 : Int) (ZPoly.primitivePart g) = 0
      rw [hzero]
      exact DensePoly.scale_neg_one_zero
    have hcontent_ne : ZPoly.content g ≠ 0 := by
      intro hzero
      apply hprim_ne
      show DensePoly.primitivePart g = 0
      exact
        DensePoly.primitivePart_eq_zero_of_content_eq_zero g
          (by simpa [ZPoly.content] using hzero)
    have hprim_primitive : ZPoly.Primitive (ZPoly.primitivePart g) :=
      ZPoly.primitivePart_primitive g hcontent_ne
    show ZPoly.content
        (DensePoly.scale (-1 : Int) (ZPoly.primitivePart g)) = 1
    rw [show ZPoly.content
            (DensePoly.scale (-1 : Int) (ZPoly.primitivePart g))
          = DensePoly.content
              (DensePoly.scale (-1 : Int) (ZPoly.primitivePart g)) from rfl,
        DensePoly.content_scale_neg_one (ZPoly.primitivePart g)]
    exact hprim_primitive
  · rw [if_neg hlead] at hne ⊢
    have hcontent_ne : ZPoly.content g ≠ 0 := by
      intro hzero
      apply hne
      show DensePoly.primitivePart g = 0
      exact
        DensePoly.primitivePart_eq_zero_of_content_eq_zero g
          (by simpa [ZPoly.content] using hzero)
    exact ZPoly.primitivePart_primitive g hcontent_ne

/-- A successful BHKS indicator candidate has nonnegative leading coefficient:
the final `normalizeFactorSign` layer is a fixed point on the candidate, so
the candidate inherits the `≥ 0` leading-coefficient guarantee of
`normalizeFactorSign`. -/
private theorem bhksIndicatorCandidate?_leadingCoeff_nonneg
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidate? f d indicator = some (candidate, quotient)) :
    0 ≤ DensePoly.leadingCoeff candidate := by
  have hnorm := bhksIndicatorCandidate?_normalizeFactorSign h
  have hsign := normalizeFactorSign_leadingCoeff_nonneg candidate
  rwa [hnorm] at hsign

/-- A successful BHKS indicator candidate is primitive: the candidate equals
`normalizeFactorSign (normalizeCandidateFactor _)`, and `shouldRecord = true`
forces the inner factor to be nonzero, hence primitive. -/
private theorem bhksIndicatorCandidate?_primitive
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidate? f d indicator = some (candidate, quotient)) :
    ZPoly.Primitive candidate := by
  unfold bhksIndicatorCandidate? at h
  cases hselected : bhksIndicatorSelectedFactors d.liftedFactors indicator with
  | none =>
      simp [hselected] at h
  | some selected =>
      simp only [hselected] at h
      let modulus := liftModulus d
      let raw :=
        DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected)
      let candidate0 :=
        normalizeCandidateFactor
          (centeredLiftPoly (ZPoly.reduceModPow raw d.p d.k) modulus)
      let candidate' := normalizeFactorSign candidate0
      change
        (if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? f candidate' with
          | some quotient => some (candidate', quotient)
          | none => none
        else
          none) = some (candidate, quotient) at h
      by_cases hrecord : shouldRecordPolynomialFactor candidate'
      · rw [if_pos hrecord] at h
        cases hquot : exactQuotient? f candidate' with
        | none =>
            simp [hquot] at h
        | some quotient' =>
            simp [hquot] at h
            rcases h with ⟨hcandidate, _hquotient⟩
            subst candidate
            have hcand'_ne : candidate' ≠ 0 := by
              intro hzero
              rw [hzero] at hrecord
              unfold shouldRecordPolynomialFactor at hrecord
              simp at hrecord
            have hcand0_ne : candidate0 ≠ 0 := by
              intro hzero
              apply hcand'_ne
              show normalizeFactorSign candidate0 = 0
              rw [hzero]
              unfold normalizeFactorSign
              have hlc :
                  ¬ DensePoly.leadingCoeff (0 : ZPoly) < 0 := by
                simp
              rw [if_neg hlc]
            have hprim_cand0 : ZPoly.Primitive candidate0 :=
              normalizeCandidateFactor_primitive hcand0_ne
            exact normalizeFactorSign_primitive _ hprim_cand0
      · rw [if_neg hrecord] at h
        simp at h

/-- A successful BHKS indicator candidate has positive degree: it is primitive
with nonnegative leading coefficient and is not a unit, so it cannot be a
constant polynomial. -/
private theorem bhksIndicatorCandidate?_positive_degree
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidate? f d indicator = some (candidate, quotient)) :
    0 < candidate.degree?.getD 0 := by
  have hrecord := bhksIndicatorCandidate?_shouldRecord h
  have hprim := bhksIndicatorCandidate?_primitive h
  have hsign := bhksIndicatorCandidate?_leadingCoeff_nonneg h
  have hne : candidate ≠ 0 := by
    intro hzero
    rw [hzero] at hrecord
    unfold shouldRecordPolynomialFactor at hrecord
    simp at hrecord
  have hne_one : candidate ≠ 1 := by
    intro hone
    rw [hone] at hrecord
    unfold shouldRecordPolynomialFactor at hrecord
    simp at hrecord
  have hne_neg : candidate ≠ DensePoly.C (-1 : Int) := by
    intro hneg
    rw [hneg] at hrecord
    unfold shouldRecordPolynomialFactor at hrecord
    simp at hrecord
  -- Show `candidate.size ≥ 2`.  Otherwise `candidate` collapses to a
  -- constant polynomial, and `Primitive` + `0 ≤ leadingCoeff` + `≠ 0` + `≠ 1`
  -- + `≠ DensePoly.C (-1)` gives a contradiction.
  have hsize_pos : 0 < candidate.size := by
    rcases Nat.lt_or_ge 0 candidate.size with hpos | _hle
    · exact hpos
    · have hsz : candidate.size = 0 := by omega
      have hcand_zero : candidate = 0 := by
        apply DensePoly.ext_coeff
        intro n
        rw [DensePoly.coeff_zero]
        exact DensePoly.coeff_eq_zero_of_size_le candidate (by omega)
      exact False.elim (hne hcand_zero)
  have hsize_ge_two : 2 ≤ candidate.size := by
    rcases Nat.lt_or_ge 1 candidate.size with hge | _hle
    · omega
    · have hsize_one : candidate.size = 1 := by omega
      have hcandidate_eq : candidate = DensePoly.C (candidate.coeff 0) := by
        apply DensePoly.ext_coeff
        intro n
        cases n with
        | zero =>
            rw [DensePoly.coeff_C]
            simp
        | succ n =>
            rw [DensePoly.coeff_C, if_neg (Nat.succ_ne_zero n)]
            exact DensePoly.coeff_eq_zero_of_size_le candidate (by omega)
      have hprim_C :
          DensePoly.content (DensePoly.C (candidate.coeff 0)) = 1 := by
        have hcontent_eq : DensePoly.content candidate
            = DensePoly.content (DensePoly.C (candidate.coeff 0)) :=
          congrArg DensePoly.content hcandidate_eq
        exact hcontent_eq.symm.trans hprim
      have hcontent_C_eq :
          DensePoly.content (DensePoly.C (candidate.coeff 0))
            = Int.ofNat (candidate.coeff 0).natAbs :=
        DensePoly.content_C (candidate.coeff 0)
      have hnat_int :
          Int.ofNat (candidate.coeff 0).natAbs = 1 := by
        rw [← hcontent_C_eq]
        exact hprim_C
      have hnat : (candidate.coeff 0).natAbs = 1 := by
        exact Int.ofNat.inj hnat_int
      have hc_cases :
          candidate.coeff 0 = ↑(1 : Nat) ∨ candidate.coeff 0 = -↑(1 : Nat) :=
        Int.natAbs_eq_iff.mp hnat
      exfalso
      rcases hc_cases with hpos | hneg
      · apply hne_one
        rw [hcandidate_eq]
        show DensePoly.C (candidate.coeff 0) = DensePoly.C 1
        rw [hpos]
        rfl
      · apply hne_neg
        rw [hcandidate_eq]
        show DensePoly.C (candidate.coeff 0) = DensePoly.C (-1)
        rw [hneg]
        rfl
  -- Now `candidate.size ≥ 2`, so degree = size - 1 ≥ 1 > 0.
  have hne_size : candidate.size ≠ 0 := by omega
  have hdeg_eq :
      (DensePoly.degree? candidate).getD 0 = candidate.size - 1 := by
    unfold DensePoly.degree?
    rw [dif_neg hne_size]
    rfl
  show 0 < (DensePoly.degree? candidate).getD 0
  rw [hdeg_eq]
  omega

/--
The candidate returned by a successful `bhksIndicatorCandidate?` call is
exactly the canonical normalization of the centred lift of the modular product.
This is a Mathlib-free surface lemma that downstream Mathlib-side proofs use to
identify the candidate against the centred lift, avoiding the need to reference
the private `liftModulus` definition from outside this file.
-/
theorem bhksIndicatorCandidate?_eq_normalized_centeredLift
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly} {selected : Array ZPoly}
    (h : bhksIndicatorCandidate? f d indicator = some (candidate, quotient))
    (hselected : bhksIndicatorSelectedFactors d.liftedFactors indicator = some selected) :
    candidate = normalizeFactorSign (normalizeCandidateFactor
      (centeredLiftPoly
        (ZPoly.reduceModPow
          (DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected))
          d.p d.k)
        (d.p ^ d.k))) := by
  unfold bhksIndicatorCandidate? at h
  rw [hselected] at h
  let modulus := liftModulus d
  let raw := DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected)
  let candidate0 :=
    normalizeCandidateFactor
      (centeredLiftPoly (ZPoly.reduceModPow raw d.p d.k) modulus)
  let candidate' := normalizeFactorSign candidate0
  change
    (if shouldRecordPolynomialFactor candidate' then
      match exactQuotient? f candidate' with
      | some quotient => some (candidate', quotient)
      | none => none
    else
      none) = some (candidate, quotient) at h
  by_cases hrecord : shouldRecordPolynomialFactor candidate'
  · rw [if_pos hrecord] at h
    cases hquot : exactQuotient? f candidate' with
    | none => simp [hquot] at h
    | some quotient' =>
        simp [hquot] at h
        rcases h with ⟨hcandidate, _hquotient⟩
        subst candidate
        rfl
  · rw [if_neg hrecord] at h
    simp at h

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
  have hnormalizeCandidate :
      normalizeCandidateFactor
          (centeredLiftPoly (ZPoly.reduceModPow raw d.p d.k) (d.p ^ d.k)) =
        expectedFactor := by
    rw [hlift]
    exact normalizeCandidateFactor_eq_of_primitive_nonneg_leading
      expectedFactor hexpected_prim hexpected_sign
  have hnormalize :
      normalizeFactorSign (normalizeCandidateFactor
          (centeredLiftPoly (ZPoly.reduceModPow raw d.p d.k) (d.p ^ d.k))) =
        expectedFactor := by
    rw [hnormalizeCandidate]
    exact normalizeFactorSign_eq_self_of_leadingCoeff_nonneg expectedFactor hexpected_sign
  have hrecord :
      shouldRecordPolynomialFactor expectedFactor = true := by
    apply shouldRecordPolynomialFactor_eq_true_of_ne
    · intro hzero
      rw [hzero] at hexpected_degree
      simp [DensePoly.degree?] at hexpected_degree
    · intro hone
      rw [hone] at hexpected_degree
      have hdeg0 : (DensePoly.degree? (1 : ZPoly)).getD 0 = 0 := by
        rfl
      rw [hdeg0] at hexpected_degree
      omega
    · intro hneg
      rw [hneg] at hexpected_degree
      have hdeg0 : (DensePoly.degree? (DensePoly.C (-1 : Int))).getD 0 = 0 := by
        simp
      rw [hdeg0] at hexpected_degree
      omega
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
       normalizeFactorSign <| normalizeCandidateFactor
         (centeredLiftPoly (ZPoly.reduceModPow raw d.p d.k) modulus)
     if shouldRecordPolynomialFactor candidate then
       match exactQuotient? f candidate with
       | some quotient => some (candidate, quotient)
       | none => none
     else
       none) = some (expectedFactor, quotient)
  simp [raw, liftModulus, hnormalize, hrecord, hquotient]

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

private theorem bhksIndicatorCandidatesStep_fold_none
    (f : ZPoly) (d : LiftData) (indicators : List (Array Int)) :
    List.foldl (bhksIndicatorCandidatesStep f d) none indicators = none := by
  induction indicators with
  | nil => rfl
  | cons indicator indicators ih =>
      rw [List.foldl_cons]
      simpa [bhksIndicatorCandidatesStep] using ih

private theorem bhksIndicatorCandidatesStep_fold_all_of_candidate
    (P : ZPoly → Prop)
    (f : ZPoly) (d : LiftData)
    (hcandidate :
      ∀ {indicator candidate quotient},
        bhksIndicatorCandidate? f d indicator = some (candidate, quotient) →
          P candidate) :
    ∀ (indicators : List (Array Int)) (acc candidates : Array ZPoly),
      (∀ factor ∈ acc.toList, P factor) →
        List.foldl (bhksIndicatorCandidatesStep f d) (some acc) indicators =
            some candidates →
          ∀ factor ∈ candidates.toList, P factor
  | [], acc, candidates, hacc, hfold => by
      simp at hfold
      cases hfold
      exact hacc
  | indicator :: indicators, acc, candidates, hacc, hfold => by
      rw [List.foldl_cons] at hfold
      cases hhead : bhksIndicatorCandidate? f d indicator with
      | none =>
          have hnone :=
            bhksIndicatorCandidatesStep_fold_none f d indicators
          simp [bhksIndicatorCandidatesStep, hhead, hnone] at hfold
      | some pair =>
          rcases pair with ⟨candidate, quotient⟩
          have hnext :
              List.foldl (bhksIndicatorCandidatesStep f d) (some (acc.push candidate))
                  indicators = some candidates := by
            simpa [bhksIndicatorCandidatesStep, hhead] using hfold
          have hacc_push :
              ∀ factor ∈ (acc.push candidate).toList, P factor := by
            intro factor hmem
            rw [Array.toList_push] at hmem
            simp only [List.mem_append, List.mem_singleton] at hmem
            cases hmem with
            | inl hacc_mem => exact hacc factor hacc_mem
            | inr hfactor =>
                rw [hfactor]
                exact hcandidate hhead
          exact
            bhksIndicatorCandidatesStep_fold_all_of_candidate
              P f d hcandidate indicators (acc.push candidate) candidates
              hacc_push hnext

private theorem bhksIndicatorCandidates?_all_of_candidate
    (P : ZPoly → Prop)
    (f : ZPoly) (d : LiftData)
    (hcandidate :
      ∀ {indicator candidate quotient},
        bhksIndicatorCandidate? f d indicator = some (candidate, quotient) →
          P candidate)
    {indicators : Array (Array Int)} {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, P factor := by
  unfold bhksIndicatorCandidates? at h
  rw [← Array.foldl_toList] at h
  exact
    bhksIndicatorCandidatesStep_fold_all_of_candidate
      P f d hcandidate indicators.toList #[] candidates (by simp) h

private theorem bhksIndicatorCandidates?_normalizeFactorSign
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, normalizeFactorSign factor = factor :=
  bhksIndicatorCandidates?_all_of_candidate
    (fun factor => normalizeFactorSign factor = factor)
    f d (fun hcandidate => bhksIndicatorCandidate?_normalizeFactorSign hcandidate) h

private theorem bhksIndicatorCandidates?_shouldRecord
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, shouldRecordPolynomialFactor factor = true :=
  bhksIndicatorCandidates?_all_of_candidate
    (fun factor => shouldRecordPolynomialFactor factor = true)
    f d (fun hcandidate => bhksIndicatorCandidate?_shouldRecord hcandidate) h

/-- Every candidate emitted by `bhksIndicatorCandidates?` divides the
input polynomial; this is the per-candidate version of the verified
exact-division check performed inside `bhksIndicatorCandidate?`. -/
theorem bhksIndicatorCandidates?_dvd
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, factor ∣ f :=
  bhksIndicatorCandidates?_all_of_candidate
    (fun factor => factor ∣ f)
    f d (fun hcandidate => bhksIndicatorCandidate?_dvd hcandidate) h

/-- Every candidate emitted by `bhksIndicatorCandidates?` is primitive.  This
is the array-level form of the per-candidate primitivity guarantee from
`normalizeCandidateFactor` plus sign normalisation. -/
theorem bhksIndicatorCandidates?_primitive
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, ZPoly.Primitive factor :=
  bhksIndicatorCandidates?_all_of_candidate
    (fun factor => ZPoly.Primitive factor)
    f d (fun hcandidate => bhksIndicatorCandidate?_primitive hcandidate) h

/-- Every candidate emitted by `bhksIndicatorCandidates?` has nonnegative
leading coefficient; this is the array-level form of the per-candidate sign
normalisation guarantee. -/
theorem bhksIndicatorCandidates?_leadingCoeff_nonneg
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, 0 ≤ DensePoly.leadingCoeff factor :=
  bhksIndicatorCandidates?_all_of_candidate
    (fun factor => 0 ≤ DensePoly.leadingCoeff factor)
    f d (fun hcandidate => bhksIndicatorCandidate?_leadingCoeff_nonneg hcandidate) h

/-- Every candidate emitted by `bhksIndicatorCandidates?` has positive degree;
this is the array-level form of the per-candidate nonconstant guarantee. -/
theorem bhksIndicatorCandidates?_positive_degree
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, 0 < factor.degree?.getD 0 :=
  bhksIndicatorCandidates?_all_of_candidate
    (fun factor => 0 < factor.degree?.getD 0)
    f d (fun hcandidate => bhksIndicatorCandidate?_positive_degree hcandidate) h

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

private theorem bhksIndicatorCandidatesStep_fold_size_eq
    (f : ZPoly) (d : LiftData) :
    ∀ (indicators : List (Array Int)) (acc candidates : Array ZPoly),
      List.foldl (bhksIndicatorCandidatesStep f d) (some acc) indicators =
          some candidates →
        candidates.size = acc.size + indicators.length
  | [], acc, candidates, hfold => by
      simp at hfold
      cases hfold
      simp
  | indicator :: indicators, acc, candidates, hfold => by
      rw [List.foldl_cons] at hfold
      cases hhead : bhksIndicatorCandidate? f d indicator with
      | none =>
          have hnone :=
            bhksIndicatorCandidatesStep_fold_none f d indicators
          simp [bhksIndicatorCandidatesStep, hhead, hnone] at hfold
      | some pair =>
          rcases pair with ⟨candidate, quotient⟩
          have hnext :
              List.foldl (bhksIndicatorCandidatesStep f d)
                  (some (acc.push candidate)) indicators = some candidates := by
            simpa [bhksIndicatorCandidatesStep, hhead] using hfold
          have ih :=
            bhksIndicatorCandidatesStep_fold_size_eq f d indicators
              (acc.push candidate) candidates hnext
          rw [ih, Array.size_push, List.length_cons]
          omega

/--
A successful BHKS indicator-candidate fold produces a candidate array of the
same size as the input indicator array.  This is the size identity used by
`ExpectedTrueFactors`-shaped consumers that need to align the per-index
indicator and factor views.
-/
theorem bhksIndicatorCandidates?_size_eq
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    candidates.size = indicators.size := by
  unfold bhksIndicatorCandidates? at h
  rw [← Array.foldl_toList] at h
  have hfold :=
    bhksIndicatorCandidatesStep_fold_size_eq f d indicators.toList #[] candidates h
  simpa [Array.length_toList] using hfold

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
    let projected := bhksProjectedRows L hrows
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
          (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows
              (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)) = false)
    (hcand :
      bhksIndicatorCandidates? f d
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows
              (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)) =
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

/-- Fuelled auxiliary for `recombinationSearchMod`.  Recurses through
`subsetSplitsWithFirst localFactors`: at every level the head local factor is
forced into the candidate, the centred-lift result is normalised and checked
against `shouldRecordPolynomialFactor`, and a successful `exactQuotient?`
divides the search down to the remaining local factors and quotient. -/
def recombinationSearchModAux
    (target : ZPoly) (modulus : Nat) (localFactors : List ZPoly) :
    Nat → Option (List ZPoly)
  | 0 => none
  | fuel + 1 =>
      if target = 1 then
        some []
      else
        firstSome (subsetSplitsWithFirst localFactors) fun split =>
          let candidate :=
            normalizeFactorSign <|
              ZPoly.primitivePart <|
                centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
          if shouldRecordPolynomialFactor candidate then
            match exactQuotient? target candidate with
            | none => none
            | some quotient =>
                match recombinationSearchModAux quotient modulus split.2 fuel with
                | none => none
                | some rest => some (candidate :: rest)
          else
            none

/-- Exhaustive lifted-factor recombination search at a fixed modulus.  Drives
the slow path by iterating subsets of the lifted local factors through
`recombinationSearchModAux`. -/
def recombinationSearchMod
    (f : ZPoly) (modulus : Nat) (localFactors : List ZPoly) : Option (List ZPoly) :=
  recombinationSearchModAux f modulus localFactors (localFactors.length + 1)

/-- Exhaustive recombination of the lifted local factors stored in `d`, run at
the Hensel modulus `p^k = liftModulus d`.  Returns the recovered integer
factors as an array on success and `#[]` when the search fails. -/
def recombineExhaustive (f : ZPoly) (d : LiftData) : Array ZPoly :=
  match recombinationSearchMod f (liftModulus d) d.liftedFactors.toList with
  | some factors => factors.toArray
  | none => #[]

/-- Scaled-candidate variant of `recombinationSearchModAux`.

The per-step candidate is built from the lifted-factor product *after* scaling
by the integer `coreLc` parameter (intended to be the leading coefficient of
the integer core polynomial), then centre-lifted, primitivised, and
sign-normalised.  For `coreLc = 1` the inner `DensePoly.scale 1 _ = _`
collapse recovers the original unscaled `recombinationSearchModAux` candidate
shape; for primitive non-monic cores the scaled product is the integer factor
identified by `RepresentsIntegerFactorAtLift`, so this variant is the basis of
the primitive recursive coverage chain. -/
def scaledRecombinationSearchModAux
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (localFactors : List ZPoly) :
    Nat → Option (List ZPoly)
  | 0 => none
  | fuel + 1 =>
      if target = 1 then
        some []
      else
        firstSome (subsetSplitsWithFirst localFactors) fun split =>
          let candidate :=
            normalizeFactorSign <|
              ZPoly.primitivePart <|
                centeredLiftPoly
                  (DensePoly.scale coreLc (Array.polyProduct split.1.toArray))
                  modulus
          if shouldRecordPolynomialFactor candidate then
            match exactQuotient? target candidate with
            | none => none
            | some quotient =>
                match scaledRecombinationSearchModAux coreLc quotient modulus
                    split.2 fuel with
                | none => none
                | some rest => some (candidate :: rest)
          else
            none

/-- Surface wrapper for `scaledRecombinationSearchModAux` mirroring
`recombinationSearchMod`: drives the search with fuel `localFactors.length + 1`,
which suffices to exhaust the recursion since every step strictly shrinks the
remaining local-factor list. -/
def scaledRecombinationSearchMod
    (coreLc : Int) (f : ZPoly) (modulus : Nat) (localFactors : List ZPoly) :
    Option (List ZPoly) :=
  scaledRecombinationSearchModAux coreLc f modulus localFactors
    (localFactors.length + 1)

/-- Exhaustive recombination of the lifted local factors stored in `d`,
using the *scaled* candidate shape parameterised by the integer leading
coefficient `coreLc`.  Returns the recovered integer factors as an array
on success and `#[]` when the search fails.

For `coreLc = 1` the inner scaling collapses and this coincides with
`recombineExhaustive`; for primitive non-monic cores `coreLc` is taken
to be the core's leading coefficient and the recovered factors are
primitive normalised divisors of the core. -/
def recombineScaledExhaustive
    (coreLc : Int) (f : ZPoly) (d : LiftData) : Array ZPoly :=
  match scaledRecombinationSearchMod coreLc f (liftModulus d)
      d.liftedFactors.toList with
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

/-- BHKS fast-core recombination loop, exposed publicly so that Mathlib-side
lemmas can quantify over its success state.  Internally driven by the
classified BHKS recovery `bhksRecoverClassified`; `none` indicates the
loop exhausted its precision bound without producing a verified factor
list. -/
def factorFastCoreWithBound
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

This is the connective schedule lemma used by the Mathlib-facing Group D
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
  letI := bounds_five
  let c : SmallPrimeCandidate :=
    { p := 5, bounds := bounds_five, prime := prime_five }
  { p := 5
    fModP := ZPoly.modP 5 cldGuardF
    factorsModP := berlekampFactorsModP cldGuardF c }

#guard factorFastCoreWithBound cldGuardF 1 factorFastCoreGuardPrimeData
    (initialHenselPrecision 1) (ZPoly.quadraticDoublingSteps 1 + 2) =
  none

#guard factorFastCoreWithBound cldGuardF 4 factorFastCoreGuardPrimeData
    (initialHenselPrecision 4) (ZPoly.quadraticDoublingSteps 4 + 2) =
  some bhksGuardFactors

namespace ZPoly

/--
Build the fixed-precision Hensel lift data for the monic transform of an
integer core.  The exhaustive slow path still recombines against the original
primitive core, but the lift stage sees the monic polynomial required by the
Hensel pipeline.
-/
def toMonicLiftData
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) : LiftData :=
  henselLiftData (toMonic core).monic
    (precisionForCoeffBound B primeData.p) primeData

/--
Optional prime-choice data for the monic polynomial sent to Hensel lifting.

The public factoring pipeline still chooses prime data from the original core.
This adjacent surface is for proof callers that need Berlekamp-form modular
factor data for `(toMonic core).monic`, the polynomial that `toMonicLiftData`
passes to `henselLiftData`.
-/
def toMonicPrimeData? (core : ZPoly) : Option PrimeChoiceData :=
  choosePrimeData? (toMonic core).monic

theorem toMonicPrimeData?_prime
    (core : ZPoly) (data : PrimeChoiceData)
    (hdata : toMonicPrimeData? core = some data) :
    Nat.Prime data.p := by
  exact choosePrimeData?_prime (toMonic core).monic data hdata

theorem toMonicPrimeData?_isGoodPrime
    (core : ZPoly) (data : PrimeChoiceData)
    (hdata : toMonicPrimeData? core = some data) :
    @isGoodPrime (toMonic core).monic data.p data.bounds = true := by
  exact choosePrimeData?_isGoodPrime (toMonic core).monic data hdata

theorem toMonicPrimeData?_factorsModP_berlekamp_form
    (core : ZPoly) (data : PrimeChoiceData)
    (hdata : toMonicPrimeData? core = some data) :
    factorsModPBerlekampForm (toMonic core).monic data := by
  obtain ⟨hzero, heq⟩ :=
    choosePrimeData?_factorsModP_berlekamp_form
      (toMonic core).monic data hdata
  exact ⟨toMonicPrimeData?_prime core data hdata, hzero, heq⟩

end ZPoly

def exhaustiveCoreFactorsWithBound
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) : Array ZPoly :=
  if B = 0 then
    #[core]
  else
    let liftData := ZPoly.toMonicLiftData core B primeData
    let factors :=
      recombineScaledExhaustive (DensePoly.leadingCoeff core) core liftData
    if factors.isEmpty then
      #[core]
    else
      factors

/-- Option-returning prime-data witness for the `cldGuardF` executable
guard. `cldGuardF` is selected so `choosePrimeData?` succeeds; the
`#guard` below asserts the success and ties the guard expectation to the
unwrapped value, exercising the `Option`-propagating boundary per #5831
(HO-5d-1b) instead of routing through total `choosePrimeData`. -/
private def exhaustiveMonicCoreGuardPrimeData? : Option PrimeChoiceData :=
  choosePrimeData? cldGuardF

#guard
  match exhaustiveMonicCoreGuardPrimeData? with
  | none => false
  | some primeData =>
      exhaustiveCoreFactorsWithBound cldGuardF 4 primeData =
        let liftData :=
          henselLiftData cldGuardF (precisionForCoeffBound 4 primeData.p) primeData
        let factors := recombineScaledExhaustive (DensePoly.leadingCoeff cldGuardF)
          cldGuardF liftData
        if factors.isEmpty then #[cldGuardF] else factors

private def exhaustiveNonMonicQuadraticGuard : ZPoly :=
  DensePoly.ofCoeffs #[1, 0, 2]

#guard (ZPoly.toMonic exhaustiveNonMonicQuadraticGuard).monic =
  DensePoly.ofCoeffs #[2, 0, 1]

#guard quadraticIntegerRootFactors? exhaustiveNonMonicQuadraticGuard = none

#guard
  match choosePrimeData? exhaustiveNonMonicQuadraticGuard with
  | none => false
  | some primeData =>
      (exhaustiveCoreFactorsWithBound exhaustiveNonMonicQuadraticGuard 4
            primeData).toList.all fun factor => normalizeFactorSign factor == factor

/-- The raw slow-path factor array used by the exhaustive recombination branch.

The body dispatches via the compatibility `choosePrimeData` wrapper. Callers
that need explicit failure on no admissible prime should use
`exhaustiveSlowRawFactorsWithBound?`. -/
def exhaustiveSlowRawFactorsWithBound (f : ZPoly) (B : Nat) : Array ZPoly :=
  reassemblePolynomialFactors (normalizeForFactor f)
    (exhaustiveCoreFactorsWithBound (normalizeForFactor f).squareFreeCore B
      (choosePrimeData (normalizeForFactor f).squareFreeCore))

/-- Option-returning slow-path raw factor array. Returns `some` exactly
when `choosePrimeData?` succeeds on the normalized square-free core,
mirroring `factorFastFactorsWithBound`'s `none`-on-no-good-prime
contract. Provides the Option-propagating boundary recommended by #5831
(HO-5d-1b) for the slow exhaustive raw-factor path. -/
def exhaustiveSlowRawFactorsWithBound? (f : ZPoly) (B : Nat) : Option (Array ZPoly) :=
  (choosePrimeData? (normalizeForFactor f).squareFreeCore).map fun primeData =>
    reassemblePolynomialFactors (normalizeForFactor f)
      (exhaustiveCoreFactorsWithBound (normalizeForFactor f).squareFreeCore B primeData)

/-- When `choosePrimeData?` succeeds, the `?` variant agrees with the
total `exhaustiveSlowRawFactorsWithBound`. -/
theorem exhaustiveSlowRawFactorsWithBound?_eq_some_of_isSome
    (f : ZPoly) (B : Nat)
    (h : (choosePrimeData? (normalizeForFactor f).squareFreeCore).isSome) :
    exhaustiveSlowRawFactorsWithBound? f B =
      some (exhaustiveSlowRawFactorsWithBound f B) := by
  obtain ⟨primeData, hchoose⟩ := Option.isSome_iff_exists.mp h
  unfold exhaustiveSlowRawFactorsWithBound? exhaustiveSlowRawFactorsWithBound
  rw [choosePrimeData_eq_of_choosePrimeData?_some hchoose, hchoose]
  rfl

/-- Raw factor array produced by the modular slow recombination branch.

Exposed publicly so the Mathlib-side layer can express per-branch
irreducibility hypotheses for the assembled output theorem.  Internal callers
go through the `factorSlowModular` wrapper. This path returns `none` when no
admissible modular prime is available. -/
def factorSlowModularFactorsWithBound (f : ZPoly) (B : Nat) : Option (Array ZPoly) :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    some (reassemblePolynomialFactors normalized #[normalized.squareFreeCore])
  else
    match quadraticIntegerRootFactors? normalized.squareFreeCore with
    | some coreFactors => some (reassemblePolynomialFactors normalized coreFactors)
    | none =>
        (choosePrimeData? normalized.squareFreeCore).map fun primeData =>
          reassemblePolynomialFactors normalized
            (exhaustiveCoreFactorsWithBound normalized.squareFreeCore B primeData)

#guard factorSlowModularFactorsWithBound exhaustiveNonMonicQuadraticGuard 4 =
  some #[exhaustiveNonMonicQuadraticGuard]

/-- Transitional total raw modular factor array retained for existing proof
surfaces while the public API moves to `factorSlowModularFactorsWithBound`.
New callers should use the `Option`-valued modular name or the total
`factorSlowTrialFactorsWithBound` backstop. -/
def factorSlowFactorsWithBound (f : ZPoly) (B : Nat) : Array ZPoly :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    reassemblePolynomialFactors normalized #[normalized.squareFreeCore]
  else
    match quadraticIntegerRootFactors? normalized.squareFreeCore with
    | some coreFactors => reassemblePolynomialFactors normalized coreFactors
    | none =>
        let primeData := choosePrimeData normalized.squareFreeCore
        let coreFactors :=
          exhaustiveCoreFactorsWithBound normalized.squareFreeCore B primeData
        reassemblePolynomialFactors normalized coreFactors

/-- Characterise the safe branch of `factorSlowModularFactorsWithBound`.

The modular form returns `some (factorSlowFactorsWithBound f B)` exactly on the
constant, quadratic-root, and prime-data-available branches, and `none` on the
branch that the transitional total array still handles through
`choosePrimeData`. -/
theorem factorSlowModularFactorsWithBound_eq_some_iff_safe_branch (f : ZPoly) (B : Nat) :
    factorSlowModularFactorsWithBound f B =
      (if (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0 ∨
          (quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore).isSome ∨
          (choosePrimeData? (normalizeForFactor f).squareFreeCore).isSome
        then some (factorSlowFactorsWithBound f B) else none) := by
  unfold factorSlowModularFactorsWithBound factorSlowFactorsWithBound
  by_cases hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · simp [hdeg]
  · simp only [hdeg, if_false]
    cases hquad : quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore with
    | some coreFactors => simp
    | none =>
        cases hchoose : choosePrimeData? (normalizeForFactor f).squareFreeCore with
        | none => simp
        | some primeData =>
            rw [choosePrimeData_eq_of_choosePrimeData?_some hchoose]
            simp

set_option maxHeartbeats 800000

/-- Classify the raw slow-path factor array by the dispatch branch that emitted
it. The final recorded `Factorization` entries still pass through
`collectFactorMultiplicities`; use `factorizationOfFactors_entry_mem_normalized_raw`
or `factorWithBound_entry_mem_raw_source` for that layer. -/
theorem factorSlowFactorsWithBound_branch
    (f : ZPoly) (B : Nat) :
    (factorSlowFactorsWithBound f B =
        reassemblePolynomialFactors (normalizeForFactor f)
          #[(normalizeForFactor f).squareFreeCore] ∧
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0) ∨
    (∃ coreFactors : Array ZPoly,
      factorSlowFactorsWithBound f B =
        reassemblePolynomialFactors (normalizeForFactor f) coreFactors ∧
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 ∧
      quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore =
        some coreFactors) ∨
    (factorSlowFactorsWithBound f B =
        reassemblePolynomialFactors (normalizeForFactor f)
          (exhaustiveCoreFactorsWithBound
            (normalizeForFactor f).squareFreeCore B
            (choosePrimeData
              (normalizeForFactor f).squareFreeCore)) ∧
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 ∧
      quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none) := by
  unfold factorSlowFactorsWithBound
  by_cases hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · left
    constructor
    · simp only [hdeg, if_true]
    · exact hdeg
  · right
    cases hquad : quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore with
    | some coreFactors =>
        left
        refine ⟨coreFactors, ?_, hdeg, rfl⟩
        simp only [hdeg, hquad, if_false]
    | none =>
        right
        constructor
        · simp only [hdeg, hquad, if_false]
        · exact ⟨hdeg, rfl⟩

/-- Witness-form variant of `factorSlowFactorsWithBound_branch`: the
exhaustive branch's core array is computed against an explicit
`primeData` paired with `hchoose : choosePrimeData? sf = some primeData`,
removing the silent fallback dispatch from the disjunct's statement. -/
theorem factorSlowFactorsWithBound_branch_of_choosePrimeData?_some
    (f : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    (hchoose :
      choosePrimeData? (normalizeForFactor f).squareFreeCore = some primeData) :
    (factorSlowFactorsWithBound f B =
        reassemblePolynomialFactors (normalizeForFactor f)
          #[(normalizeForFactor f).squareFreeCore] ∧
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0) ∨
    (∃ coreFactors : Array ZPoly,
      factorSlowFactorsWithBound f B =
        reassemblePolynomialFactors (normalizeForFactor f) coreFactors ∧
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 ∧
      quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore =
        some coreFactors) ∨
    (factorSlowFactorsWithBound f B =
        reassemblePolynomialFactors (normalizeForFactor f)
          (exhaustiveCoreFactorsWithBound
            (normalizeForFactor f).squareFreeCore B primeData) ∧
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 ∧
      quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none) := by
  have hwf :
      choosePrimeData (normalizeForFactor f).squareFreeCore = primeData :=
    choosePrimeData_eq_of_choosePrimeData?_some hchoose
  have hbranch := factorSlowFactorsWithBound_branch f B
  rw [hwf] at hbranch
  exact hbranch

def factorSlowModularWithBound (f : ZPoly) (B : Nat) : Option Factorization :=
  (factorSlowModularFactorsWithBound f B).map (factorizationOfFactors f)

private def factorSlowWithBound (f : ZPoly) (B : Nat) : Factorization :=
  factorizationOfFactors f (factorSlowFactorsWithBound f B)

private theorem factorSlowModularFactorsWithBound_eq_some_eq_factorSlowFactorsWithBound
    {f : ZPoly} {B : Nat} {rawFactors : Array ZPoly}
    (h : factorSlowModularFactorsWithBound f B = some rawFactors) :
    rawFactors = factorSlowFactorsWithBound f B := by
  rw [factorSlowModularFactorsWithBound] at h
  unfold factorSlowFactorsWithBound
  by_cases hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · simp [hdeg] at h ⊢
    exact h.symm
  · simp only [hdeg, if_false] at h ⊢
    cases hquad : quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore with
    | some coreFactors =>
        simp [hquad] at h ⊢
        exact h.symm
    | none =>
        cases hchoose : choosePrimeData? (normalizeForFactor f).squareFreeCore with
        | none =>
            simp [hquad, hchoose] at h
        | some primeData =>
            have hchoose_total :
                choosePrimeData (normalizeForFactor f).squareFreeCore = primeData :=
              choosePrimeData_eq_of_choosePrimeData?_some hchoose
            simp [hquad, hchoose, hchoose_total] at h ⊢
            exact h.symm

/--
Factor using the modular recombination path at the default Mignotte
coefficient bound. This is the middle tier of the three-tier BZ API and
returns `none` when no admissible modular prime is available.
-/
def factorSlowModular (f : ZPoly) : Option Factorization :=
  factorSlowModularWithBound f (ZPoly.defaultFactorCoeffBound f)

def factorSlow (f : ZPoly) : Factorization :=
  factorSlowWithBound f (ZPoly.defaultFactorCoeffBound f)

@[simp] theorem factorSlowModular_eq_factorSlowModularWithBound_default
    (f : ZPoly) :
    factorSlowModular f =
      factorSlowModularWithBound f (ZPoly.defaultFactorCoeffBound f) := rfl

/-- Compatibility theorem for existing product proofs: when the canonical
Option-valued modular path succeeds, its result agrees with the old total
array view used internally by the current proof layer. -/
theorem factorSlowModularWithBound_eq_some_eq_factorSlowWithBound
    {f : ZPoly} {B : Nat} {φ : Factorization}
    (h : factorSlowModularWithBound f B = some φ) :
    φ = factorSlowWithBound f B := by
  unfold factorSlowModularWithBound at h
  cases hraw : factorSlowModularFactorsWithBound f B with
  | none =>
      rw [hraw] at h
      simp at h
  | some rawFactors =>
      have hraw_eq :
          rawFactors = factorSlowFactorsWithBound f B :=
        factorSlowModularFactorsWithBound_eq_some_eq_factorSlowFactorsWithBound hraw
      rw [hraw] at h
      change some (factorizationOfFactors f rawFactors) = some φ at h
      change φ = factorizationOfFactors f (factorSlowFactorsWithBound f B)
      rw [← hraw_eq]
      exact (Option.some.inj h).symm

theorem factorSlowModularWithBound_eq_some_iff_safe_branch (f : ZPoly) (B : Nat) :
    factorSlowModularWithBound f B =
      (if (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0 ∨
          (quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore).isSome ∨
          (choosePrimeData? (normalizeForFactor f).squareFreeCore).isSome
        then some (factorSlowWithBound f B) else none) := by
  by_cases hsafe :
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0 ∨
        (quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore).isSome ∨
        (choosePrimeData? (normalizeForFactor f).squareFreeCore).isSome
  · rw [if_pos hsafe]
    unfold factorSlowModularWithBound
    rw [factorSlowModularFactorsWithBound_eq_some_iff_safe_branch, if_pos hsafe]
    rfl
  · unfold factorSlowModularWithBound
    rw [factorSlowModularFactorsWithBound_eq_some_iff_safe_branch]
    simp [hsafe]

/-- Raw factor array produced by the integer trial-division slow path.

Mirrors `factorSlowFactorsWithBound`'s constant/quadratic-root short-circuits
so the deg-0 core and integer-root cases are handled up front; the residual
exhaustive branch dispatches to the standalone integer trial-division core
(`exhaustiveIntegerTrialCoreFactorsWithBound`) instead of the modular
recombination one. This is the trial-division tier of the three-tier
`factor` combinator (SPEC PR #6580). -/
def factorSlowTrialFactorsWithBound (f : ZPoly) (B : Nat) : Array ZPoly :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    reassemblePolynomialFactors normalized #[normalized.squareFreeCore]
  else
    match quadraticIntegerRootFactors? normalized.squareFreeCore with
    | some coreFactors => reassemblePolynomialFactors normalized coreFactors
    | none =>
        let coreFactors :=
          exhaustiveIntegerTrialCoreFactorsWithBound normalized.squareFreeCore B
        reassemblePolynomialFactors normalized coreFactors

#guard factorSlowTrialFactorsWithBound exhaustiveNonMonicQuadraticGuard 4 =
  #[exhaustiveNonMonicQuadraticGuard]

private def factorSlowTrialWithBound (f : ZPoly) (B : Nat) : Factorization :=
  factorizationOfFactors f (factorSlowTrialFactorsWithBound f B)

/--
Factor using the integer trial-division path at the default Mignotte
coefficient bound. This is the trial-division tier of the three-tier
`factor` combinator (SPEC PR #6580).
-/
def factorSlowTrial (f : ZPoly) : Factorization :=
  factorSlowTrialWithBound f (ZPoly.defaultFactorCoeffBound f)

#guard factorSlowModular exhaustiveNonMonicQuadraticGuard =
  some (factorSlowTrial exhaustiveNonMonicQuadraticGuard)

/-- Raw factor array produced by the fast BHKS branch, when it succeeds.

Exposed publicly so the Mathlib-side layer can express per-branch
irreducibility hypotheses for the assembled output theorem.  Internal callers
still go through the `factorFast` wrapper. -/
def factorFastFactorsWithBound (f : ZPoly) (B : Nat) : Option (Array ZPoly) :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    some (reassemblePolynomialFactors normalized #[normalized.squareFreeCore])
  else if B = 0 then
    none
  else
    if B = 1 then
      match choosePrimeData? normalized.squareFreeCore with
      | none => none
      | some primeData =>
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
        match choosePrimeData? normalized.squareFreeCore with
        | none => none
        | some primeData =>
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

/-- Public branch predicate for the `factorWithBound` slow exhaustive modular
fallback. Under the three-tier `factor` combinator (SPEC PR #6580) this branch
fires only when `choosePrimeData?` selects an admissible prime; the
no-admissible-prime case is routed to `factorSlowTrial` and is *not* covered
by this predicate. -/
def factorWithBoundUsesExhaustiveBranch (f : ZPoly) (B : Nat) : Prop :=
  factorFastFactorsWithBound f B = none ∧
    (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 ∧
    quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none ∧
    (choosePrimeData? (normalizeForFactor f).squareFreeCore).isSome

/-- Lift a successful `factorFastCoreWithBound` call to a `factorFastFactorsWithBound`
success conclusion. The hypotheses pin down the wrapper's branch dispatch: the
input is not zero-degree (`hdeg`), the recombination budget is at least one
(`hB_pos`), the small-mod singleton predicate fails (`hnotsingleton`), and
(when `B ≠ 1`) the quadratic-root short-circuit does not apply (`hquadratic`).
The `hnotsingleton` premise is the post-#4605 form: the small-mod singleton
branch fires when `(choosePrimeData? sf).isSome ∧ size ≤ 1` is true; its
negation routes the dispatcher to the BHKS core call, which is what this
lemma's `hcore` invariant uses. -/
private theorem factorFastFactorsWithBound_eq_some_of_core_success
    (f : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    (coreFactors : Array ZPoly)
    (hB_pos : 1 ≤ B)
    (hchoose : choosePrimeData? (normalizeForFactor f).squareFreeCore = some primeData)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hnotsingleton :
      ¬ primeData.factorsModP.size ≤ 1)
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
    simp [hchoose, hnotsingleton, hcore]
  · rw [if_neg hB1]
    have hq : quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none := by
      cases hquadratic with
      | inl heq => exact absurd heq hB1
      | inr hnone => exact hnone
    rw [hq]
    simp [hchoose, hnotsingleton, hcore]

/-- Classify the raw fast-path factor array by the dispatch branch that
emitted it. Mirrors `factorSlowFactorsWithBound_branch` (line 5275) for the
fast path, which has more sub-cases due to the BHKS / quadratic-root /
small-mod prime classification cascade.

The disjunction is exhaustive but not mutually exclusive at the syntactic
level — disjuncts are distinguished by their marker conditions (degree of
the square-free core, value of `B`, size of `factorsModP`, and outcomes of
`quadraticIntegerRootFactors?` / `factorFastCoreWithBound`).

Downstream callers can dispatch each disjunct to the matching per-branch
entry-shape lemma:
* constant → `factorWithBound_entry_mem_constant_branch_raw` (line 5642);
* small-mod singleton → `factorWithBound_entry_mem_small_mod_singleton_raw`
  (line 5600);
* quadratic → `factorWithBound_entry_mem_quadratic_branch_raw` (line 5668);
* fast-core success → `factorWithBound_entry_mem_fast_core_success_raw`
  (line 5695).

Primary intended caller is the HO-1 capstone `factor_irreducible_of_nonUnit`
(`HexBerlekampZassenhausMathlib/Basic.lean:237`, #4170). -/
theorem factorFastFactorsWithBound_branch (f : ZPoly) (B : Nat) :
    (factorFastFactorsWithBound f B = none ∧
      ((normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 ∧ B = 0 ∨
       (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 ∧
         B = 1 ∧
         choosePrimeData? (normalizeForFactor f).squareFreeCore = none ∨
       (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 ∧
         1 < B ∧
         quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none ∧
         choosePrimeData? (normalizeForFactor f).squareFreeCore = none ∨
       True)) ∨
    (∃ factors, factorFastFactorsWithBound f B = some factors) := by
  cases hfast : factorFastFactorsWithBound f B with
  | none =>
      left
      exact ⟨rfl, Or.inr (Or.inr (Or.inr trivial))⟩
  | some factors =>
      right
      exact ⟨factors, rfl⟩

/-- Witness-form variant of `factorFastFactorsWithBound_branch`: the
small-mod and BHKS disjuncts reference `primeData` directly rather than
`choosePrimeData`, given an explicit
`hchoose : choosePrimeData? sf = some primeData`. Since `hchoose`
implies `primeData = choosePrimeData sf`, the (e), (i)
fast-core-none disjuncts that depend on the prime-data shape collapse
to a single fast-core-none disjunct (without the `isSome` clause, which
is automatic from `hchoose`).

Disjuncts whose statements never mention `choosePrimeData(WithFallback)`
((a), (b), (f)) are reproduced verbatim. -/
theorem factorFastFactorsWithBound_branch_of_choosePrimeData?_some
    (f : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    (hchoose :
      choosePrimeData? (normalizeForFactor f).squareFreeCore = some primeData) :
    -- (a) constant core
    (factorFastFactorsWithBound f B =
        some (reassemblePolynomialFactors (normalizeForFactor f)
          #[(normalizeForFactor f).squareFreeCore]) ∧
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0) ∨
    -- (b) B = 0
    (factorFastFactorsWithBound f B = none ∧
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 ∧
      B = 0) ∨
    -- (c) B = 1, small-mod singleton
    (factorFastFactorsWithBound f B =
        some (reassemblePolynomialFactors (normalizeForFactor f)
          #[(normalizeForFactor f).squareFreeCore]) ∧
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 ∧
      B = 1 ∧
      primeData.factorsModP.size ≤ 1) ∨
    -- (d) B = 1, fast-core success
    (∃ coreFactors, factorFastFactorsWithBound f B =
        some (reassemblePolynomialFactors (normalizeForFactor f) coreFactors) ∧
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 ∧
      B = 1 ∧
      ¬ primeData.factorsModP.size ≤ 1 ∧
      (let a := precisionForCoeffBound B primeData.p
       factorFastCoreWithBound (normalizeForFactor f).squareFreeCore a
         primeData (initialHenselPrecision a)
         (ZPoly.quadraticDoublingSteps a + 2) = some coreFactors)) ∨
    -- (e) B = 1, fast-core none
    (factorFastFactorsWithBound f B = none ∧
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 ∧
      B = 1 ∧
      ¬ primeData.factorsModP.size ≤ 1 ∧
      (let a := precisionForCoeffBound B primeData.p
       factorFastCoreWithBound (normalizeForFactor f).squareFreeCore a
         primeData (initialHenselPrecision a)
         (ZPoly.quadraticDoublingSteps a + 2) = none)) ∨
    -- (f) B > 1, quadratic
    (∃ coreFactors, factorFastFactorsWithBound f B =
        some (reassemblePolynomialFactors (normalizeForFactor f) coreFactors) ∧
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 ∧
      1 < B ∧
      quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore =
        some coreFactors) ∨
    -- (g) B > 1, small-mod singleton
    (factorFastFactorsWithBound f B =
        some (reassemblePolynomialFactors (normalizeForFactor f)
          #[(normalizeForFactor f).squareFreeCore]) ∧
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 ∧
      1 < B ∧
      quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none ∧
      primeData.factorsModP.size ≤ 1) ∨
    -- (h) B > 1, fast-core success
    (∃ coreFactors, factorFastFactorsWithBound f B =
        some (reassemblePolynomialFactors (normalizeForFactor f) coreFactors) ∧
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 ∧
      1 < B ∧
      quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none ∧
      ¬ primeData.factorsModP.size ≤ 1 ∧
      (let a := precisionForCoeffBound B primeData.p
       factorFastCoreWithBound (normalizeForFactor f).squareFreeCore a
         primeData (initialHenselPrecision a)
         (ZPoly.quadraticDoublingSteps a + 2) = some coreFactors)) ∨
    -- (i) B > 1, fast-core none
    (factorFastFactorsWithBound f B = none ∧
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 ∧
      1 < B ∧
      quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none ∧
      ¬ primeData.factorsModP.size ≤ 1 ∧
      (let a := precisionForCoeffBound B primeData.p
       factorFastCoreWithBound (normalizeForFactor f).squareFreeCore a
         primeData (initialHenselPrecision a)
         (ZPoly.quadraticDoublingSteps a + 2) = none)) := by
  unfold factorFastFactorsWithBound
  by_cases hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · left
    exact ⟨by rw [if_pos hdeg], hdeg⟩
  · rw [if_neg hdeg]
    by_cases hB0 : B = 0
    · right; left
      exact ⟨by rw [if_pos hB0], hdeg, hB0⟩
    · rw [if_neg hB0]
      by_cases hB1 : B = 1
      · rw [if_pos hB1]
        by_cases hsmall : primeData.factorsModP.size ≤ 1
        · right; right; left
          refine ⟨?_, hdeg, hB1, hsmall⟩
          simp [hchoose, hsmall]
        · cases hcore :
            factorFastCoreWithBound (normalizeForFactor f).squareFreeCore
              (precisionForCoeffBound B primeData.p) primeData
              (initialHenselPrecision (precisionForCoeffBound B primeData.p))
              (ZPoly.quadraticDoublingSteps (precisionForCoeffBound B primeData.p) + 2) with
          | some coreFactors =>
              right; right; right; left
              refine ⟨coreFactors, ?_, hdeg, hB1, hsmall, hcore⟩
              simp [hchoose, hsmall, hcore]
          | none =>
              right; right; right; right; left
              refine ⟨?_, hdeg, hB1, hsmall, hcore⟩
              simp [hchoose, hsmall, hcore]
      · rw [if_neg hB1]
        have hBgt : 1 < B := by omega
        cases hquad : quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore with
        | some coreFactors =>
            right; right; right; right; right; left
            refine ⟨coreFactors, ?_, hdeg, hBgt, rfl⟩
            rfl
        | none =>
            by_cases hsmall : primeData.factorsModP.size ≤ 1
            · right; right; right; right; right; right; left
              refine ⟨?_, hdeg, hBgt, rfl, hsmall⟩
              simp [hchoose, hsmall]
            · cases hcore :
                factorFastCoreWithBound (normalizeForFactor f).squareFreeCore
                  (precisionForCoeffBound B primeData.p) primeData
                  (initialHenselPrecision (precisionForCoeffBound B primeData.p))
                  (ZPoly.quadraticDoublingSteps
                    (precisionForCoeffBound B primeData.p) + 2) with
              | some coreFactors =>
                  right; right; right; right; right; right; right; left
                  refine ⟨coreFactors, ?_, hdeg, hBgt, rfl, hsmall, hcore⟩
                  simp [hchoose, hsmall, hcore]
              | none =>
                  right; right; right; right; right; right; right; right
                  refine ⟨?_, hdeg, hBgt, rfl, hsmall, hcore⟩
                  simp [hchoose, hsmall, hcore]

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

/--
Product of every odd prime searched by the historical bounded
`choosePrimeData?`: the fixed `smallPrimeCandidates` plus every prime formerly
materialized by the `73`/`128` extended list, namely
`3, 5, 7, 11, 13, 17, 19, 23, 31, 71, 73, 79, 83, 89, 97, 101, 103, 107,
109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271,
277, 281, 283, 293, 307, 311, 313, 317`.
-/
private def finitePrimeSearchProduct : Int :=
  8519695066439135286155430686880858459745606608870837864424372151015956571725147275621002356920661035228663328981905

/--
Regression fixture for the old bounded prime search. It is `P * X^2 + X + 1`,
where `P` is the product of every odd prime in the former closed candidate set.
For each formerly searched modulus the leading coefficient vanishes, while
over `Z` the quadratic has negative discriminant and hence no integer root.
The unbounded post-prefix walk now steps past that closed set and selects the
next good word-sized trial prime, so prime selection no longer falls through to
the no-prime branch on this input.
-/
private def finitePrimeSearchNoneQuadratic : ZPoly :=
  DensePoly.ofCoeffs #[1, 1, finitePrimeSearchProduct]

#guard
  match choosePrimeData? finitePrimeSearchNoneQuadratic with
  | none => false
  | some data => 317 < data.p

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
Expose the proof-facing fast-path success criterion used by the BHKS termination layer.
If a precision on `factorFast`'s scheduled search recovers a core
factorization for the normalized square-free core, then the public fast path
returns `some _`.
-/
theorem factorFast_ne_none_of_core_recovery_on_schedule
    (f : ZPoly) (primeData : PrimeChoiceData)
    {target : Nat} {coreFactors : Array ZPoly}
    (hB_pos : 1 ≤ factorFastPrecisionCap f)
    (hchoose :
      choosePrimeData? (normalizeForFactor f).squareFreeCore = some primeData)
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
        rw [hchoose]
        by_cases hpred : primeData.factorsModP.size ≤ 1
        · simp [hpred]
        · simp [hpred]
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
            rw [hchoose]
            by_cases hpred : primeData.factorsModP.size ≤ 1
            · simp [hpred]
            · simp [hpred]
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

Three-tier dispatch (SPEC PR #6580): the bounded fast path is tried first; on
`none` the modular slow path (`factorSlowModularWithBound`) is consulted; on
its `none` (i.e. when `choosePrimeData?` would otherwise route through the
silent fallback) the integer trial-division slow path supplies the returned
`Factorization`.
-/
def factorWithBound (f : ZPoly) (B : Nat) : Factorization :=
  match factorFastWithBound f B with
  | some r => r
  | none =>
    match factorSlowModularWithBound f B with
    | some r => r
    | none => factorSlowTrialWithBound f B

#guard Factorization.product (factorWithBound cldGuardF 1) = cldGuardF

/--
Factor using the three-tier combinator (SPEC PR #6580):
`factorFast → factorSlowModular → factorSlowTrial`, with the default Mignotte
coefficient bound.

The standalone `factorFast` entry point exposes the proof-facing combined
BHKS/Mignotte cap. The default total factorization combinator keeps the
runtime-oriented coefficient bound before falling back to the modular slow
path, and on no admissible prime continues to integer trial division so that
the removed silent prime-data fallback is never consulted.
-/
def factor (f : ZPoly) : Factorization :=
  factorWithBound f (ZPoly.defaultFactorCoeffBound f)

@[simp] theorem factor_eq_factorWithBound_default (f : ZPoly) :
    factor f = factorWithBound f (ZPoly.defaultFactorCoeffBound f) := rfl

/--
Option-returning bounded factoring entry point that propagates explicit failure
on no-admissible-prime. Returns `some (factorWithBound f B)` exactly on the
constant-core early-out, the quadratic-integer-root short-circuit, and the
prime-data-available case. Returns `none` precisely when both
`(quadraticIntegerRootFactors? sf)` and `(choosePrimeData? sf)` are `none` on
the normalized square-free core `sf`.

This is the additive Option-propagating boundary recommended by #5816 (and the
SPEC `design-principles.md` §8 fallback-discipline clause that #5775 raises).
-/
def factorWithBound? (f : ZPoly) (B : Nat) : Option Factorization :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    some (factorWithBound f B)
  else if (quadraticIntegerRootFactors? normalized.squareFreeCore).isSome then
    some (factorWithBound f B)
  else if (choosePrimeData? normalized.squareFreeCore).isSome then
    some (factorWithBound f B)
  else
    none

/--
Option-returning factoring entry point at the default Mignotte bound; mirrors
`factor` but propagates explicit failure on no-admissible-prime per #5816.
-/
def factor? (f : ZPoly) : Option Factorization :=
  factorWithBound? f (ZPoly.defaultFactorCoeffBound f)

@[simp] theorem factor?_eq_factorWithBound?_default (f : ZPoly) :
    factor? f = factorWithBound? f (ZPoly.defaultFactorCoeffBound f) := rfl

/-- When `factorWithBound?` succeeds, it agrees with the total `factorWithBound`.
The total form's fallback only engages on the `none` branch this function
exposes. -/
theorem factorWithBound?_eq_some_iff_safe_branch (f : ZPoly) (B : Nat) :
    factorWithBound? f B =
      (if (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0 ∨
          (quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore).isSome ∨
          (choosePrimeData? (normalizeForFactor f).squareFreeCore).isSome
        then some (factorWithBound f B) else none) := by
  unfold factorWithBound?
  by_cases hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · simp [hdeg]
  · by_cases hquad :
      (quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore).isSome
    · simp [hdeg, hquad]
    · by_cases hprime :
        (choosePrimeData? (normalizeForFactor f).squareFreeCore).isSome
      · simp [hdeg, hquad, hprime]
      · simp [hdeg, hquad, hprime]

/-- `factor?` and `factor` agree on the `some` branch (immediate from
`factorWithBound?_eq_some_iff_safe_branch`). -/
theorem factor?_eq_some_iff_safe_branch (f : ZPoly) :
    factor? f =
      (if (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0 ∨
          (quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore).isSome ∨
          (choosePrimeData? (normalizeForFactor f).squareFreeCore).isSome
        then some (factor f) else none) := by
  unfold factor? factor
  exact factorWithBound?_eq_some_iff_safe_branch f _

set_option maxHeartbeats 800000

/-- The bounded public factorization is built from one of three raw factor
arrays: the fast path's output (on `some`), the modular slow path's
`factorSlowFactorsWithBound` (when the fast path returns `none` and
`factorSlowModularWithBound` returns `some`), or the integer trial-division
slow path's `factorSlowTrialFactorsWithBound` (when both predecessors return
`none`). -/
theorem factorWithBound_eq_factorizationOfFactors (f : ZPoly) (B : Nat) :
    ∃ rawFactors : Array ZPoly,
      (factorFastFactorsWithBound f B = some rawFactors ∨
        (factorFastFactorsWithBound f B = none ∧
          (factorSlowModularWithBound f B).isSome = true ∧
          rawFactors = factorSlowFactorsWithBound f B) ∨
        (factorFastFactorsWithBound f B = none ∧
          factorSlowModularWithBound f B = none ∧
          rawFactors = factorSlowTrialFactorsWithBound f B)) ∧
      factorWithBound f B = factorizationOfFactors f rawFactors := by
  by_cases hfast : (factorFastFactorsWithBound f B).isSome
  · obtain ⟨rawFactors, hfast_some⟩ := Option.isSome_iff_exists.mp hfast
    refine ⟨rawFactors, Or.inl hfast_some, ?_⟩
    simp only [factorWithBound, factorFastWithBound, hfast_some, Option.map_some]
  · have hfast_none : factorFastFactorsWithBound f B = none :=
      Option.not_isSome_iff_eq_none.mp hfast
    have hfastWB : factorFastWithBound f B = none := by
      simp [factorFastWithBound, hfast_none]
    by_cases hmod : (factorSlowModularWithBound f B).isSome
    · obtain ⟨φ, hmod_some⟩ := Option.isSome_iff_exists.mp hmod
      have hφ : φ = factorSlowWithBound f B :=
        factorSlowModularWithBound_eq_some_eq_factorSlowWithBound hmod_some
      refine ⟨factorSlowFactorsWithBound f B,
        Or.inr (Or.inl ⟨hfast_none, hmod, rfl⟩), ?_⟩
      show factorWithBound f B =
        factorizationOfFactors f (factorSlowFactorsWithBound f B)
      unfold factorWithBound
      rw [hfastWB, hmod_some]
      exact hφ.trans rfl
    · have hmod_none : factorSlowModularWithBound f B = none :=
        Option.not_isSome_iff_eq_none.mp hmod
      refine ⟨factorSlowTrialFactorsWithBound f B,
        Or.inr (Or.inr ⟨hfast_none, hmod_none, rfl⟩), ?_⟩
      show factorWithBound f B =
        factorizationOfFactors f (factorSlowTrialFactorsWithBound f B)
      unfold factorWithBound
      rw [hfastWB, hmod_none]
      rfl

private theorem content_ne_zero_of_zpoly_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    ZPoly.content f ≠ 0 := by
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

private theorem signedContentScalarContract_eq_zero_iff (f : ZPoly) :
    (if f = 0 then
        0
      else if DensePoly.leadingCoeff f < 0 then
        -ZPoly.content f
      else
        ZPoly.content f) = 0 ↔ f = 0 := by
  constructor
  · intro h
    by_cases hf : f = 0
    · exact hf
    have hcontent_ne := content_ne_zero_of_zpoly_ne_zero f hf
    rw [if_neg hf] at h
    by_cases hneg : DensePoly.leadingCoeff f < 0
    · rw [if_pos hneg] at h
      exact absurd (Int.neg_eq_zero.mp h) hcontent_ne
    · rw [if_neg hneg] at h
      exact absurd h hcontent_ne
  · intro hf
    simp [hf]

/-- Scalar contract for a factorization assembled from a raw factor array.
The public statement exposes the signed-content convention without exposing
the private helper used to compute it. -/
theorem factorizationOfFactors_scalar (f : ZPoly) (rawFactors : Array ZPoly) :
    (factorizationOfFactors f rawFactors).scalar =
      if f = 0 then
        0
      else if DensePoly.leadingCoeff f < 0 then
        -ZPoly.content f
      else
        ZPoly.content f := by
  rfl

@[simp] theorem factorizationOfFactors_scalar_zero (rawFactors : Array ZPoly) :
    (factorizationOfFactors 0 rawFactors).scalar = 0 := by
  simp [factorizationOfFactors_scalar]

theorem factorizationOfFactors_scalar_of_leadingCoeff_neg
    {f : ZPoly} (rawFactors : Array ZPoly)
    (hf : f ≠ 0) (hneg : DensePoly.leadingCoeff f < 0) :
    (factorizationOfFactors f rawFactors).scalar = -ZPoly.content f := by
  simp [factorizationOfFactors_scalar, hf, hneg]

theorem factorizationOfFactors_scalar_of_leadingCoeff_pos
    {f : ZPoly} (rawFactors : Array ZPoly)
    (hf : f ≠ 0) (hpos : 0 < DensePoly.leadingCoeff f) :
    (factorizationOfFactors f rawFactors).scalar = ZPoly.content f := by
  have hnot_neg : ¬ DensePoly.leadingCoeff f < 0 := by omega
  simp [factorizationOfFactors_scalar, hf, hnot_neg]

theorem factorizationOfFactors_scalar_eq_zero_iff
    (f : ZPoly) (rawFactors : Array ZPoly) :
    (factorizationOfFactors f rawFactors).scalar = 0 ↔ f = 0 := by
  rw [factorizationOfFactors_scalar]
  exact signedContentScalarContract_eq_zero_iff f

/-- Scalar contract for the bounded public factorization entry point. -/
theorem factorWithBound_scalar (f : ZPoly) (B : Nat) :
    (factorWithBound f B).scalar =
      if f = 0 then
        0
      else if DensePoly.leadingCoeff f < 0 then
        -ZPoly.content f
      else
        ZPoly.content f := by
  obtain ⟨rawFactors, _hrawFactors, hfactor⟩ :=
    factorWithBound_eq_factorizationOfFactors f B
  rw [hfactor]
  exact factorizationOfFactors_scalar f rawFactors

@[simp] theorem factorWithBound_scalar_zero (B : Nat) :
    (factorWithBound 0 B).scalar = 0 := by
  simp [factorWithBound_scalar]

theorem factorWithBound_scalar_of_leadingCoeff_neg
    {f : ZPoly} (B : Nat)
    (hf : f ≠ 0) (hneg : DensePoly.leadingCoeff f < 0) :
    (factorWithBound f B).scalar = -ZPoly.content f := by
  simp [factorWithBound_scalar, hf, hneg]

theorem factorWithBound_scalar_of_leadingCoeff_pos
    {f : ZPoly} (B : Nat)
    (hf : f ≠ 0) (hpos : 0 < DensePoly.leadingCoeff f) :
    (factorWithBound f B).scalar = ZPoly.content f := by
  have hnot_neg : ¬ DensePoly.leadingCoeff f < 0 := by omega
  simp [factorWithBound_scalar, hf, hnot_neg]

theorem factorWithBound_scalar_eq_zero_iff (f : ZPoly) (B : Nat) :
    (factorWithBound f B).scalar = 0 ↔ f = 0 := by
  rw [factorWithBound_scalar]
  exact signedContentScalarContract_eq_zero_iff f

/-- Scalar contract for the default public factorization entry point. -/
theorem factor_scalar (f : ZPoly) :
    (factor f).scalar =
      if f = 0 then
        0
      else if DensePoly.leadingCoeff f < 0 then
        -ZPoly.content f
      else
        ZPoly.content f := by
  simpa [factor_eq_factorWithBound_default] using
    factorWithBound_scalar f (ZPoly.defaultFactorCoeffBound f)

@[simp] theorem factor_scalar_zero :
    (factor 0).scalar = 0 := by
  simp [factor_eq_factorWithBound_default]

theorem factor_scalar_of_leadingCoeff_neg
    {f : ZPoly} (hf : f ≠ 0) (hneg : DensePoly.leadingCoeff f < 0) :
    (factor f).scalar = -ZPoly.content f := by
  simpa [factor_eq_factorWithBound_default] using
    factorWithBound_scalar_of_leadingCoeff_neg
      (f := f) (ZPoly.defaultFactorCoeffBound f) hf hneg

theorem factor_scalar_of_leadingCoeff_pos
    {f : ZPoly} (hf : f ≠ 0) (hpos : 0 < DensePoly.leadingCoeff f) :
    (factor f).scalar = ZPoly.content f := by
  simpa [factor_eq_factorWithBound_default] using
    factorWithBound_scalar_of_leadingCoeff_pos
      (f := f) (ZPoly.defaultFactorCoeffBound f) hf hpos

theorem factor_scalar_eq_zero_iff (f : ZPoly) :
    (factor f).scalar = 0 ↔ f = 0 := by
  simpa [factor_eq_factorWithBound_default] using
    factorWithBound_scalar_eq_zero_iff f (ZPoly.defaultFactorCoeffBound f)

/-- Any recorded entry of `factorWithBound` comes from one of three raw factor
arrays: the fast path's output, the modular slow path's
`factorSlowFactorsWithBound` (when the fast path returns `none` and
`factorSlowModularWithBound` returns `some`), or the integer trial-division
slow path's `factorSlowTrialFactorsWithBound` (when both predecessors return
`none`), after the `collectFactorMultiplicities` sign-normalization step. -/
theorem factorWithBound_entry_mem_raw_source
    (f : ZPoly) (B : Nat) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factorWithBound f B).factors.toList) :
    ∃ rawFactors : Array ZPoly,
      (factorFastFactorsWithBound f B = some rawFactors ∨
        (factorFastFactorsWithBound f B = none ∧
          (factorSlowModularWithBound f B).isSome = true ∧
          rawFactors = factorSlowFactorsWithBound f B) ∨
        (factorFastFactorsWithBound f B = none ∧
          factorSlowModularWithBound f B = none ∧
          rawFactors = factorSlowTrialFactorsWithBound f B)) ∧
      ∃ raw ∈ rawFactors.toList, entry.1 = normalizeFactorSign raw := by
  obtain ⟨rawFactors, hrawFactors, hfactor⟩ :=
    factorWithBound_eq_factorizationOfFactors f B
  refine ⟨rawFactors, hrawFactors, ?_⟩
  apply factorizationOfFactors_entry_mem_normalized_raw
  simpa only [hfactor] using hmem

/-- Every recorded entry of `factorWithBound f B` is primitive once every raw
factor in the selected dispatch branch is primitive. The single hypothesis
`h_raw` covers all three tiers (fast, slow-modular, slow-trial) of the
three-tier `factor` combinator (SPEC PR #6580). -/
theorem factorWithBound_entry_primitive_of_chosen_raw_primitive
    {f : ZPoly} {B : Nat} {entry : ZPoly × Nat}
    (hmem : entry ∈ (factorWithBound f B).factors.toList)
    (h_raw :
      ∀ rawFactors : Array ZPoly,
        (factorFastFactorsWithBound f B = some rawFactors ∨
          (factorFastFactorsWithBound f B = none ∧
            (factorSlowModularWithBound f B).isSome = true ∧
            rawFactors = factorSlowFactorsWithBound f B) ∨
          (factorFastFactorsWithBound f B = none ∧
            factorSlowModularWithBound f B = none ∧
            rawFactors = factorSlowTrialFactorsWithBound f B)) →
        ∀ raw ∈ rawFactors.toList, ZPoly.Primitive raw) :
    ZPoly.Primitive entry.1 := by
  obtain ⟨rawFactors, hsource, raw, hraw_mem, hentry_eq⟩ :=
    factorWithBound_entry_mem_raw_source f B entry hmem
  rw [hentry_eq]
  exact normalizeFactorSign_primitive _ (h_raw rawFactors hsource raw hraw_mem)

/-- Every recorded entry of `factorWithBound f B` is primitive, assuming the
chosen raw factor array is primitive entrywise. -/
theorem factorWithBound_entries_primitive
    (f : ZPoly) (B : Nat)
    (h_raw :
      ∀ rawFactors : Array ZPoly,
        (factorFastFactorsWithBound f B = some rawFactors ∨
          (factorFastFactorsWithBound f B = none ∧
            (factorSlowModularWithBound f B).isSome = true ∧
            rawFactors = factorSlowFactorsWithBound f B) ∨
          (factorFastFactorsWithBound f B = none ∧
            factorSlowModularWithBound f B = none ∧
            rawFactors = factorSlowTrialFactorsWithBound f B)) →
        ∀ raw ∈ rawFactors.toList, ZPoly.Primitive raw) :
    ∀ entry ∈ (factorWithBound f B).factors, ZPoly.Primitive entry.1 := by
  intro entry hentry
  exact factorWithBound_entry_primitive_of_chosen_raw_primitive
    (Array.mem_toList_iff.mpr hentry) h_raw

/-- Every recorded entry of the bounded public factorization has positive
multiplicity. -/
theorem factorWithBound_entry_multiplicity_pos
    (f : ZPoly) (B : Nat) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factorWithBound f B).factors.toList) :
    0 < entry.2 := by
  obtain ⟨rawFactors, _hrawFactors, hfactor⟩ :=
    factorWithBound_eq_factorizationOfFactors f B
  apply factorizationOfFactors_entry_multiplicity_pos
  simpa only [hfactor] using hmem

/-- Every recorded entry of the bounded public factorization is fixed by
`normalizeFactorSign`. -/
theorem factorWithBound_entry_normalizeFactorSign_id
    (f : ZPoly) (B : Nat) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factorWithBound f B).factors.toList) :
    normalizeFactorSign entry.1 = entry.1 := by
  obtain ⟨rawFactors, _hrawFactors, hfactor⟩ :=
    factorWithBound_eq_factorizationOfFactors f B
  apply factorizationOfFactors_entry_normalizeFactorSign_id
  simpa only [hfactor] using hmem

/-- Every recorded entry of the bounded public factorization has positive
leading coefficient. -/
theorem factorWithBound_entry_leadingCoeff_pos
    (f : ZPoly) (B : Nat) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factorWithBound f B).factors.toList) :
    0 < DensePoly.leadingCoeff entry.1 := by
  obtain ⟨rawFactors, _hrawFactors, hfactor⟩ :=
    factorWithBound_eq_factorizationOfFactors f B
  apply factorizationOfFactors_entry_leadingCoeff_pos
  simpa only [hfactor] using hmem

/-- Every recorded entry of the bounded public factorization passes the
`shouldRecordPolynomialFactor` filter: the entry's polynomial is nonzero and
not a unit (`±1`).  Exposed publicly so Mathlib-side per-branch umbrellas can
rule out unit cores from the recorded entry set. -/
theorem factorWithBound_entry_shouldRecord
    (f : ZPoly) (B : Nat) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factorWithBound f B).factors.toList) :
    shouldRecordPolynomialFactor entry.1 = true := by
  obtain ⟨rawFactors, _hrawFactors, hfactor⟩ :=
    factorWithBound_eq_factorizationOfFactors f B
  have hmem' : entry ∈ (collectFactorMultiplicities rawFactors).toList := by
    simpa only [hfactor, factorizationOfFactors] using hmem
  exact collectFactorMultiplicities_entry_shouldRecord rawFactors entry hmem'

/-- The bounded public factorization has no duplicate polynomial keys. -/
theorem factorWithBound_pairwise_first
    (f : ZPoly) (B : Nat) :
    List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1)
      (factorWithBound f B).factors.toList := by
  obtain ⟨rawFactors, _hrawFactors, hfactor⟩ :=
    factorWithBound_eq_factorizationOfFactors f B
  simpa only [hfactor] using factorizationOfFactors_pairwise_first f rawFactors

/-- Every recorded entry of the default public factorization has positive
multiplicity. -/
theorem factor_entry_multiplicity_pos
    (f : ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factor f).factors.toList) :
    0 < entry.2 := by
  simpa [factor_eq_factorWithBound_default] using
    factorWithBound_entry_multiplicity_pos
      f (ZPoly.defaultFactorCoeffBound f) entry hmem

/-- Every recorded entry of the default public factorization is fixed by
`normalizeFactorSign`. -/
theorem factor_entry_normalizeFactorSign_id
    (f : ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factor f).factors.toList) :
    normalizeFactorSign entry.1 = entry.1 := by
  simpa [factor_eq_factorWithBound_default] using
    factorWithBound_entry_normalizeFactorSign_id
      f (ZPoly.defaultFactorCoeffBound f) entry hmem

/-- Every recorded entry of the default public factorization has positive
leading coefficient. -/
theorem factor_entry_leadingCoeff_pos
    (f : ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factor f).factors.toList) :
    0 < DensePoly.leadingCoeff entry.1 := by
  simpa [factor_eq_factorWithBound_default] using
    factorWithBound_entry_leadingCoeff_pos
      f (ZPoly.defaultFactorCoeffBound f) entry hmem

/-- Every recorded entry of the default public factorization passes the
`shouldRecordPolynomialFactor` filter. -/
theorem factor_entry_shouldRecord
    (f : ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factor f).factors.toList) :
    shouldRecordPolynomialFactor entry.1 = true := by
  simpa [factor_eq_factorWithBound_default] using
    factorWithBound_entry_shouldRecord
      f (ZPoly.defaultFactorCoeffBound f) entry hmem

/-- Any recorded entry of the default public factorization comes from the raw
factor array selected by one of the three tiers (fast, slow-modular,
slow-trial), up to sign normalization. -/
theorem factor_entry_mem_raw_source
    (f : ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (factor f).factors.toList) :
    ∃ rawFactors : Array ZPoly,
      (factorFastFactorsWithBound f (ZPoly.defaultFactorCoeffBound f) =
          some rawFactors ∨
        (factorFastFactorsWithBound f (ZPoly.defaultFactorCoeffBound f) =
            none ∧
          (factorSlowModularWithBound f (ZPoly.defaultFactorCoeffBound f)).isSome
            = true ∧
          rawFactors =
            factorSlowFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)) ∨
        (factorFastFactorsWithBound f (ZPoly.defaultFactorCoeffBound f) =
            none ∧
          factorSlowModularWithBound f (ZPoly.defaultFactorCoeffBound f) = none ∧
          rawFactors =
            factorSlowTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f))) ∧
      ∃ raw ∈ rawFactors.toList, entry.1 = normalizeFactorSign raw := by
  simpa [factor_eq_factorWithBound_default] using
    factorWithBound_entry_mem_raw_source
      f (ZPoly.defaultFactorCoeffBound f) entry hmem

/-- Every recorded entry of the default public factorization is primitive once
every raw factor in the selected default-precision dispatch branch is
primitive. -/
theorem factor_entry_primitive_of_chosen_raw_primitive
    {f : ZPoly} {entry : ZPoly × Nat}
    (hmem : entry ∈ (factor f).factors.toList)
    (h_raw :
      ∀ rawFactors : Array ZPoly,
        (factorFastFactorsWithBound f (ZPoly.defaultFactorCoeffBound f) =
            some rawFactors ∨
          (factorFastFactorsWithBound f (ZPoly.defaultFactorCoeffBound f) =
              none ∧
            (factorSlowModularWithBound f (ZPoly.defaultFactorCoeffBound f)).isSome
              = true ∧
            rawFactors =
              factorSlowFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)) ∨
          (factorFastFactorsWithBound f (ZPoly.defaultFactorCoeffBound f) =
              none ∧
            factorSlowModularWithBound f (ZPoly.defaultFactorCoeffBound f) = none ∧
            rawFactors =
              factorSlowTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f))) →
        ∀ raw ∈ rawFactors.toList, ZPoly.Primitive raw) :
    ZPoly.Primitive entry.1 :=
  factorWithBound_entry_primitive_of_chosen_raw_primitive
    (B := ZPoly.defaultFactorCoeffBound f)
    (by simpa [factor_eq_factorWithBound_default] using hmem)
    h_raw

/-- Default-precision specialisation of `factorWithBound_entries_primitive`
for the public `factor` entry point. -/
theorem factor_entries_primitive
    (f : ZPoly)
    (h_raw :
      ∀ rawFactors : Array ZPoly,
        (factorFastFactorsWithBound f (ZPoly.defaultFactorCoeffBound f) =
            some rawFactors ∨
          (factorFastFactorsWithBound f (ZPoly.defaultFactorCoeffBound f) =
              none ∧
            (factorSlowModularWithBound f (ZPoly.defaultFactorCoeffBound f)).isSome
              = true ∧
            rawFactors =
              factorSlowFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)) ∨
          (factorFastFactorsWithBound f (ZPoly.defaultFactorCoeffBound f) =
              none ∧
            factorSlowModularWithBound f (ZPoly.defaultFactorCoeffBound f) = none ∧
            rawFactors =
              factorSlowTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f))) →
        ∀ raw ∈ rawFactors.toList, ZPoly.Primitive raw) :
    ∀ entry ∈ (factor f).factors, ZPoly.Primitive entry.1 := by
  intro entry hentry
  exact factor_entry_primitive_of_chosen_raw_primitive
    (Array.mem_toList_iff.mpr hentry) h_raw

/-- The default public factorization has no duplicate polynomial keys. -/
theorem factor_pairwise_first
    (f : ZPoly) :
    List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1)
      (factor f).factors.toList := by
  simpa [factor_eq_factorWithBound_default] using
    factorWithBound_pairwise_first f (ZPoly.defaultFactorCoeffBound f)

/-- In the slow exhaustive modular fallback branch, every recorded
`factorWithBound` entry comes from the public raw exhaustive slow-factor
array, up to sign normalization by `collectFactorMultiplicities`. -/
theorem factorWithBound_entry_mem_exhaustive_branch_raw
    (f : ZPoly) (B : Nat) (entry : ZPoly × Nat)
    (hbranch : factorWithBoundUsesExhaustiveBranch f B)
    (hmem : entry ∈ (factorWithBound f B).factors.toList) :
    ∃ raw ∈ (exhaustiveSlowRawFactorsWithBound f B).toList,
      entry.1 = normalizeFactorSign raw := by
  obtain ⟨hfast, hdeg, hquad, hprime⟩ := hbranch
  obtain ⟨rawFactors, hsource, raw, hraw_mem, hraw_norm⟩ :=
    factorWithBound_entry_mem_raw_source f B entry hmem
  have hmod_some : (factorSlowModularWithBound f B).isSome = true := by
    unfold factorSlowModularWithBound factorSlowModularFactorsWithBound
    rw [if_neg hdeg, hquad]
    simpa using hprime
  rcases hsource with hfast_some | ⟨_, _, hrawFactors⟩ | ⟨_, hmod_none, _⟩
  · exfalso
    rw [hfast] at hfast_some
    cases hfast_some
  · subst rawFactors
    refine ⟨raw, ?_, hraw_norm⟩
    rw [exhaustiveSlowRawFactorsWithBound] at ⊢
    unfold factorSlowFactorsWithBound at hraw_mem
    rw [if_neg hdeg, hquad] at hraw_mem
    exact hraw_mem
  · exfalso
    rw [hmod_none] at hmod_some
    cases hmod_some

/-- Membership in the public exhaustive slow raw array splits into
normalization-prefix factors and exhaustive square-free-core factors. -/
theorem exhaustiveSlowRawFactorsWithBound_mem_normalization_or_core
    (f factor : ZPoly) (B : Nat)
    (hmem : factor ∈ (exhaustiveSlowRawFactorsWithBound f B).toList) :
    factor ∈ (polynomialNormalizationPrefixFactors (normalizeForFactor f)).toList ∨
      factor ∈
        (exhaustiveCoreFactorsWithBound (normalizeForFactor f).squareFreeCore B
          (choosePrimeData (normalizeForFactor f).squareFreeCore)).toList := by
  rw [exhaustiveSlowRawFactorsWithBound] at hmem
  exact reassemblePolynomialFactors_mem_normalization_or_core
    (normalizeForFactor f)
    (exhaustiveCoreFactorsWithBound (normalizeForFactor f).squareFreeCore B
      (choosePrimeData (normalizeForFactor f).squareFreeCore))
    factor hmem

/--
When the exhaustive slow branch's repeated-part expansion is complete, every
recorded `factorWithBound` entry from that branch comes either from the
extracted `X` power or from an exhaustive square-free-core factor. This is the
branch-shape theorem that rules out the non-decomposed repeated-part fallback
for callers that can prove the expansion-complete side condition.
-/
theorem factorWithBound_entry_mem_exhaustive_branch_xPower_or_core_of_reassemblyComplete
    (f : ZPoly) (B : Nat) (entry : ZPoly × Nat)
    (primeData : PrimeChoiceData)
    (hchoose :
      choosePrimeData? (normalizeForFactor f).squareFreeCore = some primeData)
    (hbranch : factorWithBoundUsesExhaustiveBranch f B)
    (hcomplete :
      reassemblyExpansionComplete (normalizeForFactor f)
        (exhaustiveCoreFactorsWithBound (normalizeForFactor f).squareFreeCore B
          primeData))
    (hmem : entry ∈ (factorWithBound f B).factors.toList) :
    ∃ raw,
      (raw ∈ (xPowerFactorArray (normalizeForFactor f).xPower).toList ∨
        raw ∈
          (exhaustiveCoreFactorsWithBound (normalizeForFactor f).squareFreeCore B
            primeData).toList) ∧
        entry.1 = normalizeFactorSign raw := by
  have hwf :
      choosePrimeData (normalizeForFactor f).squareFreeCore = primeData :=
    choosePrimeData_eq_of_choosePrimeData?_some hchoose
  rcases factorWithBound_entry_mem_exhaustive_branch_raw f B entry hbranch hmem with
    ⟨raw, hraw_mem, hraw_norm⟩
  refine ⟨raw, ?_, hraw_norm⟩
  rw [exhaustiveSlowRawFactorsWithBound] at hraw_mem
  rw [hwf] at hraw_mem
  exact
    reassemblePolynomialFactors_mem_xPower_or_core_of_expansionComplete
      (normalizeForFactor f)
      (exhaustiveCoreFactorsWithBound (normalizeForFactor f).squareFreeCore B
        primeData)
      raw hcomplete hraw_mem

/--
Default-precision specialization of
`factorWithBound_entry_mem_exhaustive_branch_xPower_or_core_of_reassemblyComplete`
for the public `factor` entry point.
-/
theorem factor_entry_mem_exhaustive_branch_xPower_or_core_of_reassemblyComplete
    (f : ZPoly) (entry : ZPoly × Nat)
    (primeData : PrimeChoiceData)
    (hchoose :
      choosePrimeData? (normalizeForFactor f).squareFreeCore = some primeData)
    (hbranch :
      factorWithBoundUsesExhaustiveBranch f (ZPoly.defaultFactorCoeffBound f))
    (hcomplete :
      reassemblyExpansionComplete (normalizeForFactor f)
        (exhaustiveCoreFactorsWithBound (normalizeForFactor f).squareFreeCore
          (ZPoly.defaultFactorCoeffBound f)
          primeData))
    (hmem : entry ∈ (factor f).factors.toList) :
    ∃ raw,
      (raw ∈ (xPowerFactorArray (normalizeForFactor f).xPower).toList ∨
        raw ∈
          (exhaustiveCoreFactorsWithBound (normalizeForFactor f).squareFreeCore
            (ZPoly.defaultFactorCoeffBound f)
            primeData).toList) ∧
        entry.1 = normalizeFactorSign raw := by
  simpa [factor_eq_factorWithBound_default] using
    factorWithBound_entry_mem_exhaustive_branch_xPower_or_core_of_reassemblyComplete
      f (ZPoly.defaultFactorCoeffBound f) entry primeData hchoose
      hbranch hcomplete hmem

/-- In the fast-path small-mod singleton branch, every recorded
`factorWithBound` entry comes from the normalization reassembly whose core array
is exactly the singleton square-free core. This is the branch-shape lemma needed
by Mathlib-side irreducibility proofs; it still leaves the mathematical proof
that the singleton core is irreducible to the Mathlib-side layer.

The `hchoose` premise reflects the dispatcher contract: under the small-mod
singleton dispatch (issue #4605), the fast path only fires the singleton arm
when `choosePrimeData?` selects a good prime. When `choosePrimeData? sf = none`
the fast path returns `none` and `factorWithBound` falls through to the
exhaustive slow path, so the singleton branch-shape conclusion does not apply. -/
theorem factorWithBound_entry_mem_small_mod_singleton_raw
    (f : ZPoly) (B : Nat) (entry : ZPoly × Nat)
    (primeData : PrimeChoiceData)
    (hB_pos : 1 ≤ B)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hchoose :
      choosePrimeData? (normalizeForFactor f).squareFreeCore = some primeData)
    (hsmall : primeData.factorsModP.size ≤ 1)
    (hquadratic : B = 1 ∨
      quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none)
    (hmem : entry ∈ (factorWithBound f B).factors.toList) :
    ∃ raw ∈
        (reassemblePolynomialFactors (normalizeForFactor f)
          #[(normalizeForFactor f).squareFreeCore]).toList,
      entry.1 = normalizeFactorSign raw := by
  have hfast :
      factorFastFactorsWithBound f B =
        some (reassemblePolynomialFactors (normalizeForFactor f)
          #[(normalizeForFactor f).squareFreeCore]) := by
    unfold factorFastFactorsWithBound
    rw [if_neg hdeg, if_neg (by omega : B ≠ 0)]
    by_cases hB1 : B = 1
    · rw [if_pos hB1]
      simp [hchoose, hsmall]
    · rw [if_neg hB1]
      have hquad :
          quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore =
            none := by
        cases hquadratic with
        | inl heq => exact absurd heq hB1
        | inr hnone => exact hnone
      rw [hquad]
      simp [hchoose, hsmall]
  apply factorizationOfFactors_entry_mem_normalized_raw
  simpa only [factorWithBound, factorFastWithBound, hfast, Option.map_some,
    Option.getD_some] using hmem

/-- In the fast-path constant square-free-core branch, every recorded
`factorWithBound` entry comes from the normalization reassembly whose core
array is the singleton `#[squareFreeCore]`. The constant branch is the
earliest dispatch in `factorFastFactorsWithBound` and is unconditional on the
recombination budget `B`, the small-mod prime data, and the quadratic-root
short-circuit, so the signature requires only the constant-core marker
`hdeg`. -/
theorem factorWithBound_entry_mem_constant_branch_raw
    (f : ZPoly) (B : Nat) (entry : ZPoly × Nat)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0)
    (hmem : entry ∈ (factorWithBound f B).factors.toList) :
    ∃ raw ∈
        (reassemblePolynomialFactors (normalizeForFactor f)
          #[(normalizeForFactor f).squareFreeCore]).toList,
      entry.1 = normalizeFactorSign raw := by
  have hfast :
      factorFastFactorsWithBound f B =
        some (reassemblePolynomialFactors (normalizeForFactor f)
          #[(normalizeForFactor f).squareFreeCore]) := by
    unfold factorFastFactorsWithBound
    rw [if_pos hdeg]
  apply factorizationOfFactors_entry_mem_normalized_raw
  simpa only [factorWithBound, factorFastWithBound, hfast, Option.map_some,
    Option.getD_some] using hmem

/-- In the fast-path quadratic integer-root branch, every recorded
`factorWithBound` entry comes from the normalization reassembly whose core array
is the `quadraticIntegerRootFactors?` output for the square-free core. This is
the branch-shape lemma needed by Mathlib-side quadratic-branch irreducibility
proofs; it leaves the mathematical proof that each core factor is irreducible
to the Mathlib-side layer. The `B > 1` hypothesis is required to enter the quadratic
dispatch (the `B = 1` arm of `factorFastFactorsWithBound` does not consult
`quadraticIntegerRootFactors?`). -/
theorem factorWithBound_entry_mem_quadratic_branch_raw
    (f : ZPoly) (B : Nat) (entry : ZPoly × Nat)
    (hB_gt_one : 1 < B)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    {coreFactors : Array ZPoly}
    (hquad :
      quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore
        = some coreFactors)
    (hmem : entry ∈ (factorWithBound f B).factors.toList) :
    ∃ raw ∈
        (reassemblePolynomialFactors (normalizeForFactor f) coreFactors).toList,
      entry.1 = normalizeFactorSign raw := by
  have hfast :
      factorFastFactorsWithBound f B =
        some (reassemblePolynomialFactors (normalizeForFactor f) coreFactors) := by
    unfold factorFastFactorsWithBound
    rw [if_neg hdeg, if_neg (by omega : B ≠ 0), if_neg (by omega : B ≠ 1), hquad]
  apply factorizationOfFactors_entry_mem_normalized_raw
  simpa only [factorWithBound, factorFastWithBound, hfast, Option.map_some,
    Option.getD_some] using hmem

/-- In the fast-path BHKS fast-core success branch, every recorded
`factorWithBound` entry comes from the normalization reassembly whose core array
is the successful `factorFastCoreWithBound` output for the chosen prime data.
This is the branch-shape lemma needed by Mathlib-side BHKS irreducibility
proofs; it leaves the mathematical proof that each core factor is irreducible
to the Mathlib-side layer.

The `primeData` parameter is paired with an explicit
`hchoose : choosePrimeData? sf = some primeData` witness; downstream callers
that already have a `choosePrimeData?` success witness in scope thread it
through directly, without depending on the silent fallback dispatch. -/
theorem factorWithBound_entry_mem_fast_core_success_raw
    (f : ZPoly) (B : Nat) (entry : ZPoly × Nat)
    (primeData : PrimeChoiceData)
    (hB_pos : 1 ≤ B)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hchoose :
      choosePrimeData? (normalizeForFactor f).squareFreeCore = some primeData)
    (hmulti : 1 < primeData.factorsModP.size)
    (hquadratic : B = 1 ∨
      quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none)
    {coreFactors : Array ZPoly}
    (hcore :
      let a := precisionForCoeffBound B primeData.p
      factorFastCoreWithBound (normalizeForFactor f).squareFreeCore a
        primeData (initialHenselPrecision a)
        (ZPoly.quadraticDoublingSteps a + 2) = some coreFactors)
    (hmem : entry ∈ (factorWithBound f B).factors.toList) :
    ∃ raw ∈ (reassemblePolynomialFactors (normalizeForFactor f) coreFactors).toList,
      entry.1 = normalizeFactorSign raw := by
  have hnotsingleton :
      ¬ primeData.factorsModP.size ≤ 1 := by
    omega
  have hfast :
      factorFastFactorsWithBound f B =
        some (reassemblePolynomialFactors (normalizeForFactor f) coreFactors) :=
    factorFastFactorsWithBound_eq_some_of_core_success f B
      primeData coreFactors
      hB_pos hchoose hdeg hnotsingleton hquadratic hcore
  apply factorizationOfFactors_entry_mem_normalized_raw
  simpa only [factorWithBound, factorFastWithBound, hfast, Option.map_some,
    Option.getD_some] using hmem

/-- In the slow-path quadratic integer-root branch, every recorded
`factorWithBound` entry comes from the normalization reassembly whose core array
is the `coreFactors` produced by `quadraticIntegerRootFactors?`. This branch
fires when the fast path returns `none` (e.g. `B = 0`, or `B = 1` with the
fast-core check missing) and the slow path then sees a non-constant square-free
core for which `quadraticIntegerRootFactors?` succeeds. The branch-shape lemma
mirrors `factorWithBound_entry_mem_small_mod_singleton_raw`; it leaves the
mathematical irreducibility argument for the core factors to the Mathlib-side
layer. -/
theorem factorWithBound_entry_mem_slow_quadratic_branch_raw
    (f : ZPoly) (B : Nat) (entry : ZPoly × Nat)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    {coreFactors : Array ZPoly}
    (hquad :
      quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore
        = some coreFactors)
    (hfast_none : factorFastFactorsWithBound f B = none)
    (hmem : entry ∈ (factorWithBound f B).factors.toList) :
    ∃ raw ∈
        (reassemblePolynomialFactors (normalizeForFactor f) coreFactors).toList,
      entry.1 = normalizeFactorSign raw := by
  obtain ⟨rawFactors, hsource, raw, hraw_mem, hraw_norm⟩ :=
    factorWithBound_entry_mem_raw_source f B entry hmem
  have hmod_some : (factorSlowModularWithBound f B).isSome = true := by
    unfold factorSlowModularWithBound factorSlowModularFactorsWithBound
    rw [if_neg hdeg, hquad]
    rfl
  rcases hsource with hfast_some | ⟨_, _, hrawFactors⟩ | ⟨_, hmod_none, _⟩
  · exfalso
    rw [hfast_some] at hfast_none
    cases hfast_none
  · subst rawFactors
    refine ⟨raw, ?_, hraw_norm⟩
    unfold factorSlowFactorsWithBound at hraw_mem
    simp only [if_neg hdeg, hquad] at hraw_mem
    exact hraw_mem
  · exfalso
    rw [hmod_none] at hmod_some
    cases hmod_some

private def quadraticSquareRegression : ZPoly :=
  let q : ZPoly := DensePoly.ofCoeffs #[-1, 0, 1]
  q * q

#guard (factor quadraticSquareRegression).factors =
  #[(linearFactorForRoot (-1), 2), (linearFactorForRoot 1, 2)]

private def quadraticCubeRegression : ZPoly :=
  let q : ZPoly := DensePoly.ofCoeffs #[-1, 0, 1]
  q * q * q

#guard (factor quadraticCubeRegression).factors =
  #[(linearFactorForRoot (-1), 3), (linearFactorForRoot 1, 3)]

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

/-- Mathlib-free associatedness predicate for integer polynomials: `a` and
`b` are associated when `b = a * u` for some `ZPoly`-unit `u` (i.e. `u = ±1`).
Used by HO-1 irreducibility dischargers to translate "Mathlib-side irreducible factor
of the square-free core" to the direct non-divisibility hypothesis required
by the greedy expansion helper. -/
def Associated (a b : ZPoly) : Prop :=
  ∃ u : ZPoly, ZPoly.IsUnit u ∧ b = a * u

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

/-- A polynomial of dense size `1` is the constant polynomial of its zeroth
coefficient. The trimming invariant on `DensePoly` forces the single stored
coefficient to be nonzero, so `coeff 0` already names the unique stored entry. -/
private theorem eq_C_of_size_eq_one (a : ZPoly) (hsize : a.size = 1) :
    a = DensePoly.C (a.coeff 0) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    exact DensePoly.coeff_eq_zero_of_size_le a (by omega)

/-- An integer factor of `1` is `±1`. Used to read off the unit factor in
size-two monic polynomial irreducibility proofs. -/
private theorem int_factor_one_eq_unit {x y : Int} (h : x * y = 1) :
    x = 1 ∨ x = -1 := by
  have hx_dvd : x ∣ (1 : Int) := ⟨y, h.symm⟩
  have hxnat_dvd : x.natAbs ∣ (1 : Nat) := by
    have := Int.natAbs_dvd_natAbs.mpr hx_dvd
    simpa using this
  have hxnat_le : x.natAbs ≤ 1 := Nat.le_of_dvd (by omega) hxnat_dvd
  have hx_ne : x ≠ 0 := by
    intro hzero
    rw [hzero] at h
    rw [Int.zero_mul] at h
    omega
  have hxnat_pos : 1 ≤ x.natAbs := by
    rcases Nat.eq_zero_or_pos x.natAbs with hzero | hpos
    · exact absurd (Int.natAbs_eq_zero.mp hzero) hx_ne
    · exact hpos
  have hxnat_eq : x.natAbs = 1 := by omega
  rcases Int.natAbs_eq x with heq | heq
  · left
    rw [heq, hxnat_eq]
    rfl
  · right
    rw [heq, hxnat_eq]
    rfl

/-- Correctness lemma for `isNatPrime`: the Boolean check reduces to the
elementary characterisation that `n ≥ 2` and no divisor `d` with
`2 ≤ d ≤ √n` divides `n`. -/
private theorem isNatPrime_iff (n : Nat) :
    isNatPrime n = true ↔
      2 ≤ n ∧ ∀ d : Nat, 2 ≤ d → d * d ≤ n → ¬ d ∣ n := by
  unfold isNatPrime
  rw [Bool.and_eq_true, decide_eq_true_iff, Bool.not_eq_true', List.any_eq_false]
  refine Iff.intro ?fwd ?bwd
  case fwd =>
    rintro ⟨h2, hany⟩
    refine ⟨h2, fun d hd2 hdd_le hdvd => ?_⟩
    have hd_lt_n : d < n := by
      have h2d_le_dd : 2 * d ≤ d * d := Nat.mul_le_mul_right d hd2
      have h2d_le_n : 2 * d ≤ n := Nat.le_trans h2d_le_dd hdd_le
      omega
    have hmem : d ∈ List.range n := List.mem_range.mpr hd_lt_n
    have hpred_ne_true : ¬
        ((decide (2 ≤ d) && decide (d * d ≤ n) && (n % d == 0)) = true) :=
      hany d hmem
    apply hpred_ne_true
    have h1 : (decide (2 ≤ d)) = true := decide_eq_true hd2
    have h2 : (decide (d * d ≤ n)) = true := decide_eq_true hdd_le
    have h3 : (n % d == 0) = true := by
      rw [beq_iff_eq]
      exact Nat.mod_eq_zero_of_dvd hdvd
    rw [h1, h2, h3]
    rfl
  case bwd =>
    rintro ⟨h2, hno⟩
    refine ⟨h2, fun d hmem => ?_⟩
    have hd_lt_n : d < n := List.mem_range.mp hmem
    intro hpred_true
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff,
      decide_eq_true_iff, beq_iff_eq] at hpred_true
    obtain ⟨⟨hd2, hdd_le⟩, hmod⟩ := hpred_true
    exact hno d hd2 hdd_le (Nat.dvd_of_mod_eq_zero hmod)

/-- `DensePoly.C` on integers commutes with multiplication: `C (a*b) = C a * C b`.
Used by the constant-polynomial Irreducible characterisation to split integer
factorisations into polynomial factorisations and back. -/
private theorem zpoly_C_mul_C (a b : Int) :
    DensePoly.C (a * b) = (DensePoly.C a : ZPoly) * DensePoly.C b := by
  rw [ZPoly.C_mul_eq_scale]
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Int) a (DensePoly.C b) n (Int.mul_zero a),
      DensePoly.coeff_C, DensePoly.coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, if_neg hn]
    exact (Int.mul_zero a).symm

/-- Size of `DensePoly.C k` for nonzero `k` is exactly `1`. -/
private theorem zpoly_size_C_of_ne_zero {k : Int} (hk : k ≠ 0) :
    (DensePoly.C k : ZPoly).size = 1 := by
  unfold DensePoly.size
  rw [DensePoly.coeffs_C_of_ne_zero hk]
  rfl

/-- A constant polynomial `DensePoly.C k` is `ZPoly.Irreducible` whenever
`k.natAbs` is prime in the elementary `isNatPrime` sense. -/
private theorem irreducible_C_of_isNatPrime
    {k : Int} (hp : isNatPrime k.natAbs = true) :
    ZPoly.Irreducible (DensePoly.C k) := by
  obtain ⟨hp2, hpno⟩ := (isNatPrime_iff k.natAbs).mp hp
  have hk_ne : k ≠ 0 := by
    intro hzero
    rw [hzero] at hp2
    change 2 ≤ (0 : Int).natAbs at hp2
    simp at hp2
  have hk_natAbs_ne_one : k.natAbs ≠ 1 := by omega
  have hC_ne : DensePoly.C k ≠ 0 := by
    intro hzero
    have : (DensePoly.C k).coeff 0 = (DensePoly.C (0 : Int)).coeff 0 := by
      rw [hzero]
      rfl
    rw [DensePoly.coeff_C, DensePoly.coeff_C] at this
    simp at this
    exact hk_ne this
  refine
    { not_zero := hC_ne
      not_unit := ?_
      no_factors := ?_ }
  · intro hunit
    rcases hunit with hone | hneg
    · have hk1 : k = 1 := by
        have hc : (DensePoly.C k).coeff 0 = (DensePoly.C (1 : Int)).coeff 0 :=
          congrArg (fun p => DensePoly.coeff p 0) hone
        rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
        simpa using hc
      apply hk_natAbs_ne_one
      rw [hk1]
      rfl
    · have hkn1 : k = -1 := by
        have hc : (DensePoly.C k).coeff 0 = (DensePoly.C (-1 : Int)).coeff 0 :=
          congrArg (fun p => DensePoly.coeff p 0) hneg
        rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
        simpa using hc
      apply hk_natAbs_ne_one
      rw [hkn1]
      rfl
  · intro a b hab
    by_cases ha_zero : a = 0
    · exfalso
      apply hC_ne
      rw [hab, ha_zero, DensePoly.zero_mul]
    by_cases hb_zero : b = 0
    · exfalso
      apply hC_ne
      rw [hab, hb_zero, DensePoly.mul_comm_poly, DensePoly.zero_mul]
    have ha_pos : 0 < a.size := ZPoly.size_pos_of_ne_zero a ha_zero
    have hb_pos : 0 < b.size := ZPoly.size_pos_of_ne_zero b hb_zero
    have hC_size : (DensePoly.C k).size = 1 := zpoly_size_C_of_ne_zero hk_ne
    have hab_size :
        (a * b).size = a.size + b.size - 1 :=
      ZPoly.mul_size_eq_top_succ_of_nonzero a b ha_pos hb_pos
    rw [← hab] at hab_size
    rw [hC_size] at hab_size
    have ha_one : a.size = 1 := by omega
    have hb_one : b.size = 1 := by omega
    have ha_eq : a = DensePoly.C (a.coeff 0) := eq_C_of_size_eq_one a ha_one
    have hb_eq : b = DensePoly.C (b.coeff 0) := eq_C_of_size_eq_one b hb_one
    have ha_coeff_ne : a.coeff 0 ≠ 0 := by
      intro h
      apply ha_zero
      rw [ha_eq, h]
      rfl
    have hb_coeff_ne : b.coeff 0 ≠ 0 := by
      intro h
      apply hb_zero
      rw [hb_eq, h]
      rfl
    -- (C a₀) * (C b₀) = C (a₀ * b₀) = C k, so a₀ * b₀ = k
    have hprod_C : DensePoly.C (a.coeff 0 * b.coeff 0) = DensePoly.C k := by
      calc DensePoly.C (a.coeff 0 * b.coeff 0)
          = DensePoly.C (a.coeff 0) * DensePoly.C (b.coeff 0) :=
            zpoly_C_mul_C _ _
        _ = a * b := by rw [← ha_eq, ← hb_eq]
        _ = DensePoly.C k := hab.symm
    have hcoeff_prod : a.coeff 0 * b.coeff 0 = k := by
      have hc : (DensePoly.C (a.coeff 0 * b.coeff 0)).coeff 0 =
          (DensePoly.C k).coeff 0 :=
        congrArg (fun p => DensePoly.coeff p 0) hprod_C
      rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
      simpa using hc
    have hnat_prod :
        (a.coeff 0).natAbs * (b.coeff 0).natAbs = k.natAbs := by
      have := Int.natAbs_mul (a.coeff 0) (b.coeff 0)
      rw [hcoeff_prod] at this
      exact this.symm
    by_cases ha_unit : ZPoly.IsUnit a
    · exact Or.inl ha_unit
    by_cases hb_unit : ZPoly.IsUnit b
    · exact Or.inr hb_unit
    exfalso
    have ha_natAbs_pos : 0 < (a.coeff 0).natAbs := by
      rcases Nat.eq_zero_or_pos (a.coeff 0).natAbs with hzero | hpos
      · exact absurd (Int.natAbs_eq_zero.mp hzero) ha_coeff_ne
      · exact hpos
    have hb_natAbs_pos : 0 < (b.coeff 0).natAbs := by
      rcases Nat.eq_zero_or_pos (b.coeff 0).natAbs with hzero | hpos
      · exact absurd (Int.natAbs_eq_zero.mp hzero) hb_coeff_ne
      · exact hpos
    have ha_natAbs_ge_two : 2 ≤ (a.coeff 0).natAbs := by
      have ha_natAbs_ne_one : (a.coeff 0).natAbs ≠ 1 := by
        intro hone
        apply ha_unit
        rcases Int.natAbs_eq (a.coeff 0) with heq | heq
        · left; rw [ha_eq, heq, hone]; rfl
        · right; rw [ha_eq, heq, hone]; rfl
      omega
    have hb_natAbs_ge_two : 2 ≤ (b.coeff 0).natAbs := by
      have hb_natAbs_ne_one : (b.coeff 0).natAbs ≠ 1 := by
        intro hone
        apply hb_unit
        rcases Int.natAbs_eq (b.coeff 0) with heq | heq
        · left; rw [hb_eq, heq, hone]; rfl
        · right; rw [hb_eq, heq, hone]; rfl
      omega
    rcases Nat.le_total (a.coeff 0).natAbs (b.coeff 0).natAbs with hle | hle
    · have hsq_le : (a.coeff 0).natAbs * (a.coeff 0).natAbs ≤ k.natAbs := by
        calc (a.coeff 0).natAbs * (a.coeff 0).natAbs
            ≤ (a.coeff 0).natAbs * (b.coeff 0).natAbs :=
              Nat.mul_le_mul_left _ hle
          _ = k.natAbs := hnat_prod
      have hdvd : (a.coeff 0).natAbs ∣ k.natAbs :=
        ⟨(b.coeff 0).natAbs, hnat_prod.symm⟩
      exact hpno (a.coeff 0).natAbs ha_natAbs_ge_two hsq_le hdvd
    · have hsq_le : (b.coeff 0).natAbs * (b.coeff 0).natAbs ≤ k.natAbs := by
        calc (b.coeff 0).natAbs * (b.coeff 0).natAbs
            ≤ (a.coeff 0).natAbs * (b.coeff 0).natAbs :=
              Nat.mul_le_mul_right _ hle
          _ = k.natAbs := hnat_prod
      have hdvd : (b.coeff 0).natAbs ∣ k.natAbs :=
        ⟨(a.coeff 0).natAbs, by rw [Nat.mul_comm]; exact hnat_prod.symm⟩
      exact hpno (b.coeff 0).natAbs hb_natAbs_ge_two hsq_le hdvd

/-- An irreducible constant polynomial `DensePoly.C k` (for `k ≠ 0`) has
`k.natAbs` prime in the elementary `isNatPrime` sense. -/
private theorem isNatPrime_natAbs_of_irreducible_C
    {k : Int} (hk_ne : k ≠ 0) (hirr : ZPoly.Irreducible (DensePoly.C k)) :
    isNatPrime k.natAbs = true := by
  rw [isNatPrime_iff]
  have hk_natAbs_pos : 0 < k.natAbs := by
    rcases Nat.eq_zero_or_pos k.natAbs with hzero | hpos
    · exact absurd (Int.natAbs_eq_zero.mp hzero) hk_ne
    · exact hpos
  have hk_natAbs_ne_one : k.natAbs ≠ 1 := by
    intro hone
    apply hirr.not_unit
    rcases Int.natAbs_eq k with heq | heq
    · left
      rw [heq, hone]
      rfl
    · right
      rw [heq, hone]
      rfl
  have hk_natAbs_ge_two : 2 ≤ k.natAbs := by omega
  refine ⟨hk_natAbs_ge_two, fun d hd2 hdd_le hdvd => ?_⟩
  obtain ⟨e, he⟩ := hdvd
  have he_pos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with hzero | hpos
    · rw [hzero] at he
      simp at he
      omega
    · exact hpos
  have he_ge_two : 2 ≤ e := by
    have h_le : d * d ≤ d * e := by rw [← he]; exact hdd_le
    have hd_pos : 0 < d := by omega
    have hde : d ≤ e := Nat.le_of_mul_le_mul_left h_le hd_pos
    omega
  -- |k| = d * e, so either k = (d : Int) * e or k = -((d : Int) * e).
  rcases Int.natAbs_eq k with heq | heq
  · have hk_eq : k = (d : Int) * (e : Int) := by
      rw [heq, he, Int.natCast_mul]
    have hC_split :
        DensePoly.C k = DensePoly.C (d : Int) * DensePoly.C (e : Int) := by
      rw [hk_eq, zpoly_C_mul_C]
    rcases hirr.no_factors _ _ hC_split with hua | hub
    · rcases hua with hone | hneg
      · have hd_eq : (d : Int) = 1 := by
          have hc : (DensePoly.C (d : Int)).coeff 0 =
              (DensePoly.C (1 : Int)).coeff 0 :=
            congrArg (fun p => DensePoly.coeff p 0) hone
          rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
          simpa using hc
        omega
      · have hd_eq : (d : Int) = -1 := by
          have hc : (DensePoly.C (d : Int)).coeff 0 =
              (DensePoly.C (-1 : Int)).coeff 0 :=
            congrArg (fun p => DensePoly.coeff p 0) hneg
          rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
          simp at hc
        omega
    · rcases hub with hone | hneg
      · have he_eq : (e : Int) = 1 := by
          have hc : (DensePoly.C (e : Int)).coeff 0 =
              (DensePoly.C (1 : Int)).coeff 0 :=
            congrArg (fun p => DensePoly.coeff p 0) hone
          rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
          simpa using hc
        omega
      · have he_eq : (e : Int) = -1 := by
          have hc : (DensePoly.C (e : Int)).coeff 0 =
              (DensePoly.C (-1 : Int)).coeff 0 :=
            congrArg (fun p => DensePoly.coeff p 0) hneg
          rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
          simp at hc
        omega
  · have hk_eq : k = (-(d : Int)) * (e : Int) := by
      rw [heq, he, Int.natCast_mul, Int.neg_mul]
    have hC_split :
        DensePoly.C k = DensePoly.C (-(d : Int)) * DensePoly.C (e : Int) := by
      rw [hk_eq, zpoly_C_mul_C]
    rcases hirr.no_factors _ _ hC_split with hua | hub
    · rcases hua with hone | hneg
      · have hd_eq : (-(d : Int)) = 1 := by
          have hc : (DensePoly.C (-(d : Int))).coeff 0 =
              (DensePoly.C (1 : Int)).coeff 0 :=
            congrArg (fun p => DensePoly.coeff p 0) hone
          rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
          simpa using hc
        omega
      · have hd_eq : (-(d : Int)) = -1 := by
          have hc : (DensePoly.C (-(d : Int))).coeff 0 =
              (DensePoly.C (-1 : Int)).coeff 0 :=
            congrArg (fun p => DensePoly.coeff p 0) hneg
          rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
          simpa using hc
        omega
    · rcases hub with hone | hneg
      · have he_eq : (e : Int) = 1 := by
          have hc : (DensePoly.C (e : Int)).coeff 0 =
              (DensePoly.C (1 : Int)).coeff 0 :=
            congrArg (fun p => DensePoly.coeff p 0) hone
          rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
          simpa using hc
        omega
      · have he_eq : (e : Int) = -1 := by
          have hc : (DensePoly.C (e : Int)).coeff 0 =
              (DensePoly.C (-1 : Int)).coeff 0 :=
            congrArg (fun p => DensePoly.coeff p 0) hneg
          rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
          simp at hc
        omega

/-- A monic integer polynomial of dense size two is irreducible. The proof
splits any factorization `f = a * b` by dense size: degree arithmetic forces
one factor to be a constant `±1`, so the constant factor is a `ZPoly` unit. -/
private theorem irreducible_of_size_two_monic
    (f : ZPoly) (hf_size : f.size = 2)
    (hf_monic : DensePoly.leadingCoeff f = (1 : Int)) :
    ZPoly.Irreducible f := by
  have hf_ne : f ≠ 0 := by
    intro hzero
    rw [hzero] at hf_size
    change (0 : Nat) = 2 at hf_size
    omega
  have hf_pos : 0 < f.size := by omega
  refine
    { not_zero := hf_ne
      not_unit := ?_
      no_factors := ?_ }
  · intro hunit
    rcases hunit with hone | hneg
    · rw [hone] at hf_size
      have h1 : (DensePoly.C (1 : Int)).size = 1 := rfl
      omega
    · rw [hneg] at hf_size
      have hneg_size : (DensePoly.C (-1 : Int)).size = 1 := rfl
      omega
  · intro a b hf_ab
    by_cases ha_zero : a = 0
    · exfalso
      apply hf_ne
      rw [hf_ab, ha_zero, DensePoly.zero_mul]
    by_cases hb_zero : b = 0
    · exfalso
      apply hf_ne
      rw [hf_ab, hb_zero]
      change a * (0 : ZPoly) = 0
      rw [DensePoly.mul_comm_poly, DensePoly.zero_mul]
    have ha_pos : 0 < a.size := ZPoly.size_pos_of_ne_zero a ha_zero
    have hb_pos : 0 < b.size := ZPoly.size_pos_of_ne_zero b hb_zero
    have hab_size :
        (a * b).size = a.size + b.size - 1 :=
      ZPoly.mul_size_eq_top_succ_of_nonzero a b ha_pos hb_pos
    rw [← hf_ab] at hab_size
    rw [hf_size] at hab_size
    have hsum : a.size + b.size = 3 := by omega
    have hlead :
        DensePoly.leadingCoeff a * DensePoly.leadingCoeff b = (1 : Int) := by
      have := ZPoly.leadingCoeff_mul_of_nonzero a b ha_zero hb_zero
      rw [← hf_ab] at this
      rw [hf_monic] at this
      exact this.symm
    have ha_size_le : a.size ≤ 2 := by omega
    have hb_size_le : b.size ≤ 2 := by omega
    have ha_size_eq_one_or_two : a.size = 1 ∨ a.size = 2 := by omega
    rcases ha_size_eq_one_or_two with ha_one | ha_two
    · -- a.size = 1, so a is constant; show IsUnit a
      left
      have ha_eq : a = DensePoly.C (a.coeff 0) := eq_C_of_size_eq_one a ha_one
      have ha_lead : DensePoly.leadingCoeff a = a.coeff 0 := by
        rw [DensePoly.leadingCoeff_eq_coeff_last a (by omega)]
        congr 1
        omega
      rw [ha_lead] at hlead
      have ha_coeff_unit : a.coeff 0 = 1 ∨ a.coeff 0 = -1 :=
        int_factor_one_eq_unit hlead
      rcases ha_coeff_unit with hone | hneg
      · left
        rw [ha_eq, hone]
      · right
        rw [ha_eq, hneg]
    · -- a.size = 2, so b.size = 1; symmetric case
      right
      have hb_one : b.size = 1 := by omega
      have hb_eq : b = DensePoly.C (b.coeff 0) := eq_C_of_size_eq_one b hb_one
      have hb_lead : DensePoly.leadingCoeff b = b.coeff 0 := by
        rw [DensePoly.leadingCoeff_eq_coeff_last b (by omega)]
        congr 1
        omega
      rw [hb_lead] at hlead
      rw [Int.mul_comm] at hlead
      have hb_coeff_unit : b.coeff 0 = 1 ∨ b.coeff 0 = -1 :=
        int_factor_one_eq_unit hlead
      rcases hb_coeff_unit with hone | hneg
      · left
        rw [hb_eq, hone]
      · right
        rw [hb_eq, hneg]

/-- The integer indeterminate `X` is irreducible. -/
theorem irreducible_X : ZPoly.Irreducible ZPoly.X :=
  irreducible_of_size_two_monic ZPoly.X rfl rfl

/-- A primitive integer polynomial of dense size two is irreducible. Mirrors
`irreducible_of_size_two_monic` but uses primitivity (`content f = 1`) instead
of monicness to derive that a degree-zero factor must be `±1`: if `f = C c * b`
then `c` divides every coefficient of `f`, hence `c` divides `content f = 1`,
forcing `c ∈ {±1}`. -/
private theorem irreducible_of_size_two_primitive
    (f : ZPoly) (hf_size : f.size = 2)
    (hf_prim : ZPoly.Primitive f) :
    ZPoly.Irreducible f := by
  have hf_ne : f ≠ 0 := by
    intro hzero
    rw [hzero] at hf_size
    change (0 : Nat) = 2 at hf_size
    omega
  refine
    { not_zero := hf_ne
      not_unit := ?_
      no_factors := ?_ }
  · intro hunit
    rcases hunit with hone | hneg
    · rw [hone] at hf_size
      have h1 : (DensePoly.C (1 : Int)).size = 1 := rfl
      omega
    · rw [hneg] at hf_size
      have hneg_size : (DensePoly.C (-1 : Int)).size = 1 := rfl
      omega
  · intro a b hf_ab
    by_cases ha_zero : a = 0
    · exfalso
      apply hf_ne
      rw [hf_ab, ha_zero, DensePoly.zero_mul]
    by_cases hb_zero : b = 0
    · exfalso
      apply hf_ne
      rw [hf_ab, hb_zero]
      change a * (0 : ZPoly) = 0
      rw [DensePoly.mul_comm_poly, DensePoly.zero_mul]
    have ha_pos : 0 < a.size := ZPoly.size_pos_of_ne_zero a ha_zero
    have hb_pos : 0 < b.size := ZPoly.size_pos_of_ne_zero b hb_zero
    have hab_size :
        (a * b).size = a.size + b.size - 1 :=
      ZPoly.mul_size_eq_top_succ_of_nonzero a b ha_pos hb_pos
    rw [← hf_ab] at hab_size
    rw [hf_size] at hab_size
    have hsum : a.size + b.size = 3 := by omega
    have ha_size_le : a.size ≤ 2 := by omega
    have hb_size_le : b.size ≤ 2 := by omega
    have ha_size_eq_one_or_two : a.size = 1 ∨ a.size = 2 := by omega
    -- Helper: if `g = C c * h`, then `c` divides every coefficient of `g`,
    -- so `(c.natAbs : Int)` divides `content g`.
    have const_dvd_content :
        ∀ (g h : ZPoly) (c : Int),
          g = DensePoly.C c * h → ((c.natAbs : Int) : Int) ∣ ZPoly.content g := by
      intro g h c hg_eq
      apply ZPoly.dvd_content_of_nat_dvd_coeff
      intro n
      have hcoeff : g.coeff n = c * h.coeff n := by
        rw [hg_eq, C_mul_eq_scale,
          DensePoly.coeff_scale (R := Int) c h n (Int.mul_zero _)]
      refine Int.natAbs_dvd.mpr ?_
      rw [hcoeff]
      exact ⟨h.coeff n, rfl⟩
    -- Helper: if `c.natAbs` divides `1` and `c ≠ 0`, then `c ∈ {1, -1}`.
    have nat_factor_one :
        ∀ (c : Int), c ≠ 0 → ((c.natAbs : Int) : Int) ∣ (1 : Int) →
          c = 1 ∨ c = -1 := by
      intro c hc_ne hdvd
      have hnat_dvd : c.natAbs ∣ (1 : Nat) := by
        have := Int.ofNat_dvd.mp (by simpa using hdvd)
        exact this
      have hnat_le : c.natAbs ≤ 1 := Nat.le_of_dvd (by omega) hnat_dvd
      have hnat_pos : 1 ≤ c.natAbs := by
        rcases Nat.eq_zero_or_pos c.natAbs with hzero | hpos
        · exact absurd (Int.natAbs_eq_zero.mp hzero) hc_ne
        · exact hpos
      have hnat_eq : c.natAbs = 1 := by omega
      rcases Int.natAbs_eq c with heq | heq
      · left; rw [heq, hnat_eq]; rfl
      · right; rw [heq, hnat_eq]; rfl
    rcases ha_size_eq_one_or_two with ha_one | ha_two
    · -- a.size = 1, so a is constant; show IsUnit a
      left
      have ha_eq : a = DensePoly.C (a.coeff 0) := eq_C_of_size_eq_one a ha_one
      have hf_eq : f = DensePoly.C (a.coeff 0) * b :=
        hf_ab.trans (congrArg (· * b) ha_eq)
      have hac_ne_zero : a.coeff 0 ≠ 0 := by
        intro h
        apply ha_zero
        rw [ha_eq, h]
        rfl
      have hcontent_one : ZPoly.content f = 1 := hf_prim
      have hac_dvd_content :
          ((a.coeff 0).natAbs : Int) ∣ ZPoly.content f :=
        const_dvd_content f b (a.coeff 0) hf_eq
      rw [hcontent_one] at hac_dvd_content
      rcases nat_factor_one (a.coeff 0) hac_ne_zero hac_dvd_content with
        hone | hneg
      · left; rw [ha_eq, hone]
      · right; rw [ha_eq, hneg]
    · -- a.size = 2, so b.size = 1; symmetric case via commutativity
      right
      have hb_one : b.size = 1 := by omega
      have hb_eq : b = DensePoly.C (b.coeff 0) := eq_C_of_size_eq_one b hb_one
      have hf_eq : f = DensePoly.C (b.coeff 0) * a :=
        (hf_ab.trans (DensePoly.mul_comm_poly a b)).trans
          (congrArg (· * a) hb_eq)
      have hbc_ne_zero : b.coeff 0 ≠ 0 := by
        intro h
        apply hb_zero
        rw [hb_eq, h]
        rfl
      have hcontent_one : ZPoly.content f = 1 := hf_prim
      have hbc_dvd_content :
          ((b.coeff 0).natAbs : Int) ∣ ZPoly.content f :=
        const_dvd_content f a (b.coeff 0) hf_eq
      rw [hcontent_one] at hbc_dvd_content
      rcases nat_factor_one (b.coeff 0) hbc_ne_zero hbc_dvd_content with
        hone | hneg
      · left; rw [hb_eq, hone]
      · right; rw [hb_eq, hneg]

/-- Mathlib-free Gauss reduction-mod-`p` transfer: a primitive integer
polynomial whose leading coefficient survives reduction modulo a prime `p` and
whose modular image is `FpPoly`-irreducible is itself `ZPoly.Irreducible`.

The `hnotConstant : 1 < f.size` precondition rules out the size-one constant
case explicitly: the executable `FpPoly.Irreducible` predicate only asserts the
factorization disjunction (it does not internally exclude constants the way
Mathlib's `_root_.Irreducible` does via `not_isUnit`), so the non-unit clause
for `f` is supplied at the `ZPoly` level. A primitive `ZPoly` of `size > 1` is
automatically not a `ZPoly` unit (units have size `1`).

Mathlib analog:
`HexBerlekampZassenhausMathlib.irreducible_of_isPrimitive_of_irreducible_map_intCast_zmod`
(`HexBerlekampZassenhausMathlib/IntReductionMod.lean:106`). -/
theorem Irreducible_of_modP_irreducible_of_primitive_of_admissible
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hprime : Nat.Prime p)
    (hprim : ZPoly.Primitive f)
    (hadm : leadingCoeffAdmissible f p)
    (hnotConstant : 1 < f.size)
    (hirr : FpPoly.Irreducible (ZPoly.modP p f)) :
    ZPoly.Irreducible f := by
  haveI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hprime
  have hf_size_pos : 0 < f.size :=
    leadingCoeffAdmissible_size_pos f p hadm
  have hf_ne : f ≠ 0 := by
    intro hzero
    rw [hzero] at hf_size_pos
    change (0 : Nat) < 0 at hf_size_pos
    omega
  have hmodP_f_ne : ZPoly.modP p f ≠ 0 :=
    modP_ne_zero_of_leadingCoeffAdmissible f p hadm
  have hmodP_f_size : (ZPoly.modP p f).size = f.size :=
    size_modP_eq_of_leadingCoeffAdmissible f p hadm
  refine
    { not_zero := hf_ne
      not_unit := ?_
      no_factors := ?_ }
  · -- `1 < f.size` rules out `f = C ±1`, the two possible unit shapes.
    intro hunit
    rcases hunit with hone | hneg
    · rw [hone] at hnotConstant
      have h1 : (DensePoly.C (1 : Int)).size = 1 := rfl
      omega
    · rw [hneg] at hnotConstant
      have hneg_size : (DensePoly.C (-1 : Int)).size = 1 := rfl
      omega
  · intro a b hf_ab
    have ha_ne : a ≠ 0 := by
      intro h
      apply hf_ne
      rw [hf_ab, h, DensePoly.zero_mul]
    have hb_ne : b ≠ 0 := by
      intro h
      apply hf_ne
      rw [hf_ab, h]
      change a * (0 : ZPoly) = 0
      rw [DensePoly.mul_comm_poly, DensePoly.zero_mul]
    have ha_size_pos : 0 < a.size := ZPoly.size_pos_of_ne_zero a ha_ne
    have hb_size_pos : 0 < b.size := ZPoly.size_pos_of_ne_zero b hb_ne
    have hab_size : f.size = a.size + b.size - 1 := by
      rw [hf_ab]
      exact ZPoly.mul_size_eq_top_succ_of_nonzero a b ha_size_pos hb_size_pos
    -- `modP p` distributes over multiplication.
    have hmodP_eq : ZPoly.modP p f = ZPoly.modP p a * ZPoly.modP p b := by
      rw [hf_ab, ZPoly.modP_mul]
    have hmodP_a_size_le : (ZPoly.modP p a).size ≤ a.size := size_modP_le p a
    have hmodP_b_size_le : (ZPoly.modP p b).size ≤ b.size := size_modP_le p b
    have hmodP_a_ne : ZPoly.modP p a ≠ 0 := by
      intro h
      apply hmodP_f_ne
      rw [hmodP_eq, h]
      exact DensePoly.zero_mul _
    have hmodP_b_ne : ZPoly.modP p b ≠ 0 := by
      intro h
      apply hmodP_f_ne
      rw [hmodP_eq, h]
      exact (DensePoly.mul_comm_poly (ZPoly.modP p a) 0).trans
        (DensePoly.zero_mul _)
    have hmodP_ab_size :
        (ZPoly.modP p a * ZPoly.modP p b).size =
          (ZPoly.modP p a).size + (ZPoly.modP p b).size - 1 :=
      FpPoly.size_mul_eq_add_sub_one
        (ZPoly.modP p a) (ZPoly.modP p b) hmodP_a_ne hmodP_b_ne
    have hmodP_a_size_pos : 0 < (ZPoly.modP p a).size :=
      FpPoly.size_pos_of_ne_zero hmodP_a_ne
    have hmodP_b_size_pos : 0 < (ZPoly.modP p b).size :=
      FpPoly.size_pos_of_ne_zero hmodP_b_ne
    -- Size arithmetic forces the modular images to retain the original sizes.
    have hsum :
        (ZPoly.modP p a).size + (ZPoly.modP p b).size = a.size + b.size := by
      have heq :
          (ZPoly.modP p a * ZPoly.modP p b).size = a.size + b.size - 1 := by
        rw [← hmodP_eq, hmodP_f_size, hab_size]
      rw [hmodP_ab_size] at heq
      omega
    have hmodP_a_size_eq : (ZPoly.modP p a).size = a.size := by omega
    have hmodP_b_size_eq : (ZPoly.modP p b).size = b.size := by omega
    -- `degree? = some 0` is equivalent to `size = 1` on a nonzero `DensePoly`.
    have hdeg_size :
        ∀ {g : FpPoly p}, g.degree? = some 0 → g.size = 1 := by
      intro g hdeg
      unfold DensePoly.degree? at hdeg
      by_cases hg_size : g.size = 0
      · rw [dif_pos hg_size] at hdeg
        simp at hdeg
      · rw [dif_neg hg_size] at hdeg
        injection hdeg with hdeg
        omega
    obtain ⟨_, hsplit⟩ := hirr
    have hcase := hsplit (ZPoly.modP p a) (ZPoly.modP p b) hmodP_eq.symm
    -- Local helper: a primitive product with one constant factor forces that
    -- factor to be `±1`, i.e. a `ZPoly` unit.
    have const_factor_isUnit :
        ∀ (g h : ZPoly) (c : Int),
          g = DensePoly.C c * h → c ≠ 0 → ZPoly.content g = 1 →
            ZPoly.IsUnit (DensePoly.C c) := by
      intro g h c hg_eq hc_ne hcontent_one
      have hc_dvd_content : ((c.natAbs : Int) : Int) ∣ ZPoly.content g := by
        apply ZPoly.dvd_content_of_nat_dvd_coeff
        intro n
        have hcoeff : g.coeff n = c * h.coeff n := by
          rw [hg_eq, ZPoly.C_mul_eq_scale,
            DensePoly.coeff_scale (R := Int) c h n (Int.mul_zero _)]
        refine Int.natAbs_dvd.mpr ?_
        rw [hcoeff]
        exact ⟨h.coeff n, rfl⟩
      rw [hcontent_one] at hc_dvd_content
      have hnat_dvd : c.natAbs ∣ (1 : Nat) := by
        have := Int.ofNat_dvd.mp (by simpa using hc_dvd_content)
        exact this
      have hnat_le : c.natAbs ≤ 1 := Nat.le_of_dvd (by omega) hnat_dvd
      have hnat_pos : 1 ≤ c.natAbs := by
        rcases Nat.eq_zero_or_pos c.natAbs with hzero | hpos
        · exact absurd (Int.natAbs_eq_zero.mp hzero) hc_ne
        · exact hpos
      have hnat_eq : c.natAbs = 1 := by omega
      rcases Int.natAbs_eq c with heq | heq
      · left
        rw [heq, hnat_eq]
        rfl
      · right
        rw [heq, hnat_eq]
        rfl
    rcases hcase with hca | hcb
    · -- `modP p a` is constant ⇒ `a` is constant ⇒ `a` is a unit.
      left
      have hmodP_a_size_one : (ZPoly.modP p a).size = 1 := hdeg_size hca
      have ha_size_one : a.size = 1 := by omega
      have ha_eq : a = DensePoly.C (a.coeff 0) := eq_C_of_size_eq_one a ha_size_one
      have hac_ne : a.coeff 0 ≠ 0 := by
        intro h
        apply ha_ne
        rw [ha_eq, h]
        rfl
      have hf_eq : f = DensePoly.C (a.coeff 0) * b :=
        hf_ab.trans (congrArg (· * b) ha_eq)
      have hac_isUnit :=
        const_factor_isUnit f b (a.coeff 0) hf_eq hac_ne hprim
      rcases hac_isUnit with hone | hneg
      · left; rw [ha_eq]; exact hone
      · right; rw [ha_eq]; exact hneg
    · -- Symmetric case: `modP p b` is constant ⇒ `b` is constant ⇒ `b` is a unit.
      right
      have hmodP_b_size_one : (ZPoly.modP p b).size = 1 := hdeg_size hcb
      have hb_size_one : b.size = 1 := by omega
      have hb_eq : b = DensePoly.C (b.coeff 0) := eq_C_of_size_eq_one b hb_size_one
      have hbc_ne : b.coeff 0 ≠ 0 := by
        intro h
        apply hb_ne
        rw [hb_eq, h]
        rfl
      have hf_eq : f = DensePoly.C (b.coeff 0) * a :=
        (hf_ab.trans (DensePoly.mul_comm_poly a b)).trans
          (congrArg (· * a) hb_eq)
      have hbc_isUnit :=
        const_factor_isUnit f a (b.coeff 0) hf_eq hbc_ne hprim
      rcases hbc_isUnit with hone | hneg
      · left; rw [hb_eq]; exact hone
      · right; rw [hb_eq]; exact hneg

end ZPoly

/-- `Hex.normalizeFactorSign` preserves `Hex.ZPoly.Irreducible`: the
sign-normalised polynomial equals either the original or its `-1` scaling,
and `-1` is a `ZPoly` unit, so the no-proper-factorization predicate
transfers. Mathlib-free counterpart of the Mathlib-side
`zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible`
(`HexBerlekampZassenhausMathlib/Basic.lean:12543`).  Consumed by the
Mathlib-free `factor_factors_irreducible` assembly (#4825). -/
theorem zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible
    {f : ZPoly} (hirr : ZPoly.Irreducible f) :
    ZPoly.Irreducible (normalizeFactorSign f) := by
  unfold normalizeFactorSign
  by_cases hlc : DensePoly.leadingCoeff f < 0
  · rw [if_pos hlc]
    -- Sign-flipped branch: `DensePoly.scale (-1) f`.
    have hmulzero : (-1 : Int) * (0 : Int) = 0 := by decide
    -- `scale (-1)` is an involution on `ZPoly`.
    have hinvol : ∀ g : ZPoly,
        DensePoly.scale (-1 : Int) (DensePoly.scale (-1 : Int) g) = g := by
      intro g
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_scale (R := Int) (-1) _ n hmulzero,
          DensePoly.coeff_scale (R := Int) (-1) g n hmulzero]
      omega
    have hscale_C_one : DensePoly.scale (-1 : Int) (DensePoly.C (1 : Int)) =
        DensePoly.C (-1 : Int) := by
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_scale (R := Int) (-1) _ n hmulzero,
          DensePoly.coeff_C, DensePoly.coeff_C]
      by_cases hn : n = 0
      · simp [hn]
      · rw [if_neg hn, if_neg hn]; omega
    have hscale_C_neg_one : DensePoly.scale (-1 : Int) (DensePoly.C (-1 : Int)) =
        DensePoly.C (1 : Int) := by
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_scale (R := Int) (-1) _ n hmulzero,
          DensePoly.coeff_C, DensePoly.coeff_C]
      by_cases hn : n = 0
      · simp [hn]
      · rw [if_neg hn, if_neg hn]; omega
    have hscale_mul_left : ∀ a b : ZPoly,
        DensePoly.scale (-1 : Int) (a * b) = DensePoly.scale (-1 : Int) a * b := by
      intro a b
      rw [← ZPoly.C_mul_eq_scale, ← ZPoly.C_mul_eq_scale,
          DensePoly.mul_assoc_poly (S := Int)]
    refine
      { not_zero := ?_
        not_unit := ?_
        no_factors := ?_ }
    · -- `scale (-1) f ≠ 0`.
      intro h
      apply hirr.not_zero
      have hcong := congrArg (DensePoly.scale (-1 : Int)) h
      rw [hinvol, DensePoly.scale_neg_one_zero] at hcong
      exact hcong
    · -- `scale (-1) f` is not a unit.
      intro hunit
      apply hirr.not_unit
      rcases hunit with h1 | hnegone
      · -- `scale (-1) f = C 1` ⟹ `f = C (-1)`, which is a unit.
        right
        have hcong := congrArg (DensePoly.scale (-1 : Int)) h1
        rw [hinvol, hscale_C_one] at hcong
        exact hcong
      · -- `scale (-1) f = C (-1)` ⟹ `f = C 1`, which is a unit.
        left
        have hcong := congrArg (DensePoly.scale (-1 : Int)) hnegone
        rw [hinvol, hscale_C_neg_one] at hcong
        exact hcong
    · -- Factor preservation.
      intro a b hab
      have hf_eq : f = DensePoly.scale (-1 : Int) a * b := by
        have hcong := congrArg (DensePoly.scale (-1 : Int)) hab
        rw [hinvol, hscale_mul_left] at hcong
        exact hcong
      rcases hirr.no_factors _ _ hf_eq with hsa | hb
      · left
        rcases hsa with h1 | hnegone
        · -- `scale (-1) a = C 1` ⟹ `a = C (-1)`, a unit.
          right
          have hcong := congrArg (DensePoly.scale (-1 : Int)) h1
          rw [hinvol, hscale_C_one] at hcong
          exact hcong
        · -- `scale (-1) a = C (-1)` ⟹ `a = C 1`, a unit.
          left
          have hcong := congrArg (DensePoly.scale (-1 : Int)) hnegone
          rw [hinvol, hscale_C_neg_one] at hcong
          exact hcong
      · exact Or.inr hb
  · rw [if_neg hlc]
    exact hirr

/-- Every factor emitted by the extracted `X`-power normalization array is
irreducible. -/
theorem xPowerFactorArray_irreducible
    (power : Nat) (factor : ZPoly)
    (h : factor ∈ (xPowerFactorArray power).toList) :
    ZPoly.Irreducible factor := by
  rw [mem_xPowerFactorArray_eq_X power factor h]
  exact ZPoly.irreducible_X

/-- Reassembly preserves the irreducibility proof for normalization factors
coming specifically from the extracted power of `X`. -/
theorem reassemblePolynomialFactors_xPower_irreducible
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) (factor : ZPoly)
    (_hmem : factor ∈ (reassemblePolynomialFactors d coreFactors).toList)
    (hx : factor ∈ (xPowerFactorArray d.xPower).toList) :
    ZPoly.Irreducible factor :=
  xPowerFactorArray_irreducible d.xPower factor hx

/-- Lift core-factor irreducibility through the reassembly.  When the
repeated-part expansion fully consumes its residual (so the reassembly emits
only `X` powers and the supplied core factors), every emitted raw factor is
irreducible.  This is the Mathlib-free "reassemble lift" consumed by the
assembled per-branch output theorem to discharge the `xPower` half of each
branch automatically. -/
theorem reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
    (d : FactorNormalizationData) (coreFactors : Array ZPoly)
    (hcomplete : reassemblyExpansionComplete d coreFactors)
    (h_core : ∀ factor ∈ coreFactors.toList, ZPoly.Irreducible factor)
    {factor : ZPoly}
    (hmem : factor ∈ (reassemblePolynomialFactors d coreFactors).toList) :
    ZPoly.Irreducible factor := by
  rcases reassemblePolynomialFactors_mem_xPower_or_core_of_expansionComplete
      d coreFactors factor hcomplete hmem with hx | hcore
  · exact xPowerFactorArray_irreducible d.xPower factor hx
  · exact h_core factor hcore

/-- Membership classifier for the constant square-free-core branch. The only
raw factors requiring irreducibility content are extracted powers of `X`; the
singleton core factor is `1`, and any repeated-part fallback is identified
separately for later expansion through actual core factors. -/
theorem reassemblePolynomialFactors_constant_irreducible_or_repeated_or_one
    (d : FactorNormalizationData) {factor : ZPoly}
    (hcore : d.squareFreeCore = 1)
    (hmem : factor ∈
      (reassemblePolynomialFactors d #[d.squareFreeCore]).toList) :
    ZPoly.Irreducible factor ∨
      factor ∈ (repeatedPartFactorArray d.repeatedPart).toList ∨
      factor = 1 := by
  rcases reassemblePolynomialFactors_mem d #[d.squareFreeCore] factor hmem with
    hprefix | hcore_mem
  · unfold polynomialNormalizationPrefixFactors at hprefix
    rw [Array.toList_append] at hprefix
    simp only [List.mem_append] at hprefix
    cases hprefix with
    | inl hx =>
        exact Or.inl (xPowerFactorArray_irreducible d.xPower factor hx)
    | inr hrep =>
        exact Or.inr (Or.inl hrep)
  · have hfactor : factor = d.squareFreeCore := by
      simpa using hcore_mem
    exact Or.inr (Or.inr (by simpa [hcore] using hfactor))

/-- The monic linear factor `X - r` is irreducible over `ZPoly`. -/
private theorem irreducible_linearFactorForRoot (r : Int) :
    ZPoly.Irreducible (linearFactorForRoot r) :=
  ZPoly.irreducible_of_size_two_monic (linearFactorForRoot r)
    (linearFactorForRoot_size_eq_two r)
    (leadingCoeff_linearFactorForRoot r)

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
theorem extractXPower_core_primitive_of_ne_zero
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
    rw [ZPoly.polyProduct_append, ZPoly.polyProduct_singleton, polyProduct_xPowerFactorArray_mul] at hex
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

private theorem normalizeForFactor_reassembles_with_signed_unit
    (f : ZPoly) (hf : f ≠ 0) :
    ∃ ε : Int, (ε = 1 ∨ ε = -1) ∧
      DensePoly.scale (ZPoly.content f * ε)
        (DensePoly.shift (normalizeForFactor f).xPower
          ((normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart)) =
        f := by
  let xData := ZPoly.extractXPower (ZPoly.primitivePart f)
  let sqData := ZPoly.primitiveSquareFreeDecomposition xData.core
  have hcore_primitive : ZPoly.Primitive xData.core := by
    simpa [xData] using extractXPower_core_primitive_of_ne_zero f hf
  have hcore_ne : xData.core ≠ 0 := by
    intro hzero
    have hcontent : ZPoly.content xData.core = 0 := by
      rw [hzero]
      simp [ZPoly.content, DensePoly.content_zero]
    rw [ZPoly.Primitive, hcontent] at hcore_primitive
    contradiction
  have hprimitive_core : ZPoly.primitivePart xData.core = xData.core :=
    ZPoly.primitivePart_eq_self_of_primitive xData.core hcore_primitive
  have hshift_core :
      DensePoly.shift xData.power xData.core = ZPoly.primitivePart f := by
    have hex :
        Array.polyProduct (xPowerFactorArray xData.power ++ #[xData.core]) =
          ZPoly.primitivePart f := by
      simpa [xData] using extractXPower_product (ZPoly.primitivePart f)
    rw [ZPoly.polyProduct_append, ZPoly.polyProduct_singleton, polyProduct_xPowerFactorArray_mul] at hex
    exact hex
  rcases ZPoly.primitiveSquareFreeDecomposition_reassembly_signed xData.core hcore_ne with
    ⟨ε, hε, hsq⟩
  refine ⟨ε, hε, ?_⟩
  have hsq_core :
      DensePoly.scale ε (sqData.squareFreeCore * sqData.repeatedPart) = xData.core := by
    simpa [sqData, hprimitive_core] using hsq
  have hshift_sq :
      DensePoly.scale ε
          (DensePoly.shift xData.power (sqData.squareFreeCore * sqData.repeatedPart)) =
        DensePoly.shift xData.power xData.core := by
    rw [← shift_scale_int]
    exact congrArg (DensePoly.shift xData.power) hsq_core
  have hscaled :
      DensePoly.scale (ZPoly.content f)
          (DensePoly.scale ε
            (DensePoly.shift xData.power (sqData.squareFreeCore * sqData.repeatedPart))) =
        DensePoly.scale (ZPoly.content f) (DensePoly.shift xData.power xData.core) := by
    rw [hshift_sq]
  rw [int_scale_scale] at hscaled
  rw [hshift_core, ZPoly.content_mul_primitivePart] at hscaled
  simpa [normalizeForFactor, xData, sqData] using hscaled

private theorem normalizeForFactor_reassembles_signedContentScalar
    (f : ZPoly) (hf : f ≠ 0) :
    DensePoly.scale (signedContentScalar f)
      (DensePoly.shift (normalizeForFactor f).xPower
        ((normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart)) = f := by
  let xData := ZPoly.extractXPower (ZPoly.primitivePart f)
  rcases normalizeForFactor_reassembles_with_signed_unit f hf with ⟨ε, hε, heq⟩
  -- Step 1: `content f` is positive.
  have hcontent_ne : ZPoly.content f ≠ 0 := by
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
  have hcontent_pos : 0 < ZPoly.content f := by
    have hnonneg : 0 ≤ ZPoly.content f := by
      show 0 ≤ DensePoly.content _
      rw [DensePoly.content]
      exact Int.natCast_nonneg _
    omega
  -- Step 2: the x-power core is nonzero.
  have hcore_primitive : ZPoly.Primitive xData.core := by
    simpa [xData] using extractXPower_core_primitive_of_ne_zero f hf
  have hcore_ne : xData.core ≠ 0 := by
    intro hzero
    have hcontent_core : ZPoly.content xData.core = 0 := by
      rw [hzero]
      simp [ZPoly.content, DensePoly.content_zero]
    have hone_eq_zero : (1 : Int) = 0 := by
      have := hcore_primitive
      rw [ZPoly.Primitive, hcontent_core] at this
      exact this.symm
    exact absurd hone_eq_zero (by decide)
  -- Step 3: `squareFreeCore * repeatedPart` has positive leading coefficient.
  have hA_pos :
      0 < DensePoly.leadingCoeff
        ((normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart) := by
    have h :=
      ZPoly.primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_leadingCoeff_pos
        xData.core hcore_ne
    simpa [normalizeForFactor, xData] using h
  have hA_ne :
      (normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart ≠ 0 := by
    intro hzero
    rw [hzero] at hA_pos
    have hl0 : DensePoly.leadingCoeff (0 : ZPoly) = 0 := rfl
    rw [hl0] at hA_pos
    omega
  have hB_leading :
      DensePoly.leadingCoeff
          (DensePoly.shift (normalizeForFactor f).xPower
            ((normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart)) =
        DensePoly.leadingCoeff
          ((normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart) :=
    ZPoly.leadingCoeff_shift_of_nonzero _ _ hA_ne
  have hcε_ne : ZPoly.content f * ε ≠ 0 := by
    intro hzero
    rcases Int.mul_eq_zero.mp hzero with h | h
    · exact hcontent_ne h
    · rcases hε with h1 | h1
      · rw [h1] at h; exact absurd h (by decide)
      · rw [h1] at h; exact absurd h (by decide)
  -- Step 4: extract the leading coefficient of `f` from `heq`.
  have h_f_leading :
      DensePoly.leadingCoeff f =
        (ZPoly.content f * ε) *
          DensePoly.leadingCoeff
            ((normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart) := by
    have h_LHS :
        DensePoly.leadingCoeff
            (DensePoly.scale (ZPoly.content f * ε)
              (DensePoly.shift (normalizeForFactor f).xPower
                ((normalizeForFactor f).squareFreeCore *
                  (normalizeForFactor f).repeatedPart))) =
          (ZPoly.content f * ε) *
            DensePoly.leadingCoeff
              ((normalizeForFactor f).squareFreeCore *
                (normalizeForFactor f).repeatedPart) := by
      rw [ZPoly.leadingCoeff_scale_of_nonzero _ _ hcε_ne, hB_leading]
    rw [← h_LHS, heq]
  -- Step 5: identify `signedContentScalar f = content f * ε`.
  suffices h_sign_eq : signedContentScalar f = ZPoly.content f * ε by
    rw [h_sign_eq]; exact heq
  rcases hε with hε | hε
  · -- ε = 1
    have hf_pos : 0 < DensePoly.leadingCoeff f := by
      rw [h_f_leading, hε, Int.mul_one]
      exact Int.mul_pos hcontent_pos hA_pos
    have hf_not_neg : ¬ DensePoly.leadingCoeff f < 0 := by omega
    unfold signedContentScalar
    rw [if_neg hf, if_neg hf_not_neg, hε, Int.mul_one]
  · -- ε = -1
    have hcontent_neg : ZPoly.content f * (-1 : Int) < 0 := by
      have hrw : ZPoly.content f * (-1 : Int) = -(ZPoly.content f) := by
        exact Int.mul_neg_one _
      rw [hrw]; omega
    have hf_neg : DensePoly.leadingCoeff f < 0 := by
      rw [h_f_leading, hε]
      exact Int.mul_neg_of_neg_of_pos hcontent_neg hA_pos
    unfold signedContentScalar
    rw [if_neg hf, if_pos hf_neg, hε, Int.mul_neg_one]

private theorem shift_mul_left_zpoly (k : Nat) (a b : ZPoly) :
    DensePoly.shift k (a * b) = DensePoly.shift k a * b := by
  rw [← DensePoly.monomial_one_mul_poly_eq_shift k (a * b)]
  rw [← DensePoly.monomial_one_mul_poly_eq_shift k a]
  exact (DensePoly.mul_assoc_poly (S := Int) _ _ _).symm

/--
The full normalized reassembly: combining the array-product layout from
`polyProduct_reassemblePolynomialFactors` with the signed content reconstruction
recovers the original polynomial exactly. Handles `f = 0` separately because
`signedContentScalar 0 = 0` collapses the scalar prefix.
-/
private theorem reassemblePolynomialFactors_product_eq_input
    (f : ZPoly) (coreFactors : Array ZPoly)
    (hcore : Array.polyProduct coreFactors =
      (normalizeForFactor f).squareFreeCore) :
    DensePoly.C (signedContentScalar f) *
      Array.polyProduct
        (reassemblePolynomialFactors (normalizeForFactor f) coreFactors) = f := by
  rw [polyProduct_reassemblePolynomialFactors, hcore]
  by_cases hf : f = 0
  · subst hf
    have hsig : signedContentScalar (0 : ZPoly) = 0 := by
      unfold signedContentScalar
      simp
    rw [hsig]
    have hC0 : DensePoly.C (0 : Int) = (0 : ZPoly) := by
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_C, DensePoly.coeff_zero]
      split <;> rfl
    rw [hC0]
    exact DensePoly.zero_mul _
  · rw [ZPoly.C_mul_eq_scale]
    have hrearrange :
        DensePoly.shift (normalizeForFactor f).xPower (normalizeForFactor f).repeatedPart *
            (normalizeForFactor f).squareFreeCore =
          DensePoly.shift (normalizeForFactor f).xPower
            ((normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart) := by
      rw [← shift_mul_left_zpoly]
      rw [DensePoly.mul_comm_poly (S := Int)
        (normalizeForFactor f).repeatedPart (normalizeForFactor f).squareFreeCore]
    rw [hrearrange]
    exact normalizeForFactor_reassembles_signedContentScalar f hf

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

private theorem firstSome_eq_some_of_append
    {α β : Type} (pre suffix : List α) (x : α) (f : α → Option β) (y : β)
    (hprefix : ∀ z ∈ pre, f z = none)
    (hx : f x = some y) :
    firstSome (pre ++ x :: suffix) f = some y := by
  induction pre with
  | nil =>
      simp [firstSome, hx]
  | cons z zs ih =>
      change
        (match f z with
        | some y' => some y'
        | none => firstSome (zs ++ x :: suffix) f) = some y
      rw [hprefix z (by simp)]
      exact ih (fun w hw => hprefix w (by simp [hw]))

theorem subsetSplitsWithFirst_mem_cons
    {factor : ZPoly} {factors selected rest : List ZPoly}
    (hmem : (selected, rest) ∈ subsetSplits factors) :
    (factor :: selected, rest) ∈ subsetSplitsWithFirst (factor :: factors) := by
  simp [subsetSplitsWithFirst, hmem]

/-- Constructor for `subsetSplits` membership on the empty list: the only
partition of the empty list is `([], [])`. -/
theorem subsetSplits_nil_mem :
    (([], []) : List ZPoly × List ZPoly) ∈ subsetSplits [] := by
  simp [subsetSplits]

/-- Constructor for `subsetSplits` membership on a cons list, head selected:
prepending `factor` to the `selected` side preserves enumerability. -/
theorem subsetSplits_cons_left_mem
    {factor : ZPoly} {factors selected rest : List ZPoly}
    (h : (selected, rest) ∈ subsetSplits factors) :
    (factor :: selected, rest) ∈ subsetSplits (factor :: factors) := by
  unfold subsetSplits
  refine List.mem_append.mpr (Or.inr ?_)
  exact List.mem_map.mpr ⟨(selected, rest), h, rfl⟩

/-- Constructor for `subsetSplits` membership on a cons list, head unselected:
prepending `factor` to the `rest` side preserves enumerability. -/
theorem subsetSplits_cons_right_mem
    {factor : ZPoly} {factors selected rest : List ZPoly}
    (h : (selected, rest) ∈ subsetSplits factors) :
    (selected, factor :: rest) ∈ subsetSplits (factor :: factors) := by
  unfold subsetSplits
  refine List.mem_append.mpr (Or.inl ?_)
  exact List.mem_map.mpr ⟨(selected, rest), h, rfl⟩

/-- Existence companion to `firstSome_some`: if `f x = some y` for some `x ∈ xs`,
then `firstSome xs f` is itself `some _`.  Used to chain executable completeness
arguments: showing the search at the current step can succeed reduces to
exhibiting a single subset whose candidate works. -/
theorem firstSome_isSome_of_mem
    {α β : Type} {xs : List α} {f : α → Option β} {x : α} {y : β}
    (hmem : x ∈ xs) (hxy : f x = some y) :
    (firstSome xs f).isSome = true := by
  induction xs with
  | nil => simp at hmem
  | cons z zs ih =>
      unfold firstSome
      cases hfz : f z with
      | some _ => simp
      | none =>
          rcases List.mem_cons.mp hmem with hxz | hxzs
          · subst hxz
            rw [hfz] at hxy
            cases hxy
          · simpa [hfz] using ih hxzs

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
                    exact ZPoly.polyProduct_cons_toArray (Array.polyProduct split.1.toArray) rest
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
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        by_cases hrecord : shouldRecordPolynomialFactor candidate = true
        · simp [candidate, hrecord] at hsplit
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
                      exact ZPoly.polyProduct_cons_toArray candidate rest
                    _ = candidate * quotient := by
                      rw [hrest]
                    _ = quotient * candidate := by
                      rw [DensePoly.mul_comm_poly (S := Int)]
                    _ = target := hquot_prod
        · simp [candidate, hrecord] at hsplit

private theorem recombinationSearchMod_product
    (f : ZPoly) (modulus : Nat) (localFactors factors : List ZPoly)
    (hsearch : recombinationSearchMod f modulus localFactors = some factors) :
    Array.polyProduct factors.toArray = f := by
  exact recombinationSearchModAux_product
    f modulus localFactors factors (localFactors.length + 1) hsearch

private theorem recombinationSearchModAux_normalizeFactorSign
    (target : ZPoly) (modulus : Nat) (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch : recombinationSearchModAux target modulus localFactors fuel = some factors) :
    ∀ factor ∈ factors, normalizeFactorSign factor = factor := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [recombinationSearchModAux] at hsearch
  | succ fuel ih =>
      unfold recombinationSearchModAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simp
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        let candidate :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        by_cases hrecord : shouldRecordPolynomialFactor candidate = true
        · simp [candidate, hrecord] at hsplit
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
                  intro factor hmem
                  simp at hmem
                  cases hmem with
                  | inl hfactor =>
                      rw [hfactor]
                      exact normalizeFactorSign_idem
                        (ZPoly.primitivePart <|
                          centeredLiftPoly (Array.polyProduct split.1.toArray) modulus)
                  | inr hrest =>
                      exact ih quotient split.2 rest hrec factor hrest
        · simp [candidate, hrecord] at hsplit

private theorem recombinationSearchModAux_shouldRecord
    (target : ZPoly) (modulus : Nat) (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch : recombinationSearchModAux target modulus localFactors fuel = some factors) :
    ∀ factor ∈ factors, shouldRecordPolynomialFactor factor = true := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [recombinationSearchModAux] at hsearch
  | succ fuel ih =>
      unfold recombinationSearchModAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simp
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        let candidate :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        by_cases hrecord : shouldRecordPolynomialFactor candidate = true
        · simp [candidate, hrecord] at hsplit
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
                  intro factor hmem
                  simp at hmem
                  cases hmem with
                  | inl hfactor =>
                      rw [hfactor]
                      exact hrecord
                  | inr hrest =>
                      exact ih quotient split.2 rest hrec factor hrest
        · simp [candidate, hrecord] at hsplit

private theorem recombinationSearchMod_normalizeFactorSign
    (f : ZPoly) (modulus : Nat) (localFactors factors : List ZPoly)
    (hsearch : recombinationSearchMod f modulus localFactors = some factors) :
    ∀ factor ∈ factors, normalizeFactorSign factor = factor :=
  recombinationSearchModAux_normalizeFactorSign
    f modulus localFactors factors (localFactors.length + 1) hsearch

private theorem recombinationSearchMod_shouldRecord
    (f : ZPoly) (modulus : Nat) (localFactors factors : List ZPoly)
    (hsearch : recombinationSearchMod f modulus localFactors = some factors) :
    ∀ factor ∈ factors, shouldRecordPolynomialFactor factor = true :=
  recombinationSearchModAux_shouldRecord
    f modulus localFactors factors (localFactors.length + 1) hsearch

private theorem scaledRecombinationSearchModAux_normalizeFactorSign
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch :
      scaledRecombinationSearchModAux coreLc target modulus localFactors fuel
        = some factors) :
    ∀ factor ∈ factors, normalizeFactorSign factor = factor := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [scaledRecombinationSearchModAux] at hsearch
  | succ fuel ih =>
      unfold scaledRecombinationSearchModAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simp
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        let candidate :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly
                (DensePoly.scale coreLc (Array.polyProduct split.1.toArray))
                modulus
        by_cases hrecord : shouldRecordPolynomialFactor candidate = true
        · simp [candidate, hrecord] at hsplit
          cases hquot : exactQuotient? target candidate with
          | none =>
              simp [candidate, hquot] at hsplit
          | some quotient =>
              simp [candidate, hquot] at hsplit
              cases hrec :
                  scaledRecombinationSearchModAux coreLc quotient modulus
                    split.2 fuel with
              | none =>
                  simp [hrec] at hsplit
              | some rest =>
                  simp [hrec] at hsplit
                  cases hsplit
                  intro factor hmem
                  simp at hmem
                  cases hmem with
                  | inl hfactor =>
                      rw [hfactor]
                      exact normalizeFactorSign_idem
                        (ZPoly.primitivePart <|
                          centeredLiftPoly
                            (DensePoly.scale coreLc
                              (Array.polyProduct split.1.toArray))
                            modulus)
                  | inr hrest =>
                      exact ih quotient split.2 rest hrec factor hrest
        · simp [candidate, hrecord] at hsplit

private theorem scaledRecombinationSearchModAux_shouldRecord
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch :
      scaledRecombinationSearchModAux coreLc target modulus localFactors fuel
        = some factors) :
    ∀ factor ∈ factors, shouldRecordPolynomialFactor factor = true := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [scaledRecombinationSearchModAux] at hsearch
  | succ fuel ih =>
      unfold scaledRecombinationSearchModAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simp
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        let candidate :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly
                (DensePoly.scale coreLc (Array.polyProduct split.1.toArray))
                modulus
        by_cases hrecord : shouldRecordPolynomialFactor candidate = true
        · simp [candidate, hrecord] at hsplit
          cases hquot : exactQuotient? target candidate with
          | none =>
              simp [candidate, hquot] at hsplit
          | some quotient =>
              simp [candidate, hquot] at hsplit
              cases hrec :
                  scaledRecombinationSearchModAux coreLc quotient modulus
                    split.2 fuel with
              | none =>
                  simp [hrec] at hsplit
              | some rest =>
                  simp [hrec] at hsplit
                  cases hsplit
                  intro factor hmem
                  simp at hmem
                  cases hmem with
                  | inl hfactor =>
                      rw [hfactor]
                      exact hrecord
                  | inr hrest =>
                      exact ih quotient split.2 rest hrec factor hrest
        · simp [candidate, hrecord] at hsplit

private theorem scaledRecombinationSearchModAux_primitive
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch :
      scaledRecombinationSearchModAux coreLc target modulus localFactors fuel
        = some factors) :
    ∀ factor ∈ factors, ZPoly.Primitive factor := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [scaledRecombinationSearchModAux] at hsearch
  | succ fuel ih =>
      unfold scaledRecombinationSearchModAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simp
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        let candidate :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly
                (DensePoly.scale coreLc (Array.polyProduct split.1.toArray))
                modulus
        by_cases hrecord : shouldRecordPolynomialFactor candidate = true
        · simp [candidate, hrecord] at hsplit
          cases hquot : exactQuotient? target candidate with
          | none =>
              simp [candidate, hquot] at hsplit
          | some quotient =>
              simp [candidate, hquot] at hsplit
              cases hrec :
                  scaledRecombinationSearchModAux coreLc quotient modulus
                    split.2 fuel with
              | none =>
                  simp [hrec] at hsplit
              | some rest =>
                  simp [hrec] at hsplit
                  cases hsplit
                  intro factor hmem
                  simp at hmem
                  cases hmem with
                  | inl hfactor =>
                      rw [hfactor]
                      -- The head emitted candidate is primitive: from
                      -- `hrecord` we get nonzeroness of the candidate, which
                      -- (via `normalizeFactorSign_ne_zero_of_ne_zero`)
                      -- propagates back through `primitivePart`'s
                      -- zero-condition (`primitivePart_eq_zero_of_content_eq_zero`)
                      -- to `content (centeredLift ...) ≠ 0`, hence
                      -- `Primitive (primitivePart (centeredLift ...))` by
                      -- `primitivePart_primitive`, and finally
                      -- `Primitive (normalizeFactorSign ...)` by deliverable 1.
                      have hcand_ne :
                          normalizeFactorSign (ZPoly.primitivePart
                              (centeredLiftPoly
                                (DensePoly.scale coreLc
                                  (Array.polyProduct split.1.toArray))
                                modulus)) ≠ 0 := by
                        unfold shouldRecordPolynomialFactor at hrecord
                        simp at hrecord
                        exact hrecord.1.1
                      have hpp_ne :
                          ZPoly.primitivePart
                              (centeredLiftPoly
                                (DensePoly.scale coreLc
                                  (Array.polyProduct split.1.toArray))
                                modulus) ≠ 0 := by
                        intro hpp
                        apply hcand_ne
                        rw [hpp]
                        unfold normalizeFactorSign
                        rw [if_neg
                          (by decide : ¬ DensePoly.leadingCoeff (0 : ZPoly) < 0)]
                      have hcontent_ne :
                          ZPoly.content
                              (centeredLiftPoly
                                (DensePoly.scale coreLc
                                  (Array.polyProduct split.1.toArray))
                                modulus) ≠ 0 := by
                        intro hcontent
                        apply hpp_ne
                        show DensePoly.primitivePart _ = 0
                        exact DensePoly.primitivePart_eq_zero_of_content_eq_zero _
                          (by simpa [ZPoly.content] using hcontent)
                      have hpp_primitive :
                          ZPoly.Primitive
                            (ZPoly.primitivePart
                              (centeredLiftPoly
                                (DensePoly.scale coreLc
                                  (Array.polyProduct split.1.toArray))
                                modulus)) :=
                        ZPoly.primitivePart_primitive _ hcontent_ne
                      exact normalizeFactorSign_primitive _ hpp_primitive
                  | inr hrest =>
                      exact ih quotient split.2 rest hrec factor hrest
        · simp [candidate, hrecord] at hsplit

private theorem scaledRecombinationSearchMod_normalizeFactorSign
    (coreLc : Int) (f : ZPoly) (modulus : Nat)
    (localFactors factors : List ZPoly)
    (hsearch :
      scaledRecombinationSearchMod coreLc f modulus localFactors = some factors) :
    ∀ factor ∈ factors, normalizeFactorSign factor = factor :=
  scaledRecombinationSearchModAux_normalizeFactorSign
    coreLc f modulus localFactors factors (localFactors.length + 1) hsearch

private theorem scaledRecombinationSearchMod_primitive
    (coreLc : Int) (f : ZPoly) (modulus : Nat)
    (localFactors factors : List ZPoly)
    (hsearch :
      scaledRecombinationSearchMod coreLc f modulus localFactors = some factors) :
    ∀ factor ∈ factors, ZPoly.Primitive factor :=
  scaledRecombinationSearchModAux_primitive
    coreLc f modulus localFactors factors (localFactors.length + 1) hsearch

private theorem scaledRecombinationSearchMod_shouldRecord
    (coreLc : Int) (f : ZPoly) (modulus : Nat)
    (localFactors factors : List ZPoly)
    (hsearch :
      scaledRecombinationSearchMod coreLc f modulus localFactors = some factors) :
    ∀ factor ∈ factors, shouldRecordPolynomialFactor factor = true :=
  scaledRecombinationSearchModAux_shouldRecord
    coreLc f modulus localFactors factors (localFactors.length + 1) hsearch

private theorem recombineExhaustive_product
    (f : ZPoly) (d : LiftData) (factors : List ZPoly)
    (hsearch :
      recombinationSearchMod f (liftModulus d) d.liftedFactors.toList =
        some factors) :
    Array.polyProduct (recombineExhaustive f d) = f := by
  unfold recombineExhaustive
  simp [hsearch, recombinationSearchMod_product f (liftModulus d)
    d.liftedFactors.toList factors hsearch]

private theorem recombineExhaustive_normalizeFactorSign
    (f : ZPoly) (d : LiftData) :
    ∀ factor ∈ (recombineExhaustive f d).toList,
      normalizeFactorSign factor = factor := by
  unfold recombineExhaustive
  cases hsearch :
      recombinationSearchMod f (liftModulus d) d.liftedFactors.toList with
  | none =>
      simp
  | some factors =>
      intro factor hmem
      exact recombinationSearchMod_normalizeFactorSign f (liftModulus d)
        d.liftedFactors.toList factors hsearch factor (by simpa using hmem)

private theorem recombineExhaustive_shouldRecord
    (f : ZPoly) (d : LiftData) :
    ∀ factor ∈ (recombineExhaustive f d).toList,
      shouldRecordPolynomialFactor factor = true := by
  unfold recombineExhaustive
  cases hsearch :
      recombinationSearchMod f (liftModulus d) d.liftedFactors.toList with
  | none =>
      simp
  | some factors =>
      intro factor hmem
      exact recombinationSearchMod_shouldRecord f (liftModulus d)
        d.liftedFactors.toList factors hsearch factor (by simpa using hmem)

private theorem recombineScaledExhaustive_normalizeFactorSign
    (coreLc : Int) (f : ZPoly) (d : LiftData) :
    ∀ factor ∈ (recombineScaledExhaustive coreLc f d).toList,
      normalizeFactorSign factor = factor := by
  unfold recombineScaledExhaustive
  cases hsearch :
      scaledRecombinationSearchMod coreLc f (liftModulus d)
        d.liftedFactors.toList with
  | none =>
      simp
  | some factors =>
      intro factor hmem
      exact scaledRecombinationSearchMod_normalizeFactorSign coreLc f
        (liftModulus d) d.liftedFactors.toList factors hsearch factor
        (by simpa using hmem)

private theorem recombineScaledExhaustive_primitive
    (coreLc : Int) (f : ZPoly) (d : LiftData) :
    ∀ factor ∈ (recombineScaledExhaustive coreLc f d).toList,
      ZPoly.Primitive factor := by
  unfold recombineScaledExhaustive
  cases hsearch :
      scaledRecombinationSearchMod coreLc f (liftModulus d)
        d.liftedFactors.toList with
  | none =>
      simp
  | some factors =>
      intro factor hmem
      exact scaledRecombinationSearchMod_primitive coreLc f
        (liftModulus d) d.liftedFactors.toList factors hsearch factor
        (by simpa using hmem)

private theorem recombineScaledExhaustive_shouldRecord
    (coreLc : Int) (f : ZPoly) (d : LiftData) :
    ∀ factor ∈ (recombineScaledExhaustive coreLc f d).toList,
      shouldRecordPolynomialFactor factor = true := by
  unfold recombineScaledExhaustive
  cases hsearch :
      scaledRecombinationSearchMod coreLc f (liftModulus d)
        d.liftedFactors.toList with
  | none =>
      simp
  | some factors =>
      intro factor hmem
      exact scaledRecombinationSearchMod_shouldRecord coreLc f (liftModulus d)
        d.liftedFactors.toList factors hsearch factor (by simpa using hmem)

private theorem scaledRecombinationSearchModAux_product
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch :
      scaledRecombinationSearchModAux coreLc target modulus localFactors fuel
        = some factors) :
    Array.polyProduct factors.toArray = target := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [scaledRecombinationSearchModAux] at hsearch
  | succ fuel ih =>
      unfold scaledRecombinationSearchModAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simpa [Array.polyProduct] using htarget.symm
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        let candidate :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly
                (DensePoly.scale coreLc (Array.polyProduct split.1.toArray))
                modulus
        by_cases hrecord : shouldRecordPolynomialFactor candidate = true
        · simp [candidate, hrecord] at hsplit
          cases hquot : exactQuotient? target candidate with
          | none =>
              simp [candidate, hquot] at hsplit
          | some quotient =>
              simp [candidate, hquot] at hsplit
              cases hrec :
                  scaledRecombinationSearchModAux coreLc quotient modulus
                    split.2 fuel with
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
                      exact ZPoly.polyProduct_cons_toArray candidate rest
                    _ = candidate * quotient := by
                      rw [hrest]
                    _ = quotient * candidate := by
                      rw [DensePoly.mul_comm_poly (S := Int)]
                    _ = target := hquot_prod
        · simp [candidate, hrecord] at hsplit

private theorem scaledRecombinationSearchMod_product
    (coreLc : Int) (f : ZPoly) (modulus : Nat)
    (localFactors factors : List ZPoly)
    (hsearch :
      scaledRecombinationSearchMod coreLc f modulus localFactors = some factors) :
    Array.polyProduct factors.toArray = f := by
  exact scaledRecombinationSearchModAux_product
    coreLc f modulus localFactors factors (localFactors.length + 1) hsearch

private theorem recombineScaledExhaustive_product
    (coreLc : Int) (f : ZPoly) (d : LiftData) (factors : List ZPoly)
    (hsearch :
      scaledRecombinationSearchMod coreLc f (liftModulus d) d.liftedFactors.toList =
        some factors) :
    Array.polyProduct (recombineScaledExhaustive coreLc f d) = f := by
  unfold recombineScaledExhaustive
  simp [hsearch, scaledRecombinationSearchMod_product coreLc f (liftModulus d)
    d.liftedFactors.toList factors hsearch]

/-- Pointwise: scaling a `ZPoly` by the integer `1` is a no-op. -/
private theorem densePoly_int_scale_one (p : ZPoly) :
    DensePoly.scale (1 : Int) p = p := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Int) 1 p n (Int.mul_zero 1)]
  exact Int.one_mul (p.coeff n)

/-- `scaledRecombinationSearchModAux` at `coreLc = 1` collapses to the unscaled
`recombinationSearchModAux`: the only difference between the two routines is the
inner `DensePoly.scale coreLc` applied to the lifted-factor product, which is a
no-op when `coreLc = 1`. -/
private theorem scaledRecombinationSearchModAux_eq_recombinationSearchModAux_of_one
    (target : ZPoly) (modulus : Nat) (localFactors : List ZPoly) (fuel : Nat) :
    scaledRecombinationSearchModAux 1 target modulus localFactors fuel =
      recombinationSearchModAux target modulus localFactors fuel := by
  induction fuel generalizing target localFactors with
  | zero => rfl
  | succ fuel ih =>
      unfold scaledRecombinationSearchModAux recombinationSearchModAux
      by_cases htarget : target = 1
      · simp [htarget]
      · simp only [htarget, if_false]
        congr 1
        funext split
        simp only [densePoly_int_scale_one]
        by_cases hrecord :
            shouldRecordPolynomialFactor (normalizeFactorSign <|
                ZPoly.primitivePart <|
                  centeredLiftPoly (Array.polyProduct split.1.toArray) modulus) = true
        · simp only [hrecord, if_true]
          cases hquot : exactQuotient? target (normalizeFactorSign <|
              ZPoly.primitivePart <|
                centeredLiftPoly (Array.polyProduct split.1.toArray) modulus) with
          | none => rfl
          | some quotient =>
              simp only [ih]
        · simp only [hrecord, Bool.false_eq_true, if_false]

/-- Surface-level collapse: `scaledRecombinationSearchMod 1 = recombinationSearchMod`. -/
private theorem scaledRecombinationSearchMod_eq_recombinationSearchMod_of_one
    (f : ZPoly) (modulus : Nat) (localFactors : List ZPoly) :
    scaledRecombinationSearchMod 1 f modulus localFactors =
      recombinationSearchMod f modulus localFactors := by
  unfold scaledRecombinationSearchMod recombinationSearchMod
  exact scaledRecombinationSearchModAux_eq_recombinationSearchModAux_of_one
    f modulus localFactors (localFactors.length + 1)

/-- Executable collapse: `recombineScaledExhaustive 1 = recombineExhaustive`.

The scaled and unscaled exhaustive recombination wrappers agree when the
scaling coefficient is `1` (i.e., for monic cores).  Used by the Mathlib-side
`exhaustiveCoreFactorsWithBound_mem_of_recombinationSearchMod_some` to translate
an unscaled search witness into the scaled executable call site introduced by
the swap. -/
theorem recombineScaledExhaustive_eq_recombineExhaustive_of_one
    (f : ZPoly) (d : LiftData) :
    recombineScaledExhaustive 1 f d = recombineExhaustive f d := by
  unfold recombineScaledExhaustive recombineExhaustive
  rw [scaledRecombinationSearchMod_eq_recombinationSearchMod_of_one]

/-- Base case for the exhaustive recombination search: when the running target
has already been reduced to `1`, the search terminates and returns the empty
factor list. -/
theorem recombinationSearchModAux_one
    (modulus : Nat) (localFactors : List ZPoly) (fuel : Nat) :
    recombinationSearchModAux 1 modulus localFactors (fuel + 1) = some [] := by
  unfold recombinationSearchModAux
  simp

/-- Executable completeness of `recombinationSearchModAux`: if a single
exhaustive-search step can pick the candidate produced by centred-lifting
`selected` (a subset of `localFactors` whose order-preserving partition has
`rest` as complement), and the recursive search on the residual `(quotient,
rest)` succeeds with the supplied fuel, then the search at the current step
also succeeds.

This is the Mathlib-free step lemma underpinning Group A coverage proofs: it
exposes that any subset of the lifted local factors with a working candidate
is enumerated by `subsetSplitsWithFirst`, and that the search descends through
that candidate to the residual problem. -/
theorem recombinationSearchModAux_isSome_of_step
    {target candidate quotient : ZPoly} {modulus fuel : Nat}
    {localFactors selected rest : List ZPoly}
    (htarget_ne_one : target ≠ 1)
    (hsplit : (selected, rest) ∈ subsetSplitsWithFirst localFactors)
    (hcandidate_def :
      candidate = normalizeFactorSign
        (ZPoly.primitivePart (centeredLiftPoly (Array.polyProduct selected.toArray) modulus)))
    (hrecord : shouldRecordPolynomialFactor candidate = true)
    (hquot : exactQuotient? target candidate = some quotient)
    (hsearch_rest :
      (recombinationSearchModAux quotient modulus rest fuel).isSome = true) :
    (recombinationSearchModAux target modulus localFactors (fuel + 1)).isSome = true := by
  obtain ⟨restFactors, hrest⟩ := Option.isSome_iff_exists.mp hsearch_rest
  unfold recombinationSearchModAux
  rw [if_neg htarget_ne_one]
  refine firstSome_isSome_of_mem (y := candidate :: restFactors) hsplit ?_
  show (let candidate' := normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct selected.toArray) modulus
        if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? target candidate' with
          | none => none
          | some quotient' =>
              match recombinationSearchModAux quotient' modulus rest fuel with
              | none => none
              | some r => some (candidate' :: r)
        else none) = some (candidate :: restFactors)
  rw [show (normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct selected.toArray) modulus) = candidate
        from hcandidate_def.symm]
  rw [if_pos hrecord]
  simp only [hquot, hrest]

/-- Companion to `recombinationSearchModAux_isSome_of_step` at the
`recombinationSearchMod` surface.  Hides the fuel parameter, requiring the
caller to supply the recursive isSome witness already specialised to fuel
`localFactors.length`.  Useful for downstream callers that want to chain
step lemmas with a fixed shared fuel budget. -/
theorem recombinationSearchMod_isSome_of_step
    {target candidate quotient : ZPoly} {modulus : Nat}
    {localFactors selected rest : List ZPoly}
    (htarget_ne_one : target ≠ 1)
    (hsplit : (selected, rest) ∈ subsetSplitsWithFirst localFactors)
    (hcandidate_def :
      candidate = normalizeFactorSign
        (ZPoly.primitivePart (centeredLiftPoly (Array.polyProduct selected.toArray) modulus)))
    (hrecord : shouldRecordPolynomialFactor candidate = true)
    (hquot : exactQuotient? target candidate = some quotient)
    (hsearch_rest :
      (recombinationSearchModAux quotient modulus rest localFactors.length).isSome = true) :
    (recombinationSearchMod target modulus localFactors).isSome = true := by
  unfold recombinationSearchMod
  exact recombinationSearchModAux_isSome_of_step (fuel := localFactors.length)
    htarget_ne_one hsplit hcandidate_def hrecord hquot hsearch_rest

/--
Exact-output version of `recombinationSearchModAux_isSome_of_step`.

The earlier completeness lemma is intentionally weak: it only proves that the
search succeeds when a particular split would work.  This theorem is the
concrete-output companion used by coverage proofs: if that split is positioned
after a prefix whose recombination attempts all fail, then the executable
`firstSome` traversal returns the candidate from this split as the head of the
resulting factor list.
-/
theorem recombinationSearchModAux_eq_some_of_step_of_prefix_none
    {target candidate quotient : ZPoly} {modulus fuel : Nat}
    {localFactors selected rest restFactors : List ZPoly}
    {pre suffix : List (List ZPoly × List ZPoly)}
    (htarget_ne_one : target ≠ 1)
    (hsplits :
      subsetSplitsWithFirst localFactors = pre ++ (selected, rest) :: suffix)
    (hprefix :
      ∀ split ∈ pre,
        (let candidate' :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? target candidate' with
          | none => none
          | some quotient' =>
              match recombinationSearchModAux quotient' modulus split.2 fuel with
              | none => none
              | some r => some (candidate' :: r)
        else none) = none)
    (hcandidate_def :
      candidate = normalizeFactorSign
        (ZPoly.primitivePart (centeredLiftPoly (Array.polyProduct selected.toArray) modulus)))
    (hrecord : shouldRecordPolynomialFactor candidate = true)
    (hquot : exactQuotient? target candidate = some quotient)
    (hsearch_rest :
      recombinationSearchModAux quotient modulus rest fuel = some restFactors) :
    recombinationSearchModAux target modulus localFactors (fuel + 1) =
      some (candidate :: restFactors) := by
  unfold recombinationSearchModAux
  rw [if_neg htarget_ne_one, hsplits]
  refine firstSome_eq_some_of_append pre suffix (selected, rest) _ _ hprefix ?_
  show (let candidate' :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct selected.toArray) modulus
        if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? target candidate' with
          | none => none
          | some quotient' =>
              match recombinationSearchModAux quotient' modulus rest fuel with
              | none => none
              | some r => some (candidate' :: r)
        else none) = some (candidate :: restFactors)
  rw [show (normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct selected.toArray) modulus) = candidate
        from hcandidate_def.symm]
  rw [if_pos hrecord]
  simp only [hquot, hsearch_rest]

/--
Scaled-candidate counterpart of `recombinationSearchModAux_eq_some_of_step_of_prefix_none`.

Structurally identical to the unscaled step lemma, with the inner `let
candidate' := ...` expression in both the prefix-none hypothesis and the goal
applying `DensePoly.scale coreLc` to the lifted-factor product before
centre-lifting.  This is the step driver the primitive recursive coverage
proof in #4647 will use, where the candidate is recovered from the integer
factor via `scaledRecombinationCandidate_eq_factor_of_recovery`.
-/
theorem scaledRecombinationSearchModAux_eq_some_of_step_of_prefix_none
    {coreLc : Int} {target candidate quotient : ZPoly} {modulus fuel : Nat}
    {localFactors selected rest restFactors : List ZPoly}
    {pre suffix : List (List ZPoly × List ZPoly)}
    (htarget_ne_one : target ≠ 1)
    (hsplits :
      subsetSplitsWithFirst localFactors = pre ++ (selected, rest) :: suffix)
    (hprefix :
      ∀ split ∈ pre,
        (let candidate' :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly
                (DensePoly.scale coreLc (Array.polyProduct split.1.toArray))
                modulus
        if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? target candidate' with
          | none => none
          | some quotient' =>
              match scaledRecombinationSearchModAux coreLc quotient' modulus
                  split.2 fuel with
              | none => none
              | some r => some (candidate' :: r)
        else none) = none)
    (hcandidate_def :
      candidate = normalizeFactorSign
        (ZPoly.primitivePart
          (centeredLiftPoly
            (DensePoly.scale coreLc (Array.polyProduct selected.toArray))
            modulus)))
    (hrecord : shouldRecordPolynomialFactor candidate = true)
    (hquot : exactQuotient? target candidate = some quotient)
    (hsearch_rest :
      scaledRecombinationSearchModAux coreLc quotient modulus rest fuel =
        some restFactors) :
    scaledRecombinationSearchModAux coreLc target modulus localFactors
        (fuel + 1) =
      some (candidate :: restFactors) := by
  unfold scaledRecombinationSearchModAux
  rw [if_neg htarget_ne_one, hsplits]
  refine firstSome_eq_some_of_append pre suffix (selected, rest) _ _ hprefix ?_
  show (let candidate' :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly
                (DensePoly.scale coreLc (Array.polyProduct selected.toArray))
                modulus
        if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? target candidate' with
          | none => none
          | some quotient' =>
              match scaledRecombinationSearchModAux coreLc quotient' modulus
                  rest fuel with
              | none => none
              | some r => some (candidate' :: r)
        else none) = some (candidate :: restFactors)
  rw [show (normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly
                (DensePoly.scale coreLc (Array.polyProduct selected.toArray))
                modulus) = candidate
        from hcandidate_def.symm]
  rw [if_pos hrecord]
  simp only [hquot, hsearch_rest]

/--
Surface exact-output companion for `recombinationSearchMod`.

This hides the fuel parameter in the same way as
`recombinationSearchMod_isSome_of_step`, while retaining the returned factor
list when the selected split is the first successful split.
-/
theorem recombinationSearchMod_eq_some_of_step_of_prefix_none
    {target candidate quotient : ZPoly} {modulus : Nat}
    {localFactors selected rest restFactors : List ZPoly}
    {pre suffix : List (List ZPoly × List ZPoly)}
    (htarget_ne_one : target ≠ 1)
    (hsplits :
      subsetSplitsWithFirst localFactors = pre ++ (selected, rest) :: suffix)
    (hprefix :
      ∀ split ∈ pre,
        (let candidate' :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? target candidate' with
          | none => none
          | some quotient' =>
              match recombinationSearchModAux quotient' modulus split.2 localFactors.length with
              | none => none
              | some r => some (candidate' :: r)
        else none) = none)
    (hcandidate_def :
      candidate = normalizeFactorSign
        (ZPoly.primitivePart (centeredLiftPoly (Array.polyProduct selected.toArray) modulus)))
    (hrecord : shouldRecordPolynomialFactor candidate = true)
    (hquot : exactQuotient? target candidate = some quotient)
    (hsearch_rest :
      recombinationSearchModAux quotient modulus rest localFactors.length = some restFactors) :
    recombinationSearchMod target modulus localFactors =
      some (candidate :: restFactors) := by
  unfold recombinationSearchMod
  exact
    recombinationSearchModAux_eq_some_of_step_of_prefix_none
      (fuel := localFactors.length) htarget_ne_one hsplits hprefix
      hcandidate_def hrecord hquot hsearch_rest

/-- When `recombinationSearchMod` succeeds on the lifted-factor list, the
`recombineExhaustive` wrapper returns exactly the array of recovered factors.
This is the equality lemma that lets downstream irreducibility proofs replace a
`recombineExhaustive` term with a concrete factor list once the search is
known to succeed. -/
theorem recombineExhaustive_eq_of_recombinationSearchMod_some
    {f : ZPoly} {d : LiftData} {factors : List ZPoly}
    (h : recombinationSearchMod f (liftModulus d) d.liftedFactors.toList = some factors) :
    recombineExhaustive f d = factors.toArray := by
  unfold recombineExhaustive
  rw [h]

/-- Scaled-candidate counterpart of
`recombineExhaustive_eq_of_recombinationSearchMod_some`: when the scaled
search succeeds on the lifted-factor list, `recombineScaledExhaustive`
returns exactly the array of recovered factors. -/
theorem recombineScaledExhaustive_eq_of_scaledRecombinationSearchMod_some
    {coreLc : Int} {f : ZPoly} {d : LiftData} {factors : List ZPoly}
    (h : scaledRecombinationSearchMod coreLc f (liftModulus d)
        d.liftedFactors.toList = some factors) :
    recombineScaledExhaustive coreLc f d = factors.toArray := by
  unfold recombineScaledExhaustive
  rw [h]

theorem exhaustiveCoreFactorsWithBound_normalizeFactorSign
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    (hcore : normalizeFactorSign core = core) :
    ∀ factor ∈ (exhaustiveCoreFactorsWithBound core B primeData).toList,
      normalizeFactorSign factor = factor := by
  rw [exhaustiveCoreFactorsWithBound]
  by_cases hB : B = 0
  · simp [hB, hcore]
  · simp only [hB, if_false]
    by_cases hempty :
        (recombineScaledExhaustive (DensePoly.leadingCoeff core) core
            (ZPoly.toMonicLiftData core B primeData)).isEmpty
    · simp [hempty, hcore]
    · simp only [hempty]
      exact recombineScaledExhaustive_normalizeFactorSign (DensePoly.leadingCoeff core) core
        (ZPoly.toMonicLiftData core B primeData)

theorem exhaustiveCoreFactorsWithBound_shouldRecord
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    (hcore : shouldRecordPolynomialFactor core = true) :
    ∀ factor ∈ (exhaustiveCoreFactorsWithBound core B primeData).toList,
      shouldRecordPolynomialFactor factor = true := by
  rw [exhaustiveCoreFactorsWithBound]
  by_cases hB : B = 0
  · simp [hB, hcore]
  · simp only [hB, if_false]
    by_cases hempty :
        (recombineScaledExhaustive (DensePoly.leadingCoeff core) core
            (ZPoly.toMonicLiftData core B primeData)).isEmpty
    · simp [hempty, hcore]
    · simp only [hempty]
      exact recombineScaledExhaustive_shouldRecord (DensePoly.leadingCoeff core) core
        (ZPoly.toMonicLiftData core B primeData)

/-- Every emitted factor of the exhaustive recombination wrapper is
primitive when the input core is primitive. The two `#[core]` short-circuit
branches return the input itself; the genuine recombination branch
dispatches to `recombineScaledExhaustive_primitive`. -/
theorem exhaustiveCoreFactorsWithBound_primitive
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    (hcore_primitive : ZPoly.Primitive core) :
    ∀ factor ∈ (exhaustiveCoreFactorsWithBound core B primeData).toList,
      ZPoly.Primitive factor := by
  rw [exhaustiveCoreFactorsWithBound]
  by_cases hB : B = 0
  · simp [hB, hcore_primitive]
  · simp only [hB, if_false]
    by_cases hempty :
        (recombineScaledExhaustive (DensePoly.leadingCoeff core) core
            (ZPoly.toMonicLiftData core B primeData)).isEmpty
    · simp [hempty, hcore_primitive]
    · simp only [hempty]
      exact recombineScaledExhaustive_primitive (DensePoly.leadingCoeff core) core
        (ZPoly.toMonicLiftData core B primeData)

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
          (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors)
              hrows)) = true
    · simp [hdeg] at hrecover
    · simp only [hdeg, Bool.false_eq_true, if_false] at hrecover
      cases hcand : bhksIndicatorCandidates? f d
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors)
              hrows)) with
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

private theorem bhksRecoverClassified_success_all_of_candidates
    (P : ZPoly → Prop)
    (hall :
      ∀ {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
        {candidates : Array ZPoly},
        bhksIndicatorCandidates? f d indicators = some candidates →
          ∀ factor ∈ candidates.toList, P factor)
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (hrecover : bhksRecoverClassified f d = .success candidates) :
    ∀ factor ∈ candidates.toList, P factor := by
  rw [bhksRecoverClassified] at hrecover
  by_cases hrows : 1 ≤ (bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount +
      (bhksLatticeBasis f d.p d.k d.liftedFactors).coeffWidth
  · rw [dif_pos hrows] at hrecover
    let projected :=
      bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows
    let indicators := bhksEquivalenceClassIndicators projected
    by_cases hdeg : bhksDegenerateIndicatorPartition projected indicators = true
    · simp [projected, indicators, hdeg] at hrecover
    · simp only [projected, indicators, hdeg, Bool.false_eq_true, if_false] at hrecover
      cases hcand : bhksIndicatorCandidates? f d indicators with
      | none => simp [projected, indicators, hcand] at hrecover
      | some cands =>
          simp only [projected, indicators, hcand] at hrecover
          by_cases hprod : Array.polyProduct cands == f
          · simp only [hprod, if_true] at hrecover
            cases hrecover
            exact hall hcand
          · simp [hprod] at hrecover
  · rw [dif_neg hrows] at hrecover
    simp at hrecover

private theorem bhksRecoverClassified_success_normalizeFactorSign
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (h : bhksRecoverClassified f d = .success candidates) :
    ∀ factor ∈ candidates.toList, normalizeFactorSign factor = factor :=
  bhksRecoverClassified_success_all_of_candidates
    (fun factor => normalizeFactorSign factor = factor)
    (fun hcand => bhksIndicatorCandidates?_normalizeFactorSign hcand) h

private theorem bhksRecoverClassified_success_shouldRecord
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (h : bhksRecoverClassified f d = .success candidates) :
    ∀ factor ∈ candidates.toList, shouldRecordPolynomialFactor factor = true :=
  bhksRecoverClassified_success_all_of_candidates
    (fun factor => shouldRecordPolynomialFactor factor = true)
    (fun hcand => bhksIndicatorCandidates?_shouldRecord hcand) h

/-- A successful BHKS recovery emits only candidates that divide `f`,
since each candidate has passed the executable exact-division check
inside `bhksIndicatorCandidate?`.  The dependence of the conclusion on
`f` prevents a one-liner via `bhksRecoverClassified_success_all_of_candidates`,
so we unfold `bhksRecoverClassified` directly. -/
private theorem bhksRecoverClassified_success_dvd
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (hrecover : bhksRecoverClassified f d = .success candidates) :
    ∀ factor ∈ candidates.toList, factor ∣ f := by
  rw [bhksRecoverClassified] at hrecover
  by_cases hrows : 1 ≤ (bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount +
      (bhksLatticeBasis f d.p d.k d.liftedFactors).coeffWidth
  · rw [dif_pos hrows] at hrecover
    let projected :=
      bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows
    let indicators := bhksEquivalenceClassIndicators projected
    by_cases hdeg : bhksDegenerateIndicatorPartition projected indicators = true
    · simp [projected, indicators, hdeg] at hrecover
    · simp only [projected, indicators, hdeg, Bool.false_eq_true, if_false] at hrecover
      cases hcand : bhksIndicatorCandidates? f d indicators with
      | none => simp [projected, indicators, hcand] at hrecover
      | some cands =>
          simp only [projected, indicators, hcand] at hrecover
          by_cases hprod : Array.polyProduct cands == f
          · simp only [hprod, if_true] at hrecover
            cases hrecover
            exact bhksIndicatorCandidates?_dvd hcand
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
theorem factorFastCoreWithBound_product
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

private theorem factorFastCoreWithBound_some_all_of_recovery
    (P : ZPoly → Prop)
    (hrecover :
      ∀ {core : ZPoly} {d : LiftData} {candidates : Array ZPoly},
        bhksRecoverClassified core d = .success candidates →
          ∀ factor ∈ candidates.toList, P factor)
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) :
    ∀ k fuel coreFactors,
      factorFastCoreWithBound core B primeData k fuel = some coreFactors →
        ∀ factor ∈ coreFactors.toList, P factor := by
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
          exact hrecover hclass
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

private theorem factorFastCoreWithBound_some_normalizeFactorSign
    {core : ZPoly} {B : Nat} {primeData : PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array ZPoly}
    (h : factorFastCoreWithBound core B primeData k fuel = some coreFactors) :
    ∀ factor ∈ coreFactors.toList, normalizeFactorSign factor = factor :=
  factorFastCoreWithBound_some_all_of_recovery
    (fun factor => normalizeFactorSign factor = factor)
    (fun hrecover => bhksRecoverClassified_success_normalizeFactorSign hrecover)
    core B primeData k fuel coreFactors h

theorem factorFastCoreWithBound_some_shouldRecord
    {core : ZPoly} {B : Nat} {primeData : PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array ZPoly}
    (h : factorFastCoreWithBound core B primeData k fuel = some coreFactors) :
    ∀ factor ∈ coreFactors.toList, shouldRecordPolynomialFactor factor = true :=
  factorFastCoreWithBound_some_all_of_recovery
    (fun factor => shouldRecordPolynomialFactor factor = true)
    (fun hrecover => bhksRecoverClassified_success_shouldRecord hrecover)
    core B primeData k fuel coreFactors h

/-- Every factor emitted by the BHKS fast-recombination loop divides the
input core. The success branch is the only branch that exits with
`some coreFactors`, and `bhksRecoverClassified_success_dvd` certifies
divisibility for each candidate at that exit. -/
theorem factorFastCoreWithBound_some_dvd
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) :
    ∀ k fuel coreFactors,
      factorFastCoreWithBound core B primeData k fuel = some coreFactors →
        ∀ factor ∈ coreFactors.toList, factor ∣ core := by
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
          exact bhksRecoverClassified_success_dvd hclass
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
multiplying to `core`) or the result of a successful
`scaledRecombinationSearchMod` call (`recombineScaledExhaustive_product`). -/
theorem exhaustiveCoreFactorsWithBound_product
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) :
    Array.polyProduct (exhaustiveCoreFactorsWithBound core B primeData) = core := by
  rw [exhaustiveCoreFactorsWithBound]
  by_cases hB : B = 0
  · simp [hB, Array.polyProduct]
  · simp only [hB, if_false]
    by_cases hempty :
        (recombineScaledExhaustive (DensePoly.leadingCoeff core) core
            (ZPoly.toMonicLiftData core B primeData)).isEmpty
    · simp [hempty, Array.polyProduct]
    · simp only [hempty]
      cases hsearch : scaledRecombinationSearchMod (DensePoly.leadingCoeff core) core
          (liftModulus
            (ZPoly.toMonicLiftData core B primeData))
          (ZPoly.toMonicLiftData core B primeData).liftedFactors.toList with
      | none =>
          have hnil :
              recombineScaledExhaustive (DensePoly.leadingCoeff core) core
                (ZPoly.toMonicLiftData core B primeData) = #[] := by
            rw [recombineScaledExhaustive]
            simp [hsearch]
          rw [hnil] at hempty
          simp at hempty
      | some xs =>
          exact recombineScaledExhaustive_product (DensePoly.leadingCoeff core) core
            (ZPoly.toMonicLiftData core B primeData)
            xs hsearch

/-- The leading coefficient of an `Array.polyProduct` over a list of polynomials
with strictly positive leading coefficients is strictly positive. Chains
`ZPoly.leadingCoeff_mul_pos_of_pos` through the foldl unfold given by
`ZPoly.polyProduct_cons_toArray`. -/
private theorem leadingCoeff_polyProduct_toArray_pos :
    ∀ (factors : List ZPoly),
      (∀ q ∈ factors, 0 < DensePoly.leadingCoeff q) →
      0 < DensePoly.leadingCoeff (Array.polyProduct factors.toArray) := by
  intro factors
  induction factors with
  | nil =>
      intro _
      change 0 < DensePoly.leadingCoeff (Array.polyProduct (#[] : Array ZPoly))
      change 0 < DensePoly.leadingCoeff (1 : ZPoly)
      decide
  | cons head rest ih =>
      intro hpos
      have hhead_pos : 0 < DensePoly.leadingCoeff head := hpos head List.mem_cons_self
      have hrest_pos : ∀ q ∈ rest, 0 < DensePoly.leadingCoeff q :=
        fun q hq => hpos q (List.mem_cons_of_mem _ hq)
      rw [ZPoly.polyProduct_cons_toArray]
      exact ZPoly.leadingCoeff_mul_pos_of_pos head _ hhead_pos (ih hrest_pos)

/-- If the executable `Array.polyProduct` of a list of polynomials is monic and
every entry has positive leading coefficient, then every entry is monic.

The product of positive integer leading coefficients equals the monic product's
leading coefficient `1`; since each factor is a positive integer, each must
itself be `1`. Used by the exhaustive-arm reassembly discharger to recover
monicness of emitted core factors from monicness of the squarefree core. -/
private theorem polyProduct_toArray_monic_factors_monic_of_pos_lc :
    ∀ (factors : List ZPoly),
      DensePoly.Monic (Array.polyProduct factors.toArray) →
      (∀ q ∈ factors, 0 < DensePoly.leadingCoeff q) →
      ∀ q ∈ factors, DensePoly.Monic q := by
  intro factors
  induction factors with
  | nil =>
      intro _ _ q hq
      cases hq
  | cons head rest ih =>
      intro hmonic hpos q hq
      have hhead_pos : 0 < DensePoly.leadingCoeff head := hpos head List.mem_cons_self
      have hrest_pos : ∀ q' ∈ rest, 0 < DensePoly.leadingCoeff q' :=
        fun q' hq' => hpos q' (List.mem_cons_of_mem _ hq')
      have hhead_ne : head ≠ 0 := by
        intro h0
        rw [h0] at hhead_pos
        change (0 : Int) < DensePoly.leadingCoeff (0 : ZPoly) at hhead_pos
        have hzero : DensePoly.leadingCoeff (0 : ZPoly) = 0 := by decide
        rw [hzero] at hhead_pos
        exact absurd hhead_pos (by decide)
      have hrest_lc_pos : 0 < DensePoly.leadingCoeff (Array.polyProduct rest.toArray) :=
        leadingCoeff_polyProduct_toArray_pos rest hrest_pos
      have hrest_prod_ne : Array.polyProduct rest.toArray ≠ 0 := by
        intro h0
        rw [h0] at hrest_lc_pos
        change (0 : Int) < DensePoly.leadingCoeff (0 : ZPoly) at hrest_lc_pos
        have hzero : DensePoly.leadingCoeff (0 : ZPoly) = 0 := by decide
        rw [hzero] at hrest_lc_pos
        exact absurd hrest_lc_pos (by decide)
      have hprod_eq :
          Array.polyProduct (head :: rest).toArray =
            head * Array.polyProduct rest.toArray :=
        ZPoly.polyProduct_cons_toArray head rest
      have hlc_mul :
          DensePoly.leadingCoeff (head * Array.polyProduct rest.toArray) =
            DensePoly.leadingCoeff head *
              DensePoly.leadingCoeff (Array.polyProduct rest.toArray) :=
        ZPoly.leadingCoeff_mul_of_nonzero head _ hhead_ne hrest_prod_ne
      have hmonic_unfold :
          DensePoly.leadingCoeff (Array.polyProduct (head :: rest).toArray) = 1 :=
        hmonic
      have hone :
          DensePoly.leadingCoeff head *
              DensePoly.leadingCoeff (Array.polyProduct rest.toArray) = 1 := by
        rw [← hlc_mul, ← hprod_eq]
        exact hmonic_unfold
      have ha : 1 ≤ DensePoly.leadingCoeff head := hhead_pos
      have hb : 1 ≤ DensePoly.leadingCoeff (Array.polyProduct rest.toArray) :=
        hrest_lc_pos
      -- From `a * b = 1` with `a ≥ 1`, `b ≥ 1`: `a * 1 ≤ a * b = 1`, so `a ≤ 1`.
      -- Combined with `a ≥ 1`, `a = 1`.
      have hhead_eq : DensePoly.leadingCoeff head = 1 := by
        have hupper :
            DensePoly.leadingCoeff head * 1 ≤
              DensePoly.leadingCoeff head *
                DensePoly.leadingCoeff (Array.polyProduct rest.toArray) :=
          Int.mul_le_mul (Int.le_refl _) hb (by decide : (0 : Int) ≤ 1)
            (by omega : (0 : Int) ≤ DensePoly.leadingCoeff head)
        rw [Int.mul_one, hone] at hupper
        omega
      have hrest_eq :
          DensePoly.leadingCoeff (Array.polyProduct rest.toArray) = 1 := by
        have hone' := hone
        rw [hhead_eq, Int.one_mul] at hone'
        exact hone'
      have hrest_monic : DensePoly.Monic (Array.polyProduct rest.toArray) := hrest_eq
      have hhead_monic : DensePoly.Monic head := hhead_eq
      rw [List.mem_cons] at hq
      rcases hq with hh | hr
      · rw [hh]; exact hhead_monic
      · exact ih hrest_monic hrest_pos q hr

/-- Every emitted factor of the exhaustive recombination wrapper is monic when
the input core is monic with positive degree. The product chain
(`exhaustiveCoreFactorsWithBound_product` together with the executable
sign-normalisation and `shouldRecord` invariants
`exhaustiveCoreFactorsWithBound_normalizeFactorSign` /
`exhaustiveCoreFactorsWithBound_shouldRecord`) forces each emitted factor's
leading coefficient to be a positive integer dividing `1`, hence itself `1`. -/
theorem exhaustiveCoreFactorsWithBound_monic
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    (hcore_monic : DensePoly.Monic core)
    (hcore_record : shouldRecordPolynomialFactor core = true) :
    ∀ factor ∈ (exhaustiveCoreFactorsWithBound core B primeData).toList,
      DensePoly.Monic factor := by
  have hcore_norm : normalizeFactorSign core = core :=
    normalizeFactorSign_eq_self_of_leadingCoeff_nonneg core
      (by rw [show DensePoly.leadingCoeff core = 1 from hcore_monic]; decide)
  have hprod :
      Array.polyProduct (exhaustiveCoreFactorsWithBound core B primeData) = core :=
    exhaustiveCoreFactorsWithBound_product core B primeData
  have hprod_monic :
      DensePoly.Monic (Array.polyProduct
        (exhaustiveCoreFactorsWithBound core B primeData)) := by
    rw [hprod]; exact hcore_monic
  -- Transport to the list-level helper.
  have hprod_monic' :
      DensePoly.Monic (Array.polyProduct
        (exhaustiveCoreFactorsWithBound core B primeData).toList.toArray) := by
    rw [Array.toArray_toList]; exact hprod_monic
  have hemit_norm :=
    exhaustiveCoreFactorsWithBound_normalizeFactorSign core B primeData hcore_norm
  have hemit_record :=
    exhaustiveCoreFactorsWithBound_shouldRecord core B primeData hcore_record
  have hpos :
      ∀ q ∈ (exhaustiveCoreFactorsWithBound core B primeData).toList,
        0 < DensePoly.leadingCoeff q := by
    intro q hq
    have hq_norm : normalizeFactorSign q = q := hemit_norm q hq
    have hq_record : shouldRecordPolynomialFactor q = true := hemit_record q hq
    have hq_ne : q ≠ 0 := by
      unfold shouldRecordPolynomialFactor at hq_record
      simp at hq_record
      exact hq_record.1.1
    have hq_lc_nonneg : 0 ≤ DensePoly.leadingCoeff q := by
      rw [← hq_norm]
      exact normalizeFactorSign_leadingCoeff_nonneg q
    have hq_lc_ne : DensePoly.leadingCoeff q ≠ 0 :=
      ZPoly.leadingCoeff_ne_zero_of_ne_zero q hq_ne
    omega
  exact polyProduct_toArray_monic_factors_monic_of_pos_lc
    (exhaustiveCoreFactorsWithBound core B primeData).toList hprod_monic' hpos

/-- Every emitted factor of the exhaustive recombination wrapper has positive
`degree?` when the input core is monic and `shouldRecord = true`. A monic
polynomial of `degree? = 0` is the constant `1`, which is excluded by
`shouldRecord`, so every emitted factor has positive degree. -/
theorem exhaustiveCoreFactorsWithBound_degree_pos
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    (hcore_monic : DensePoly.Monic core)
    (hcore_record : shouldRecordPolynomialFactor core = true) :
    ∀ factor ∈ (exhaustiveCoreFactorsWithBound core B primeData).toList,
      0 < factor.degree?.getD 0 := by
  intro q hq
  have hq_monic : DensePoly.Monic q :=
    exhaustiveCoreFactorsWithBound_monic core B primeData hcore_monic hcore_record q hq
  have hemit_record :=
    exhaustiveCoreFactorsWithBound_shouldRecord core B primeData hcore_record
  have hq_record : shouldRecordPolynomialFactor q = true := hemit_record q hq
  -- shouldRecord excludes `q = 1`. A monic `q` with `degree? = 0` is `1`.
  rcases Nat.eq_zero_or_pos (q.degree?.getD 0) with hdeg_eq | hpos
  case inr => exact hpos
  case inl =>
    exfalso
    have hq_ne : q ≠ 0 := by
      intro h0
      have hlc1 : DensePoly.leadingCoeff q = 1 := hq_monic
      rw [h0] at hlc1
      have hlc0 : DensePoly.leadingCoeff (0 : ZPoly) = 0 := by decide
      omega
    have hq_size_pos : 0 < q.size := ZPoly.size_pos_of_ne_zero q hq_ne
    have hdeg_unfold : q.degree?.getD 0 =
        (if q.size = 0 then 0 else q.size - 1) := by
      unfold DensePoly.degree?
      by_cases h : q.size = 0 <;> simp [h]
    rw [hdeg_unfold] at hdeg_eq
    have hsize_eq : q.size = 1 := by
      by_cases h : q.size = 0
      · omega
      · split at hdeg_eq <;> omega
    have hq_eq_C : q = DensePoly.C (q.coeff 0) := ZPoly.eq_C_of_size_eq_one q hsize_eq
    have hq_lc : DensePoly.leadingCoeff q = q.coeff 0 := by
      rw [DensePoly.leadingCoeff_eq_coeff_last q hq_size_pos]
      congr 1; omega
    have hq_lc1 : DensePoly.leadingCoeff q = 1 := hq_monic
    have hq_coeff0 : q.coeff 0 = 1 := by rw [← hq_lc]; exact hq_lc1
    have hq_one : q = 1 := by
      rw [hq_eq_C, hq_coeff0]
      rfl
    unfold shouldRecordPolynomialFactor at hq_record
    simp [hq_one] at hq_record

/-- Weakened-conclusion sibling of `exhaustiveCoreFactorsWithBound_degree_pos`:
every emitted factor of the exhaustive recombination wrapper has positive
`degree?` when the input core is primitive with positive leading coefficient
and `shouldRecord = true`. A size-`1` emitted factor combines
`Primitive q` (forcing `|q.coeff 0| = 1`) with `normalizeFactorSign q = q`
(forcing `q.coeff 0 ≥ 0`) to conclude `q = 1`, which is excluded by
`shouldRecord`. -/
theorem exhaustiveCoreFactorsWithBound_degree_pos_of_primitive_pos_lc_core
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    (hcore_primitive : ZPoly.Primitive core)
    (hcore_lc_pos : 0 < DensePoly.leadingCoeff core)
    (hcore_record : shouldRecordPolynomialFactor core = true) :
    ∀ factor ∈ (exhaustiveCoreFactorsWithBound core B primeData).toList,
      0 < factor.degree?.getD 0 := by
  intro q hq
  have hcore_norm : normalizeFactorSign core = core :=
    normalizeFactorSign_eq_self_of_leadingCoeff_nonneg core (by omega)
  have hemit_norm :=
    exhaustiveCoreFactorsWithBound_normalizeFactorSign core B primeData hcore_norm
  have hemit_record :=
    exhaustiveCoreFactorsWithBound_shouldRecord core B primeData hcore_record
  have hemit_primitive :=
    exhaustiveCoreFactorsWithBound_primitive core B primeData hcore_primitive
  have hq_norm : normalizeFactorSign q = q := hemit_norm q hq
  have hq_record : shouldRecordPolynomialFactor q = true := hemit_record q hq
  have hq_primitive : ZPoly.Primitive q := hemit_primitive q hq
  rcases Nat.eq_zero_or_pos (q.degree?.getD 0) with hdeg_eq | hpos
  case inr => exact hpos
  case inl =>
    exfalso
    have hq_ne : q ≠ 0 := by
      unfold shouldRecordPolynomialFactor at hq_record
      simp at hq_record
      exact hq_record.1.1
    have hq_size_pos : 0 < q.size := ZPoly.size_pos_of_ne_zero q hq_ne
    have hdeg_unfold : q.degree?.getD 0 =
        (if q.size = 0 then 0 else q.size - 1) := by
      unfold DensePoly.degree?
      by_cases h : q.size = 0 <;> simp [h]
    rw [hdeg_unfold] at hdeg_eq
    have hsize_eq : q.size = 1 := by
      by_cases h : q.size = 0
      · omega
      · split at hdeg_eq <;> omega
    have hq_eq_C : q = DensePoly.C (q.coeff 0) := ZPoly.eq_C_of_size_eq_one q hsize_eq
    have hq_lc : DensePoly.leadingCoeff q = q.coeff 0 := by
      rw [DensePoly.leadingCoeff_eq_coeff_last q hq_size_pos]
      congr 1; omega
    have hq_lc_nonneg : 0 ≤ DensePoly.leadingCoeff q := by
      rw [← hq_norm]
      exact normalizeFactorSign_leadingCoeff_nonneg q
    have hq_coeff0_nonneg : 0 ≤ q.coeff 0 := by rw [← hq_lc]; exact hq_lc_nonneg
    -- Primitive q + q = C (q.coeff 0) ⇒ |q.coeff 0| = 1, then ≥ 0 ⇒ = 1.
    have hcontent_q_eq : ZPoly.content q = Int.ofNat (q.coeff 0).natAbs :=
      (congrArg DensePoly.content hq_eq_C).trans (DensePoly.content_C (q.coeff 0))
    have hcontent_q_one : ZPoly.content q = 1 := hq_primitive
    have habs1 : (q.coeff 0).natAbs = 1 := by
      have hcast : (((q.coeff 0).natAbs : Int)) = (1 : Int) := by
        rw [← Int.ofNat_eq_natCast, ← hcontent_q_eq]; exact hcontent_q_one
      exact_mod_cast hcast
    have hq_coeff0_eq : q.coeff 0 = 1 := by
      rcases Int.natAbs_eq (q.coeff 0) with h | h
      · rw [h, habs1]; rfl
      · rw [h, habs1] at hq_coeff0_nonneg
        omega
    have hq_one : q = 1 := by
      rw [hq_eq_C, hq_coeff0_eq]
      rfl
    unfold shouldRecordPolynomialFactor at hq_record
    simp [hq_one] at hq_record

private theorem polyProduct_push (factors : Array ZPoly) (factor : ZPoly) :
    Array.polyProduct (factors.push factor) =
      Array.polyProduct factors * factor := by
  cases factors with
  | mk xs =>
      induction xs generalizing factor with
      | nil =>
          simp [Array.polyProduct, ZPoly.one_mul_zpoly]
      | cons x xs ih =>
          simp [Array.polyProduct, List.foldl_cons] at ih ⊢

private theorem splitIntegerRootFactorsAux_product
    (target : ZPoly) (roots : List Int) (fuel : Nat) :
    ∀ factors residual,
      splitIntegerRootFactorsAux target roots fuel = (factors, residual) →
        residual * Array.polyProduct factors = target := by
  induction fuel generalizing target roots with
  | zero =>
      intro factors residual hsplit
      rw [splitIntegerRootFactorsAux] at hsplit
      injection hsplit with hfactors hresidual
      subst factors
      subst residual
      exact DensePoly.mul_one_right_poly (S := Int) target
  | succ fuel ih =>
      intro factors residual hsplit
      cases roots with
      | nil =>
          rw [splitIntegerRootFactorsAux] at hsplit
          injection hsplit with hfactors hresidual
          subst factors
          subst residual
          exact DensePoly.mul_one_right_poly (S := Int) target
      | cons root roots =>
          unfold splitIntegerRootFactorsAux at hsplit
          cases hquot : exactQuotient? target (linearFactorForRoot root) with
          | none =>
              simp [hquot] at hsplit
              exact ih target roots factors residual hsplit
          | some quotient =>
              simp [hquot] at hsplit
              cases hrest : splitIntegerRootFactorsAux quotient roots fuel with
              | mk restFactors restResidual =>
                  simp [hrest] at hsplit
                  rcases hsplit with ⟨hfactors, hresidual⟩
                  subst factors
                  subst residual
                  have hrec :
                      restResidual * Array.polyProduct restFactors = quotient :=
                    ih quotient roots restFactors restResidual hrest
                  have hquot_prod :
                      quotient * linearFactorForRoot root = target :=
                    exactQuotient?_product hquot
                  calc
                    restResidual *
                        Array.polyProduct (#[linearFactorForRoot root] ++ restFactors) =
                        restResidual *
                          (linearFactorForRoot root * Array.polyProduct restFactors) := by
                          rw [ZPoly.polyProduct_append, ZPoly.polyProduct_singleton]
                    _ = restResidual *
                          (Array.polyProduct restFactors * linearFactorForRoot root) := by
                          rw [DensePoly.mul_comm_poly (S := Int)
                            (linearFactorForRoot root) (Array.polyProduct restFactors)]
                    _ = (restResidual * Array.polyProduct restFactors) *
                          linearFactorForRoot root := by
                          rw [DensePoly.mul_assoc_poly (S := Int)]
                    _ = quotient * linearFactorForRoot root := by
                          rw [hrec]
                    _ = target := hquot_prod

private theorem splitIntegerRootFactorsAux_normalizeFactorSign
    (target : ZPoly) (roots : List Int) (fuel : Nat) :
    ∀ factors residual,
      splitIntegerRootFactorsAux target roots fuel = (factors, residual) →
        ∀ factor ∈ factors.toList, normalizeFactorSign factor = factor := by
  induction fuel generalizing target roots with
  | zero =>
      intro factors residual hsplit factor hmem
      rw [splitIntegerRootFactorsAux] at hsplit
      injection hsplit with hfactors hresidual
      subst factors
      simp at hmem
  | succ fuel ih =>
      intro factors residual hsplit factor hmem
      cases roots with
      | nil =>
          rw [splitIntegerRootFactorsAux] at hsplit
          injection hsplit with hfactors hresidual
          subst factors
          simp at hmem
      | cons root roots =>
          unfold splitIntegerRootFactorsAux at hsplit
          cases hquot : exactQuotient? target (linearFactorForRoot root) with
          | none =>
              simp [hquot] at hsplit
              exact ih target roots factors residual hsplit factor hmem
          | some quotient =>
              simp [hquot] at hsplit
              cases hrest : splitIntegerRootFactorsAux quotient roots fuel with
              | mk restFactors restResidual =>
                  simp [hrest] at hsplit
                  rcases hsplit with ⟨hfactors, hresidual⟩
                  subst factors
                  subst residual
                  rw [Array.toList_append] at hmem
                  simp at hmem
                  cases hmem with
                  | inl hroot =>
                      rw [hroot]
                      exact normalizeFactorSign_linearFactorForRoot root
                  | inr hrest_mem =>
                      exact ih quotient roots restFactors restResidual hrest factor (by
                        simpa using hrest_mem)

private theorem splitIntegerRootFactorsAux_shouldRecord
    (target : ZPoly) (roots : List Int) (fuel : Nat) :
    ∀ factors residual,
      splitIntegerRootFactorsAux target roots fuel = (factors, residual) →
        ∀ factor ∈ factors.toList, shouldRecordPolynomialFactor factor = true := by
  induction fuel generalizing target roots with
  | zero =>
      intro factors residual hsplit factor hmem
      rw [splitIntegerRootFactorsAux] at hsplit
      injection hsplit with hfactors hresidual
      subst factors
      simp at hmem
  | succ fuel ih =>
      intro factors residual hsplit factor hmem
      cases roots with
      | nil =>
          rw [splitIntegerRootFactorsAux] at hsplit
          injection hsplit with hfactors hresidual
          subst factors
          simp at hmem
      | cons root roots =>
          unfold splitIntegerRootFactorsAux at hsplit
          cases hquot : exactQuotient? target (linearFactorForRoot root) with
          | none =>
              simp [hquot] at hsplit
              exact ih target roots factors residual hsplit factor hmem
          | some quotient =>
              simp [hquot] at hsplit
              cases hrest : splitIntegerRootFactorsAux quotient roots fuel with
              | mk restFactors restResidual =>
                  simp [hrest] at hsplit
                  rcases hsplit with ⟨hfactors, hresidual⟩
                  subst factors
                  subst residual
                  rw [Array.toList_append] at hmem
                  simp at hmem
                  cases hmem with
                  | inl hroot =>
                      rw [hroot]
                      exact shouldRecordPolynomialFactor_linearFactorForRoot root
                  | inr hrest_mem =>
                      exact ih quotient roots restFactors restResidual hrest factor (by
                        simpa using hrest_mem)

private theorem splitIntegerRootFactorsAux_irreducible
    (target : ZPoly) (roots : List Int) (fuel : Nat) :
    ∀ factors residual,
      splitIntegerRootFactorsAux target roots fuel = (factors, residual) →
        ∀ factor ∈ factors.toList, ZPoly.Irreducible factor := by
  induction fuel generalizing target roots with
  | zero =>
      intro factors residual hsplit factor hmem
      rw [splitIntegerRootFactorsAux] at hsplit
      injection hsplit with hfactors hresidual
      subst factors
      simp at hmem
  | succ fuel ih =>
      intro factors residual hsplit factor hmem
      cases roots with
      | nil =>
          rw [splitIntegerRootFactorsAux] at hsplit
          injection hsplit with hfactors hresidual
          subst factors
          simp at hmem
      | cons root roots =>
          unfold splitIntegerRootFactorsAux at hsplit
          cases hquot : exactQuotient? target (linearFactorForRoot root) with
          | none =>
              simp [hquot] at hsplit
              exact ih target roots factors residual hsplit factor hmem
          | some quotient =>
              simp [hquot] at hsplit
              cases hrest : splitIntegerRootFactorsAux quotient roots fuel with
              | mk restFactors restResidual =>
                  simp [hrest] at hsplit
                  rcases hsplit with ⟨hfactors, hresidual⟩
                  subst factors
                  subst residual
                  rw [Array.toList_append] at hmem
                  simp at hmem
                  cases hmem with
                  | inl hroot =>
                      rw [hroot]
                      exact irreducible_linearFactorForRoot root
                  | inr hrest_mem =>
                      exact ih quotient roots restFactors restResidual hrest factor (by
                        simpa using hrest_mem)

/-- Factors emitted by the integer-root splitter are monic linear root factors,
and hence irreducible. This is the theorem-level wrapper used by the
quadratic-root branch before any optional residual factor is appended. -/
theorem splitIntegerRootFactorsAux_factor_irreducible
    {target : ZPoly} {roots : List Int} {fuel : Nat}
    {factors : Array ZPoly} {residual factor : ZPoly}
    (hsplit : splitIntegerRootFactorsAux target roots fuel = (factors, residual))
    (hmem : factor ∈ factors.toList) :
    ZPoly.Irreducible factor :=
  splitIntegerRootFactorsAux_irreducible target roots fuel factors residual
    hsplit factor hmem

private theorem splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos
    (target : ZPoly) (roots : List Int) (fuel : Nat) :
    ∀ factors residual,
      splitIntegerRootFactorsAux target roots fuel = (factors, residual) →
        0 < DensePoly.leadingCoeff (Array.polyProduct factors) := by
  induction fuel generalizing target roots with
  | zero =>
      intro factors residual hsplit
      rw [splitIntegerRootFactorsAux] at hsplit
      injection hsplit with hfactors hresidual
      subst factors
      change 0 < DensePoly.leadingCoeff (DensePoly.C (1 : Int))
      simp [DensePoly.leadingCoeff, DensePoly.coeffs_C_of_ne_zero
        (by decide : (1 : Int) ≠ 0)]
  | succ fuel ih =>
      intro factors residual hsplit
      cases roots with
      | nil =>
          rw [splitIntegerRootFactorsAux] at hsplit
          injection hsplit with hfactors hresidual
          subst factors
          change 0 < DensePoly.leadingCoeff (DensePoly.C (1 : Int))
          simp [DensePoly.leadingCoeff, DensePoly.coeffs_C_of_ne_zero
            (by decide : (1 : Int) ≠ 0)]
      | cons root roots =>
          unfold splitIntegerRootFactorsAux at hsplit
          cases hquot : exactQuotient? target (linearFactorForRoot root) with
          | none =>
              simp [hquot] at hsplit
              exact ih target roots factors residual hsplit
          | some quotient =>
              simp [hquot] at hsplit
              cases hrest : splitIntegerRootFactorsAux quotient roots fuel with
              | mk restFactors restResidual =>
                  simp [hrest] at hsplit
                  rcases hsplit with ⟨hfactors, hresidual⟩
                  subst factors
                  subst residual
                  rw [ZPoly.polyProduct_append, ZPoly.polyProduct_singleton]
                  apply ZPoly.leadingCoeff_mul_pos_of_pos
                  · rw [leadingCoeff_linearFactorForRoot]
                    omega
                  · exact ih quotient roots restFactors restResidual hrest

/-- The factors emitted by `splitIntegerRootFactorsAux` are exactly the
images of some sublist of the input `roots` list under `linearFactorForRoot`.
Sibling of `splitIntegerRootFactorsAux_product` / `_irreducible` / etc.
Consumed by the #4785 pairwise non-association proof to read off the
distinct-roots invariant via `List.Sublist`-then-`Nodup` transfer. -/
private theorem splitIntegerRootFactorsAux_factors_distinct_roots
    (target : ZPoly) (roots : List Int) (fuel : Nat) :
    ∀ factors residual,
      splitIntegerRootFactorsAux target roots fuel = (factors, residual) →
        ∃ rs : List Int, rs.Sublist roots ∧
          factors.toList = rs.map linearFactorForRoot := by
  induction fuel generalizing target roots with
  | zero =>
      intro factors residual hsplit
      rw [splitIntegerRootFactorsAux] at hsplit
      injection hsplit with hfactors hresidual
      subst factors
      refine ⟨[], ?_, ?_⟩
      · exact List.nil_sublist roots
      · simp
  | succ fuel ih =>
      intro factors residual hsplit
      cases roots with
      | nil =>
          rw [splitIntegerRootFactorsAux] at hsplit
          injection hsplit with hfactors hresidual
          subst factors
          refine ⟨[], ?_, ?_⟩
          · exact List.nil_sublist _
          · simp
      | cons root roots =>
          unfold splitIntegerRootFactorsAux at hsplit
          cases hquot : exactQuotient? target (linearFactorForRoot root) with
          | none =>
              simp [hquot] at hsplit
              rcases ih target roots factors residual hsplit with
                ⟨rs, hsub, hshape⟩
              exact ⟨rs, hsub.cons root, hshape⟩
          | some quotient =>
              simp [hquot] at hsplit
              cases hrest : splitIntegerRootFactorsAux quotient roots fuel with
              | mk restFactors restResidual =>
                  simp [hrest] at hsplit
                  rcases hsplit with ⟨hfactors, hresidual⟩
                  subst factors
                  subst residual
                  rcases ih quotient roots restFactors restResidual hrest with
                    ⟨rs, hsub, hshape⟩
                  refine ⟨root :: rs, ?_, ?_⟩
                  · exact hsub.cons_cons root
                  · rw [Array.toList_append]
                    simp [hshape]

/-- Public wrapper of the splitter distinct-roots invariant: factors emitted
by `splitIntegerRootFactorsAux` are `linearFactorForRoot rᵢ` for some sublist
`rs` of the input `roots`. Composed with `roots.Nodup` (e.g. via
`integerRootCandidates_nodup`) to read off pairwise distinctness of the
factor roots, used by the #4785 linear-vs-linear pairwise non-association
case. -/
theorem splitIntegerRootFactorsAux_factors_form
    {target : ZPoly} {roots : List Int} {fuel : Nat}
    {factors : Array ZPoly} {residual : ZPoly}
    (hsplit : splitIntegerRootFactorsAux target roots fuel = (factors, residual)) :
    ∃ rs : List Int, rs.Sublist roots ∧
      factors.toList = rs.map linearFactorForRoot :=
  splitIntegerRootFactorsAux_factors_distinct_roots target roots fuel
    factors residual hsplit

/-- Each candidate emitted by `trialDivisionCandidatesOfDegree B d` has degree
exactly `d`, positive leading coefficient, and passes `shouldRecord`. -/
private theorem mem_trialDivisionCandidatesOfDegree {B d : Nat} {p : ZPoly}
    (hmem : p ∈ trialDivisionCandidatesOfDegree B d) :
    p.degree?.getD 0 = d ∧ 0 < DensePoly.leadingCoeff p ∧
      shouldRecordPolynomialFactor p = true := by
  unfold trialDivisionCandidatesOfDegree at hmem
  rcases List.mem_filterMap.mp hmem with ⟨coeffs, _hcoeffs, heq⟩
  by_cases hcheck :
      (DensePoly.ofCoeffs coeffs.toArray).degree?.getD 0 = d ∧
        0 < DensePoly.leadingCoeff (DensePoly.ofCoeffs coeffs.toArray) ∧
        shouldRecordPolynomialFactor (DensePoly.ofCoeffs coeffs.toArray) = true
  · rw [if_pos hcheck] at heq
    cases heq
    exact hcheck
  · rw [if_neg hcheck] at heq
    contradiction

/-- Each candidate emitted by `trialDivisionCandidatesUpTo B maxDeg` has
positive degree, positive leading coefficient, and passes `shouldRecord`. -/
private theorem mem_trialDivisionCandidatesUpTo {B maxDeg : Nat} {p : ZPoly}
    (hmem : p ∈ trialDivisionCandidatesUpTo B maxDeg) :
    0 < p.degree?.getD 0 ∧ 0 < DensePoly.leadingCoeff p ∧
      shouldRecordPolynomialFactor p = true := by
  unfold trialDivisionCandidatesUpTo at hmem
  rcases List.mem_flatMap.mp hmem with ⟨d, _hd_range, hpd⟩
  obtain ⟨hdeg, hlc, hrec⟩ := mem_trialDivisionCandidatesOfDegree hpd
  refine ⟨?_, hlc, hrec⟩
  rw [hdeg]; omega

/-- The polyProduct invariant for the candidate-peel auxiliary: emitted
factors and final residual multiply back to the original target. -/
private theorem trialDivisionPeelAux_product
    (target : ZPoly) (candidates : List ZPoly) :
    ∀ factors residual,
      trialDivisionPeelAux target candidates = (factors, residual) →
        residual * Array.polyProduct factors = target := by
  induction candidates generalizing target with
  | nil =>
      intro factors residual hsplit
      simp [trialDivisionPeelAux] at hsplit
      rcases hsplit with ⟨rfl, rfl⟩
      exact DensePoly.mul_one_right_poly (S := Int) target
  | cons c cs ih =>
      intro factors residual hsplit
      unfold trialDivisionPeelAux at hsplit
      cases hquot : exactQuotient? target c with
      | none =>
          simp [hquot] at hsplit
          exact ih target factors residual hsplit
      | some q =>
          simp [hquot] at hsplit
          cases hrest : trialDivisionPeelAux q cs with
          | mk rfact rres =>
              simp [hrest] at hsplit
              rcases hsplit with ⟨hfactors, hresidual⟩
              subst factors
              subst residual
              have hih : rres * Array.polyProduct rfact = q :=
                ih q rfact rres hrest
              have hqcq : q * c = target := exactQuotient?_product hquot
              calc
                rres * Array.polyProduct (#[c] ++ rfact)
                    = rres * (c * Array.polyProduct rfact) := by
                      rw [ZPoly.polyProduct_append, ZPoly.polyProduct_singleton]
                _ = rres * (Array.polyProduct rfact * c) := by
                      rw [DensePoly.mul_comm_poly (S := Int) c
                        (Array.polyProduct rfact)]
                _ = (rres * Array.polyProduct rfact) * c := by
                      rw [DensePoly.mul_assoc_poly (S := Int)]
                _ = q * c := by rw [hih]
                _ = target := hqcq

/-- Each emitted factor of the candidate-peel auxiliary is a member of the
input candidate list. -/
private theorem trialDivisionPeelAux_factor_mem
    (target : ZPoly) (candidates : List ZPoly) :
    ∀ factors residual,
      trialDivisionPeelAux target candidates = (factors, residual) →
        ∀ factor ∈ factors.toList, factor ∈ candidates := by
  induction candidates generalizing target with
  | nil =>
      intro factors residual hsplit factor hmem
      simp [trialDivisionPeelAux] at hsplit
      rcases hsplit with ⟨rfl, rfl⟩
      simp at hmem
  | cons c cs ih =>
      intro factors residual hsplit factor hmem
      unfold trialDivisionPeelAux at hsplit
      cases hquot : exactQuotient? target c with
      | none =>
          simp [hquot] at hsplit
          exact List.mem_cons_of_mem c
            (ih target factors residual hsplit factor hmem)
      | some q =>
          simp [hquot] at hsplit
          cases hrest : trialDivisionPeelAux q cs with
          | mk rfact rres =>
              simp [hrest] at hsplit
              rcases hsplit with ⟨hfactors, hresidual⟩
              subst factors
              subst residual
              rw [Array.toList_append] at hmem
              simp at hmem
              cases hmem with
              | inl hself =>
                  rw [hself]
                  exact List.mem_cons_self
              | inr hrest_mem =>
                  exact List.mem_cons_of_mem c
                    (ih q rfact rres hrest factor (by simpa using hrest_mem))

/-- When the peel target has positive leading coefficient and every candidate
in the input list has positive leading coefficient, the residual emitted by
`trialDivisionPeelAux` retains a positive leading coefficient. -/
private theorem trialDivisionPeelAux_residual_leadingCoeff_pos
    (target : ZPoly) (candidates : List ZPoly)
    (htarget_pos : 0 < DensePoly.leadingCoeff target)
    (hcand_pos : ∀ c ∈ candidates, 0 < DensePoly.leadingCoeff c) :
    ∀ factors residual,
      trialDivisionPeelAux target candidates = (factors, residual) →
        0 < DensePoly.leadingCoeff residual := by
  induction candidates generalizing target with
  | nil =>
      intro factors residual hsplit
      simp [trialDivisionPeelAux] at hsplit
      rcases hsplit with ⟨rfl, rfl⟩
      exact htarget_pos
  | cons c cs ih =>
      intro factors residual hsplit
      have hc_pos : 0 < DensePoly.leadingCoeff c :=
        hcand_pos c List.mem_cons_self
      have hcs_pos : ∀ c' ∈ cs, 0 < DensePoly.leadingCoeff c' :=
        fun c' h => hcand_pos c' (List.mem_cons_of_mem c h)
      unfold trialDivisionPeelAux at hsplit
      cases hquot : exactQuotient? target c with
      | none =>
          simp [hquot] at hsplit
          exact ih target htarget_pos hcs_pos factors residual hsplit
      | some q =>
          simp [hquot] at hsplit
          cases hrest : trialDivisionPeelAux q cs with
          | mk rfact rres =>
              simp [hrest] at hsplit
              rcases hsplit with ⟨hfactors, hresidual⟩
              subst factors
              subst residual
              have hqcq : q * c = target := exactQuotient?_product hquot
              have htarget_ne : target ≠ 0 := by
                intro hz
                rw [hz] at htarget_pos
                change 0 < (0 : Int) at htarget_pos
                omega
              have hc_ne : c ≠ 0 := by
                intro hz
                rw [hz] at hc_pos
                change 0 < (0 : Int) at hc_pos
                omega
              have hq_ne : q ≠ 0 := by
                intro hz
                apply htarget_ne
                rw [← hqcq, hz]
                exact DensePoly.zero_mul _
              have hlc_mul :
                  DensePoly.leadingCoeff q * DensePoly.leadingCoeff c =
                    DensePoly.leadingCoeff target := by
                rw [← hqcq]
                exact (ZPoly.leadingCoeff_mul_of_nonzero q c hq_ne hc_ne).symm
              have hq_pos : 0 < DensePoly.leadingCoeff q := by
                rcases Int.lt_or_le 0 (DensePoly.leadingCoeff q) with hp | hle
                · exact hp
                · exfalso
                  have hc_nn : 0 ≤ DensePoly.leadingCoeff c :=
                    Int.le_of_lt hc_pos
                  have hna : 0 ≤ -DensePoly.leadingCoeff q := by omega
                  have hprod_neg_nn :
                      0 ≤ -DensePoly.leadingCoeff q *
                        DensePoly.leadingCoeff c :=
                    Int.mul_nonneg hna hc_nn
                  have hneg_eq :
                      -DensePoly.leadingCoeff q * DensePoly.leadingCoeff c =
                        -(DensePoly.leadingCoeff q * DensePoly.leadingCoeff c) :=
                    Int.neg_mul _ _
                  rw [hneg_eq, hlc_mul] at hprod_neg_nn
                  omega
              exact ih q hq_pos hcs_pos rfact rres hrest

/-- Each emitted factor of the candidate-peel auxiliary satisfies the
property `P` whenever every input candidate does. -/
private theorem trialDivisionPeelAux_factor_property
    {P : ZPoly → Prop} (target : ZPoly) (candidates : List ZPoly)
    (hcand : ∀ c ∈ candidates, P c) :
    ∀ factors residual,
      trialDivisionPeelAux target candidates = (factors, residual) →
        ∀ factor ∈ factors.toList, P factor := by
  intro factors residual hsplit factor hmem
  exact hcand factor
    (trialDivisionPeelAux_factor_mem target candidates factors residual hsplit
      factor hmem)

/-- PolyProduct identity for the standalone integer trial-division core. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_polyProduct
    (core : ZPoly) (B : Nat) :
    Array.polyProduct (exhaustiveIntegerTrialCoreFactorsWithBound core B) =
      core := by
  let split := splitIntegerRootFactorsAux core (integerRootCandidates core)
    (integerRootCandidates core).length
  let peel := trialDivisionPeelAux split.2
    (trialDivisionCandidatesUpTo B (split.2.degree?.getD 0 / 2))
  have hsplit_prod : split.2 * Array.polyProduct split.1 = core :=
    splitIntegerRootFactorsAux_product core (integerRootCandidates core)
      (integerRootCandidates core).length split.1 split.2 rfl
  have hpeel_prod : peel.2 * Array.polyProduct peel.1 = split.2 :=
    trialDivisionPeelAux_product split.2
      (trialDivisionCandidatesUpTo B (split.2.degree?.getD 0 / 2))
      peel.1 peel.2 rfl
  change Array.polyProduct
      (if peel.2 = 1 then split.1 ++ peel.1
        else (split.1 ++ peel.1).push peel.2) = core
  by_cases hres_one : peel.2 = 1
  · rw [if_pos hres_one]
    rw [hres_one, ZPoly.one_mul_zpoly] at hpeel_prod
    rw [ZPoly.polyProduct_append, hpeel_prod,
        DensePoly.mul_comm_poly (S := Int)]
    exact hsplit_prod
  · rw [if_neg hres_one]
    rw [polyProduct_push, ZPoly.polyProduct_append,
        DensePoly.mul_assoc_poly (S := Int),
        DensePoly.mul_comm_poly (S := Int) (Array.polyProduct peel.1) peel.2,
        hpeel_prod, DensePoly.mul_comm_poly (S := Int)]
    exact hsplit_prod

/-- Each factor emitted by the standalone integer trial-division core is
fixed by `normalizeFactorSign`, provided `core` has positive leading
coefficient. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_normalizeFactorSign
    (core : ZPoly) (B : Nat)
    (hcore_pos : 0 < DensePoly.leadingCoeff core) :
    ∀ factor ∈ (exhaustiveIntegerTrialCoreFactorsWithBound core B).toList,
      normalizeFactorSign factor = factor := by
  let split := splitIntegerRootFactorsAux core (integerRootCandidates core)
    (integerRootCandidates core).length
  let candidates :=
    trialDivisionCandidatesUpTo B (split.2.degree?.getD 0 / 2)
  let peel := trialDivisionPeelAux split.2 candidates
  have hsplit_norm :
      ∀ factor ∈ split.1.toList, normalizeFactorSign factor = factor :=
    splitIntegerRootFactorsAux_normalizeFactorSign core
      (integerRootCandidates core) (integerRootCandidates core).length
      split.1 split.2 rfl
  have hsplit_prod : split.2 * Array.polyProduct split.1 = core :=
    splitIntegerRootFactorsAux_product core (integerRootCandidates core)
      (integerRootCandidates core).length split.1 split.2 rfl
  have hsplit_lc_pos :
      0 < DensePoly.leadingCoeff (Array.polyProduct split.1) :=
    splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core
      (integerRootCandidates core) (integerRootCandidates core).length
      split.1 split.2 rfl
  have hcore_ne : core ≠ 0 := by
    intro hz
    rw [hz] at hcore_pos
    change 0 < (0 : Int) at hcore_pos
    omega
  have hsplit1_ne : Array.polyProduct split.1 ≠ 0 := by
    intro hz
    rw [hz] at hsplit_lc_pos
    change 0 < (0 : Int) at hsplit_lc_pos
    omega
  have hsplit2_ne : split.2 ≠ 0 := by
    intro hz
    apply hcore_ne
    rw [← hsplit_prod, hz]
    exact DensePoly.zero_mul _
  have hsplit2_pos : 0 < DensePoly.leadingCoeff split.2 := by
    have hlc :
        DensePoly.leadingCoeff core =
          DensePoly.leadingCoeff split.2 *
            DensePoly.leadingCoeff (Array.polyProduct split.1) := by
      rw [← hsplit_prod]
      exact ZPoly.leadingCoeff_mul_of_nonzero split.2
        (Array.polyProduct split.1) hsplit2_ne hsplit1_ne
    rcases Int.lt_or_le 0 (DensePoly.leadingCoeff split.2) with hp | hle
    · exact hp
    · exfalso
      have hnn : 0 ≤ DensePoly.leadingCoeff (Array.polyProduct split.1) :=
        Int.le_of_lt hsplit_lc_pos
      have hna : 0 ≤ -DensePoly.leadingCoeff split.2 := by omega
      have hprod_neg_nn :
          0 ≤ -DensePoly.leadingCoeff split.2 *
            DensePoly.leadingCoeff (Array.polyProduct split.1) :=
        Int.mul_nonneg hna hnn
      have hneg_eq :
          -DensePoly.leadingCoeff split.2 *
              DensePoly.leadingCoeff (Array.polyProduct split.1) =
            -(DensePoly.leadingCoeff split.2 *
              DensePoly.leadingCoeff (Array.polyProduct split.1)) :=
        Int.neg_mul _ _
      rw [hneg_eq, ← hlc] at hprod_neg_nn
      omega
  have hcand_norm :
      ∀ c ∈ candidates, normalizeFactorSign c = c := by
    intro c hc
    obtain ⟨_, hlc, _⟩ := mem_trialDivisionCandidatesUpTo hc
    unfold normalizeFactorSign
    have hnot_neg : ¬ DensePoly.leadingCoeff c < 0 := by omega
    rw [if_neg hnot_neg]
  have hcand_pos :
      ∀ c ∈ candidates, 0 < DensePoly.leadingCoeff c :=
    fun c hc => (mem_trialDivisionCandidatesUpTo hc).2.1
  have hpeel_norm :
      ∀ factor ∈ peel.1.toList, normalizeFactorSign factor = factor :=
    trialDivisionPeelAux_factor_property
      (P := fun p => normalizeFactorSign p = p)
      split.2 candidates hcand_norm peel.1 peel.2 rfl
  have hpeel_res_pos : 0 < DensePoly.leadingCoeff peel.2 :=
    trialDivisionPeelAux_residual_leadingCoeff_pos split.2 candidates
      hsplit2_pos hcand_pos peel.1 peel.2 rfl
  change ∀ factor ∈ (if peel.2 = 1 then split.1 ++ peel.1
      else (split.1 ++ peel.1).push peel.2).toList,
    normalizeFactorSign factor = factor
  intro factor hmem
  by_cases hres_one : peel.2 = 1
  · rw [if_pos hres_one] at hmem
    rw [Array.toList_append] at hmem
    rcases List.mem_append.mp hmem with hlin | hpeel
    · exact hsplit_norm factor hlin
    · exact hpeel_norm factor hpeel
  · rw [if_neg hres_one] at hmem
    rw [Array.toList_push, Array.toList_append] at hmem
    rcases List.mem_append.mp hmem with hpref | hres
    · rcases List.mem_append.mp hpref with hlin | hpeel
      · exact hsplit_norm factor hlin
      · exact hpeel_norm factor hpeel
    · have hfactor_eq : factor = peel.2 := by
        rcases List.mem_singleton.mp hres with rfl
        rfl
      rw [hfactor_eq]
      unfold normalizeFactorSign
      have hnot_neg : ¬ DensePoly.leadingCoeff peel.2 < 0 := by omega
      rw [if_neg hnot_neg]

/-- Each factor emitted by the standalone integer trial-division core
satisfies `shouldRecordPolynomialFactor`, provided `core` has positive
leading coefficient. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_shouldRecord
    (core : ZPoly) (B : Nat)
    (hcore_pos : 0 < DensePoly.leadingCoeff core) :
    ∀ factor ∈ (exhaustiveIntegerTrialCoreFactorsWithBound core B).toList,
      shouldRecordPolynomialFactor factor = true := by
  let split := splitIntegerRootFactorsAux core (integerRootCandidates core)
    (integerRootCandidates core).length
  let candidates :=
    trialDivisionCandidatesUpTo B (split.2.degree?.getD 0 / 2)
  let peel := trialDivisionPeelAux split.2 candidates
  have hsplit_record :
      ∀ factor ∈ split.1.toList, shouldRecordPolynomialFactor factor = true :=
    splitIntegerRootFactorsAux_shouldRecord core (integerRootCandidates core)
      (integerRootCandidates core).length split.1 split.2 rfl
  have hsplit_prod : split.2 * Array.polyProduct split.1 = core :=
    splitIntegerRootFactorsAux_product core (integerRootCandidates core)
      (integerRootCandidates core).length split.1 split.2 rfl
  have hsplit_lc_pos :
      0 < DensePoly.leadingCoeff (Array.polyProduct split.1) :=
    splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core
      (integerRootCandidates core) (integerRootCandidates core).length
      split.1 split.2 rfl
  have hcore_ne : core ≠ 0 := by
    intro hz
    rw [hz] at hcore_pos
    change 0 < (0 : Int) at hcore_pos
    omega
  have hsplit1_ne : Array.polyProduct split.1 ≠ 0 := by
    intro hz
    rw [hz] at hsplit_lc_pos
    change 0 < (0 : Int) at hsplit_lc_pos
    omega
  have hsplit2_ne : split.2 ≠ 0 := by
    intro hz
    apply hcore_ne
    rw [← hsplit_prod, hz]
    exact DensePoly.zero_mul _
  have hsplit2_pos : 0 < DensePoly.leadingCoeff split.2 := by
    have hlc :
        DensePoly.leadingCoeff core =
          DensePoly.leadingCoeff split.2 *
            DensePoly.leadingCoeff (Array.polyProduct split.1) := by
      rw [← hsplit_prod]
      exact ZPoly.leadingCoeff_mul_of_nonzero split.2
        (Array.polyProduct split.1) hsplit2_ne hsplit1_ne
    rcases Int.lt_or_le 0 (DensePoly.leadingCoeff split.2) with hp | hle
    · exact hp
    · exfalso
      have hnn : 0 ≤ DensePoly.leadingCoeff (Array.polyProduct split.1) :=
        Int.le_of_lt hsplit_lc_pos
      have hna : 0 ≤ -DensePoly.leadingCoeff split.2 := by omega
      have hprod_neg_nn :
          0 ≤ -DensePoly.leadingCoeff split.2 *
            DensePoly.leadingCoeff (Array.polyProduct split.1) :=
        Int.mul_nonneg hna hnn
      have hneg_eq :
          -DensePoly.leadingCoeff split.2 *
              DensePoly.leadingCoeff (Array.polyProduct split.1) =
            -(DensePoly.leadingCoeff split.2 *
              DensePoly.leadingCoeff (Array.polyProduct split.1)) :=
        Int.neg_mul _ _
      rw [hneg_eq, ← hlc] at hprod_neg_nn
      omega
  have hcand_record :
      ∀ c ∈ candidates, shouldRecordPolynomialFactor c = true :=
    fun c hc => (mem_trialDivisionCandidatesUpTo hc).2.2
  have hcand_pos :
      ∀ c ∈ candidates, 0 < DensePoly.leadingCoeff c :=
    fun c hc => (mem_trialDivisionCandidatesUpTo hc).2.1
  have hpeel_record :
      ∀ factor ∈ peel.1.toList,
        shouldRecordPolynomialFactor factor = true :=
    trialDivisionPeelAux_factor_property
      (P := fun p => shouldRecordPolynomialFactor p = true)
      split.2 candidates hcand_record peel.1 peel.2 rfl
  have hpeel_res_pos : 0 < DensePoly.leadingCoeff peel.2 :=
    trialDivisionPeelAux_residual_leadingCoeff_pos split.2 candidates
      hsplit2_pos hcand_pos peel.1 peel.2 rfl
  change ∀ factor ∈ (if peel.2 = 1 then split.1 ++ peel.1
      else (split.1 ++ peel.1).push peel.2).toList,
    shouldRecordPolynomialFactor factor = true
  intro factor hmem
  by_cases hres_one : peel.2 = 1
  · rw [if_pos hres_one] at hmem
    rw [Array.toList_append] at hmem
    rcases List.mem_append.mp hmem with hlin | hpeel
    · exact hsplit_record factor hlin
    · exact hpeel_record factor hpeel
  · rw [if_neg hres_one] at hmem
    rw [Array.toList_push, Array.toList_append] at hmem
    rcases List.mem_append.mp hmem with hpref | hres
    · rcases List.mem_append.mp hpref with hlin | hpeel
      · exact hsplit_record factor hlin
      · exact hpeel_record factor hpeel
    · have hfactor_eq : factor = peel.2 := by
        rcases List.mem_singleton.mp hres with rfl
        rfl
      rw [hfactor_eq]
      have hpeel_ne_zero : peel.2 ≠ 0 := by
        intro hz
        rw [hz] at hpeel_res_pos
        change 0 < (0 : Int) at hpeel_res_pos
        omega
      have hpeel_ne_neg_one : peel.2 ≠ DensePoly.C (-1 : Int) := by
        intro hneg
        have hlc_neg : DensePoly.leadingCoeff peel.2 = -1 := by
          rw [hneg]
          change DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) = -1
          simp [DensePoly.leadingCoeff,
            DensePoly.coeffs_C_of_ne_zero (by decide : (-1 : Int) ≠ 0)]
        rw [hlc_neg] at hpeel_res_pos
        omega
      unfold shouldRecordPolynomialFactor
      simp [hpeel_ne_zero, hres_one, hpeel_ne_neg_one]

/-- `positiveDivisors n` returns a duplicate-free list of natural divisors:
the underlying source `List.range (n + 1)` is `Nodup`, and `List.filter`
preserves this. -/
private theorem positiveDivisors_nodup (n : Nat) :
    (positiveDivisors n).Nodup := by
  unfold positiveDivisors
  exact (List.nodup_range : (List.range (n + 1)).Nodup).filter _

/-- Helper: `Nodup` of the per-divisor pair-list flat-map is preserved as
long as every divisor is positive. The positivity rules out `d = -d` and
ensures `[d, -d]` and `[d', -d']` are disjoint for distinct positive
`d ≠ d'`. -/
private theorem nodup_flatMap_pos_divisor_pairs (ds : List Nat)
    (hds_nodup : ds.Nodup) (hds_pos : ∀ d ∈ ds, 0 < d) :
    (ds.flatMap fun d => [Int.ofNat d, -Int.ofNat d]).Nodup := by
  induction ds with
  | nil => simp
  | cons d rest ih =>
      simp only [List.flatMap_cons]
      rcases List.nodup_cons.mp hds_nodup with ⟨hd_not_mem, hrest_nodup⟩
      have hd_pos : 0 < d := hds_pos d (by simp)
      have hrest_pos : ∀ d' ∈ rest, 0 < d' := by
        intro d' hd'
        exact hds_pos d' (by simp [hd'])
      have ih' := ih hrest_nodup hrest_pos
      rw [List.nodup_append]
      refine ⟨?_, ih', ?_⟩
      · -- `[Int.ofNat d, -Int.ofNat d].Nodup`
        simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil,
          List.nodup_nil, and_true, not_false_eq_true]
        intro hself
        have hd_int : (d : Int) > 0 := by exact_mod_cast hd_pos
        have : (Int.ofNat d : Int) = -(Int.ofNat d : Int) := hself
        have hcoe : (Int.ofNat d : Int) = (d : Int) := rfl
        rw [hcoe] at this
        omega
      · -- Disjointness with the rest of the flatMap
        intro a ha_pair b hb_rest hab
        rcases List.mem_flatMap.mp hb_rest with ⟨d', hd'_mem, hb_mem⟩
        have hd'_pos : 0 < d' := hrest_pos d' hd'_mem
        have hd_ne_d' : d ≠ d' := by
          intro hde
          apply hd_not_mem
          rw [hde]
          exact hd'_mem
        have hd_int : (d : Int) > 0 := by exact_mod_cast hd_pos
        have hd'_int : (d' : Int) > 0 := by exact_mod_cast hd'_pos
        have hd_int_ne : (d : Int) ≠ (d' : Int) := by
          intro h
          have : d = d' := by exact_mod_cast h
          exact hd_ne_d' this
        have hcoe : (Int.ofNat d : Int) = (d : Int) := rfl
        have hcoe' : (Int.ofNat d' : Int) = (d' : Int) := rfl
        -- Concretely unfold membership in the two-element list.
        have ha_dec : a = Int.ofNat d ∨ a = -Int.ofNat d := by
          simpa using ha_pair
        have hb_dec : b = Int.ofNat d' ∨ b = -Int.ofNat d' := by
          simpa using hb_mem
        rcases ha_dec with ha | ha <;> rcases hb_dec with hb | hb <;>
          (rw [ha, hcoe] at hab; rw [hb, hcoe'] at hab; omega)

/-- `integerRootCandidates f` returns a duplicate-free list of candidate
integer roots: positive divisors are distinct, and the per-divisor pair
`[d, -d]` is duplicate-free for `d ≠ 0` (which `positiveDivisors` ensures by
filtering out `d = 0`). The two pairs for distinct positive `d₁ ≠ d₂` share
no elements either. Consumed by the #4785 pairwise non-association proof
together with `splitIntegerRootFactorsAux_factors_form` to read off
pairwise distinctness of the factor roots. -/
private theorem integerRootCandidates_nodup (f : ZPoly) :
    (integerRootCandidates f).Nodup := by
  unfold integerRootCandidates
  apply nodup_flatMap_pos_divisor_pairs
  · exact positiveDivisors_nodup _
  · intro d hd
    unfold positiveDivisors at hd
    rw [List.mem_filter] at hd
    rcases hd with ⟨_hmem, hpred⟩
    simp at hpred
    omega

/-- **#4747 HO-1 support lemma — `normalizeFactorSign` identity on quadratic-arm
core factors.** Every factor emitted by `quadraticIntegerRootFactors? core` is a
fixed point of `normalizeFactorSign`. For linear factors `linearFactorForRoot r`,
the leading coefficient is `1`; for the optional residual, positivity of its
leading coefficient is forced by `0 < DensePoly.leadingCoeff core` combined with
the splitter invariant
`splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos`. Used by the
Mathlib-side discharger
`reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero` to discharge
the `hnorm` precondition of
`normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover`
(#4759). -/
theorem quadraticIntegerRootFactors?_normalizeFactorSign
    {core : ZPoly} {factors : Array ZPoly}
    (hcore_pos : 0 < DensePoly.leadingCoeff core)
    (hquad : quadraticIntegerRootFactors? core = some factors) :
    ∀ factor ∈ factors.toList, normalizeFactorSign factor = factor := by
  unfold quadraticIntegerRootFactors? at hquad
  by_cases hdeg : core.degree?.getD 0 = 2
  · simp only [hdeg, if_true] at hquad
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    have hsplit_norm :
        ∀ factor ∈ split.1.toList, normalizeFactorSign factor = factor := by
      simpa [split, roots] using
        splitIntegerRootFactorsAux_normalizeFactorSign core roots roots.length
          split.1 split.2 rfl
    by_cases hsize : split.1.size = 0
    · simp [roots, split, hsize] at hquad
    · simp only [roots, split, hsize, if_false] at hquad
      by_cases hres_one : split.2 = 1
      · rw [if_pos hres_one] at hquad
        cases hquad
        exact hsplit_norm
      · rw [if_neg hres_one] at hquad
        by_cases hres_deg : split.2.degree?.getD 0 ≤ 1
        · rw [if_pos hres_deg] at hquad
          cases hquad
          intro factor hmem
          rw [Array.toList_push] at hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          cases hmem with
          | inl hsplit_mem =>
              exact hsplit_norm factor hsplit_mem
          | inr hres =>
              rw [hres]
              apply normalizeFactorSign_eq_self_of_leadingCoeff_nonneg
              change 0 ≤ DensePoly.leadingCoeff split.2
              have hsplit_prod :
                  split.2 * Array.polyProduct split.1 = core := by
                simpa [split, roots] using
                  splitIntegerRootFactorsAux_product core roots roots.length
                    split.1 split.2 rfl
              have hsplit_lc_pos :
                  0 < DensePoly.leadingCoeff (Array.polyProduct split.1) := by
                simpa [split, roots] using
                  splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core roots roots.length
                    split.1 split.2 rfl
              have hsplit_poly_ne : Array.polyProduct split.1 ≠ 0 := by
                intro hzero
                rw [hzero] at hsplit_lc_pos
                change 0 < (0 : Int) at hsplit_lc_pos
                omega
              have hres_ne : split.2 ≠ 0 := by
                intro hzero
                have hcore_zero : core = 0 := by
                  rw [← hsplit_prod, hzero]
                  exact DensePoly.zero_mul _
                rw [hcore_zero] at hcore_pos
                change 0 < (0 : Int) at hcore_pos
                omega
              have hlc :
                  DensePoly.leadingCoeff core =
                    DensePoly.leadingCoeff split.2 *
                      DensePoly.leadingCoeff (Array.polyProduct split.1) := by
                rw [← hsplit_prod]
                exact ZPoly.leadingCoeff_mul_of_nonzero
                    split.2 (Array.polyProduct split.1) hres_ne hsplit_poly_ne
              by_cases hnonneg : 0 ≤ DensePoly.leadingCoeff split.2
              · exact hnonneg
              · have hle : DensePoly.leadingCoeff split.2 < 0 := by omega
                have hcore_neg : DensePoly.leadingCoeff core < 0 := by
                  rw [hlc]
                  exact Int.mul_neg_of_neg_of_pos hle hsplit_lc_pos
                omega
        · simp [roots, split, hres_deg] at hquad
  · simp [hdeg] at hquad

theorem quadraticIntegerRootFactors?_shouldRecord
    {core : ZPoly} {factors : Array ZPoly}
    (hcore_pos : 0 < DensePoly.leadingCoeff core)
    (hquad : quadraticIntegerRootFactors? core = some factors) :
    ∀ factor ∈ factors.toList, shouldRecordPolynomialFactor factor = true := by
  unfold quadraticIntegerRootFactors? at hquad
  by_cases hdeg : core.degree?.getD 0 = 2
  · simp only [hdeg, if_true] at hquad
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    have hsplit_record :
        ∀ factor ∈ split.1.toList, shouldRecordPolynomialFactor factor = true := by
      simpa [split, roots] using
        splitIntegerRootFactorsAux_shouldRecord core roots roots.length
          split.1 split.2 rfl
    by_cases hsize : split.1.size = 0
    · simp [roots, split, hsize] at hquad
    · simp only [roots, split, hsize, if_false] at hquad
      by_cases hres_one : split.2 = 1
      · rw [if_pos hres_one] at hquad
        cases hquad
        exact hsplit_record
      · rw [if_neg hres_one] at hquad
        by_cases hres_deg : split.2.degree?.getD 0 ≤ 1
        · rw [if_pos hres_deg] at hquad
          cases hquad
          intro factor hmem
          rw [Array.toList_push] at hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          cases hmem with
          | inl hsplit_mem =>
              exact hsplit_record factor hsplit_mem
          | inr hres =>
              rw [hres]
              have hsplit_prod :
                  split.2 * Array.polyProduct split.1 = core := by
                simpa [split, roots] using
                  splitIntegerRootFactorsAux_product core roots roots.length
                    split.1 split.2 rfl
              have hsplit_lc_pos :
                  0 < DensePoly.leadingCoeff (Array.polyProduct split.1) := by
                simpa [split, roots] using
                  splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core roots roots.length
                    split.1 split.2 rfl
              have hsplit_poly_ne : Array.polyProduct split.1 ≠ 0 := by
                intro hzero
                rw [hzero] at hsplit_lc_pos
                change 0 < (0 : Int) at hsplit_lc_pos
                omega
              have hres_ne : split.2 ≠ 0 := by
                intro hzero
                have hcore_zero : core = 0 := by
                  rw [← hsplit_prod, hzero]
                  exact DensePoly.zero_mul _
                rw [hcore_zero] at hcore_pos
                change 0 < (0 : Int) at hcore_pos
                omega
              have hres_ne_one : split.2 ≠ 1 := hres_one
              have hres_ne_neg_one : split.2 ≠ DensePoly.C (-1 : Int) := by
                intro hneg_one
                have hlc :
                    DensePoly.leadingCoeff core =
                      DensePoly.leadingCoeff split.2 *
                        DensePoly.leadingCoeff (Array.polyProduct split.1) := by
                  rw [← hsplit_prod]
                  exact ZPoly.leadingCoeff_mul_of_nonzero
                    split.2 (Array.polyProduct split.1) hres_ne hsplit_poly_ne
                rw [hneg_one] at hlc
                have hneg_lc :
                    DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) = -1 := by decide
                rw [hneg_lc] at hlc
                have hcore_neg : DensePoly.leadingCoeff core < 0 := by
                  rw [hlc]
                  omega
                omega
              simp [shouldRecordPolynomialFactor, split, roots, hres_ne, hres_ne_one,
                hres_ne_neg_one]
        · simp [roots, split, hres_deg] at hquad
  · simp [hdeg] at hquad

/-- In the quadratic integer-root branch, every emitted factor other than the
optional final residual comes from the integer-root splitter and is therefore
irreducible. When the split is complete (`residual = 1`), this covers every
recorded quadratic-branch factor. -/
theorem quadraticIntegerRootFactors?_factor_irreducible_of_ne_residual
    {core : ZPoly} {factors : Array ZPoly} {factor : ZPoly}
    (hquad : quadraticIntegerRootFactors? core = some factors)
    (hmem : factor ∈ factors.toList)
    (hnot_residual :
      factor ≠
        (splitIntegerRootFactorsAux core (integerRootCandidates core)
          (integerRootCandidates core).length).2) :
    ZPoly.Irreducible factor := by
  unfold quadraticIntegerRootFactors? at hquad
  by_cases hdeg : core.degree?.getD 0 = 2
  · simp only [hdeg, if_true] at hquad
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    by_cases hsize : split.1.size = 0
    · simp [roots, split, hsize] at hquad
    · simp only [roots, split, hsize, if_false] at hquad
      by_cases hres_one : split.2 = 1
      · rw [if_pos hres_one] at hquad
        cases hquad
        exact splitIntegerRootFactorsAux_factor_irreducible
          (target := core) (roots := roots) (fuel := roots.length)
          (factors := split.1) (residual := split.2) rfl hmem
      · rw [if_neg hres_one] at hquad
        by_cases hres_deg : split.2.degree?.getD 0 ≤ 1
        · rw [if_pos hres_deg] at hquad
          cases hquad
          rw [Array.toList_push] at hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          cases hmem with
          | inl hsplit_mem =>
              exact splitIntegerRootFactorsAux_factor_irreducible
                (target := core) (roots := roots) (fuel := roots.length)
                (factors := split.1) (residual := split.2) rfl hsplit_mem
          | inr hres =>
              exact absurd hres hnot_residual
        · simp [roots, split, hres_deg] at hquad
  · simp [hdeg] at hquad

/-- The optional final residual of the quadratic integer-root branch is
irreducible whenever the core is primitive with positive leading coefficient.
The function's degree filter forces the residual's `degree?.getD 0` to be at
most `1`; primitivity rules out degree-`0` residuals (which would be non-unit
constants dividing every coefficient of the primitive core); hence the
residual, when emitted, has size two and is irreducible by the
`irreducible_of_size_two_primitive` companion of `_monic`, applied to the
residual's own primitivity inherited from the product `split.2 *
polyProduct split.1 = core`.

This helper exists for `_factor_irreducible_of_primitive` (the public
combined wrapper); callers outside this file should prefer the wrapper
because its signature avoids referencing the file-`private`
`splitIntegerRootFactorsAux` and `integerRootCandidates`. -/
private theorem quadraticIntegerRootFactors?_residual_irreducible
    {core : ZPoly} {factors : Array ZPoly}
    (hcore_pos : 0 < DensePoly.leadingCoeff core)
    (hcore_primitive : ZPoly.Primitive core)
    (hquad : quadraticIntegerRootFactors? core = some factors)
    {factor : ZPoly}
    (hmem : factor ∈ factors.toList)
    (hres : factor =
      (splitIntegerRootFactorsAux core (integerRootCandidates core)
        (integerRootCandidates core).length).2) :
    ZPoly.Irreducible factor := by
  unfold quadraticIntegerRootFactors? at hquad
  by_cases hdeg : core.degree?.getD 0 = 2
  · simp only [hdeg, if_true] at hquad
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    by_cases hsize : split.1.size = 0
    · simp [roots, split, hsize] at hquad
    · simp only [roots, split, hsize, if_false] at hquad
      by_cases hres_one : split.2 = 1
      · -- split.2 = 1: factor = 1 from hres. But hmem : factor ∈ split.1.toList,
        -- and every element of split.1 is irreducible.
        rw [if_pos hres_one] at hquad
        cases hquad
        exact splitIntegerRootFactorsAux_factor_irreducible
          (target := core) (roots := roots) (fuel := roots.length)
          (factors := split.1) (residual := split.2) rfl hmem
      · rw [if_neg hres_one] at hquad
        by_cases hres_deg : split.2.degree?.getD 0 ≤ 1
        · rw [if_pos hres_deg] at hquad
          cases hquad
          have hsplit_prod :
              split.2 * Array.polyProduct split.1 = core := by
            simpa [split, roots] using
              splitIntegerRootFactorsAux_product core roots roots.length
                split.1 split.2 rfl
          have hsplit_lc_pos :
              0 < DensePoly.leadingCoeff (Array.polyProduct split.1) := by
            simpa [split, roots] using
              splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core roots
                roots.length split.1 split.2 rfl
          have hsplit_poly_ne : Array.polyProduct split.1 ≠ 0 := by
            intro hzero
            rw [hzero] at hsplit_lc_pos
            change 0 < (0 : Int) at hsplit_lc_pos
            omega
          have hcore_ne : core ≠ 0 := by
            intro hzero
            rw [hzero] at hcore_pos
            change 0 < (0 : Int) at hcore_pos
            omega
          -- factor = split.2 from hres. Need: Irreducible split.2.
          rw [hres]
          have hres_ne_zero : split.2 ≠ 0 := by
            intro hzero
            apply hcore_ne
            rw [← hsplit_prod, hzero, DensePoly.zero_mul]
          have hres_size_pos : 0 < split.2.size :=
            ZPoly.size_pos_of_ne_zero split.2 hres_ne_zero
          have hres_size_le : split.2.size ≤ 2 := by
            unfold DensePoly.degree? at hres_deg
            have hnz : split.2.size ≠ 0 := by omega
            simp [hnz] at hres_deg
            omega
          have hcore_lc :
              DensePoly.leadingCoeff core =
                DensePoly.leadingCoeff split.2 *
                  DensePoly.leadingCoeff (Array.polyProduct split.1) := by
            rw [← hsplit_prod]
            exact ZPoly.leadingCoeff_mul_of_nonzero
              split.2 (Array.polyProduct split.1) hres_ne_zero hsplit_poly_ne
          -- size = 1 case: derive contradiction via primitivity.
          rcases (by omega : split.2.size = 1 ∨ split.2.size = 2) with h_one_size | h_two_size
          · exfalso
            have hres_eq : split.2 = DensePoly.C (split.2.coeff 0) :=
              ZPoly.eq_C_of_size_eq_one split.2 h_one_size
            have hcore_expand :
                core = DensePoly.C (split.2.coeff 0) * Array.polyProduct split.1 := by
              rw [← hsplit_prod]
              exact congrArg (· * Array.polyProduct split.1) hres_eq
            have hcoeff_core : ∀ n, core.coeff n =
                split.2.coeff 0 * (Array.polyProduct split.1).coeff n := by
              intro n
              rw [hcore_expand, ZPoly.C_mul_eq_scale,
                DensePoly.coeff_scale (R := Int) (split.2.coeff 0) _ n (Int.mul_zero _)]
            have hc_dvd : ∀ n, ((split.2.coeff 0).natAbs : Int) ∣ core.coeff n := by
              intro n
              rw [hcoeff_core]
              exact Int.natAbs_dvd.mpr ⟨_, rfl⟩
            have hc_dvd_content :
                ((split.2.coeff 0).natAbs : Int) ∣ ZPoly.content core :=
              ZPoly.dvd_content_of_nat_dvd_coeff core _ hc_dvd
            rw [show ZPoly.content core = 1 from hcore_primitive] at hc_dvd_content
            have hc_ne : split.2.coeff 0 ≠ 0 := by
              intro h
              apply hres_ne_zero
              rw [hres_eq, h]; rfl
            have hres_lc : DensePoly.leadingCoeff split.2 = split.2.coeff 0 := by
              rw [DensePoly.leadingCoeff_eq_coeff_last split.2 (by omega)]
              congr 1; omega
            rw [hres_lc] at hcore_lc
            have hc_pos : 0 < split.2.coeff 0 := by
              rcases Int.lt_or_lt_of_ne hc_ne with hlt | hgt
              · exfalso
                have : DensePoly.leadingCoeff core < 0 := by
                  rw [hcore_lc]
                  exact Int.mul_neg_of_neg_of_pos hlt hsplit_lc_pos
                omega
              · exact hgt
            have hnat_dvd : (split.2.coeff 0).natAbs ∣ (1 : Nat) :=
              Int.ofNat_dvd.mp (by simpa using hc_dvd_content)
            have hnat_le : (split.2.coeff 0).natAbs ≤ 1 := Nat.le_of_dvd (by omega) hnat_dvd
            have hnat_pos : 1 ≤ (split.2.coeff 0).natAbs := by
              rcases Nat.eq_zero_or_pos (split.2.coeff 0).natAbs with hz | hp
              · exact absurd (Int.natAbs_eq_zero.mp hz) hc_ne
              · exact hp
            have hnat_eq : (split.2.coeff 0).natAbs = 1 := by omega
            have hc_eq_one : split.2.coeff 0 = 1 := by
              rcases Int.natAbs_eq (split.2.coeff 0) with hpos | hneg
              · rw [hpos, hnat_eq]; rfl
              · exfalso
                have : split.2.coeff 0 = -1 := by rw [hneg, hnat_eq]; rfl
                omega
            apply hres_one
            rw [hres_eq, hc_eq_one]
            rfl
          · -- size = 2 case: prove irreducibility directly.
            -- We mirror irreducible_of_size_two_primitive but use core's primitivity
            -- (rather than split.2's own primitivity, which we'd otherwise need to
            -- derive from `core = split.2 * polyProduct split.1`).
            refine
              { not_zero := hres_ne_zero
                not_unit := ?_
                no_factors := ?_ }
            · intro hunit
              rcases hunit with hone | hneg_unit
              · rw [hone] at h_two_size
                have h1 : (DensePoly.C (1 : Int)).size = 1 := rfl
                omega
              · rw [hneg_unit] at h_two_size
                have hneg_size : (DensePoly.C (-1 : Int)).size = 1 := rfl
                omega
            · intro a b hab
              by_cases ha_zero : a = 0
              · exfalso; apply hres_ne_zero
                rw [hab, ha_zero, DensePoly.zero_mul]
              by_cases hb_zero : b = 0
              · exfalso; apply hres_ne_zero
                rw [hab, hb_zero]
                change a * (0 : ZPoly) = 0
                rw [DensePoly.mul_comm_poly, DensePoly.zero_mul]
              have ha_pos : 0 < a.size := ZPoly.size_pos_of_ne_zero a ha_zero
              have hb_pos : 0 < b.size := ZPoly.size_pos_of_ne_zero b hb_zero
              have hab_size :
                  (a * b).size = a.size + b.size - 1 :=
                ZPoly.mul_size_eq_top_succ_of_nonzero a b ha_pos hb_pos
              rw [← hab] at hab_size
              rw [h_two_size] at hab_size
              have hsum : a.size + b.size = 3 := by omega
              -- The constant-factor argument: if a = C c (size 1), then
              --   core = split.2 * polyProduct split.1 = a * b * polyProduct split.1
              --        = C c * (b * polyProduct split.1).
              -- c divides every coeff of core, so c.natAbs ∣ content core = 1, so c = ±1.
              have const_factor_to_unit :
                  ∀ (u v : ZPoly), u.size = 1 → split.2 = u * v →
                    ZPoly.IsUnit u := by
                intro u v hu_one hsplit_uv
                have hu_eq : u = DensePoly.C (u.coeff 0) :=
                  ZPoly.eq_C_of_size_eq_one u hu_one
                have hu_ne : u ≠ 0 := by
                  intro hzero
                  apply hres_ne_zero
                  rw [hsplit_uv, hzero, DensePoly.zero_mul]
                have huc_ne : u.coeff 0 ≠ 0 := by
                  intro hzero
                  apply hu_ne
                  rw [hu_eq, hzero]; rfl
                have hcore_eq : core =
                    DensePoly.C (u.coeff 0) * (v * Array.polyProduct split.1) := by
                  rw [← hsplit_prod, hsplit_uv]
                  rw [show u * v * Array.polyProduct split.1 =
                        DensePoly.C (u.coeff 0) * v * Array.polyProduct split.1 from
                      congrArg (· * v * Array.polyProduct split.1) hu_eq]
                  rw [DensePoly.mul_assoc_poly]
                have hu_dvd : ∀ n, ((u.coeff 0).natAbs : Int) ∣ core.coeff n := by
                  intro n
                  rw [hcore_eq, ZPoly.C_mul_eq_scale,
                    DensePoly.coeff_scale (R := Int) (u.coeff 0) _ n (Int.mul_zero _)]
                  exact Int.natAbs_dvd.mpr ⟨_, rfl⟩
                have hu_dvd_content :
                    ((u.coeff 0).natAbs : Int) ∣ ZPoly.content core :=
                  ZPoly.dvd_content_of_nat_dvd_coeff core _ hu_dvd
                rw [show ZPoly.content core = 1 from hcore_primitive] at hu_dvd_content
                have hnat_dvd : (u.coeff 0).natAbs ∣ (1 : Nat) :=
                  Int.ofNat_dvd.mp (by simpa using hu_dvd_content)
                have hnat_le : (u.coeff 0).natAbs ≤ 1 := Nat.le_of_dvd (by omega) hnat_dvd
                have hnat_pos : 1 ≤ (u.coeff 0).natAbs := by
                  rcases Nat.eq_zero_or_pos (u.coeff 0).natAbs with hz | hp
                  · exact absurd (Int.natAbs_eq_zero.mp hz) huc_ne
                  · exact hp
                have hnat_eq : (u.coeff 0).natAbs = 1 := by omega
                rcases Int.natAbs_eq (u.coeff 0) with heq | heq
                · left; rw [hu_eq, heq, hnat_eq]; rfl
                · right; rw [hu_eq, heq, hnat_eq]; rfl
              have ha_size_eq : a.size = 1 ∨ a.size = 2 := by omega
              rcases ha_size_eq with ha_one | ha_two
              · left
                exact const_factor_to_unit a b ha_one hab
              · right
                have hb_one : b.size = 1 := by omega
                exact const_factor_to_unit b a hb_one
                  (hab.trans (DensePoly.mul_comm_poly a b))
        · simp [roots, split, hres_deg] at hquad
  · simp [hdeg] at hquad

/-- Every factor emitted by the quadratic integer-root branch is irreducible
when the core is primitive with positive leading coefficient. Non-residual
factors come from the integer-root splitter (linear, hence irreducible);
the optional final residual is also irreducible because primitivity rules
out degree-`0` residuals (non-unit constants would divide every coefficient
of the primitive core) and the function's degree filter restricts residuals
to size two, where the `irreducible_of_size_two_primitive` companion of
`_monic` applies via the constant-factor argument on `core`.

This is the public wrapper used by Mathlib-side callers: its
signature avoids referencing the file-`private` `splitIntegerRootFactorsAux`
and `integerRootCandidates` (the residual is identified internally via
case analysis). -/
theorem quadraticIntegerRootFactors?_factor_irreducible_of_primitive
    {core : ZPoly} {factors : Array ZPoly}
    (hcore_pos : 0 < DensePoly.leadingCoeff core)
    (hcore_primitive : ZPoly.Primitive core)
    (hquad : quadraticIntegerRootFactors? core = some factors)
    {factor : ZPoly}
    (hmem : factor ∈ factors.toList) :
    ZPoly.Irreducible factor := by
  by_cases hres :
      factor =
        (splitIntegerRootFactorsAux core (integerRootCandidates core)
          (integerRootCandidates core).length).2
  · exact quadraticIntegerRootFactors?_residual_irreducible
      hcore_pos hcore_primitive hquad hmem hres
  · exact quadraticIntegerRootFactors?_factor_irreducible_of_ne_residual
      hquad hmem hres

theorem quadraticIntegerRootFactors?_product
    {core : ZPoly} {factors : Array ZPoly}
    (hquad : quadraticIntegerRootFactors? core = some factors) :
    Array.polyProduct factors = core := by
  unfold quadraticIntegerRootFactors? at hquad
  by_cases hdeg : core.degree?.getD 0 = 2
  · simp only [hdeg, if_true] at hquad
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    have hsplit_prod :
        split.2 * Array.polyProduct split.1 = core := by
      simpa [split, roots] using
        splitIntegerRootFactorsAux_product core roots roots.length split.1 split.2 rfl
    by_cases hsize : split.1.size = 0
    · simp [roots, split, hsize] at hquad
    · simp only [roots, split, hsize, if_false] at hquad
      by_cases hres_one : split.2 = 1
      · rw [if_pos hres_one] at hquad
        cases hquad
        simpa [hres_one, ZPoly.one_mul_zpoly] using hsplit_prod
      · rw [if_neg hres_one] at hquad
        by_cases hres_deg : split.2.degree?.getD 0 ≤ 1
        · rw [if_pos hres_deg] at hquad
          cases hquad
          rw [polyProduct_push]
          rw [DensePoly.mul_comm_poly (S := Int)]
          exact hsplit_prod
        · rw [if_neg hres_deg] at hquad
          contradiction
  · simp [hdeg] at hquad

/-- **#4747 HO-1 support lemma — public surface for the polyProduct invariant of the
quadratic integer-root branch.** Whenever `quadraticIntegerRootFactors? core`
returns `some coreFactors`, the executable `Array.polyProduct` of the recorded
factors reconstructs `core` exactly. Public wrapper of the private
`quadraticIntegerRootFactors?_product`, used by the Mathlib-side
discharger `reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero`
(`HexBerlekampZassenhausMathlib/IntReductionMod.lean`) when feeding the
factorPower repeated-part decomposition (#4759) and the no-tail divisibility
lemma (#4807) into `Hex.reassemblyExpansionComplete`. Sibling dischargers:
constant arm `Hex.reassemblyExpansionComplete_constant_of_ne_zero` (#4585 /
PR #4598); small-mod singleton arm
`Hex.reassemblyExpansionComplete_singleton_of_irreducible` (#4597). -/
theorem polyProduct_quadraticIntegerRootFactors?_some
    {core : ZPoly} {coreFactors : Array ZPoly}
    (hquad : quadraticIntegerRootFactors? core = some coreFactors) :
    Array.polyProduct coreFactors = core :=
  quadraticIntegerRootFactors?_product hquad

/-- **#4747 HO-1 support lemma — every factor emitted by `quadraticIntegerRootFactors?`
has dense size two.** The branch is only entered when
`core.degree?.getD 0 = 2`. Linear factors emitted by the splitter are
`linearFactorForRoot r = X - r`, which has size `2` by
`linearFactorForRoot_size_eq_two`. The optional final residual has
`degree?.getD 0 ≤ 1` by construction, so its size is `≤ 2`; the case
`size = 1` (constant residual) is incompatible with primitivity of `core`
combined with positivity of `leadingCoeff core` (the same argument used in
`quadraticIntegerRootFactors?_residual_irreducible` to rule out non-unit
constant residuals).

Used by the Mathlib-side discharger
`reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero` to
discharge the per-factor `0 < q.degree?.getD 0` and `0 < leadingCoeff q`
preconditions of the non-monic expansion-complete surface
`expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc`. -/
theorem quadraticIntegerRootFactors?_factor_size_eq_two
    {core : ZPoly} {coreFactors : Array ZPoly}
    (hcore_pos : 0 < DensePoly.leadingCoeff core)
    (hcore_primitive : ZPoly.Primitive core)
    (hquad : quadraticIntegerRootFactors? core = some coreFactors)
    {factor : ZPoly} (hmem : factor ∈ coreFactors.toList) :
    factor.size = 2 := by
  unfold quadraticIntegerRootFactors? at hquad
  by_cases hdeg : core.degree?.getD 0 = 2
  · simp only [hdeg, if_true] at hquad
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    obtain ⟨rs, _hsub, hshape⟩ :=
      splitIntegerRootFactorsAux_factors_form
        (target := core) (roots := roots) (fuel := roots.length)
        (factors := split.1) (residual := split.2) rfl
    have hsplit_size :
        ∀ f ∈ split.1.toList, f.size = 2 := by
      intro f hf
      rw [hshape] at hf
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hf
      exact linearFactorForRoot_size_eq_two r
    by_cases hsize : split.1.size = 0
    · simp [roots, split, hsize] at hquad
    · simp only [roots, split, hsize, if_false] at hquad
      by_cases hres_one : split.2 = 1
      · rw [if_pos hres_one] at hquad
        cases hquad
        exact hsplit_size factor hmem
      · rw [if_neg hres_one] at hquad
        by_cases hres_deg : split.2.degree?.getD 0 ≤ 1
        · rw [if_pos hres_deg] at hquad
          cases hquad
          rw [Array.toList_push] at hmem
          rcases List.mem_append.mp hmem with hsplit_mem | hres_mem
          · exact hsplit_size factor hsplit_mem
          · -- Residual case: derive size = 2 by ruling out size = 1 via primitivity.
            have hfactor_eq : factor = split.2 := by
              rcases List.mem_singleton.mp hres_mem with rfl
              rfl
            rw [hfactor_eq]
            have hsplit_prod :
                split.2 * Array.polyProduct split.1 = core := by
              simpa [split, roots] using
                splitIntegerRootFactorsAux_product core roots roots.length
                  split.1 split.2 rfl
            have hsplit_lc_pos :
                0 < DensePoly.leadingCoeff (Array.polyProduct split.1) := by
              simpa [split, roots] using
                splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core roots
                  roots.length split.1 split.2 rfl
            have hsplit_poly_ne : Array.polyProduct split.1 ≠ 0 := by
              intro hzero
              rw [hzero] at hsplit_lc_pos
              change 0 < (0 : Int) at hsplit_lc_pos
              omega
            have hcore_ne : core ≠ 0 := by
              intro hzero
              rw [hzero] at hcore_pos
              change 0 < (0 : Int) at hcore_pos
              omega
            have hres_ne_zero : split.2 ≠ 0 := by
              intro hzero
              apply hcore_ne
              rw [← hsplit_prod, hzero, DensePoly.zero_mul]
            have hres_size_pos : 0 < split.2.size :=
              ZPoly.size_pos_of_ne_zero split.2 hres_ne_zero
            have hres_size_le : split.2.size ≤ 2 := by
              unfold DensePoly.degree? at hres_deg
              have hnz : split.2.size ≠ 0 := by omega
              simp [hnz] at hres_deg
              omega
            have hcore_lc :
                DensePoly.leadingCoeff core =
                  DensePoly.leadingCoeff split.2 *
                    DensePoly.leadingCoeff (Array.polyProduct split.1) := by
              rw [← hsplit_prod]
              exact ZPoly.leadingCoeff_mul_of_nonzero
                split.2 (Array.polyProduct split.1) hres_ne_zero hsplit_poly_ne
            rcases (by omega : split.2.size = 1 ∨ split.2.size = 2) with h_one | h_two
            · exfalso
              have hres_eq : split.2 = DensePoly.C (split.2.coeff 0) :=
                ZPoly.eq_C_of_size_eq_one split.2 h_one
              have hcore_expand :
                  core = DensePoly.C (split.2.coeff 0) * Array.polyProduct split.1 := by
                rw [← hsplit_prod]
                exact congrArg (· * Array.polyProduct split.1) hres_eq
              have hcoeff_core : ∀ n, core.coeff n =
                  split.2.coeff 0 * (Array.polyProduct split.1).coeff n := by
                intro n
                rw [hcore_expand, ZPoly.C_mul_eq_scale,
                  DensePoly.coeff_scale (R := Int) (split.2.coeff 0) _ n (Int.mul_zero _)]
              have hc_dvd : ∀ n, ((split.2.coeff 0).natAbs : Int) ∣ core.coeff n := by
                intro n
                rw [hcoeff_core]
                exact Int.natAbs_dvd.mpr ⟨_, rfl⟩
              have hc_dvd_content :
                  ((split.2.coeff 0).natAbs : Int) ∣ ZPoly.content core :=
                ZPoly.dvd_content_of_nat_dvd_coeff core _ hc_dvd
              rw [show ZPoly.content core = 1 from hcore_primitive] at hc_dvd_content
              have hc_ne : split.2.coeff 0 ≠ 0 := by
                intro h
                apply hres_ne_zero
                rw [hres_eq, h]; rfl
              have hres_lc : DensePoly.leadingCoeff split.2 = split.2.coeff 0 := by
                rw [DensePoly.leadingCoeff_eq_coeff_last split.2 (by omega)]
                congr 1; omega
              rw [hres_lc] at hcore_lc
              have hc_pos : 0 < split.2.coeff 0 := by
                rcases Int.lt_or_lt_of_ne hc_ne with hlt | hgt
                · exfalso
                  have : DensePoly.leadingCoeff core < 0 := by
                    rw [hcore_lc]
                    exact Int.mul_neg_of_neg_of_pos hlt hsplit_lc_pos
                  omega
                · exact hgt
              have hnat_dvd : (split.2.coeff 0).natAbs ∣ (1 : Nat) :=
                Int.ofNat_dvd.mp (by simpa using hc_dvd_content)
              have hnat_le : (split.2.coeff 0).natAbs ≤ 1 :=
                Nat.le_of_dvd (by omega) hnat_dvd
              have hnat_pos : 1 ≤ (split.2.coeff 0).natAbs := by
                rcases Nat.eq_zero_or_pos (split.2.coeff 0).natAbs with hz | hp
                · exact absurd (Int.natAbs_eq_zero.mp hz) hc_ne
                · exact hp
              have hnat_eq : (split.2.coeff 0).natAbs = 1 := by omega
              have hc_eq_one : split.2.coeff 0 = 1 := by
                rcases Int.natAbs_eq (split.2.coeff 0) with hpos | hneg
                · rw [hpos, hnat_eq]; rfl
                · exfalso
                  have : split.2.coeff 0 = -1 := by rw [hneg, hnat_eq]; rfl
                  omega
              apply hres_one
              rw [hres_eq, hc_eq_one]
              rfl
            · exact h_two
        · simp [roots, split, hres_deg] at hquad
  · simp [hdeg] at hquad

private theorem toRatPoly_linearFactorForRoot_size (r : Int) :
    (ZPoly.toRatPoly (linearFactorForRoot r)).size = 2 := by
  rw [ZPoly.size_toRatPoly]
  exact linearFactorForRoot_size_eq_two r

private theorem toRatPoly_linearFactorForRoot_ne_zero (r : Int) :
    ZPoly.toRatPoly (linearFactorForRoot r) ≠ 0 :=
  ZPoly.toRatPoly_ne_zero_of_ne_zero (linearFactorForRoot r)
    (linearFactorForRoot_ne_zero r)

private theorem toRatPoly_dvd {p q : ZPoly} (h : p ∣ q) :
    ZPoly.toRatPoly p ∣ ZPoly.toRatPoly q := by
  rcases h with ⟨k, hk⟩
  exact ⟨ZPoly.toRatPoly k, by rw [hk, ZPoly.toRatPoly_mul]⟩

/-- A polynomial that is square-free over `Rat` (in the `Hex.ZPoly.SquareFreeRat`
sense) is not divisible by `(X - r)²` for any integer root `r`.

This is consumed by the pairwise non-association proof for
`quadraticIntegerRootFactors? core` (#4785, downstream of the
`reassemblyExpansionComplete` discharger #4747): if the residual final
factor were associated to an extracted linear factor `linearFactorForRoot r`,
then `linearFactorForRoot r * linearFactorForRoot r` would divide `core`,
which this lemma rules out under squarefreeness. The `(X - r)` shape of
`linearFactorForRoot r` lets us avoid a generic
`p² ∣ f → ¬ SquareFreeRat f` lemma: we work directly with the rational
derivative product rule, the divisor argument is reduced to
`(X - r).size = 2 ≤ gcd.size` after lifting to `DensePoly Rat`. -/
private theorem linearFactor_squared_not_dvd_of_squareFreeRat
    {core : ZPoly} (hne : core ≠ 0) (hsq : Hex.ZPoly.SquareFreeRat core)
    {r : Int} :
    ¬ (linearFactorForRoot r * linearFactorForRoot r) ∣ core := by
  intro hdvd
  rcases hdvd with ⟨g, hg⟩
  -- Lift the witness equation `core = L * L * g` to `DensePoly Rat`.
  let L' := ZPoly.toRatPoly (linearFactorForRoot r)
  let g' := ZPoly.toRatPoly g
  let coreRat := ZPoly.toRatPoly core
  have hcoreRat_eq : coreRat = L' * (L' * g') := by
    show ZPoly.toRatPoly core = _
    rw [hg, ZPoly.toRatPoly_mul, ZPoly.toRatPoly_mul, DensePoly.mul_assoc_poly]
  -- Divisibilities of `coreRat` and `derivative coreRat` by `L'`.
  have hL'_dvd_L'g' : L' ∣ L' * g' := ⟨g', rfl⟩
  have hL'_dvd_coreRat : L' ∣ coreRat := by
    rw [hcoreRat_eq]; exact ⟨L' * g', rfl⟩
  have hL'_dvd_deriv : L' ∣ DensePoly.derivative coreRat := by
    rw [hcoreRat_eq, DensePoly.derivative_mul L' (L' * g')]
    apply DensePoly.dvd_add_poly
    · exact DensePoly.dvd_mul_left_poly (DensePoly.derivative L') hL'_dvd_L'g'
    · exact ⟨DensePoly.derivative (L' * g'), rfl⟩
  -- Combine into divisibility of the gcd.
  have hL'_dvd_gcd : L' ∣ DensePoly.gcd coreRat (DensePoly.derivative coreRat) :=
    DensePoly.dvd_gcd L' _ _ hL'_dvd_coreRat hL'_dvd_deriv
  -- Size argument: `L'.size = 2 ≤ gcd.size`, but squarefreeness says `gcd.size ≤ 1`.
  have hL'_size : L'.size = 2 := toRatPoly_linearFactorForRoot_size r
  have hL'_size_ne : L'.size ≠ 0 := by omega
  have hcoreRat_ne : coreRat ≠ 0 :=
    ZPoly.toRatPoly_ne_zero_of_ne_zero core hne
  have hgcd_dvd_coreRat :=
    DensePoly.gcd_dvd_left coreRat (DensePoly.derivative coreRat)
  have hgcd_ne :
      DensePoly.gcd coreRat (DensePoly.derivative coreRat) ≠ 0 := by
    intro h
    apply hcoreRat_ne
    rcases hgcd_dvd_coreRat with ⟨k, hk⟩
    rw [h, DensePoly.zero_mul] at hk
    exact hk
  have hgcd_size_ne :
      (DensePoly.gcd coreRat (DensePoly.derivative coreRat)).size ≠ 0 := by
    intro hsize
    apply hgcd_ne
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_eq_zero_of_size_le _ (by omega)]
    exact (DensePoly.coeff_zero n).symm
  have hsize_le :=
    ZPoly.rat_size_le_of_dvd_nonzero hL'_size_ne hgcd_size_ne hL'_dvd_gcd
  have hsq' :
      (DensePoly.gcd coreRat (DensePoly.derivative coreRat)).size ≤ 1 := hsq
  omega

/-- Distinct integer roots produce non-`ZPoly`-associated `linearFactorForRoot`
outputs. Both `linearFactorForRoot r` and `linearFactorForRoot s` are monic, so
the unit factor `u` in any `Associated` witness `LF s = LF r * u` is forced to
`C 1` (the `C (-1)` branch flips the leading coefficient). With `u = C 1`,
comparing the constant coefficient yields `-r = -s`, contradicting `r ≠ s`.
Consumed by the linear-vs-linear case of
`quadraticIntegerRootFactors?_pairwise_not_associated` (#4785). -/
private theorem linearFactorForRoot_not_associated_of_ne
    {r s : Int} (hrs : r ≠ s) :
    ¬ ZPoly.Associated (linearFactorForRoot r) (linearFactorForRoot s) := by
  rintro ⟨u, hu, heq⟩
  rcases hu with hu1 | hu_neg
  · -- `u = C 1`, so `LF s = LF r`; comparing `coeff 0` gives `-s = -r`.
    have h_eq : linearFactorForRoot s = linearFactorForRoot r := by
      rw [heq, hu1]
      change linearFactorForRoot r * (1 : ZPoly) = linearFactorForRoot r
      exact DensePoly.mul_one_right_poly (S := Int) _
    have hs_coeff : (linearFactorForRoot s).coeff 0 = -s := by
      unfold linearFactorForRoot
      rw [DensePoly.coeff_ofCoeffs]
      rfl
    have hr_coeff : (linearFactorForRoot r).coeff 0 = -r := by
      unfold linearFactorForRoot
      rw [DensePoly.coeff_ofCoeffs]
      rfl
    have hcoeff_eq : (linearFactorForRoot s).coeff 0 =
        (linearFactorForRoot r).coeff 0 := by rw [h_eq]
    rw [hs_coeff, hr_coeff] at hcoeff_eq
    omega
  · -- `u = C (-1)`, so leading coefficient becomes `1 * (-1) = -1 ≠ 1`.
    have hLFr_ne : linearFactorForRoot r ≠ 0 := linearFactorForRoot_ne_zero r
    have hCneg_ne : DensePoly.C (-1 : Int) ≠ (0 : ZPoly) := by
      intro hz
      have hsize : (DensePoly.C (-1 : Int)).size = 1 := rfl
      rw [hz] at hsize
      change (0 : ZPoly).size = 1 at hsize
      have h0 : (0 : ZPoly).size = 0 := rfl
      omega
    have hlc_eq :
        DensePoly.leadingCoeff (linearFactorForRoot s) =
          DensePoly.leadingCoeff (linearFactorForRoot r) *
            DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) := by
      rw [heq, hu_neg]
      exact ZPoly.leadingCoeff_mul_of_nonzero _ _ hLFr_ne hCneg_ne
    have hC_lc : DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) = (-1 : Int) := by
      simp [DensePoly.leadingCoeff,
        DensePoly.coeffs_C_of_ne_zero (by decide : (-1 : Int) ≠ 0)]
    rw [leadingCoeff_linearFactorForRoot, leadingCoeff_linearFactorForRoot,
        hC_lc] at hlc_eq
    omega

/-- If `r ∈ rs`, then `linearFactorForRoot r` divides the left-fold product
of `rs.map linearFactorForRoot`. Proven by induction on `rs`: the head case is
direct, and the tail case lifts the inductive divisor over a single left
multiplication using `list_foldl_mul_eq_mul_foldl_one`. Consumed by the
linear-vs-residual case of
`quadraticIntegerRootFactors?_pairwise_not_associated` (#4785) to extract
a copy of `linearFactorForRoot r` from `Array.polyProduct split.1` and pair
it with the residual to yield `(linearFactorForRoot r)^2 ∣ core`, then refuted
via `linearFactor_squared_not_dvd_of_squareFreeRat`. -/
private theorem linearFactor_dvd_listFoldl_of_mem
    {rs : List Int} {r : Int} (hmem : r ∈ rs) :
    linearFactorForRoot r ∣
      (rs.map linearFactorForRoot).foldl (· * ·) (1 : ZPoly) := by
  induction rs with
  | nil => exact absurd hmem List.not_mem_nil
  | cons head tail ih =>
    rw [List.map_cons, List.foldl_cons, ZPoly.one_mul_zpoly,
        ZPoly.list_foldl_mul_eq_mul_foldl_one (linearFactorForRoot head)
          (tail.map linearFactorForRoot)]
    rcases List.mem_cons.mp hmem with rfl | hin
    · exact ⟨(tail.map linearFactorForRoot).foldl (· * ·) 1, rfl⟩
    · obtain ⟨k, hk⟩ := ih hin
      refine ⟨linearFactorForRoot head * k, ?_⟩
      rw [hk,
          ← DensePoly.mul_assoc_poly (S := Int) (linearFactorForRoot head)
            (linearFactorForRoot r) k,
          DensePoly.mul_comm_poly (S := Int) (linearFactorForRoot head)
            (linearFactorForRoot r),
          DensePoly.mul_assoc_poly (S := Int) (linearFactorForRoot r)
            (linearFactorForRoot head) k]

/-- **#4785 HO-1 support lemma — pairwise non-association of the quadratic
integer-root branch output.** The factors emitted by
`quadraticIntegerRootFactors? core` are pairwise non-`ZPoly`-associated
whenever `core` is primitive, has positive leading coefficient, and is
square-free over `Rat[x]`.

Linear-vs-linear pairs follow from `splitIntegerRootFactorsAux_factors_form`
(the splitter records `linearFactorForRoot rᵢ` for distinct roots `rᵢ`
forming a `Sublist` of `integerRootCandidates core`, which is `Nodup`) and
`linearFactorForRoot_not_associated_of_ne`.

Linear-vs-residual pairs are ruled out by case analysis on the
`ZPoly.Associated` unit factor `u`: the `u = C (-1)` branch contradicts the
residual's positive leading coefficient (inherited from `core`'s positive
leading coefficient via the splitter's monic-product invariant), and the
`u = C 1` branch produces `(linearFactorForRoot r)^2 ∣ core`, refuted by
`linearFactor_squared_not_dvd_of_squareFreeRat`.

Combines with `irreducible_not_dvd_of_not_associated` (HO-1 support lemma #4603)
into the `reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero`
discharger (#4747 residual). -/
theorem quadraticIntegerRootFactors?_pairwise_not_associated
    {core : ZPoly} (hcore_lc_pos : 0 < DensePoly.leadingCoeff core)
    (hcore_primitive : ZPoly.Primitive core)
    (hcore_squarefree : Hex.ZPoly.SquareFreeRat core)
    {coreFactors : Array ZPoly}
    (hquad : quadraticIntegerRootFactors? core = some coreFactors) :
    coreFactors.toList.Pairwise (fun q₁ q₂ => ¬ ZPoly.Associated q₁ q₂) := by
  have hcore_ne : core ≠ 0 := by
    intro hz
    rw [hz] at hcore_lc_pos
    change 0 < (0 : Int) at hcore_lc_pos
    omega
  -- Acknowledge the primitivity hypothesis (kept in the signature for
  -- symmetry with the `_factor_irreducible_of_primitive` wrapper; the
  -- residual-leading-coefficient argument and the squared-divisibility
  -- contradiction discharge the linear-vs-residual case without it).
  have _ := hcore_primitive
  unfold quadraticIntegerRootFactors? at hquad
  by_cases hdeg : core.degree?.getD 0 = 2
  · simp only [hdeg, if_true] at hquad
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    have hroots_nodup : roots.Nodup := integerRootCandidates_nodup core
    obtain ⟨rs, hsub, hshape⟩ :=
      splitIntegerRootFactorsAux_factors_form (target := core) (roots := roots)
        (fuel := roots.length) (factors := split.1) (residual := split.2) rfl
    have hrs_nodup : rs.Nodup := hsub.nodup hroots_nodup
    -- Pairwise non-association on the splitter's recorded linears.
    have hLL :
        (split.1.toList).Pairwise (fun q₁ q₂ => ¬ ZPoly.Associated q₁ q₂) := by
      rw [hshape, List.pairwise_map]
      exact hrs_nodup.imp (fun hne => linearFactorForRoot_not_associated_of_ne hne)
    by_cases hsize : split.1.size = 0
    · simp [roots, split, hsize] at hquad
    · simp only [roots, split, hsize, if_false] at hquad
      by_cases hres_one : split.2 = 1
      · rw [if_pos hres_one] at hquad
        cases hquad
        exact hLL
      · rw [if_neg hres_one] at hquad
        by_cases hres_deg : split.2.degree?.getD 0 ≤ 1
        · rw [if_pos hres_deg] at hquad
          cases hquad
          rw [Array.toList_push]
          -- Residual leading-coefficient invariants.
          have hsplit_prod :
              split.2 * Array.polyProduct split.1 = core :=
            splitIntegerRootFactorsAux_product core roots roots.length
              split.1 split.2 rfl
          have hpoly_lc_pos :
              0 < DensePoly.leadingCoeff (Array.polyProduct split.1) :=
            splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core roots
              roots.length split.1 split.2 rfl
          have hpoly_ne : Array.polyProduct split.1 ≠ 0 := by
            intro hz
            rw [hz] at hpoly_lc_pos
            change 0 < (0 : Int) at hpoly_lc_pos
            omega
          have hres_ne : split.2 ≠ 0 := by
            intro hz
            apply hcore_ne
            rw [← hsplit_prod, hz, DensePoly.zero_mul]
          have hcore_lc_eq :
              DensePoly.leadingCoeff core =
                DensePoly.leadingCoeff split.2 *
                  DensePoly.leadingCoeff (Array.polyProduct split.1) := by
            rw [← hsplit_prod]
            exact ZPoly.leadingCoeff_mul_of_nonzero split.2 _ hres_ne hpoly_ne
          have hres_lc_pos : 0 < DensePoly.leadingCoeff split.2 := by
            have hres_lc_ne :
                DensePoly.leadingCoeff split.2 ≠ 0 :=
              ZPoly.leadingCoeff_ne_zero_of_ne_zero split.2 hres_ne
            rcases Int.lt_or_lt_of_ne hres_lc_ne with hlt | hgt
            · exfalso
              have hcore_neg : DensePoly.leadingCoeff core < 0 := by
                rw [hcore_lc_eq]
                exact Int.mul_neg_of_neg_of_pos hlt hpoly_lc_pos
              omega
            · exact hgt
          -- Translate `Array.polyProduct split.1` to the list left-fold form.
          have hpolyProd_eq :
              Array.polyProduct split.1 =
                (rs.map linearFactorForRoot).foldl (· * ·) (1 : ZPoly) := by
            unfold Array.polyProduct
            rw [← Array.foldl_toList, hshape]
          have hcross :
              ∀ a ∈ split.1.toList, ¬ ZPoly.Associated a split.2 := by
            rw [hshape]
            intro a ha
            obtain ⟨r, hr_rs, rfl⟩ := List.mem_map.mp ha
            rintro ⟨u, hu, heq⟩
            rcases hu with hu1 | hu_neg
            · -- `u = C 1`: `split.2 = LF r`, so `(LF r)^2 ∣ core`.
              have hsplit2_eq : split.2 = linearFactorForRoot r := by
                rw [heq, hu1]
                change linearFactorForRoot r * (1 : ZPoly) = linearFactorForRoot r
                exact DensePoly.mul_one_right_poly (S := Int) _
              have hLF_dvd :
                  linearFactorForRoot r ∣ Array.polyProduct split.1 := by
                rw [hpolyProd_eq]
                exact linearFactor_dvd_listFoldl_of_mem hr_rs
              obtain ⟨k, hk⟩ := hLF_dvd
              have hdvd :
                  linearFactorForRoot r * linearFactorForRoot r ∣ core := by
                refine ⟨k, ?_⟩
                rw [← hsplit_prod, hsplit2_eq, hk,
                    DensePoly.mul_assoc_poly (S := Int)]
              exact linearFactor_squared_not_dvd_of_squareFreeRat
                hcore_ne hcore_squarefree hdvd
            · -- `u = C (-1)`: leading coefficient of `split.2` becomes `-1`.
              have hCneg_ne : DensePoly.C (-1 : Int) ≠ (0 : ZPoly) := by
                intro hz
                have hsize : (DensePoly.C (-1 : Int)).size = 1 := rfl
                rw [hz] at hsize
                change (0 : ZPoly).size = 1 at hsize
                have h0 : (0 : ZPoly).size = 0 := rfl
                omega
              have hC_lc :
                  DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) = (-1 : Int) := by
                simp [DensePoly.leadingCoeff,
                  DensePoly.coeffs_C_of_ne_zero (by decide : (-1 : Int) ≠ 0)]
              have hlc_eq :
                  DensePoly.leadingCoeff split.2 =
                    DensePoly.leadingCoeff (linearFactorForRoot r) *
                      DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) := by
                rw [heq, hu_neg]
                exact ZPoly.leadingCoeff_mul_of_nonzero _ _
                  (linearFactorForRoot_ne_zero r) hCneg_ne
              rw [leadingCoeff_linearFactorForRoot, hC_lc] at hlc_eq
              rw [hlc_eq] at hres_lc_pos
              omega
          rw [List.pairwise_append]
          refine ⟨hLL, List.pairwise_singleton _ _, ?_⟩
          intro a ha b hb
          rw [List.mem_singleton] at hb
          rw [hb]
          exact hcross a ha
        · simp [roots, split, hres_deg] at hquad
  · simp [hdeg] at hquad

/-- Every factor emitted by `quadraticIntegerRootFactors?` has positive leading
coefficient when the input core has positive leading coefficient. This packages
the normalization and recording invariants for Mathlib-side callers of the
non-monic repeated-part expansion helper. -/
theorem quadraticIntegerRootFactors?_leadingCoeff_pos
    {core : ZPoly} (hcore_pos : 0 < DensePoly.leadingCoeff core)
    {factors : Array ZPoly}
    (hquad : quadraticIntegerRootFactors? core = some factors) :
    ∀ factor ∈ factors.toList, 0 < DensePoly.leadingCoeff factor := by
  intro factor hmem
  have hnorm :
      normalizeFactorSign factor = factor :=
    quadraticIntegerRootFactors?_normalizeFactorSign hcore_pos hquad factor hmem
  have hnonneg : 0 ≤ DensePoly.leadingCoeff factor := by
    rw [← hnorm]
    exact normalizeFactorSign_leadingCoeff_nonneg factor
  have hrecord :
      shouldRecordPolynomialFactor factor = true :=
    quadraticIntegerRootFactors?_shouldRecord hcore_pos hquad factor hmem
  have hfactor_ne : factor ≠ 0 := by
    intro hzero
    unfold shouldRecordPolynomialFactor at hrecord
    simp [hzero] at hrecord
  have hlc_ne :
      DensePoly.leadingCoeff factor ≠ 0 :=
    ZPoly.leadingCoeff_ne_zero_of_ne_zero factor hfactor_ne
  omega

/-- Every factor emitted by `quadraticIntegerRootFactors?` has positive degree
when the input core is primitive with positive leading coefficient. Linear
entries are the splitter's `linearFactorForRoot` outputs; the optional residual
cannot be constant because then its positive constant coefficient would divide
the primitive core's content. -/
theorem quadraticIntegerRootFactors?_degree_pos_of_primitive
    {core : ZPoly} (hcore_pos : 0 < DensePoly.leadingCoeff core)
    (hcore_primitive : ZPoly.Primitive core)
    {factors : Array ZPoly}
    (hquad : quadraticIntegerRootFactors? core = some factors) :
    ∀ factor ∈ factors.toList, 0 < factor.degree?.getD 0 := by
  intro factor hmem
  unfold quadraticIntegerRootFactors? at hquad
  by_cases hdeg : core.degree?.getD 0 = 2
  · simp only [hdeg, if_true] at hquad
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    obtain ⟨rs, _hsub, hshape⟩ :=
      splitIntegerRootFactorsAux_factors_form (target := core) (roots := roots)
        (fuel := roots.length) (factors := split.1) (residual := split.2) rfl
    have hlinear_degree :
        ∀ factor ∈ split.1.toList, 0 < factor.degree?.getD 0 := by
      intro g hg
      rw [hshape] at hg
      rcases List.mem_map.mp hg with ⟨r, _hr, rfl⟩
      exact linearFactorForRoot_degree_pos r
    by_cases hsize : split.1.size = 0
    · simp [roots, split, hsize] at hquad
    · simp only [roots, split, hsize, if_false] at hquad
      by_cases hres_one : split.2 = 1
      · rw [if_pos hres_one] at hquad
        cases hquad
        exact hlinear_degree factor hmem
      · rw [if_neg hres_one] at hquad
        by_cases hres_deg : split.2.degree?.getD 0 ≤ 1
        · rw [if_pos hres_deg] at hquad
          cases hquad
          rw [Array.toList_push] at hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hsplit_mem | hres_mem
          · exact hlinear_degree factor hsplit_mem
          · subst factor
            have hsplit_prod :
                split.2 * Array.polyProduct split.1 = core :=
              splitIntegerRootFactorsAux_product core roots roots.length
                split.1 split.2 rfl
            have hpoly_lc_pos :
                0 < DensePoly.leadingCoeff (Array.polyProduct split.1) :=
              splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core roots
                roots.length split.1 split.2 rfl
            have hpoly_ne : Array.polyProduct split.1 ≠ 0 := by
              intro hz
              rw [hz] at hpoly_lc_pos
              change 0 < (0 : Int) at hpoly_lc_pos
              omega
            have hcore_ne : core ≠ 0 := by
              intro hz
              rw [hz] at hcore_pos
              change 0 < (0 : Int) at hcore_pos
              omega
            have hres_ne : split.2 ≠ 0 := by
              intro hz
              apply hcore_ne
              rw [← hsplit_prod, hz, DensePoly.zero_mul]
            have hcore_lc_eq :
                DensePoly.leadingCoeff core =
                  DensePoly.leadingCoeff split.2 *
                    DensePoly.leadingCoeff (Array.polyProduct split.1) := by
              rw [← hsplit_prod]
              exact ZPoly.leadingCoeff_mul_of_nonzero split.2 _ hres_ne hpoly_ne
            have hres_lc_pos : 0 < DensePoly.leadingCoeff split.2 := by
              have hres_lc_ne :
                  DensePoly.leadingCoeff split.2 ≠ 0 :=
                ZPoly.leadingCoeff_ne_zero_of_ne_zero split.2 hres_ne
              rcases Int.lt_or_lt_of_ne hres_lc_ne with hlt | hgt
              · exfalso
                have hcore_neg : DensePoly.leadingCoeff core < 0 := by
                  rw [hcore_lc_eq]
                  exact Int.mul_neg_of_neg_of_pos hlt hpoly_lc_pos
                omega
              · exact hgt
            by_cases hposdeg : 0 < split.2.degree?.getD 0
            · exact hposdeg
            exfalso
            have hres_deg_zero : split.2.degree?.getD 0 = 0 := by omega
            have hres_size_one : split.2.size = 1 := by
              unfold DensePoly.degree? at hres_deg_zero
              have hsize_ne : split.2.size ≠ 0 := by
                have hpos := ZPoly.size_pos_of_ne_zero split.2 hres_ne
                omega
              simp [hsize_ne] at hres_deg_zero
              omega
            have hres_eq : split.2 = DensePoly.C (split.2.coeff 0) :=
              ZPoly.eq_C_of_size_eq_one split.2 hres_size_one
            have hcore_expand :
                core = DensePoly.C (split.2.coeff 0) * Array.polyProduct split.1 := by
              rw [← hsplit_prod]
              exact congrArg (· * Array.polyProduct split.1) hres_eq
            have hcoeff_core : ∀ n, core.coeff n =
                split.2.coeff 0 * (Array.polyProduct split.1).coeff n := by
              intro n
              rw [hcore_expand, ZPoly.C_mul_eq_scale,
                DensePoly.coeff_scale (R := Int) (split.2.coeff 0) _ n (Int.mul_zero _)]
            have hc_dvd : ∀ n, ((split.2.coeff 0).natAbs : Int) ∣ core.coeff n := by
              intro n
              rw [hcoeff_core]
              exact Int.natAbs_dvd.mpr ⟨_, rfl⟩
            have hc_dvd_content :
                ((split.2.coeff 0).natAbs : Int) ∣ ZPoly.content core :=
              ZPoly.dvd_content_of_nat_dvd_coeff core _ hc_dvd
            rw [show ZPoly.content core = 1 from hcore_primitive] at hc_dvd_content
            have hc_ne : split.2.coeff 0 ≠ 0 := by
              intro h
              apply hres_ne
              rw [hres_eq, h]
              rfl
            have hres_lc : DensePoly.leadingCoeff split.2 = split.2.coeff 0 := by
              rw [DensePoly.leadingCoeff_eq_coeff_last split.2 (by omega)]
              congr 1
              omega
            have hc_pos : 0 < split.2.coeff 0 := by
              rw [← hres_lc]
              exact hres_lc_pos
            have hnat_dvd : (split.2.coeff 0).natAbs ∣ (1 : Nat) :=
              Int.ofNat_dvd.mp (by simpa using hc_dvd_content)
            have hnat_le : (split.2.coeff 0).natAbs ≤ 1 :=
              Nat.le_of_dvd (by omega) hnat_dvd
            have hnat_pos : 1 ≤ (split.2.coeff 0).natAbs := by
              rcases Nat.eq_zero_or_pos (split.2.coeff 0).natAbs with hz | hp
              · exact absurd (Int.natAbs_eq_zero.mp hz) hc_ne
              · exact hp
            have hnat_eq : (split.2.coeff 0).natAbs = 1 := by omega
            have hc_eq_one : split.2.coeff 0 = 1 := by
              rcases Int.natAbs_eq (split.2.coeff 0) with hpos_abs | hneg_abs
              · rw [hpos_abs, hnat_eq]
                rfl
              · exfalso
                have : split.2.coeff 0 = -1 := by
                  rw [hneg_abs, hnat_eq]
                  rfl
                omega
            apply hres_one
            rw [hres_eq, hc_eq_one]
            rfl
        · rw [if_neg hres_deg] at hquad
          contradiction
  · rw [if_neg hdeg] at hquad
    contradiction

private theorem factorSlowFactorsWithBound_polyProduct
    (f : ZPoly) (B : Nat) :
    DensePoly.C (signedContentScalar f) *
      Array.polyProduct (factorSlowFactorsWithBound f B) = f := by
  unfold factorSlowFactorsWithBound
  by_cases hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · simp only [hdeg, if_true]
    exact reassemblePolynomialFactors_product_eq_input f
      #[(normalizeForFactor f).squareFreeCore] (by simp [Array.polyProduct])
  · simp only [hdeg, if_false]
    cases hquad : quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore with
    | some coreFactors =>
        exact reassemblePolynomialFactors_product_eq_input f coreFactors
          (quadraticIntegerRootFactors?_product hquad)
    | none =>
        exact reassemblePolynomialFactors_product_eq_input f
          (exhaustiveCoreFactorsWithBound (normalizeForFactor f).squareFreeCore B
            (choosePrimeData (normalizeForFactor f).squareFreeCore))
          (exhaustiveCoreFactorsWithBound_product
            (normalizeForFactor f).squareFreeCore B
            (choosePrimeData (normalizeForFactor f).squareFreeCore))

set_option maxHeartbeats 3000000 in
private theorem factorFastFactorsWithBound_polyProduct_of_some
    {f : ZPoly} {B : Nat} {factors : Array ZPoly}
    (hfast : factorFastFactorsWithBound f B = some factors) :
    DensePoly.C (signedContentScalar f) * Array.polyProduct factors = f := by
  unfold factorFastFactorsWithBound at hfast
  by_cases hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · simp only [hdeg, if_true] at hfast
    have hfactors := Option.some.inj hfast
    rw [← hfactors]
    exact reassemblePolynomialFactors_product_eq_input f
      #[(normalizeForFactor f).squareFreeCore] (by simp [Array.polyProduct])
  · simp only [hdeg, if_false] at hfast
    by_cases hB0 : B = 0
    · simp [hB0] at hfast
    · simp only [hB0, if_false] at hfast
      by_cases hB1 : B = 1
      · simp only [hB1, if_true] at hfast
        subst B
        cases hchoose : choosePrimeData? (normalizeForFactor f).squareFreeCore with
        | none =>
            simp [hchoose] at hfast
        | some primeData =>
            by_cases hsmall : primeData.factorsModP.size ≤ 1
            · simp [hchoose, hsmall] at hfast
              have hfactors := hfast
              rw [← hfactors]
              exact reassemblePolynomialFactors_product_eq_input f
                #[(normalizeForFactor f).squareFreeCore]
                (by simp [Array.polyProduct])
            · simp [hchoose, hsmall] at hfast
              cases hcore :
                  factorFastCoreWithBound (normalizeForFactor f).squareFreeCore
                    (precisionForCoeffBound 1 primeData.p) primeData
                    (initialHenselPrecision (precisionForCoeffBound 1 primeData.p))
                    (ZPoly.quadraticDoublingSteps
                      (precisionForCoeffBound 1 primeData.p) + 2) with
              | none =>
                  rw [hcore] at hfast
                  contradiction
              | some coreFactors =>
                  rw [hcore] at hfast
                  have hfactors := Option.some.inj hfast
                  rw [← hfactors]
                  exact reassemblePolynomialFactors_product_eq_input f coreFactors
                    (factorFastCoreWithBound_product
                      (normalizeForFactor f).squareFreeCore
                      (precisionForCoeffBound 1 primeData.p) primeData
                      (initialHenselPrecision (precisionForCoeffBound 1 primeData.p))
                      (ZPoly.quadraticDoublingSteps
                        (precisionForCoeffBound 1 primeData.p) + 2)
                      coreFactors hcore)
      · simp only [hB1, if_false] at hfast
        cases hquad : quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore with
        | some coreFactors =>
            simp only [hquad, Option.some.injEq] at hfast
            rw [← hfast]
            exact reassemblePolynomialFactors_product_eq_input f coreFactors
              (quadraticIntegerRootFactors?_product hquad)
        | none =>
            simp only [hquad] at hfast
            cases hchoose : choosePrimeData? (normalizeForFactor f).squareFreeCore with
            | none =>
                simp [hchoose] at hfast
            | some primeData =>
                by_cases hsmall : primeData.factorsModP.size ≤ 1
                · simp [hchoose, hsmall] at hfast
                  have hfactors := hfast
                  rw [← hfactors]
                  exact reassemblePolynomialFactors_product_eq_input f
                    #[(normalizeForFactor f).squareFreeCore]
                    (by simp [Array.polyProduct])
                · simp [hchoose, hsmall] at hfast
                  cases hcore :
                      factorFastCoreWithBound (normalizeForFactor f).squareFreeCore
                        (precisionForCoeffBound B primeData.p) primeData
                        (initialHenselPrecision (precisionForCoeffBound B primeData.p))
                        (ZPoly.quadraticDoublingSteps
                          (precisionForCoeffBound B primeData.p) + 2) with
                  | none =>
                      rw [hcore] at hfast
                      contradiction
                  | some coreFactors =>
                      rw [hcore] at hfast
                      have hfactors := Option.some.inj hfast
                      rw [← hfactors]
                      exact reassemblePolynomialFactors_product_eq_input f coreFactors
                        (factorFastCoreWithBound_product
                          (normalizeForFactor f).squareFreeCore
                          (precisionForCoeffBound B primeData.p) primeData
                          (initialHenselPrecision (precisionForCoeffBound B primeData.p))
                          (ZPoly.quadraticDoublingSteps
                            (precisionForCoeffBound B primeData.p) + 2)
                          coreFactors hcore)

private theorem factorSlowWithBound_product_of_all_recorded_normalized
    (f : ZPoly) (B : Nat)
    (hnormalized :
      ∀ factor ∈ (factorSlowFactorsWithBound f B).toList,
        normalizeFactorSign factor = factor)
    (hrecorded :
      ∀ factor ∈ (factorSlowFactorsWithBound f B).toList,
        shouldRecordPolynomialFactor factor = true) :
    Factorization.product (factorSlowWithBound f B) = f := by
  unfold factorSlowWithBound
  exact
    factorizationOfFactors_product_of_raw_product_of_all_recorded_normalized
      f (factorSlowFactorsWithBound f B)
      (factorSlowFactorsWithBound_polyProduct f B) hnormalized hrecorded

theorem extractXPower_core_ne_zero_of_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    (ZPoly.extractXPower (ZPoly.primitivePart f)).core ≠ 0 :=
  ZPoly.ne_zero_of_primitive _ (extractXPower_core_primitive_of_ne_zero f hf)

theorem repeatedPart_ne_zero_of_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    (normalizeForFactor f).repeatedPart ≠ 0 := by
  unfold normalizeForFactor
  simp only
  intro hzero
  have hcore_ne := extractXPower_core_ne_zero_of_ne_zero f hf
  have hprod_primitive :=
    ZPoly.primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive _ hcore_ne
  have hprod_ne :
      (ZPoly.primitiveSquareFreeDecomposition
            (ZPoly.extractXPower (ZPoly.primitivePart f)).core).squareFreeCore *
        (ZPoly.primitiveSquareFreeDecomposition
            (ZPoly.extractXPower (ZPoly.primitivePart f)).core).repeatedPart ≠ 0 :=
    ZPoly.ne_zero_of_primitive _ hprod_primitive
  apply hprod_ne
  rw [hzero]
  rw [DensePoly.mul_comm_poly (S := Int)]
  exact DensePoly.zero_mul _

private theorem repeatedPart_leadingCoeff_pos_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0) :
    0 < DensePoly.leadingCoeff (normalizeForFactor f).repeatedPart := by
  have hne := repeatedPart_ne_zero_of_ne_zero f hf
  have hnonneg :
      0 ≤ DensePoly.leadingCoeff (normalizeForFactor f).repeatedPart := by
    unfold normalizeForFactor
    exact ZPoly.leadingCoeff_repeatedPart_nonneg _
  have hne_lead :
      DensePoly.leadingCoeff (normalizeForFactor f).repeatedPart ≠ 0 :=
    ZPoly.leadingCoeff_ne_zero_of_ne_zero _ hne
  omega

private theorem repeatedPart_ne_C_neg_one_of_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    (normalizeForFactor f).repeatedPart ≠ DensePoly.C (-1 : Int) := by
  intro h
  have hpos := repeatedPart_leadingCoeff_pos_of_ne_zero f hf
  rw [h] at hpos
  have hneg : DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) = -1 := by decide
  rw [hneg] at hpos
  omega

private theorem repeatedPartFactorArray_normalizeFactorSign_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0)
    (factor : ZPoly)
    (h : factor ∈ (repeatedPartFactorArray (normalizeForFactor f).repeatedPart).toList) :
    normalizeFactorSign factor = factor := by
  rw [mem_repeatedPartFactorArray_eq _ factor h]
  apply normalizeFactorSign_eq_self_of_leadingCoeff_nonneg
  have hpos := repeatedPart_leadingCoeff_pos_of_ne_zero f hf
  omega

private theorem repeatedPartFactorArray_shouldRecord_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0)
    (factor : ZPoly)
    (h : factor ∈ (repeatedPartFactorArray (normalizeForFactor f).repeatedPart).toList) :
    shouldRecordPolynomialFactor factor = true := by
  have hfactor_eq := mem_repeatedPartFactorArray_eq _ factor h
  have hne_one := mem_repeatedPartFactorArray_ne_one _ factor h
  rw [hfactor_eq]
  unfold shouldRecordPolynomialFactor
  simp [repeatedPart_ne_zero_of_ne_zero f hf, hne_one,
    repeatedPart_ne_C_neg_one_of_ne_zero f hf]

private theorem polynomialNormalizationPrefixFactors_normalizeFactorSign_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0)
    (factor : ZPoly)
    (h : factor ∈ (polynomialNormalizationPrefixFactors (normalizeForFactor f)).toList) :
    normalizeFactorSign factor = factor := by
  unfold polynomialNormalizationPrefixFactors at h
  rw [Array.toList_append] at h
  simp only [List.mem_append] at h
  cases h with
  | inl hx =>
      exact xPowerFactorArray_normalizeFactorSign _ factor hx
  | inr hrep =>
      exact repeatedPartFactorArray_normalizeFactorSign_of_ne_zero f hf factor hrep

private theorem polynomialNormalizationPrefixFactors_shouldRecord_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0)
    (factor : ZPoly)
    (h : factor ∈ (polynomialNormalizationPrefixFactors (normalizeForFactor f)).toList) :
    shouldRecordPolynomialFactor factor = true := by
  unfold polynomialNormalizationPrefixFactors at h
  rw [Array.toList_append] at h
  simp only [List.mem_append] at h
  cases h with
  | inl hx =>
      exact xPowerFactorArray_shouldRecord _ factor hx
  | inr hrep =>
      exact repeatedPartFactorArray_shouldRecord_of_ne_zero f hf factor hrep

/-- Lift a per-coreFactor normalize property through the reassembly: any factor
appearing in `reassemblePolynomialFactors` is either a normalization-prefix
factor (handled by `polynomialNormalizationPrefixFactors_normalizeFactorSign_of_ne_zero`)
or appears in the supplied `coreFactors`. -/
private theorem reassemblePolynomialFactors_normalizeFactorSign_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0) (coreFactors : Array ZPoly)
    (hcore : ∀ factor ∈ coreFactors.toList, normalizeFactorSign factor = factor)
    (factor : ZPoly)
    (hmem : factor ∈
      (reassemblePolynomialFactors (normalizeForFactor f) coreFactors).toList) :
    normalizeFactorSign factor = factor := by
  rcases reassemblePolynomialFactors_mem _ _ _ hmem with hprefix | hcoreMem
  · exact polynomialNormalizationPrefixFactors_normalizeFactorSign_of_ne_zero
      f hf factor hprefix
  · exact hcore factor hcoreMem

/-- Lift a per-coreFactor `shouldRecord` property through the reassembly. -/
private theorem reassemblePolynomialFactors_shouldRecord_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0) (coreFactors : Array ZPoly)
    (hcore : ∀ factor ∈ coreFactors.toList, shouldRecordPolynomialFactor factor = true)
    (factor : ZPoly)
    (hmem : factor ∈
      (reassemblePolynomialFactors (normalizeForFactor f) coreFactors).toList) :
    shouldRecordPolynomialFactor factor = true := by
  rcases reassemblePolynomialFactors_mem _ _ _ hmem with hprefix | hcoreMem
  · exact polynomialNormalizationPrefixFactors_shouldRecord_of_ne_zero f hf factor hprefix
  · exact hcore factor hcoreMem

private theorem consumeExactPower_one (target : ZPoly) (fuel : Nat) :
    consumeExactPower target (1 : ZPoly) fuel = (target, 0) := by
  cases fuel with
  | zero => rfl
  | succ n =>
      unfold consumeExactPower
      have hexact : exactQuotient? target (1 : ZPoly) = none := by
        unfold exactQuotient?
        simp
      rw [hexact]

/-- The expansion against `#[1]` never emits any factors: `consumeExactPower _ 1`
returns multiplicity zero, so `expandRepeatedPartFactorArray rp #[1] = (#[], rp)`. -/
private theorem expandRepeatedPartFactorArray_singleton_one (rp : ZPoly) :
    expandRepeatedPartFactorArray rp #[1] = ((#[] : Array ZPoly), rp) := by
  unfold expandRepeatedPartFactorArray
  show expandRepeatedPartFactorsAux [(1 : ZPoly)] rp (rp.size + 1) = (#[], rp)
  unfold expandRepeatedPartFactorsAux
  rw [consumeExactPower_one]
  show ((List.replicate 0 (1 : ZPoly)).toArray ++
      (expandRepeatedPartFactorsAux [] rp (rp.size + 1)).1,
      (expandRepeatedPartFactorsAux [] rp (rp.size + 1)).2) = (#[], rp)
  show ((List.replicate 0 (1 : ZPoly)).toArray ++ ((#[] : Array ZPoly), rp).1,
      ((#[] : Array ZPoly), rp).2) = (#[], rp)
  simp

/-- **#4603 HO-1 support lemma — irreducibility/non-associate translation.** Two
irreducible integer polynomials that are not associated do not divide one
another: if `q₁` divides `q₂` and both are irreducible, the irreducibility
decomposition `q₂ = q₁ * w` forces either `q₁` or `w` to be a unit, and the
first case contradicts `Irreducible q₁`. Used by downstream HO-1 dischargers
to translate the Mathlib structural fact's "pairwise non-associate
irreducible factors" condition into the direct non-divisibility hypothesis
consumed by `expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition`. -/
theorem irreducible_not_dvd_of_not_associated
    {q₁ q₂ : ZPoly} (hq₁ : ZPoly.Irreducible q₁) (hq₂ : ZPoly.Irreducible q₂)
    (hassoc : ¬ ZPoly.Associated q₁ q₂) :
    ¬ q₁ ∣ q₂ := by
  intro hdvd
  rcases hdvd with ⟨w, hw⟩
  rcases hq₂.no_factors q₁ w hw with hunit_q | hunit_w
  · exact hq₁.not_unit hunit_q
  · exact hassoc ⟨w, hunit_w, hw⟩

/-- Converse of `exactQuotient?_product`: when `candidate` does not divide
`target` in `ZPoly`, the exact-quotient probe necessarily returns `none`.
A direct contrapositive of the witness extraction. -/
private theorem exactQuotient?_eq_none_of_not_dvd
    {target candidate : ZPoly}
    (hnot_dvd : ¬ candidate ∣ target) :
    exactQuotient? target candidate = none := by
  cases hcase : exactQuotient? target candidate with
  | none => rfl
  | some w =>
      exfalso
      apply hnot_dvd
      have hmul : w * candidate = target := exactQuotient?_product hcase
      refine ⟨w, ?_⟩
      rw [← hmul]
      exact DensePoly.mul_comm_poly (S := Int) w candidate

/-- Greedy peel of `candidate^?` from `target` exits at multiplicity zero
when `candidate` does not divide `target`. Combines
`exactQuotient?_eq_none_of_not_dvd` with one unfold of `consumeExactPower`. -/
private theorem consumeExactPower_eq_self_zero_of_not_dvd
    {target candidate : ZPoly}
    (hnot_dvd : ¬ candidate ∣ target) (fuel : Nat) :
    consumeExactPower target candidate fuel = (target, 0) := by
  cases fuel with
  | zero => rfl
  | succ n =>
      unfold consumeExactPower
      rw [exactQuotient?_eq_none_of_not_dvd hnot_dvd]

/-- **#4603 HO-1 support lemma — single-factor expansion helper.** For a monic
positive-degree integer polynomial `q` that does not divide a residual `r`,
the greedy `consumeExactPower` on `q ^ k * r` extracts exactly `k` copies of
`q` and returns `r` as the residual, provided the fuel covers `k + 1`
iterations. The monic positive-degree hypothesis is what makes
`exactQuotient?` agree with `ZPoly`-level divisibility (via
`exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree`); the
`¬ q ∣ r` hypothesis closes off the last `consumeExactPower` step at
multiplicity `k`. Used by
`expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition` to
recurse one head factor at a time. -/
private theorem consumeExactPower_pow_mul_of_not_dvd
    (q r : ZPoly) (k : Nat)
    (hq_monic : DensePoly.Monic q)
    (hq_degree : 0 < q.degree?.getD 0)
    (hnot_dvd : ¬ q ∣ r)
    (fuel : Nat) (hfuel : k + 1 ≤ fuel) :
    consumeExactPower (Factorization.polyPow q k * r) q fuel = (r, k) := by
  induction k generalizing fuel with
  | zero =>
      rw [polyPow_zero_lemma, ZPoly.one_mul_zpoly]
      exact consumeExactPower_eq_self_zero_of_not_dvd hnot_dvd fuel
  | succ m ih =>
      cases fuel with
      | zero => omega
      | succ fuel' =>
          have hfuel' : m + 1 ≤ fuel' := by omega
          have htarget_eq :
              (Factorization.polyPow q m * r) * q =
                Factorization.polyPow q (m + 1) * r := by
            rw [polyPow_succ_lemma]
            rw [DensePoly.mul_assoc_poly (S := Int) (Factorization.polyPow q m) r q]
            rw [DensePoly.mul_comm_poly (S := Int) r q]
            rw [← DensePoly.mul_assoc_poly (S := Int) (Factorization.polyPow q m) q r]
          have hquot :
              exactQuotient? (Factorization.polyPow q (m + 1) * r) q =
                some (Factorization.polyPow q m * r) :=
            exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree
              hq_monic hq_degree htarget_eq
          unfold consumeExactPower
          rw [hquot]
          simp only
          rw [ih fuel' hfuel']

/-- **#4778 HO-1 support lemma — non-monic single-factor expansion helper.**
Non-monic analogue of `consumeExactPower_pow_mul_of_not_dvd`: drops the
`Monic q` hypothesis in favour of `0 < leadingCoeff q`, routing the
divisibility-extraction step through
`exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq` (the non-monic
companion of `exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree`,
landed via #4773 → #4774). Used by
`expandRepeatedPartFactorsAux_residual_eq_one_of_pow_decomposition_of_pos_lc`
to handle quadratic-arm core factors emitted by
`quadraticIntegerRootFactors?` that are primitive, positive-leading, but
non-monic (e.g. the `2X + 3` residual from `(X-1)(2X+3) = 2X^2 + X - 3`).
Dependency chain: #4773 → #4774 → this. -/
private theorem consumeExactPower_pow_mul_of_not_dvd_of_pos_lc
    (q r : ZPoly) (k : Nat)
    (hq_pos_lc : 0 < DensePoly.leadingCoeff q)
    (hq_degree : 0 < q.degree?.getD 0)
    (hnot_dvd : ¬ q ∣ r)
    (fuel : Nat) (hfuel : k + 1 ≤ fuel) :
    consumeExactPower (Factorization.polyPow q k * r) q fuel = (r, k) := by
  induction k generalizing fuel with
  | zero =>
      rw [polyPow_zero_lemma, ZPoly.one_mul_zpoly]
      exact consumeExactPower_eq_self_zero_of_not_dvd hnot_dvd fuel
  | succ m ih =>
      cases fuel with
      | zero => omega
      | succ fuel' =>
          have hfuel' : m + 1 ≤ fuel' := by omega
          have htarget_eq :
              (Factorization.polyPow q m * r) * q =
                Factorization.polyPow q (m + 1) * r := by
            rw [polyPow_succ_lemma]
            rw [DensePoly.mul_assoc_poly (S := Int) (Factorization.polyPow q m) r q]
            rw [DensePoly.mul_comm_poly (S := Int) r q]
            rw [← DensePoly.mul_assoc_poly (S := Int) (Factorization.polyPow q m) q r]
          have hquot :
              exactQuotient? (Factorization.polyPow q (m + 1) * r) q =
                some (Factorization.polyPow q m * r) :=
            exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq
              hq_pos_lc hq_degree htarget_eq
          unfold consumeExactPower
          rw [hquot]
          simp only
          rw [ih fuel' hfuel']

/-- **#4603 HO-1 support lemma — list-level pow-decomposition expansion helper.**
Given a list of monic positive-degree polynomials and a matching list of
exponents, if the running residual `rp` factors as
`(∏ (qᵢ, eᵢ) ∈ pairs, qᵢ ^ eᵢ)` and each head factor fails to divide its
suffix product (the "tail non-divisibility" prefix witness), then
`expandRepeatedPartFactorsAux` reduces the residual to `1`. Proved by
induction on the core-factor list, peeling off one head factor at a time
via `consumeExactPower_pow_mul_of_not_dvd`. The fuel budget must cover each
individual exponent (which is automatic for the default
`rp.size + 1` budget when the core factors are nonzero). -/
private theorem expandRepeatedPartFactorsAux_residual_eq_one_of_pow_decomposition :
    ∀ (coreFactors : List ZPoly) (exponents : List Nat) (rp : ZPoly) (fuel : Nat),
      exponents.length = coreFactors.length →
      (∀ q ∈ coreFactors, DensePoly.Monic q) →
      (∀ q ∈ coreFactors, 0 < q.degree?.getD 0) →
      (∀ pre q e suf,
        coreFactors.zip exponents = pre ++ (q, e) :: suf →
        ¬ q ∣ (suf.map (fun (qe : ZPoly × Nat) =>
                Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1) →
      rp = ((coreFactors.zip exponents).map
              (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1 →
      (∀ (qe : ZPoly × Nat), qe ∈ coreFactors.zip exponents → qe.2 + 1 ≤ fuel) →
      (expandRepeatedPartFactorsAux coreFactors rp fuel).2 = 1 := by
  intro coreFactors
  induction coreFactors with
  | nil =>
      intro exponents rp fuel _ _ _ _ hdecomp _
      unfold expandRepeatedPartFactorsAux
      simp only [List.zip_nil_left, List.map_nil, List.foldl_nil] at hdecomp
      exact hdecomp
  | cons q qs ih =>
      intro exponents rp fuel hlen hmonic hdegree hnot_dvd_tail hdecomp hfuel
      cases exponents with
      | nil => simp at hlen
      | cons e es =>
          have hq_monic : DensePoly.Monic q := hmonic q List.mem_cons_self
          have hq_degree : 0 < q.degree?.getD 0 := hdegree q List.mem_cons_self
          have hzip_eq : (q :: qs).zip (e :: es) = (q, e) :: qs.zip es := rfl
          let tailProduct : ZPoly :=
            ((qs.zip es).map
              (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1
          have htail_def :
              tailProduct =
                ((qs.zip es).map
                  (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2)).foldl
                    (· * ·) 1 := rfl
          have hrp_eq : rp = Factorization.polyPow q e * tailProduct := by
            rw [hdecomp, hzip_eq]
            simp only [List.map_cons, List.foldl_cons]
            rw [ZPoly.one_mul_zpoly]
            exact ZPoly.list_foldl_mul_eq_mul_foldl_one
              (Factorization.polyPow q e)
              ((qs.zip es).map
                (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2))
          have hnot_dvd_head : ¬ q ∣ tailProduct := by
            rw [htail_def]
            exact hnot_dvd_tail [] q e (qs.zip es) (by rw [hzip_eq, List.nil_append])
          have hfuel_head : e + 1 ≤ fuel :=
            hfuel (q, e) (by rw [hzip_eq]; exact List.mem_cons_self)
          have hcep :
              consumeExactPower rp q fuel = (tailProduct, e) := by
            rw [hrp_eq]
            exact consumeExactPower_pow_mul_of_not_dvd q tailProduct e
              hq_monic hq_degree hnot_dvd_head fuel hfuel_head
          unfold expandRepeatedPartFactorsAux
          rw [hcep]
          simp only
          have hlen' : es.length = qs.length := by
            simpa using hlen
          have hmonic' : ∀ q' ∈ qs, DensePoly.Monic q' :=
            fun q' hq' => hmonic q' (List.mem_cons_of_mem _ hq')
          have hdegree' : ∀ q' ∈ qs, 0 < q'.degree?.getD 0 :=
            fun q' hq' => hdegree q' (List.mem_cons_of_mem _ hq')
          have hnot_dvd_tail' :
              ∀ pre q' e' suf,
                qs.zip es = pre ++ (q', e') :: suf →
                ¬ q' ∣ (suf.map (fun (qe : ZPoly × Nat) =>
                          Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1 := by
            intro pre q' e' suf hsplit
            apply hnot_dvd_tail ((q, e) :: pre) q' e' suf
            rw [hzip_eq, List.cons_append, hsplit]
          have hfuel' :
              ∀ (qe : ZPoly × Nat), qe ∈ qs.zip es → qe.2 + 1 ≤ fuel := by
            intro qe hqe
            apply hfuel qe
            rw [hzip_eq]
            exact List.mem_cons_of_mem _ hqe
          exact ih es tailProduct fuel hlen' hmonic' hdegree'
            hnot_dvd_tail' htail_def hfuel'

/-- **#4778 HO-1 support lemma — non-monic list-level pow-decomposition expansion
helper.** Non-monic analogue of
`expandRepeatedPartFactorsAux_residual_eq_one_of_pow_decomposition`: replaces
the per-factor `Monic q` hypothesis by `0 < leadingCoeff q`, routing the
single-factor extraction through `consumeExactPower_pow_mul_of_not_dvd_of_pos_lc`
(which itself uses `exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq` from
the #4773 → #4774 dependency chain). Used by the public array-level surface
`expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc`,
which is the quadratic-arm discharger
`reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero` (#4747
residual) precondition that needs to admit a non-monic primitive
positive-leading core factor such as `2X + 3`. -/
private theorem expandRepeatedPartFactorsAux_residual_eq_one_of_pow_decomposition_of_pos_lc :
    ∀ (coreFactors : List ZPoly) (exponents : List Nat) (rp : ZPoly) (fuel : Nat),
      exponents.length = coreFactors.length →
      (∀ q ∈ coreFactors, 0 < DensePoly.leadingCoeff q) →
      (∀ q ∈ coreFactors, 0 < q.degree?.getD 0) →
      (∀ pre q e suf,
        coreFactors.zip exponents = pre ++ (q, e) :: suf →
        ¬ q ∣ (suf.map (fun (qe : ZPoly × Nat) =>
                Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1) →
      rp = ((coreFactors.zip exponents).map
              (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1 →
      (∀ (qe : ZPoly × Nat), qe ∈ coreFactors.zip exponents → qe.2 + 1 ≤ fuel) →
      (expandRepeatedPartFactorsAux coreFactors rp fuel).2 = 1 := by
  intro coreFactors
  induction coreFactors with
  | nil =>
      intro exponents rp fuel _ _ _ _ hdecomp _
      unfold expandRepeatedPartFactorsAux
      simp only [List.zip_nil_left, List.map_nil, List.foldl_nil] at hdecomp
      exact hdecomp
  | cons q qs ih =>
      intro exponents rp fuel hlen hpos_lc hdegree hnot_dvd_tail hdecomp hfuel
      cases exponents with
      | nil => simp at hlen
      | cons e es =>
          have hq_pos_lc : 0 < DensePoly.leadingCoeff q := hpos_lc q List.mem_cons_self
          have hq_degree : 0 < q.degree?.getD 0 := hdegree q List.mem_cons_self
          have hzip_eq : (q :: qs).zip (e :: es) = (q, e) :: qs.zip es := rfl
          let tailProduct : ZPoly :=
            ((qs.zip es).map
              (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1
          have htail_def :
              tailProduct =
                ((qs.zip es).map
                  (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2)).foldl
                    (· * ·) 1 := rfl
          have hrp_eq : rp = Factorization.polyPow q e * tailProduct := by
            rw [hdecomp, hzip_eq]
            simp only [List.map_cons, List.foldl_cons]
            rw [ZPoly.one_mul_zpoly]
            exact ZPoly.list_foldl_mul_eq_mul_foldl_one
              (Factorization.polyPow q e)
              ((qs.zip es).map
                (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2))
          have hnot_dvd_head : ¬ q ∣ tailProduct := by
            rw [htail_def]
            exact hnot_dvd_tail [] q e (qs.zip es) (by rw [hzip_eq, List.nil_append])
          have hfuel_head : e + 1 ≤ fuel :=
            hfuel (q, e) (by rw [hzip_eq]; exact List.mem_cons_self)
          have hcep :
              consumeExactPower rp q fuel = (tailProduct, e) := by
            rw [hrp_eq]
            exact consumeExactPower_pow_mul_of_not_dvd_of_pos_lc q tailProduct e
              hq_pos_lc hq_degree hnot_dvd_head fuel hfuel_head
          unfold expandRepeatedPartFactorsAux
          rw [hcep]
          simp only
          have hlen' : es.length = qs.length := by
            simpa using hlen
          have hpos_lc' : ∀ q' ∈ qs, 0 < DensePoly.leadingCoeff q' :=
            fun q' hq' => hpos_lc q' (List.mem_cons_of_mem _ hq')
          have hdegree' : ∀ q' ∈ qs, 0 < q'.degree?.getD 0 :=
            fun q' hq' => hdegree q' (List.mem_cons_of_mem _ hq')
          have hnot_dvd_tail' :
              ∀ pre q' e' suf,
                qs.zip es = pre ++ (q', e') :: suf →
                ¬ q' ∣ (suf.map (fun (qe : ZPoly × Nat) =>
                          Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1 := by
            intro pre q' e' suf hsplit
            apply hnot_dvd_tail ((q, e) :: pre) q' e' suf
            rw [hzip_eq, List.cons_append, hsplit]
          have hfuel' :
              ∀ (qe : ZPoly × Nat), qe ∈ qs.zip es → qe.2 + 1 ≤ fuel := by
            intro qe hqe
            apply hfuel qe
            rw [hzip_eq]
            exact List.mem_cons_of_mem _ hqe
          exact ih es tailProduct fuel hlen' hpos_lc' hdegree'
            hnot_dvd_tail' htail_def hfuel'

/-- **#4603 HO-1 support lemma — array-level pow-decomposition expansion helper.**
Public surface for `expandRepeatedPartFactorsAux_residual_eq_one_of_pow_decomposition`
that targets `expandRepeatedPartFactorArray` directly. Given a list of monic
positive-degree core factors, a matching list of exponents, a head-product
decomposition `rp = ∏ qᵢ ^ eᵢ`, and pairwise tail-non-divisibility for each
head factor relative to the suffix product, the greedy expansion completely
consumes `rp` and reports residual `1`. The downstream discharger
`reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero` (HO-1
support-lemma sub-issue C) supplies the structural decomposition (Mathlib-side,
from sub-issue #4602) and uses this helper to conclude
`reassemblyExpansionComplete` on the quadratic arms. Compare the small-mod
singleton sibling `expandRepeatedPartFactorArray_pow_singleton` (#4597
deliverable 2), which specialises this shape to a single irreducible. -/
theorem expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition
    (rp : ZPoly) (coreFactors : Array ZPoly)
    (hmonic : ∀ q ∈ coreFactors.toList, DensePoly.Monic q)
    (hdegree : ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0)
    (exponents : List Nat)
    (hlen : exponents.length = coreFactors.size)
    (hnot_dvd_tail :
      ∀ pre q e suf,
        coreFactors.toList.zip exponents = pre ++ (q, e) :: suf →
        ¬ q ∣ (suf.map (fun (qe : ZPoly × Nat) =>
                Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1)
    (hdecomp :
      rp = ((coreFactors.toList.zip exponents).map
              (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1)
    (hfuel :
      ∀ (qe : ZPoly × Nat),
        qe ∈ coreFactors.toList.zip exponents → qe.2 + 1 ≤ rp.size + 1) :
    (expandRepeatedPartFactorArray rp coreFactors).2 = 1 := by
  unfold expandRepeatedPartFactorArray
  have hlen' : exponents.length = coreFactors.toList.length := by
    simpa using hlen
  exact expandRepeatedPartFactorsAux_residual_eq_one_of_pow_decomposition
    coreFactors.toList exponents rp (rp.size + 1)
    hlen' hmonic hdegree hnot_dvd_tail hdecomp hfuel

/-- Public `factorPower` spelling of
`expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition`.

The underlying expansion proof was developed against the private recursive
power helper used by `Factorization.product`; downstream Mathlib-side
assemblers cannot name that helper. This wrapper exposes the same contract
using `Factorization.factorPower`, whose definition is judgmentally the same
power operation and is part of the public API. -/
theorem expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition
    (rp : ZPoly) (coreFactors : Array ZPoly)
    (hmonic : ∀ q ∈ coreFactors.toList, DensePoly.Monic q)
    (hdegree : ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0)
    (exponents : List Nat)
    (hlen : exponents.length = coreFactors.size)
    (hnot_dvd_tail :
      ∀ pre q e suf,
        coreFactors.toList.zip exponents = pre ++ (q, e) :: suf →
        ¬ q ∣ (suf.map (fun (qe : ZPoly × Nat) =>
                Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1)
    (hdecomp :
      rp = ((coreFactors.toList.zip exponents).map
              (fun (qe : ZPoly × Nat) =>
                Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1)
    (hfuel :
      ∀ (qe : ZPoly × Nat),
        qe ∈ coreFactors.toList.zip exponents → qe.2 + 1 ≤ rp.size + 1) :
    (expandRepeatedPartFactorArray rp coreFactors).2 = 1 := by
  refine expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition
    rp coreFactors hmonic hdegree exponents hlen ?_ ?_ hfuel
  · intro pre q e suf hsplit
    simpa [Factorization.factorPower] using hnot_dvd_tail pre q e suf hsplit
  · simpa [Factorization.factorPower] using hdecomp

/-- **#4778 HO-1 support lemma — non-monic array-level pow-decomposition expansion
helper.** Non-monic analogue of
`expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition`:
replaces the per-factor `Monic q` hypothesis by `0 < leadingCoeff q`,
delegating to the list-level non-monic helper
`expandRepeatedPartFactorsAux_residual_eq_one_of_pow_decomposition_of_pos_lc`.
Intermediate between the list-level proof and the public-API factorPower
wrapper below; used by
`expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc`
(the surface used by the quadratic-arm discharger
`reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero`,
#4747 residual). Dependency chain: #4773 → #4774 → here. -/
theorem expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition_of_pos_lc
    (rp : ZPoly) (coreFactors : Array ZPoly)
    (hpos_lc : ∀ q ∈ coreFactors.toList, 0 < DensePoly.leadingCoeff q)
    (hdegree : ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0)
    (exponents : List Nat)
    (hlen : exponents.length = coreFactors.size)
    (hnot_dvd_tail :
      ∀ pre q e suf,
        coreFactors.toList.zip exponents = pre ++ (q, e) :: suf →
        ¬ q ∣ (suf.map (fun (qe : ZPoly × Nat) =>
                Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1)
    (hdecomp :
      rp = ((coreFactors.toList.zip exponents).map
              (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1)
    (hfuel :
      ∀ (qe : ZPoly × Nat),
        qe ∈ coreFactors.toList.zip exponents → qe.2 + 1 ≤ rp.size + 1) :
    (expandRepeatedPartFactorArray rp coreFactors).2 = 1 := by
  unfold expandRepeatedPartFactorArray
  have hlen' : exponents.length = coreFactors.toList.length := by
    simpa using hlen
  exact expandRepeatedPartFactorsAux_residual_eq_one_of_pow_decomposition_of_pos_lc
    coreFactors.toList exponents rp (rp.size + 1)
    hlen' hpos_lc hdegree hnot_dvd_tail hdecomp hfuel

/-- **#4778 HO-1 support lemma — non-monic public `factorPower` array-level
expansion-complete surface.** Non-monic analogue of
`expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition`:
replaces the per-factor `Monic q` hypothesis by `0 < leadingCoeff q`, exposing
the contract using `Factorization.factorPower` (the public-API power operation
referenced by Mathlib-side assemblers). Consumed by the quadratic-arm
discharger `reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero`
(#4747 residual) when the core factor emitted by `quadraticIntegerRootFactors?`
is primitive and positive-leading but non-monic (e.g. the `2X + 3` residual
from `(X-1)(2X+3) = 2X^2 + X - 3`). Dependency chain: #4773 → #4774 → here. -/
theorem expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc
    (rp : ZPoly) (coreFactors : Array ZPoly)
    (hpos_lc : ∀ q ∈ coreFactors.toList, 0 < DensePoly.leadingCoeff q)
    (hdegree : ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0)
    (exponents : List Nat)
    (hlen : exponents.length = coreFactors.size)
    (hnot_dvd_tail :
      ∀ pre q e suf,
        coreFactors.toList.zip exponents = pre ++ (q, e) :: suf →
        ¬ q ∣ (suf.map (fun (qe : ZPoly × Nat) =>
                Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1)
    (hdecomp :
      rp = ((coreFactors.toList.zip exponents).map
              (fun (qe : ZPoly × Nat) =>
                Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1)
    (hfuel :
      ∀ (qe : ZPoly × Nat),
        qe ∈ coreFactors.toList.zip exponents → qe.2 + 1 ≤ rp.size + 1) :
    (expandRepeatedPartFactorArray rp coreFactors).2 = 1 := by
  refine expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition_of_pos_lc
    rp coreFactors hpos_lc hdegree exponents hlen ?_ ?_ hfuel
  · intro pre q e suf hsplit
    simpa [Factorization.factorPower] using hnot_dvd_tail pre q e suf hsplit
  · simpa [Factorization.factorPower] using hdecomp

/-- An irreducible `ZPoly` does not divide the unit `1`. Used by the small-mod
singleton arm specialisation `expandRepeatedPartFactorArray_pow_singleton`
(#4597 deliverable 2) to discharge the wrapper's tail-non-divisibility
precondition for the singleton case, where the suffix product collapses to
`1` and the only obligation is `¬ q ∣ 1`. The proof is a direct size argument:
`size_le_of_dvd_nonzero` would force `q.size ≤ 1`, but irreducibility (via the
non-zero, non-unit conditions on the leading coefficient) forces `q.size ≥ 2`. -/
private theorem irreducible_not_dvd_one {q : ZPoly}
    (hq_irr : ZPoly.Irreducible q) : ¬ q ∣ (1 : ZPoly) := by
  intro hdvd
  have hq_ne : q ≠ 0 := hq_irr.not_zero
  have hone_ne : (1 : ZPoly) ≠ 0 := by
    intro h
    have : (1 : ZPoly).size = 1 := rfl
    rw [h] at this
    exact absurd this (by decide)
  have hq_size_le : q.size ≤ (1 : ZPoly).size :=
    ZPoly.size_le_of_dvd_nonzero hq_ne hone_ne hdvd
  have h1 : (1 : ZPoly).size = 1 := rfl
  have hq_pos : 0 < q.size := ZPoly.size_pos_of_ne_zero q hq_ne
  have hq_one : q.size = 1 := by omega
  -- A `q` of size 1 is constant, hence the leading coefficient appears at
  -- index 0; combined with `q ∣ 1` forcing the leading coefficient to be a
  -- unit in `ℤ`, this contradicts `not_unit`.
  have hq_eq : q = DensePoly.C (q.coeff 0) := ZPoly.eq_C_of_size_eq_one q hq_one
  rcases hdvd with ⟨w, hw⟩
  -- hw : (1 : ZPoly) = q * w
  have hw_ne : w ≠ 0 := by
    intro hw_zero
    rw [hw_zero] at hw
    -- (1 : ZPoly) = q * 0 = 0, contradicting hone_ne
    rw [DensePoly.mul_comm_poly, DensePoly.zero_mul] at hw
    exact hone_ne hw
  have hw_pos : 0 < w.size := ZPoly.size_pos_of_ne_zero w hw_ne
  have hqw_size : (q * w).size = q.size + w.size - 1 :=
    ZPoly.mul_size_eq_top_succ_of_nonzero q w hq_pos hw_pos
  rw [← hw, h1] at hqw_size
  have hw_one : w.size = 1 := by omega
  have hlead :
      DensePoly.leadingCoeff q * DensePoly.leadingCoeff w = (1 : Int) := by
    have := ZPoly.leadingCoeff_mul_of_nonzero q w hq_ne hw_ne
    rw [← hw] at this
    have : DensePoly.leadingCoeff q * DensePoly.leadingCoeff w =
        DensePoly.leadingCoeff (1 : ZPoly) := this.symm
    rw [this]
    rfl
  have hq_lead : DensePoly.leadingCoeff q = q.coeff 0 := by
    rw [DensePoly.leadingCoeff_eq_coeff_last q (by omega)]
    congr 1; omega
  rw [hq_lead] at hlead
  have hcoeff_unit : q.coeff 0 = 1 ∨ q.coeff 0 = -1 :=
    ZPoly.int_factor_one_eq_unit hlead
  apply hq_irr.not_unit
  rcases hcoeff_unit with h | h
  · left; rw [hq_eq, h]
  · right; rw [hq_eq, h]

/-- **#4597 HO-1 support lemma — small-mod singleton arm expansion specialisation.**
Singleton specialisation of
`expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition`:
when the repeated part `rp` is the `k`-th `Hex.Factorization.factorPower` of an
irreducible monic positive-degree `q`, expanding against the singleton core
`#[q]` consumes the repeated part exactly, emitting `k` copies of `q` and
reporting residual `1`. Used by the small-mod singleton arm public wrapper
`factor_small_mod_singleton_branch_entry_irreducible_of_choosePrimeData`
(#4564 / PR #4581) via the public discharger
`Hex.reassemblyExpansionComplete_singleton_of_irreducible` (#4597
deliverable 3). Sibling specialisations: constant arm
`reassemblyExpansionComplete_constant_of_ne_zero` (#4585 / PR #4598);
quadratic arm tracked by #4747. -/
theorem expandRepeatedPartFactorArray_pow_singleton
    (q : ZPoly) (k : Nat)
    (hq_monic : DensePoly.Monic q)
    (hq_degree : 0 < q.degree?.getD 0)
    (hq_irr : ZPoly.Irreducible q)
    (rp : ZPoly) (hrp : rp = Factorization.factorPower q k)
    (hfuel : k + 1 ≤ rp.size + 1) :
    expandRepeatedPartFactorArray rp #[q] =
      ((List.replicate k q).toArray, 1) := by
  have hnot_dvd : ¬ q ∣ (1 : ZPoly) := irreducible_not_dvd_one hq_irr
  have hmul : rp = Factorization.polyPow q k * 1 := by
    rw [hrp]; exact (DensePoly.mul_one_right_poly _).symm
  have hcep : consumeExactPower rp q (rp.size + 1) = (1, k) := by
    rw [hmul]
    apply consumeExactPower_pow_mul_of_not_dvd q 1 k hq_monic hq_degree hnot_dvd
    rw [← hmul]; exact hfuel
  unfold expandRepeatedPartFactorArray
  show expandRepeatedPartFactorsAux [q] rp (rp.size + 1) = _
  unfold expandRepeatedPartFactorsAux
  rw [hcep]
  show ((List.replicate k q).toArray ++
      (expandRepeatedPartFactorsAux [] (1 : ZPoly) (rp.size + 1)).1,
      (expandRepeatedPartFactorsAux [] (1 : ZPoly) (rp.size + 1)).2) =
    ((List.replicate k q).toArray, 1)
  unfold expandRepeatedPartFactorsAux
  simp

/-- **#4955 support lemma — non-monic singleton arm expansion specialisation.**
Non-monic counterpart of `expandRepeatedPartFactorArray_pow_singleton`:
replaces the `Monic q` premise by `0 < leadingCoeff q`, with a
**weakened conclusion** — only the residual projection `.2 = 1`, not the
full pair. The full-pair version has no non-monic counterpart at the
executable layer (`consumeExactPower_pow_mul_of_not_dvd` is genuinely
monic-only; under non-monic `q`, the recursive `consumeExactPower` step's
quotient is not in general a power of `q`, even if the residual collapses
to `1`). The residual-only form suffices for the mid-layer
`_of_pos_lc` sibling of
`reassemblyExpansionComplete_singleton_of_irreducible` (#4956), which
unfolds `reassemblyExpansionComplete` to `(expand ...).2 = 1`. The
proof routes through the array-level public surface
`expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc`
(#4778) specialised to `coreFactors = #[q]`, `exponents = [k]`. -/
theorem expandRepeatedPartFactorArray_pow_singleton_of_pos_lc
    (q : ZPoly) (k : Nat)
    (hq_pos_lc : 0 < DensePoly.leadingCoeff q)
    (hq_degree : 0 < q.degree?.getD 0)
    (hq_irr : ZPoly.Irreducible q)
    (rp : ZPoly) (hrp : rp = Factorization.factorPower q k)
    (hfuel : k + 1 ≤ rp.size + 1) :
    (expandRepeatedPartFactorArray rp #[q]).2 = 1 := by
  have hsingleton_toList : (#[q] : Array ZPoly).toList = [q] := rfl
  refine expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc
    rp #[q] ?hpos_lc ?hdegree [k] ?hlen ?hnot_dvd_tail ?hdecomp ?hfuel
  · intro q' hq'
    rw [hsingleton_toList] at hq'
    have : q' = q := by simpa using hq'
    rw [this]; exact hq_pos_lc
  · intro q' hq'
    rw [hsingleton_toList] at hq'
    have : q' = q := by simpa using hq'
    rw [this]; exact hq_degree
  · rfl
  · intro pre q' e suf hsplit
    -- The zip reduces to `[(q, k)]`; length forces `pre = []` and `suf = []`.
    rw [hsingleton_toList] at hsplit
    have hzip : ([q] : List ZPoly).zip [k] = [(q, k)] := rfl
    rw [hzip] at hsplit
    have hlen_eq : 1 = pre.length + (suf.length + 1) := by
      have := congrArg List.length hsplit
      simpa using this
    have hpre_len : pre.length = 0 := by omega
    have hsuf_len : suf.length = 0 := by omega
    have hpre : pre = [] := List.length_eq_zero_iff.mp hpre_len
    have hsuf : suf = [] := List.length_eq_zero_iff.mp hsuf_len
    subst hpre; subst hsuf
    -- hsplit : [(q, k)] = [(q', e)]
    have hq'_eq : q' = q := by
      have h := hsplit
      simp at h
      exact h.1.symm
    simp only [List.map_nil, List.foldl_nil]
    rw [hq'_eq]
    exact irreducible_not_dvd_one hq_irr
  · rw [hrp, hsingleton_toList]
    simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
      List.foldl_cons, List.foldl_nil, ZPoly.one_mul_zpoly]
  · intro qe hqe
    rw [hsingleton_toList] at hqe
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false] at hqe
    rw [hqe]
    exact hfuel

/-- The reassembled output for a single-`1` core list is exactly the
normalization prefix followed by `1`. Both branches of `reassemblePolynomialFactors`
collapse to this shape because the expansion never extracts anything when the
sole candidate is the unit `1`. -/
private theorem reassemblePolynomialFactors_singleton_one_eq
    (d : FactorNormalizationData) :
    reassemblePolynomialFactors d #[1] = polynomialNormalizationPrefixFactors d ++ #[1] := by
  unfold reassemblePolynomialFactors
  rw [expandRepeatedPartFactorArray_singleton_one]
  simp only
  by_cases hrp : d.repeatedPart = 1
  · rw [if_pos hrp]
    unfold polynomialNormalizationPrefixFactors repeatedPartFactorArray
    rw [hrp]
    simp
  · rw [if_neg hrp]

private theorem squareFreeCore_ne_zero_of_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    (normalizeForFactor f).squareFreeCore ≠ 0 := by
  unfold normalizeForFactor
  simp only
  intro hzero
  have hcore_ne := extractXPower_core_ne_zero_of_ne_zero f hf
  have hprod_primitive :=
    ZPoly.primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive _ hcore_ne
  have hprod_ne :
      (ZPoly.primitiveSquareFreeDecomposition
            (ZPoly.extractXPower (ZPoly.primitivePart f)).core).squareFreeCore *
        (ZPoly.primitiveSquareFreeDecomposition
            (ZPoly.extractXPower (ZPoly.primitivePart f)).core).repeatedPart ≠ 0 :=
    ZPoly.ne_zero_of_primitive _ hprod_primitive
  apply hprod_ne
  rw [hzero]
  exact DensePoly.zero_mul _

theorem squareFreeCore_leadingCoeff_pos_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0) :
    0 < DensePoly.leadingCoeff (normalizeForFactor f).squareFreeCore := by
  have hne := squareFreeCore_ne_zero_of_ne_zero f hf
  have hnonneg :
      0 ≤ DensePoly.leadingCoeff (normalizeForFactor f).squareFreeCore := by
    unfold normalizeForFactor
    exact ZPoly.leadingCoeff_squareFreeCore_nonneg _
  have hne_lead :
      DensePoly.leadingCoeff (normalizeForFactor f).squareFreeCore ≠ 0 :=
    ZPoly.leadingCoeff_ne_zero_of_ne_zero _ hne
  omega

/-- When the normalized square-free core has degree zero (and `f ≠ 0`), the
primitive square-free decomposition forces the core to be exactly `1`.  Exposed
publicly so Mathlib-side per-branch wrappers (in particular the fast-path
constant arm) can rule out the singleton-core entry from the recorded factor
set. -/
theorem squareFreeCore_eq_one_of_constant_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0) :
    (normalizeForFactor f).squareFreeCore = 1 := by
  unfold normalizeForFactor at hdeg ⊢
  simpa using
    ZPoly.primitiveSquareFreeDecomposition_squareFreeCore_eq_one_of_degree_zero
      (ZPoly.extractXPower (ZPoly.primitivePart f)).core
      (by
        simpa using squareFreeCore_ne_zero_of_ne_zero f hf)
      hdeg

/-- Companion to `squareFreeCore_eq_one_of_constant_of_ne_zero`: the recorded
`repeatedPart` collapses to `1` in the constant branch. -/
private theorem normalizeForFactor_repeatedPart_eq_one_of_constant
    (f : ZPoly) (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0) :
    (normalizeForFactor f).repeatedPart = 1 := by
  unfold normalizeForFactor at hdeg ⊢
  simpa using
    ZPoly.primitiveSquareFreeDecomposition_repeatedPart_eq_one_of_squareFreeCore_degree_zero
      (ZPoly.extractXPower (ZPoly.primitivePart f)).core
      (by
        simpa using squareFreeCore_ne_zero_of_ne_zero f hf)
      hdeg

/-- **#4585 HO-1 support lemma — fast-path constant arm `reassemblyExpansionComplete`
discharger.** When the recorded square-free core has degree zero (and `f ≠ 0`),
the singleton-core reassembly is automatically expansion-complete: the
square-free core collapses to `1` via
`squareFreeCore_eq_one_of_constant_of_ne_zero`, the singleton-`1` expansion is
the identity via `expandRepeatedPartFactorArray_singleton_one`, and the residual
`(normalizeForFactor f).repeatedPart` is forced to `1` by
`normalizeForFactor_repeatedPart_eq_one_of_constant` (the constant-branch
specialisation of
`ZPoly.primitiveSquareFreeDecomposition_repeatedPart_eq_one_of_squareFreeCore_degree_zero`).
Used by the fast-path constant arm public wrapper
`factor_constant_branch_entry_irreducible_of_choosePrimeData` (#4565) so it can
drop its explicit `hcomplete` hypothesis. The small-mod singleton (#4564),
slow-quadratic (#4575), and fast-quadratic (#4571) `hcomplete` dischargers are
siblings tracked separately. -/
theorem reassemblyExpansionComplete_constant_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0) :
    reassemblyExpansionComplete (normalizeForFactor f)
      #[(normalizeForFactor f).squareFreeCore] := by
  have hcore_one := squareFreeCore_eq_one_of_constant_of_ne_zero f hf hdeg
  have hrep_one := normalizeForFactor_repeatedPart_eq_one_of_constant f hf hdeg
  unfold reassemblyExpansionComplete
  rw [hcore_one, expandRepeatedPartFactorArray_singleton_one]
  exact hrep_one

/-- The normalized square-free core has positive leading coefficient
(`squareFreeCore_leadingCoeff_pos_of_ne_zero`), so its sign-normalisation
is the identity. Exposed publicly for HO-1 support-lemma callers in the
Mathlib-side layer (notably the small-mod singleton arm specialisation of
`normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover`,
which discharges its `hnorm` precondition with this lemma). -/
theorem squareFreeCore_normalizeFactorSign_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0) :
    normalizeFactorSign (normalizeForFactor f).squareFreeCore =
      (normalizeForFactor f).squareFreeCore := by
  apply normalizeFactorSign_eq_self_of_leadingCoeff_nonneg
  have hpos := squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  omega

private theorem squareFreeCore_shouldRecord_of_degree_pos
    (f : ZPoly) (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0) :
    shouldRecordPolynomialFactor (normalizeForFactor f).squareFreeCore = true := by
  have hne_zero : (normalizeForFactor f).squareFreeCore ≠ 0 :=
    squareFreeCore_ne_zero_of_ne_zero f hf
  have hne_one : (normalizeForFactor f).squareFreeCore ≠ 1 := by
    intro hone
    apply hdeg
    rw [hone]
    change (DensePoly.C (1 : Int)).degree?.getD 0 = 0
    exact DensePoly.degree?_C_getD 1
  have hne_neg_one : (normalizeForFactor f).squareFreeCore ≠ DensePoly.C (-1 : Int) := by
    intro hneg
    apply hdeg
    rw [hneg]
    exact DensePoly.degree?_C_getD (-1)
  unfold shouldRecordPolynomialFactor
  simp [hne_zero, hne_one, hne_neg_one]

private theorem filteredNormalizedFactors_append_one_of_all_recorded_normalized
    (factors : List ZPoly)
    (hnormalized :
      ∀ factor ∈ factors, normalizeFactorSign factor = factor)
    (hrecorded :
      ∀ factor ∈ factors, shouldRecordPolynomialFactor factor = true) :
    filteredNormalizedFactors (factors ++ [1]) = factors := by
  induction factors with
  | nil =>
      rw [List.nil_append]
      rw [filteredNormalizedFactors_cons_drop]
      · rfl
      · rw [normalizeFactorSign_one]
        exact shouldRecordPolynomialFactor_one
  | cons factor factors ih =>
      have hfactor_normalized :
          normalizeFactorSign factor = factor :=
        hnormalized factor (by simp)
      have hfactor_recorded :
          shouldRecordPolynomialFactor factor = true :=
        hrecorded factor (by simp)
      have hkeep :
          shouldRecordPolynomialFactor (normalizeFactorSign factor) = true := by
        rw [hfactor_normalized]
        exact hfactor_recorded
      rw [List.cons_append]
      rw [filteredNormalizedFactors_cons_keep _ hkeep, hfactor_normalized]
      rw [ih
        (fun factor hmem => hnormalized factor (by simp [hmem]))
        (fun factor hmem => hrecorded factor (by simp [hmem]))]

private theorem polyProduct_filteredNormalizedFactors_append_one_of_all_recorded_normalized
    (factors : Array ZPoly)
    (hnormalized :
      ∀ factor ∈ factors.toList, normalizeFactorSign factor = factor)
    (hrecorded :
      ∀ factor ∈ factors.toList, shouldRecordPolynomialFactor factor = true) :
    Array.polyProduct (filteredNormalizedFactors (factors ++ #[1]).toList).toArray =
      Array.polyProduct factors := by
  rw [Array.toList_append]
  change Array.polyProduct
      (filteredNormalizedFactors (factors.toList ++ [1])).toArray =
    Array.polyProduct factors
  rw [filteredNormalizedFactors_append_one_of_all_recorded_normalized
    factors.toList hnormalized hrecorded]

private theorem factorSlowWithBound_product_of_constant_branch
    (f : ZPoly) (B : Nat)
    (hf : f ≠ 0)
    (hbranch : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0) :
    Factorization.product (factorSlowWithBound f B) = f := by
  unfold factorSlowWithBound factorSlowFactorsWithBound
  rw [if_pos hbranch]
  have hcore_one := squareFreeCore_eq_one_of_constant_of_ne_zero f hf hbranch
  rw [hcore_one]
  apply factorizationOfFactors_product_of_filtered_product
  · exact reassemblePolynomialFactors_product_eq_input f #[1] (by
      rw [ZPoly.polyProduct_singleton]
      exact hcore_one.symm)
  · rw [reassemblePolynomialFactors_singleton_one_eq]
    rw [polyProduct_filteredNormalizedFactors_append_one_of_all_recorded_normalized]
    rw [ZPoly.polyProduct_append, ZPoly.polyProduct_singleton]
    exact (DensePoly.mul_one_right_poly (S := Int) _).symm
    · intro factor hmem
      exact polynomialNormalizationPrefixFactors_normalizeFactorSign_of_ne_zero
        f hf factor hmem
    · intro factor hmem
      exact polynomialNormalizationPrefixFactors_shouldRecord_of_ne_zero
        f hf factor hmem

private theorem factorSlowWithBound_product_of_quadratic_branch
    (f : ZPoly) (B : Nat)
    (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (coreFactors : Array ZPoly)
    (hquad : quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore =
      some coreFactors) :
    Factorization.product (factorSlowWithBound f B) = f := by
  apply factorSlowWithBound_product_of_all_recorded_normalized
  · unfold factorSlowFactorsWithBound
    rw [if_neg hdeg]
    rw [hquad]
    intro factor hmem
    refine reassemblePolynomialFactors_normalizeFactorSign_of_ne_zero f hf
      coreFactors ?_ factor hmem
    intro c hc
    exact quadraticIntegerRootFactors?_normalizeFactorSign
      (squareFreeCore_leadingCoeff_pos_of_ne_zero f hf) hquad c hc
  · unfold factorSlowFactorsWithBound
    rw [if_neg hdeg]
    rw [hquad]
    intro factor hmem
    refine reassemblePolynomialFactors_shouldRecord_of_ne_zero f hf
      coreFactors ?_ factor hmem
    intro c hc
    exact quadraticIntegerRootFactors?_shouldRecord
      (squareFreeCore_leadingCoeff_pos_of_ne_zero f hf) hquad c hc

private theorem factorSlowWithBound_product_of_exhaustive_branch
    (f : ZPoly) (B : Nat)
    (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hquad : quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none) :
    Factorization.product (factorSlowWithBound f B) = f := by
  apply factorSlowWithBound_product_of_all_recorded_normalized
  · unfold factorSlowFactorsWithBound
    rw [if_neg hdeg]
    rw [hquad]
    intro factor hmem
    refine reassemblePolynomialFactors_normalizeFactorSign_of_ne_zero f hf
      (exhaustiveCoreFactorsWithBound (normalizeForFactor f).squareFreeCore B
        (choosePrimeData (normalizeForFactor f).squareFreeCore))
      ?_ factor hmem
    intro c hc
    exact exhaustiveCoreFactorsWithBound_normalizeFactorSign
      (normalizeForFactor f).squareFreeCore B
      (choosePrimeData (normalizeForFactor f).squareFreeCore)
      (squareFreeCore_normalizeFactorSign_of_ne_zero f hf) c hc
  · unfold factorSlowFactorsWithBound
    rw [if_neg hdeg]
    rw [hquad]
    intro factor hmem
    refine reassemblePolynomialFactors_shouldRecord_of_ne_zero f hf
      (exhaustiveCoreFactorsWithBound (normalizeForFactor f).squareFreeCore B
        (choosePrimeData (normalizeForFactor f).squareFreeCore))
      ?_ factor hmem
    intro c hc
    exact exhaustiveCoreFactorsWithBound_shouldRecord
      (normalizeForFactor f).squareFreeCore B
      (choosePrimeData (normalizeForFactor f).squareFreeCore)
      (squareFreeCore_shouldRecord_of_degree_pos f hf hdeg) c hc

private theorem factorSlowWithBound_product
    (f : ZPoly) (B : Nat) :
    Factorization.product (factorSlowWithBound f B) = f := by
  by_cases hf : f = 0
  · subst f
    unfold factorSlowWithBound
    exact factorizationOfFactors_product_of_zero (factorSlowFactorsWithBound 0 B)
  · by_cases hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
    · exact factorSlowWithBound_product_of_constant_branch f B hf hdeg
    · cases hquad :
        quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore with
      | some coreFactors =>
          exact factorSlowWithBound_product_of_quadratic_branch
            f B hf hdeg coreFactors hquad
      | none =>
          exact factorSlowWithBound_product_of_exhaustive_branch
            f B hf hdeg hquad

private theorem factorFastFactorsWithBound_product_of_some_of_all_recorded_normalized
    {f : ZPoly} {B : Nat} {factors : Array ZPoly}
    (hfast : factorFastFactorsWithBound f B = some factors)
    (hnormalized :
      ∀ factor ∈ factors.toList, normalizeFactorSign factor = factor)
    (hrecorded :
      ∀ factor ∈ factors.toList, shouldRecordPolynomialFactor factor = true) :
    Factorization.product (factorizationOfFactors f factors) = f :=
  factorizationOfFactors_product_of_raw_product_of_all_recorded_normalized
    f factors (factorFastFactorsWithBound_polyProduct_of_some hfast)
    hnormalized hrecorded

private theorem factorFastWithBound_product_of_constant_branch
    (f : ZPoly) (B : Nat) {φ : Factorization}
    (hf : f ≠ 0)
    (hbranch : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0)
    (h : factorFastWithBound f B = some φ) :
    Factorization.product φ = f := by
  unfold factorFastWithBound factorFastFactorsWithBound at h
  rw [if_pos hbranch] at h
  have hphi :
      factorizationOfFactors f
          (reassemblePolynomialFactors (normalizeForFactor f)
            #[(normalizeForFactor f).squareFreeCore]) = φ := by
    simpa using h
  rw [← hphi]
  have hcore_one := squareFreeCore_eq_one_of_constant_of_ne_zero f hf hbranch
  rw [hcore_one]
  apply factorizationOfFactors_product_of_filtered_product
  · exact reassemblePolynomialFactors_product_eq_input f #[1] (by
      rw [ZPoly.polyProduct_singleton]
      exact hcore_one.symm)
  · rw [reassemblePolynomialFactors_singleton_one_eq]
    rw [polyProduct_filteredNormalizedFactors_append_one_of_all_recorded_normalized]
    rw [ZPoly.polyProduct_append, ZPoly.polyProduct_singleton]
    exact (DensePoly.mul_one_right_poly (S := Int) _).symm
    · intro factor hmem
      exact polynomialNormalizationPrefixFactors_normalizeFactorSign_of_ne_zero
        f hf factor hmem
    · intro factor hmem
      exact polynomialNormalizationPrefixFactors_shouldRecord_of_ne_zero
        f hf factor hmem

private theorem factorFastWithBound_product_of_squareFreeCore_emit
    (f : ZPoly) (B : Nat) {factors : Array ZPoly}
    (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hfast : factorFastFactorsWithBound f B =
      some (reassemblePolynomialFactors (normalizeForFactor f)
        #[(normalizeForFactor f).squareFreeCore]))
    (hresult : factors = reassemblePolynomialFactors (normalizeForFactor f)
      #[(normalizeForFactor f).squareFreeCore]) :
    Factorization.product (factorizationOfFactors f factors) = f := by
  subst hresult
  apply factorFastFactorsWithBound_product_of_some_of_all_recorded_normalized hfast
  · intro factor hmem
    refine reassemblePolynomialFactors_normalizeFactorSign_of_ne_zero f hf
      #[(normalizeForFactor f).squareFreeCore] ?_ factor hmem
    intro c hc
    have hc' : c = (normalizeForFactor f).squareFreeCore := by
      simpa using hc
    rw [hc']
    exact squareFreeCore_normalizeFactorSign_of_ne_zero f hf
  · intro factor hmem
    refine reassemblePolynomialFactors_shouldRecord_of_ne_zero f hf
      #[(normalizeForFactor f).squareFreeCore] ?_ factor hmem
    intro c hc
    have hc' : c = (normalizeForFactor f).squareFreeCore := by
      simpa using hc
    rw [hc']
    exact squareFreeCore_shouldRecord_of_degree_pos f hf hdeg

private theorem factorFastWithBound_product_of_small_mod_branch
    (f : ZPoly) (B : Nat) {φ : Factorization}
    (primeData : PrimeChoiceData)
    (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hB_pos : 1 ≤ B)
    (hchoose :
      choosePrimeData? (normalizeForFactor f).squareFreeCore = some primeData)
    (hsmall : primeData.factorsModP.size ≤ 1)
    (hquadratic : B = 1 ∨
      quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none)
    (h : factorFastWithBound f B = some φ) :
    Factorization.product φ = f := by
  have hfast :
      factorFastFactorsWithBound f B =
        some (reassemblePolynomialFactors (normalizeForFactor f)
          #[(normalizeForFactor f).squareFreeCore]) := by
    unfold factorFastFactorsWithBound
    rw [if_neg hdeg, if_neg (by omega : B ≠ 0)]
    by_cases hB1 : B = 1
    · rw [if_pos hB1]
      simp [hchoose, hsmall]
    · rw [if_neg hB1]
      have hq : quadraticIntegerRootFactors?
          (normalizeForFactor f).squareFreeCore = none := by
        cases hquadratic with
        | inl heq => exact absurd heq hB1
        | inr hnone => exact hnone
      rw [hq]
      simp [hchoose, hsmall]
  have hphi :
      factorizationOfFactors f
          (reassemblePolynomialFactors (normalizeForFactor f)
            #[(normalizeForFactor f).squareFreeCore]) = φ := by
    rw [factorFastWithBound_eq_some_of_factors_some f B hfast] at h
    exact Option.some.inj h
  rw [← hphi]
  exact factorFastWithBound_product_of_squareFreeCore_emit f B hf hdeg hfast rfl

private theorem factorFastWithBound_product_of_quadratic_branch
    (f : ZPoly) (B : Nat) {φ : Factorization}
    (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hB_ge_two : 2 ≤ B)
    (coreFactors : Array ZPoly)
    (hquad : quadraticIntegerRootFactors?
      (normalizeForFactor f).squareFreeCore = some coreFactors)
    (h : factorFastWithBound f B = some φ) :
    Factorization.product φ = f := by
  have hfast :
      factorFastFactorsWithBound f B =
        some (reassemblePolynomialFactors (normalizeForFactor f) coreFactors) := by
    unfold factorFastFactorsWithBound
    rw [if_neg hdeg, if_neg (by omega : B ≠ 0), if_neg (by omega : B ≠ 1)]
    rw [hquad]
  have hphi :
      factorizationOfFactors f
          (reassemblePolynomialFactors (normalizeForFactor f) coreFactors) = φ := by
    rw [factorFastWithBound_eq_some_of_factors_some f B hfast] at h
    exact Option.some.inj h
  rw [← hphi]
  apply factorFastFactorsWithBound_product_of_some_of_all_recorded_normalized hfast
  · intro factor hmem
    refine reassemblePolynomialFactors_normalizeFactorSign_of_ne_zero f hf
      coreFactors ?_ factor hmem
    intro c hc
    exact quadraticIntegerRootFactors?_normalizeFactorSign
      (squareFreeCore_leadingCoeff_pos_of_ne_zero f hf) hquad c hc
  · intro factor hmem
    refine reassemblePolynomialFactors_shouldRecord_of_ne_zero f hf
      coreFactors ?_ factor hmem
    intro c hc
    exact quadraticIntegerRootFactors?_shouldRecord
      (squareFreeCore_leadingCoeff_pos_of_ne_zero f hf) hquad c hc

/-- Inner kernel for `_product_of_core_success_branch`. Takes the
`factorFastFactorsWithBound` success witness `hfast` directly after the
caller has threaded the explicit `choosePrimeData? = some primeData`
witness through the fast-path dispatcher. The per-factor normalisation /
recording facts go through `factorFastCoreWithBound_some_*`. -/
private theorem factorFastWithBound_product_of_factorFastFactorsWithBound_some_core
    (f : ZPoly) (B : Nat) {φ : Factorization}
    (primeData : PrimeChoiceData)
    (hf : f ≠ 0)
    (coreFactors : Array ZPoly)
    (hfast :
      factorFastFactorsWithBound f B =
        some (reassemblePolynomialFactors (normalizeForFactor f) coreFactors))
    (hcore :
      let a := precisionForCoeffBound B primeData.p
      factorFastCoreWithBound (normalizeForFactor f).squareFreeCore a
        primeData (initialHenselPrecision a)
        (ZPoly.quadraticDoublingSteps a + 2) = some coreFactors)
    (h : factorFastWithBound f B = some φ) :
    Factorization.product φ = f := by
  have hphi :
      factorizationOfFactors f
          (reassemblePolynomialFactors (normalizeForFactor f) coreFactors) = φ := by
    rw [factorFastWithBound_eq_some_of_factors_some f B hfast] at h
    exact Option.some.inj h
  rw [← hphi]
  apply factorFastFactorsWithBound_product_of_some_of_all_recorded_normalized hfast
  · intro factor hmem
    refine reassemblePolynomialFactors_normalizeFactorSign_of_ne_zero f hf
      coreFactors ?_ factor hmem
    intro c hc
    exact
      factorFastCoreWithBound_some_normalizeFactorSign
        (core := (normalizeForFactor f).squareFreeCore)
        (B := precisionForCoeffBound B primeData.p)
        (primeData := primeData)
        (k := initialHenselPrecision (precisionForCoeffBound B primeData.p))
        (fuel := ZPoly.quadraticDoublingSteps
          (precisionForCoeffBound B primeData.p) + 2)
        (coreFactors := coreFactors)
        hcore c hc
  · intro factor hmem
    refine reassemblePolynomialFactors_shouldRecord_of_ne_zero f hf
      coreFactors ?_ factor hmem
    intro c hc
    exact
      factorFastCoreWithBound_some_shouldRecord
        (core := (normalizeForFactor f).squareFreeCore)
        (B := precisionForCoeffBound B primeData.p)
        (primeData := primeData)
        (k := initialHenselPrecision (precisionForCoeffBound B primeData.p))
        (fuel := ZPoly.quadraticDoublingSteps
          (precisionForCoeffBound B primeData.p) + 2)
        (coreFactors := coreFactors)
        hcore c hc

private theorem factorFastWithBound_product_of_core_success_branch
    (f : ZPoly) (B : Nat) {φ : Factorization}
    (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hB_pos : 1 ≤ B)
    (primeData : PrimeChoiceData)
    (hchoose :
      choosePrimeData? (normalizeForFactor f).squareFreeCore = some primeData)
    (hnotsingleton :
      ¬ primeData.factorsModP.size ≤ 1)
    (hquadratic : B = 1 ∨
      quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none)
    (coreFactors : Array ZPoly)
    (hcore :
      let a := precisionForCoeffBound B primeData.p
      factorFastCoreWithBound (normalizeForFactor f).squareFreeCore a
        primeData (initialHenselPrecision a)
        (ZPoly.quadraticDoublingSteps a + 2) = some coreFactors)
    (h : factorFastWithBound f B = some φ) :
    Factorization.product φ = f := by
  have hfast :
      factorFastFactorsWithBound f B =
        some (reassemblePolynomialFactors (normalizeForFactor f) coreFactors) :=
    factorFastFactorsWithBound_eq_some_of_core_success
      f B primeData coreFactors hB_pos hchoose hdeg hnotsingleton hquadratic hcore
  exact factorFastWithBound_product_of_factorFastFactorsWithBound_some_core
    f B primeData hf coreFactors hfast hcore h

private theorem factorFastWithBound_product_of_some
    {f : ZPoly} {B : Nat} {φ : Factorization}
    (h : factorFastWithBound f B = some φ) :
    Factorization.product φ = f := by
  by_cases hf : f = 0
  · subst f
    unfold factorFastWithBound at h
    cases hfast : factorFastFactorsWithBound 0 B with
    | none =>
        rw [hfast] at h
        simp at h
    | some factors =>
        rw [hfast] at h
        change some (factorizationOfFactors 0 factors) = some φ at h
        rw [← Option.some.inj h]
        exact factorizationOfFactors_product_of_zero factors
  · by_cases hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
    · exact factorFastWithBound_product_of_constant_branch f B hf hdeg h
    · by_cases hB0 : B = 0
      · subst B
        unfold factorFastWithBound factorFastFactorsWithBound at h
        rw [if_neg hdeg] at h
        simp at h
      · have hB_pos : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB0
        by_cases hB1 : B = 1
        · -- B = 1: dispatch on choosePrimeData? and small-mod predicate
          subst B
          match hc : choosePrimeData? (normalizeForFactor f).squareFreeCore with
          | some primeData =>
              by_cases hsmall : primeData.factorsModP.size ≤ 1
              · exact factorFastWithBound_product_of_small_mod_branch
                  f 1 primeData hf hdeg hB_pos hc hsmall (Or.inl rfl) h
              · cases hcore :
                    factorFastCoreWithBound (normalizeForFactor f).squareFreeCore
                      (precisionForCoeffBound 1 primeData.p)
                      primeData
                      (initialHenselPrecision
                        (precisionForCoeffBound 1 primeData.p))
                      (ZPoly.quadraticDoublingSteps
                        (precisionForCoeffBound 1 primeData.p) + 2) with
                | none =>
                    exfalso
                    have hfast_none : factorFastFactorsWithBound f 1 = none := by
                      unfold factorFastFactorsWithBound
                      rw [if_neg hdeg, if_neg (show (1 : Nat) ≠ 0 by omega),
                          if_pos rfl]
                      simp [hc, hsmall, hcore]
                    unfold factorFastWithBound at h
                    rw [hfast_none] at h
                    simp at h
                | some coreFactors =>
                    have hnotsingleton :
                        ¬ primeData.factorsModP.size ≤ 1 := hsmall
                    exact factorFastWithBound_product_of_core_success_branch
                      f 1 hf hdeg hB_pos primeData hc
                      hnotsingleton (Or.inl rfl) coreFactors hcore h
          | none =>
              exfalso
              have hfast_none : factorFastFactorsWithBound f 1 = none := by
                unfold factorFastFactorsWithBound
                rw [if_neg hdeg, if_neg (show (1 : Nat) ≠ 0 by omega),
                    if_pos rfl]
                simp [hc]
              unfold factorFastWithBound at h
              rw [hfast_none] at h
              simp at h
        · -- B > 1
          have hB_ge_two : 2 ≤ B := by omega
          cases hquadNone :
              quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore with
          | some coreFactors =>
              exact factorFastWithBound_product_of_quadratic_branch
                f B hf hdeg hB_ge_two coreFactors hquadNone h
          | none =>
          match hc : choosePrimeData? (normalizeForFactor f).squareFreeCore with
          | some primeData =>
              by_cases hsmall : primeData.factorsModP.size ≤ 1
              · exact factorFastWithBound_product_of_small_mod_branch
                  f B primeData hf hdeg hB_pos hc hsmall (Or.inr hquadNone) h
              · cases hcore :
                    factorFastCoreWithBound (normalizeForFactor f).squareFreeCore
                      (precisionForCoeffBound B primeData.p)
                      primeData
                      (initialHenselPrecision
                        (precisionForCoeffBound B primeData.p))
                      (ZPoly.quadraticDoublingSteps
                        (precisionForCoeffBound B primeData.p) + 2) with
                | none =>
                    exfalso
                    have hfast_none : factorFastFactorsWithBound f B = none := by
                      unfold factorFastFactorsWithBound
                      have hB1 : B ≠ 1 := by omega
                      rw [if_neg hdeg, if_neg hB0, if_neg hB1, hquadNone]
                      simp [hc, hsmall, hcore]
                    unfold factorFastWithBound at h
                    rw [hfast_none] at h
                    simp at h
                | some coreFactors =>
                    have hnotsingleton :
                        ¬ primeData.factorsModP.size ≤ 1 := hsmall
                    exact factorFastWithBound_product_of_core_success_branch
                      f B hf hdeg hB_pos primeData hc
                      hnotsingleton (Or.inr hquadNone) coreFactors hcore h
          | none =>
              exfalso
              have hfast_none : factorFastFactorsWithBound f B = none := by
                unfold factorFastFactorsWithBound
                have hB1 : B ≠ 1 := by omega
                rw [if_neg hdeg, if_neg hB0, if_neg hB1, hquadNone]
                simp [hc]
              unfold factorFastWithBound at h
              rw [hfast_none] at h
              simp at h

/-- Product contract for the public slow-path backstop. -/
theorem factorSlow_product (f : ZPoly) :
    Factorization.product (factorSlow f) = f := by
  exact factorSlowWithBound_product f (ZPoly.defaultFactorCoeffBound f)

theorem factorSlowTrialFactorsWithBound_polyProduct
    (f : ZPoly) (B : Nat) :
    DensePoly.C (signedContentScalar f) *
      Array.polyProduct (factorSlowTrialFactorsWithBound f B) = f := by
  unfold factorSlowTrialFactorsWithBound
  by_cases hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · simp only [hdeg, if_true]
    exact reassemblePolynomialFactors_product_eq_input f
      #[(normalizeForFactor f).squareFreeCore] (by simp [Array.polyProduct])
  · simp only [hdeg, if_false]
    cases hquad : quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore with
    | some coreFactors =>
        exact reassemblePolynomialFactors_product_eq_input f coreFactors
          (quadraticIntegerRootFactors?_product hquad)
    | none =>
        exact reassemblePolynomialFactors_product_eq_input f
          (exhaustiveIntegerTrialCoreFactorsWithBound
            (normalizeForFactor f).squareFreeCore B)
          (exhaustiveIntegerTrialCoreFactorsWithBound_polyProduct
            (normalizeForFactor f).squareFreeCore B)

private theorem factorSlowTrialWithBound_product_of_all_recorded_normalized
    (f : ZPoly) (B : Nat)
    (hnormalized :
      ∀ factor ∈ (factorSlowTrialFactorsWithBound f B).toList,
        normalizeFactorSign factor = factor)
    (hrecorded :
      ∀ factor ∈ (factorSlowTrialFactorsWithBound f B).toList,
        shouldRecordPolynomialFactor factor = true) :
    Factorization.product (factorSlowTrialWithBound f B) = f := by
  unfold factorSlowTrialWithBound
  exact
    factorizationOfFactors_product_of_raw_product_of_all_recorded_normalized
      f (factorSlowTrialFactorsWithBound f B)
      (factorSlowTrialFactorsWithBound_polyProduct f B) hnormalized hrecorded

private theorem factorSlowTrialWithBound_product_of_constant_branch
    (f : ZPoly) (B : Nat)
    (hf : f ≠ 0)
    (hbranch : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0) :
    Factorization.product (factorSlowTrialWithBound f B) = f := by
  unfold factorSlowTrialWithBound factorSlowTrialFactorsWithBound
  rw [if_pos hbranch]
  have hcore_one := squareFreeCore_eq_one_of_constant_of_ne_zero f hf hbranch
  rw [hcore_one]
  apply factorizationOfFactors_product_of_filtered_product
  · exact reassemblePolynomialFactors_product_eq_input f #[1] (by
      rw [ZPoly.polyProduct_singleton]
      exact hcore_one.symm)
  · rw [reassemblePolynomialFactors_singleton_one_eq]
    rw [polyProduct_filteredNormalizedFactors_append_one_of_all_recorded_normalized]
    rw [ZPoly.polyProduct_append, ZPoly.polyProduct_singleton]
    exact (DensePoly.mul_one_right_poly (S := Int) _).symm
    · intro factor hmem
      exact polynomialNormalizationPrefixFactors_normalizeFactorSign_of_ne_zero
        f hf factor hmem
    · intro factor hmem
      exact polynomialNormalizationPrefixFactors_shouldRecord_of_ne_zero
        f hf factor hmem

private theorem factorSlowTrialWithBound_product_of_quadratic_branch
    (f : ZPoly) (B : Nat)
    (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (coreFactors : Array ZPoly)
    (hquad : quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore =
      some coreFactors) :
    Factorization.product (factorSlowTrialWithBound f B) = f := by
  apply factorSlowTrialWithBound_product_of_all_recorded_normalized
  · unfold factorSlowTrialFactorsWithBound
    rw [if_neg hdeg]
    rw [hquad]
    intro factor hmem
    refine reassemblePolynomialFactors_normalizeFactorSign_of_ne_zero f hf
      coreFactors ?_ factor hmem
    intro c hc
    exact quadraticIntegerRootFactors?_normalizeFactorSign
      (squareFreeCore_leadingCoeff_pos_of_ne_zero f hf) hquad c hc
  · unfold factorSlowTrialFactorsWithBound
    rw [if_neg hdeg]
    rw [hquad]
    intro factor hmem
    refine reassemblePolynomialFactors_shouldRecord_of_ne_zero f hf
      coreFactors ?_ factor hmem
    intro c hc
    exact quadraticIntegerRootFactors?_shouldRecord
      (squareFreeCore_leadingCoeff_pos_of_ne_zero f hf) hquad c hc

private theorem factorSlowTrialWithBound_product_of_trial_branch
    (f : ZPoly) (B : Nat)
    (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hquad : quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none) :
    Factorization.product (factorSlowTrialWithBound f B) = f := by
  apply factorSlowTrialWithBound_product_of_all_recorded_normalized
  · unfold factorSlowTrialFactorsWithBound
    rw [if_neg hdeg]
    rw [hquad]
    intro factor hmem
    refine reassemblePolynomialFactors_normalizeFactorSign_of_ne_zero f hf
      (exhaustiveIntegerTrialCoreFactorsWithBound
        (normalizeForFactor f).squareFreeCore B)
      ?_ factor hmem
    intro c hc
    exact exhaustiveIntegerTrialCoreFactorsWithBound_normalizeFactorSign
      (normalizeForFactor f).squareFreeCore B
      (squareFreeCore_leadingCoeff_pos_of_ne_zero f hf) c hc
  · unfold factorSlowTrialFactorsWithBound
    rw [if_neg hdeg]
    rw [hquad]
    intro factor hmem
    refine reassemblePolynomialFactors_shouldRecord_of_ne_zero f hf
      (exhaustiveIntegerTrialCoreFactorsWithBound
        (normalizeForFactor f).squareFreeCore B)
      ?_ factor hmem
    intro c hc
    exact exhaustiveIntegerTrialCoreFactorsWithBound_shouldRecord
      (normalizeForFactor f).squareFreeCore B
      (squareFreeCore_leadingCoeff_pos_of_ne_zero f hf) c hc

theorem factorSlowTrialWithBound_product (f : ZPoly) (B : Nat) :
    Factorization.product (factorSlowTrialWithBound f B) = f := by
  by_cases hf : f = 0
  · subst f
    unfold factorSlowTrialWithBound
    exact factorizationOfFactors_product_of_zero (factorSlowTrialFactorsWithBound 0 B)
  · by_cases hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
    · exact factorSlowTrialWithBound_product_of_constant_branch f B hf hdeg
    · cases hquad :
        quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore with
      | some coreFactors =>
          exact factorSlowTrialWithBound_product_of_quadratic_branch
            f B hf hdeg coreFactors hquad
      | none =>
          exact factorSlowTrialWithBound_product_of_trial_branch
            f B hf hdeg hquad

/-- Product contract for the public trial-division slow-path entry point. -/
theorem factorSlowTrial_product (f : ZPoly) :
    Factorization.product (factorSlowTrial f) = f := by
  exact factorSlowTrialWithBound_product f (ZPoly.defaultFactorCoeffBound f)

/--
Product contract for the bounded factorization entry point.
-/
theorem factorWithBound_product (f : ZPoly) (B : Nat) :
    Factorization.product (factorWithBound f B) = f := by
  unfold factorWithBound
  cases hfast : factorFastWithBound f B with
  | some φ =>
      exact factorFastWithBound_product_of_some hfast
  | none =>
      cases hmod : factorSlowModularWithBound f B with
      | some φ =>
          rw [factorSlowModularWithBound_eq_some_eq_factorSlowWithBound hmod]
          exact factorSlowWithBound_product f B
      | none =>
          exact factorSlowTrialWithBound_product f B

/-- Product contract for the public fast path whenever it returns a
certificate. -/
theorem factorFast_product_of_some
    {f : ZPoly} {φ : Factorization}
    (h : factorFast f = some φ) :
    Factorization.product φ = f := by
  exact factorFastWithBound_product_of_some h

/-- Product contract for the public total factorization entry point. -/
theorem factor_product (f : ZPoly) :
    Factorization.product (factor f) = f := by
  exact factorWithBound_product f (ZPoly.defaultFactorCoeffBound f)

/-- Product preservation for the Option-returning bounded API on its successful
branch. The `none` branch is the explicit no-admissible-prime surface; when a
certificate is returned, it is exactly the total bounded factorization. -/
theorem factorWithBound?_product_of_some
    {f : ZPoly} {B : Nat} {φ : Factorization}
    (h : factorWithBound? f B = some φ) :
    Factorization.product φ = f := by
  rw [factorWithBound?_eq_some_iff_safe_branch] at h
  by_cases hsafe :
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0 ∨
        (quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore).isSome ∨
        (choosePrimeData? (normalizeForFactor f).squareFreeCore).isSome
  · rw [if_pos hsafe] at h
    cases h
    exact factorWithBound_product f B
  · rw [if_neg hsafe] at h
    cases h

/-- Product preservation for the Option-returning default API on its successful
branch. This is the proof-facing contract for callers that choose to propagate
no-admissible-prime failure instead of consuming the total fallback. -/
theorem factor?_product_of_some
    {f : ZPoly} {φ : Factorization}
    (h : factor? f = some φ) :
    Factorization.product φ = f := by
  exact factorWithBound?_product_of_some h

/-- A successful `factorWithBound?` result is exactly the total bounded
factorization. The `none` branch is the explicit no-admissible-prime surface;
on `some`, all total-API contracts can be transported to the returned record. -/
theorem factorWithBound?_eq_some_eq_factorWithBound
    {f : ZPoly} {B : Nat} {φ : Factorization}
    (h : factorWithBound? f B = some φ) :
    φ = factorWithBound f B := by
  rw [factorWithBound?_eq_some_iff_safe_branch] at h
  by_cases hsafe :
      (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0 ∨
        (quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore).isSome ∨
        (choosePrimeData? (normalizeForFactor f).squareFreeCore).isSome
  · rw [if_pos hsafe] at h
    exact (Option.some.inj h).symm
  · rw [if_neg hsafe] at h
    cases h

/-- A successful `factor?` result is exactly the total default factorization. -/
theorem factor?_eq_some_eq_factor
    {f : ZPoly} {φ : Factorization}
    (h : factor? f = some φ) :
    φ = factor f := by
  unfold factor? at h
  simpa [factor_eq_factorWithBound_default] using
    factorWithBound?_eq_some_eq_factorWithBound h

/-- Scalar contract for the Option-returning bounded API on its successful
branch. -/
theorem factorWithBound?_scalar_of_some
    {f : ZPoly} {B : Nat} {φ : Factorization}
    (h : factorWithBound? f B = some φ) :
    φ.scalar =
      if f = 0 then
        0
      else if DensePoly.leadingCoeff f < 0 then
        -ZPoly.content f
      else
        ZPoly.content f := by
  rw [factorWithBound?_eq_some_eq_factorWithBound h]
  exact factorWithBound_scalar f B

/-- Scalar contract for the Option-returning default API on its successful
branch. -/
theorem factor?_scalar_of_some
    {f : ZPoly} {φ : Factorization}
    (h : factor? f = some φ) :
    φ.scalar =
      if f = 0 then
        0
      else if DensePoly.leadingCoeff f < 0 then
        -ZPoly.content f
      else
        ZPoly.content f := by
  rw [factor?_eq_some_eq_factor h]
  exact factor_scalar f

/-- Every entry emitted by a successful `factorWithBound?` call has positive
multiplicity. -/
theorem factorWithBound?_entry_multiplicity_pos_of_some
    {f : ZPoly} {B : Nat} {φ : Factorization}
    (h : factorWithBound? f B = some φ)
    (entry : ZPoly × Nat)
    (hmem : entry ∈ φ.factors.toList) :
    0 < entry.2 := by
  rw [factorWithBound?_eq_some_eq_factorWithBound h] at hmem
  exact factorWithBound_entry_multiplicity_pos f B entry hmem

/-- Every entry emitted by a successful `factor?` call has positive
multiplicity. -/
theorem factor?_entry_multiplicity_pos_of_some
    {f : ZPoly} {φ : Factorization}
    (h : factor? f = some φ)
    (entry : ZPoly × Nat)
    (hmem : entry ∈ φ.factors.toList) :
    0 < entry.2 := by
  rw [factor?_eq_some_eq_factor h] at hmem
  exact factor_entry_multiplicity_pos f entry hmem

/-- Entries emitted by a successful `factorWithBound?` call are sign-normalized. -/
theorem factorWithBound?_entry_normalizeFactorSign_id_of_some
    {f : ZPoly} {B : Nat} {φ : Factorization}
    (h : factorWithBound? f B = some φ)
    (entry : ZPoly × Nat)
    (hmem : entry ∈ φ.factors.toList) :
    normalizeFactorSign entry.1 = entry.1 := by
  rw [factorWithBound?_eq_some_eq_factorWithBound h] at hmem
  exact factorWithBound_entry_normalizeFactorSign_id f B entry hmem

/-- Entries emitted by a successful `factor?` call are sign-normalized. -/
theorem factor?_entry_normalizeFactorSign_id_of_some
    {f : ZPoly} {φ : Factorization}
    (h : factor? f = some φ)
    (entry : ZPoly × Nat)
    (hmem : entry ∈ φ.factors.toList) :
    normalizeFactorSign entry.1 = entry.1 := by
  rw [factor?_eq_some_eq_factor h] at hmem
  exact factor_entry_normalizeFactorSign_id f entry hmem

/-- Entries emitted by a successful `factorWithBound?` call have positive
leading coefficient. -/
theorem factorWithBound?_entry_leadingCoeff_pos_of_some
    {f : ZPoly} {B : Nat} {φ : Factorization}
    (h : factorWithBound? f B = some φ)
    (entry : ZPoly × Nat)
    (hmem : entry ∈ φ.factors.toList) :
    0 < DensePoly.leadingCoeff entry.1 := by
  rw [factorWithBound?_eq_some_eq_factorWithBound h] at hmem
  exact factorWithBound_entry_leadingCoeff_pos f B entry hmem

/-- Entries emitted by a successful `factor?` call have positive leading
coefficient. -/
theorem factor?_entry_leadingCoeff_pos_of_some
    {f : ZPoly} {φ : Factorization}
    (h : factor? f = some φ)
    (entry : ZPoly × Nat)
    (hmem : entry ∈ φ.factors.toList) :
    0 < DensePoly.leadingCoeff entry.1 := by
  rw [factor?_eq_some_eq_factor h] at hmem
  exact factor_entry_leadingCoeff_pos f entry hmem

/-- Entries emitted by a successful `factorWithBound?` call pass the executable
recording filter. -/
theorem factorWithBound?_entry_shouldRecord_of_some
    {f : ZPoly} {B : Nat} {φ : Factorization}
    (h : factorWithBound? f B = some φ)
    (entry : ZPoly × Nat)
    (hmem : entry ∈ φ.factors.toList) :
    shouldRecordPolynomialFactor entry.1 = true := by
  rw [factorWithBound?_eq_some_eq_factorWithBound h] at hmem
  exact factorWithBound_entry_shouldRecord f B entry hmem

/-- Entries emitted by a successful `factor?` call pass the executable
recording filter. -/
theorem factor?_entry_shouldRecord_of_some
    {f : ZPoly} {φ : Factorization}
    (h : factor? f = some φ)
    (entry : ZPoly × Nat)
    (hmem : entry ∈ φ.factors.toList) :
    shouldRecordPolynomialFactor entry.1 = true := by
  rw [factor?_eq_some_eq_factor h] at hmem
  exact factor_entry_shouldRecord f entry hmem

/-- A successful `factorWithBound?` result has no duplicate polynomial keys. -/
theorem factorWithBound?_pairwise_first_of_some
    {f : ZPoly} {B : Nat} {φ : Factorization}
    (h : factorWithBound? f B = some φ) :
    List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1) φ.factors.toList := by
  rw [factorWithBound?_eq_some_eq_factorWithBound h]
  exact factorWithBound_pairwise_first f B

/-- A successful `factor?` result has no duplicate polynomial keys. -/
theorem factor?_pairwise_first_of_some
    {f : ZPoly} {φ : Factorization}
    (h : factor? f = some φ) :
    List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1) φ.factors.toList := by
  rw [factor?_eq_some_eq_factor h]
  exact factor_pairwise_first f

/--
A successful integer certificate exposes the per-prime polynomial check fact:
every recorded `PrimeFactorData` block satisfies `checkForPolynomial f` —
admissible prime, positive recorded factor degrees, modular degree-sum and
factor-product alignment, and aligned nested Rabin certificates. Callers
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
