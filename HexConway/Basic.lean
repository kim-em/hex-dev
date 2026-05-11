import HexBerlekamp.RabinSoundness
import HexGfqRing.Basic

/-!
Tier 1 Conway-polynomial lookup support for `hex-conway`.

This module exposes the committed imported-table lookup
`luebeckConwayPolynomial?`, keeping the baseline Tier 1 story separate
from later Tier 2 Conway-compatibility proofs and Tier 3 search.
-/
namespace Hex

namespace Conway

instance : ZMod64.Bounds 2 := ⟨by decide, by decide⟩
instance : ZMod64.Bounds 3 := ⟨by decide, by decide⟩
instance : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
instance : ZMod64.Bounds 7 := ⟨by decide, by decide⟩
instance : ZMod64.Bounds 11 := ⟨by decide, by decide⟩
instance : ZMod64.Bounds 13 := ⟨by decide, by decide⟩

/-- Committed Lübeck Conway-table coefficients, stored ascending by degree. -/
def luebeckConwayCoeffs? : Nat → Nat → Option (List Nat)
  | 2, 1 => some [1, 1]
  | 2, 2 => some [1, 1, 1]
  | 2, 3 => some [1, 1, 0, 1]
  | 2, 4 => some [1, 1, 0, 0, 1]
  | 2, 5 => some [1, 0, 1, 0, 0, 1]
  | 2, 6 => some [1, 1, 0, 1, 1, 0, 1]
  | 3, 1 => some [1, 1]
  | 3, 2 => some [2, 2, 1]
  | 3, 3 => some [1, 2, 0, 1]
  | 3, 4 => some [2, 0, 0, 2, 1]
  | 3, 5 => some [1, 2, 0, 0, 0, 1]
  | 3, 6 => some [2, 2, 1, 0, 2, 0, 1]
  | 5, 1 => some [3, 1]
  | 5, 2 => some [2, 4, 1]
  | 5, 3 => some [3, 3, 0, 1]
  | 5, 4 => some [2, 4, 4, 0, 1]
  | 5, 5 => some [3, 4, 0, 0, 0, 1]
  | 5, 6 => some [2, 0, 1, 4, 1, 0, 1]
  | 7, 1 => some [4, 1]
  | 7, 2 => some [3, 6, 1]
  | 7, 3 => some [4, 0, 6, 1]
  | 7, 4 => some [3, 4, 5, 0, 1]
  | 7, 5 => some [4, 1, 0, 0, 0, 1]
  | 7, 6 => some [3, 6, 4, 5, 1, 0, 1]
  | 11, 1 => some [9, 1]
  | 11, 2 => some [2, 7, 1]
  | 11, 3 => some [9, 2, 0, 1]
  | 11, 4 => some [2, 10, 8, 0, 1]
  | 11, 5 => some [9, 0, 10, 0, 0, 1]
  | 11, 6 => some [2, 7, 6, 4, 3, 0, 1]
  | 13, 1 => some [11, 1]
  | 13, 2 => some [2, 12, 1]
  | 13, 3 => some [11, 2, 0, 1]
  | 13, 4 => some [2, 12, 3, 0, 1]
  | 13, 5 => some [11, 4, 0, 0, 0, 1]
  | 13, 6 => some [2, 11, 11, 10, 0, 0, 1]
  | _, _ => none

/-- Build an `FpPoly p` from ascending natural-number coefficients. -/
def luebeckConwayPolynomialOfCoeffs
    (p : Nat) [ZMod64.Bounds p] (coeffs : List Nat) : FpPoly p :=
  FpPoly.ofCoeffs (coeffs.toArray.map (fun n => ZMod64.ofNat p n))

private theorem one_ne_zero_two : (1 : ZMod64 2) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 2) 1 0).mp h
  simp at hm

/-- The committed Conway entry `C(2, 1) = X + 1` from the imported
Luebeck table.

Defined directly as a record literal (rather than via
`luebeckConwayPolynomialOfCoeffs`) so that `Monic` reduces to `rfl`
and `degree` reduces to `decide`; the Bench file uses the same idiom
for the higher-degree entries. -/
def luebeckConwayPolynomial_2_1 : FpPoly 2 :=
  { coeffs := #[(1 : ZMod64 2), 1]
    normalized := by
      right
      simpa using one_ne_zero_two }

/-- Tier 1 imported-table lookup for committed Luebeck Conway entries. -/
def luebeckConwayPolynomial? (p n : Nat) [ZMod64.Bounds p] : Option (FpPoly p) :=
  (luebeckConwayCoeffs? p n).map (luebeckConwayPolynomialOfCoeffs p)

@[simp] theorem luebeckConwayPolynomial?_hit_2_1 :
    luebeckConwayPolynomial? 2 1 = some luebeckConwayPolynomial_2_1 := by
  show some (luebeckConwayPolynomialOfCoeffs 2 [1, 1]) = some luebeckConwayPolynomial_2_1
  congr 1
  apply DensePoly.ext_coeff
  intro n
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 2 [1, 1]) n =
        ([1, 1].toArray.map (fun k => ZMod64.ofNat 2 k)).getD n
          (Zero.zero : ZMod64 2) from
      DensePoly.coeff_ofCoeffs _ n]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_2_1]
  match n with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

@[simp] theorem luebeckConwayPolynomial?_miss_two_zero :
    luebeckConwayPolynomial? 2 0 = (none : Option (FpPoly 2)) :=
  rfl

/-- The committed `C(2, 1)` entry is monic, so it can be fed to the
executable Rabin checker. -/
theorem luebeckConwayPolynomial_2_1_monic :
    DensePoly.Monic luebeckConwayPolynomial_2_1 := by
  rfl

/-- The committed `C(2, 1)` entry has positive degree. -/
theorem luebeckConwayPolynomial_2_1_degree_pos :
    0 < FpPoly.degree luebeckConwayPolynomial_2_1 := by
  decide

private theorem prime_two : Hex.Nat.Prime 2 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · exact Or.inr rfl

instance instPrimeModulusTwo : ZMod64.PrimeModulus 2 :=
  ZMod64.primeModulusOfPrime prime_two

private theorem prime_three : Hex.Nat.Prime 3 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 3 := Nat.le_of_dvd (by decide : 0 < 3) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · exact Or.inr rfl

instance instPrimeModulus3 : ZMod64.PrimeModulus 3 :=
  ZMod64.primeModulusOfPrime prime_three

private theorem prime_five : Hex.Nat.Prime 5 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

instance instPrimeModulus5 : ZMod64.PrimeModulus 5 :=
  ZMod64.primeModulusOfPrime prime_five

private theorem prime_seven : Hex.Nat.Prime 7 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 7 := Nat.le_of_dvd (by decide : 0 < 7) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

instance instPrimeModulus7 : ZMod64.PrimeModulus 7 :=
  ZMod64.primeModulusOfPrime prime_seven

private theorem prime_eleven : Hex.Nat.Prime 11 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 11 := Nat.le_of_dvd (by decide : 0 < 11) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

instance instPrimeModulus11 : ZMod64.PrimeModulus 11 :=
  ZMod64.primeModulusOfPrime prime_eleven

private theorem prime_thirteen : Hex.Nat.Prime 13 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 13 := Nat.le_of_dvd (by decide : 0 < 13) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 ∨ m = 12 ∨ m = 13 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

instance instPrimeModulus13 : ZMod64.PrimeModulus 13 :=
  ZMod64.primeModulusOfPrime prime_thirteen

/-- Certificate for `C(2, 1) = X + 1`: degree-1 monic with no maximal proper
divisors of `n = 1`, so `bezout` is empty. The pow-chain stores
`X^(2^0) mod (X+1) = 1` and `X^(2^1) mod (X+1) = 1`. -/
private def cert_2_1 : Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 1
  powChain := #[FpPoly.ofCoeffs #[(1 : ZMod64 2)], FpPoly.ofCoeffs #[(1 : ZMod64 2)]]
  bezout := #[]

set_option maxRecDepth 4096 in
private theorem cert_2_1_linear_check :
    Berlekamp.checkIrreducibilityCertificateLinear
        luebeckConwayPolynomial_2_1 luebeckConwayPolynomial_2_1_monic cert_2_1 = true := by
  decide

/-- The committed `C(2, 1)` entry is irreducible. -/
theorem luebeckConwayPolynomial_2_1_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_2_1 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_2_1
    luebeckConwayPolynomial_2_1_monic
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      luebeckConwayPolynomial_2_1 luebeckConwayPolynomial_2_1_monic cert_2_1
      cert_2_1_linear_check)

/-- The committed `C(2, 2)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_2_2 : FpPoly 2 :=
  { coeffs := #[(1 : ZMod64 2), 1, 1]
    normalized := by
      right
      decide }

/-- The committed `C(2, 2)` entry is monic. -/
theorem luebeckConwayPolynomial_2_2_monic :
    DensePoly.Monic luebeckConwayPolynomial_2_2 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_2_2 :
    luebeckConwayPolynomial? 2 2 = some luebeckConwayPolynomial_2_2 := by
  show some (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 1]) = some luebeckConwayPolynomial_2_2
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 1]) k =
        ([1, 1, 1].toArray.map (fun m => ZMod64.ofNat 2 m)).getD k
          (Zero.zero : ZMod64 2) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_2_2]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

/-- The committed `C(2, 3)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_2_3 : FpPoly 2 :=
  { coeffs := #[(1 : ZMod64 2), 1, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(2, 3)` entry is monic. -/
theorem luebeckConwayPolynomial_2_3_monic :
    DensePoly.Monic luebeckConwayPolynomial_2_3 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_2_3 :
    luebeckConwayPolynomial? 2 3 = some luebeckConwayPolynomial_2_3 := by
  show some (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1]) = some luebeckConwayPolynomial_2_3
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1]) k =
        ([1, 1, 0, 1].toArray.map (fun m => ZMod64.ofNat 2 m)).getD k
          (Zero.zero : ZMod64 2) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_2_3]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

/-- The committed `C(2, 4)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_2_4 : FpPoly 2 :=
  { coeffs := #[(1 : ZMod64 2), 1, 0, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(2, 4)` entry is monic. -/
theorem luebeckConwayPolynomial_2_4_monic :
    DensePoly.Monic luebeckConwayPolynomial_2_4 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_2_4 :
    luebeckConwayPolynomial? 2 4 = some luebeckConwayPolynomial_2_4 := by
  show some (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 0, 1]) = some luebeckConwayPolynomial_2_4
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 0, 1]) k =
        ([1, 1, 0, 0, 1].toArray.map (fun m => ZMod64.ofNat 2 m)).getD k
          (Zero.zero : ZMod64 2) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_2_4]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | _ + 5 => rfl

/-- The committed `C(2, 5)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_2_5 : FpPoly 2 :=
  { coeffs := #[(1 : ZMod64 2), 0, 1, 0, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(2, 5)` entry is monic. -/
theorem luebeckConwayPolynomial_2_5_monic :
    DensePoly.Monic luebeckConwayPolynomial_2_5 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_2_5 :
    luebeckConwayPolynomial? 2 5 = some luebeckConwayPolynomial_2_5 := by
  show some (luebeckConwayPolynomialOfCoeffs 2 [1, 0, 1, 0, 0, 1]) = some luebeckConwayPolynomial_2_5
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 2 [1, 0, 1, 0, 0, 1]) k =
        ([1, 0, 1, 0, 0, 1].toArray.map (fun m => ZMod64.ofNat 2 m)).getD k
          (Zero.zero : ZMod64 2) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_2_5]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | _ + 6 => rfl

/-- The committed `C(2, 6)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_2_6 : FpPoly 2 :=
  { coeffs := #[(1 : ZMod64 2), 1, 0, 1, 1, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(2, 6)` entry is monic. -/
theorem luebeckConwayPolynomial_2_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_2_6 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_2_6 :
    luebeckConwayPolynomial? 2 6 = some luebeckConwayPolynomial_2_6 := by
  show some (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1, 1, 0, 1]) = some luebeckConwayPolynomial_2_6
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1, 1, 0, 1]) k =
        ([1, 1, 0, 1, 1, 0, 1].toArray.map (fun m => ZMod64.ofNat 2 m)).getD k
          (Zero.zero : ZMod64 2) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_2_6]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | _ + 7 => rfl

/-- The committed `C(3, 1)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_3_1 : FpPoly 3 :=
  { coeffs := #[(1 : ZMod64 3), 1]
    normalized := by
      right
      decide }

/-- The committed `C(3, 1)` entry is monic. -/
theorem luebeckConwayPolynomial_3_1_monic :
    DensePoly.Monic luebeckConwayPolynomial_3_1 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_3_1 :
    luebeckConwayPolynomial? 3 1 = some luebeckConwayPolynomial_3_1 := by
  show some (luebeckConwayPolynomialOfCoeffs 3 [1, 1]) = some luebeckConwayPolynomial_3_1
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 3 [1, 1]) k =
        ([1, 1].toArray.map (fun m => ZMod64.ofNat 3 m)).getD k
          (Zero.zero : ZMod64 3) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_3_1]
  match k with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- The committed `C(3, 2)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_3_2 : FpPoly 3 :=
  { coeffs := #[(2 : ZMod64 3), 2, 1]
    normalized := by
      right
      decide }

/-- The committed `C(3, 2)` entry is monic. -/
theorem luebeckConwayPolynomial_3_2_monic :
    DensePoly.Monic luebeckConwayPolynomial_3_2 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_3_2 :
    luebeckConwayPolynomial? 3 2 = some luebeckConwayPolynomial_3_2 := by
  show some (luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1]) = some luebeckConwayPolynomial_3_2
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1]) k =
        ([2, 2, 1].toArray.map (fun m => ZMod64.ofNat 3 m)).getD k
          (Zero.zero : ZMod64 3) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_3_2]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

/-- The committed `C(3, 3)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_3_3 : FpPoly 3 :=
  { coeffs := #[(1 : ZMod64 3), 2, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(3, 3)` entry is monic. -/
theorem luebeckConwayPolynomial_3_3_monic :
    DensePoly.Monic luebeckConwayPolynomial_3_3 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_3_3 :
    luebeckConwayPolynomial? 3 3 = some luebeckConwayPolynomial_3_3 := by
  show some (luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 1]) = some luebeckConwayPolynomial_3_3
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 1]) k =
        ([1, 2, 0, 1].toArray.map (fun m => ZMod64.ofNat 3 m)).getD k
          (Zero.zero : ZMod64 3) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_3_3]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

/-- The committed `C(3, 4)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_3_4 : FpPoly 3 :=
  { coeffs := #[(2 : ZMod64 3), 0, 0, 2, 1]
    normalized := by
      right
      decide }

/-- The committed `C(3, 4)` entry is monic. -/
theorem luebeckConwayPolynomial_3_4_monic :
    DensePoly.Monic luebeckConwayPolynomial_3_4 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_3_4 :
    luebeckConwayPolynomial? 3 4 = some luebeckConwayPolynomial_3_4 := by
  show some (luebeckConwayPolynomialOfCoeffs 3 [2, 0, 0, 2, 1]) = some luebeckConwayPolynomial_3_4
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 3 [2, 0, 0, 2, 1]) k =
        ([2, 0, 0, 2, 1].toArray.map (fun m => ZMod64.ofNat 3 m)).getD k
          (Zero.zero : ZMod64 3) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_3_4]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | _ + 5 => rfl

/-- The committed `C(3, 5)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_3_5 : FpPoly 3 :=
  { coeffs := #[(1 : ZMod64 3), 2, 0, 0, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(3, 5)` entry is monic. -/
theorem luebeckConwayPolynomial_3_5_monic :
    DensePoly.Monic luebeckConwayPolynomial_3_5 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_3_5 :
    luebeckConwayPolynomial? 3 5 = some luebeckConwayPolynomial_3_5 := by
  show some (luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 0, 0, 1]) = some luebeckConwayPolynomial_3_5
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 0, 0, 1]) k =
        ([1, 2, 0, 0, 0, 1].toArray.map (fun m => ZMod64.ofNat 3 m)).getD k
          (Zero.zero : ZMod64 3) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_3_5]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | _ + 6 => rfl

/-- The committed `C(3, 6)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_3_6 : FpPoly 3 :=
  { coeffs := #[(2 : ZMod64 3), 2, 1, 0, 2, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(3, 6)` entry is monic. -/
theorem luebeckConwayPolynomial_3_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_3_6 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_3_6 :
    luebeckConwayPolynomial? 3 6 = some luebeckConwayPolynomial_3_6 := by
  show some (luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1, 0, 2, 0, 1]) = some luebeckConwayPolynomial_3_6
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1, 0, 2, 0, 1]) k =
        ([2, 2, 1, 0, 2, 0, 1].toArray.map (fun m => ZMod64.ofNat 3 m)).getD k
          (Zero.zero : ZMod64 3) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_3_6]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | _ + 7 => rfl

/-- The committed `C(5, 1)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_5_1 : FpPoly 5 :=
  { coeffs := #[(3 : ZMod64 5), 1]
    normalized := by
      right
      decide }

/-- The committed `C(5, 1)` entry is monic. -/
theorem luebeckConwayPolynomial_5_1_monic :
    DensePoly.Monic luebeckConwayPolynomial_5_1 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_5_1 :
    luebeckConwayPolynomial? 5 1 = some luebeckConwayPolynomial_5_1 := by
  show some (luebeckConwayPolynomialOfCoeffs 5 [3, 1]) = some luebeckConwayPolynomial_5_1
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 5 [3, 1]) k =
        ([3, 1].toArray.map (fun m => ZMod64.ofNat 5 m)).getD k
          (Zero.zero : ZMod64 5) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_5_1]
  match k with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- The committed `C(5, 2)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_5_2 : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 4, 1]
    normalized := by
      right
      decide }

/-- The committed `C(5, 2)` entry is monic. -/
theorem luebeckConwayPolynomial_5_2_monic :
    DensePoly.Monic luebeckConwayPolynomial_5_2 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_5_2 :
    luebeckConwayPolynomial? 5 2 = some luebeckConwayPolynomial_5_2 := by
  show some (luebeckConwayPolynomialOfCoeffs 5 [2, 4, 1]) = some luebeckConwayPolynomial_5_2
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 5 [2, 4, 1]) k =
        ([2, 4, 1].toArray.map (fun m => ZMod64.ofNat 5 m)).getD k
          (Zero.zero : ZMod64 5) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_5_2]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

/-- The committed `C(5, 3)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_5_3 : FpPoly 5 :=
  { coeffs := #[(3 : ZMod64 5), 3, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(5, 3)` entry is monic. -/
theorem luebeckConwayPolynomial_5_3_monic :
    DensePoly.Monic luebeckConwayPolynomial_5_3 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_5_3 :
    luebeckConwayPolynomial? 5 3 = some luebeckConwayPolynomial_5_3 := by
  show some (luebeckConwayPolynomialOfCoeffs 5 [3, 3, 0, 1]) = some luebeckConwayPolynomial_5_3
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 5 [3, 3, 0, 1]) k =
        ([3, 3, 0, 1].toArray.map (fun m => ZMod64.ofNat 5 m)).getD k
          (Zero.zero : ZMod64 5) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_5_3]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

/-- The committed `C(5, 4)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_5_4 : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 4, 4, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(5, 4)` entry is monic. -/
theorem luebeckConwayPolynomial_5_4_monic :
    DensePoly.Monic luebeckConwayPolynomial_5_4 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_5_4 :
    luebeckConwayPolynomial? 5 4 = some luebeckConwayPolynomial_5_4 := by
  show some (luebeckConwayPolynomialOfCoeffs 5 [2, 4, 4, 0, 1]) = some luebeckConwayPolynomial_5_4
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 5 [2, 4, 4, 0, 1]) k =
        ([2, 4, 4, 0, 1].toArray.map (fun m => ZMod64.ofNat 5 m)).getD k
          (Zero.zero : ZMod64 5) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_5_4]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | _ + 5 => rfl

/-- The committed `C(5, 5)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_5_5 : FpPoly 5 :=
  { coeffs := #[(3 : ZMod64 5), 4, 0, 0, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(5, 5)` entry is monic. -/
theorem luebeckConwayPolynomial_5_5_monic :
    DensePoly.Monic luebeckConwayPolynomial_5_5 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_5_5 :
    luebeckConwayPolynomial? 5 5 = some luebeckConwayPolynomial_5_5 := by
  show some (luebeckConwayPolynomialOfCoeffs 5 [3, 4, 0, 0, 0, 1]) = some luebeckConwayPolynomial_5_5
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 5 [3, 4, 0, 0, 0, 1]) k =
        ([3, 4, 0, 0, 0, 1].toArray.map (fun m => ZMod64.ofNat 5 m)).getD k
          (Zero.zero : ZMod64 5) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_5_5]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | _ + 6 => rfl

/-- The committed `C(5, 6)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_5_6 : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 1, 4, 1, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(5, 6)` entry is monic. -/
theorem luebeckConwayPolynomial_5_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_5_6 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_5_6 :
    luebeckConwayPolynomial? 5 6 = some luebeckConwayPolynomial_5_6 := by
  show some (luebeckConwayPolynomialOfCoeffs 5 [2, 0, 1, 4, 1, 0, 1]) = some luebeckConwayPolynomial_5_6
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 5 [2, 0, 1, 4, 1, 0, 1]) k =
        ([2, 0, 1, 4, 1, 0, 1].toArray.map (fun m => ZMod64.ofNat 5 m)).getD k
          (Zero.zero : ZMod64 5) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_5_6]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | _ + 7 => rfl

/-- The committed `C(7, 1)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_7_1 : FpPoly 7 :=
  { coeffs := #[(4 : ZMod64 7), 1]
    normalized := by
      right
      decide }

/-- The committed `C(7, 1)` entry is monic. -/
theorem luebeckConwayPolynomial_7_1_monic :
    DensePoly.Monic luebeckConwayPolynomial_7_1 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_7_1 :
    luebeckConwayPolynomial? 7 1 = some luebeckConwayPolynomial_7_1 := by
  show some (luebeckConwayPolynomialOfCoeffs 7 [4, 1]) = some luebeckConwayPolynomial_7_1
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 7 [4, 1]) k =
        ([4, 1].toArray.map (fun m => ZMod64.ofNat 7 m)).getD k
          (Zero.zero : ZMod64 7) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_7_1]
  match k with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- The committed `C(7, 2)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_7_2 : FpPoly 7 :=
  { coeffs := #[(3 : ZMod64 7), 6, 1]
    normalized := by
      right
      decide }

/-- The committed `C(7, 2)` entry is monic. -/
theorem luebeckConwayPolynomial_7_2_monic :
    DensePoly.Monic luebeckConwayPolynomial_7_2 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_7_2 :
    luebeckConwayPolynomial? 7 2 = some luebeckConwayPolynomial_7_2 := by
  show some (luebeckConwayPolynomialOfCoeffs 7 [3, 6, 1]) = some luebeckConwayPolynomial_7_2
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 7 [3, 6, 1]) k =
        ([3, 6, 1].toArray.map (fun m => ZMod64.ofNat 7 m)).getD k
          (Zero.zero : ZMod64 7) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_7_2]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

/-- The committed `C(7, 3)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_7_3 : FpPoly 7 :=
  { coeffs := #[(4 : ZMod64 7), 0, 6, 1]
    normalized := by
      right
      decide }

/-- The committed `C(7, 3)` entry is monic. -/
theorem luebeckConwayPolynomial_7_3_monic :
    DensePoly.Monic luebeckConwayPolynomial_7_3 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_7_3 :
    luebeckConwayPolynomial? 7 3 = some luebeckConwayPolynomial_7_3 := by
  show some (luebeckConwayPolynomialOfCoeffs 7 [4, 0, 6, 1]) = some luebeckConwayPolynomial_7_3
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 7 [4, 0, 6, 1]) k =
        ([4, 0, 6, 1].toArray.map (fun m => ZMod64.ofNat 7 m)).getD k
          (Zero.zero : ZMod64 7) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_7_3]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

/-- The committed `C(7, 4)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_7_4 : FpPoly 7 :=
  { coeffs := #[(3 : ZMod64 7), 4, 5, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(7, 4)` entry is monic. -/
theorem luebeckConwayPolynomial_7_4_monic :
    DensePoly.Monic luebeckConwayPolynomial_7_4 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_7_4 :
    luebeckConwayPolynomial? 7 4 = some luebeckConwayPolynomial_7_4 := by
  show some (luebeckConwayPolynomialOfCoeffs 7 [3, 4, 5, 0, 1]) = some luebeckConwayPolynomial_7_4
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 7 [3, 4, 5, 0, 1]) k =
        ([3, 4, 5, 0, 1].toArray.map (fun m => ZMod64.ofNat 7 m)).getD k
          (Zero.zero : ZMod64 7) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_7_4]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | _ + 5 => rfl

/-- The committed `C(7, 5)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_7_5 : FpPoly 7 :=
  { coeffs := #[(4 : ZMod64 7), 1, 0, 0, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(7, 5)` entry is monic. -/
theorem luebeckConwayPolynomial_7_5_monic :
    DensePoly.Monic luebeckConwayPolynomial_7_5 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_7_5 :
    luebeckConwayPolynomial? 7 5 = some luebeckConwayPolynomial_7_5 := by
  show some (luebeckConwayPolynomialOfCoeffs 7 [4, 1, 0, 0, 0, 1]) = some luebeckConwayPolynomial_7_5
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 7 [4, 1, 0, 0, 0, 1]) k =
        ([4, 1, 0, 0, 0, 1].toArray.map (fun m => ZMod64.ofNat 7 m)).getD k
          (Zero.zero : ZMod64 7) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_7_5]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | _ + 6 => rfl

/-- The committed `C(7, 6)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_7_6 : FpPoly 7 :=
  { coeffs := #[(3 : ZMod64 7), 6, 4, 5, 1, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(7, 6)` entry is monic. -/
theorem luebeckConwayPolynomial_7_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_7_6 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_7_6 :
    luebeckConwayPolynomial? 7 6 = some luebeckConwayPolynomial_7_6 := by
  show some (luebeckConwayPolynomialOfCoeffs 7 [3, 6, 4, 5, 1, 0, 1]) = some luebeckConwayPolynomial_7_6
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 7 [3, 6, 4, 5, 1, 0, 1]) k =
        ([3, 6, 4, 5, 1, 0, 1].toArray.map (fun m => ZMod64.ofNat 7 m)).getD k
          (Zero.zero : ZMod64 7) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_7_6]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | _ + 7 => rfl

/-- The committed `C(11, 1)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_11_1 : FpPoly 11 :=
  { coeffs := #[(9 : ZMod64 11), 1]
    normalized := by
      right
      decide }

/-- The committed `C(11, 1)` entry is monic. -/
theorem luebeckConwayPolynomial_11_1_monic :
    DensePoly.Monic luebeckConwayPolynomial_11_1 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_11_1 :
    luebeckConwayPolynomial? 11 1 = some luebeckConwayPolynomial_11_1 := by
  show some (luebeckConwayPolynomialOfCoeffs 11 [9, 1]) = some luebeckConwayPolynomial_11_1
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 11 [9, 1]) k =
        ([9, 1].toArray.map (fun m => ZMod64.ofNat 11 m)).getD k
          (Zero.zero : ZMod64 11) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_11_1]
  match k with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- The committed `C(11, 2)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_11_2 : FpPoly 11 :=
  { coeffs := #[(2 : ZMod64 11), 7, 1]
    normalized := by
      right
      decide }

/-- The committed `C(11, 2)` entry is monic. -/
theorem luebeckConwayPolynomial_11_2_monic :
    DensePoly.Monic luebeckConwayPolynomial_11_2 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_11_2 :
    luebeckConwayPolynomial? 11 2 = some luebeckConwayPolynomial_11_2 := by
  show some (luebeckConwayPolynomialOfCoeffs 11 [2, 7, 1]) = some luebeckConwayPolynomial_11_2
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 11 [2, 7, 1]) k =
        ([2, 7, 1].toArray.map (fun m => ZMod64.ofNat 11 m)).getD k
          (Zero.zero : ZMod64 11) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_11_2]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

/-- The committed `C(11, 3)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_11_3 : FpPoly 11 :=
  { coeffs := #[(9 : ZMod64 11), 2, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(11, 3)` entry is monic. -/
theorem luebeckConwayPolynomial_11_3_monic :
    DensePoly.Monic luebeckConwayPolynomial_11_3 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_11_3 :
    luebeckConwayPolynomial? 11 3 = some luebeckConwayPolynomial_11_3 := by
  show some (luebeckConwayPolynomialOfCoeffs 11 [9, 2, 0, 1]) = some luebeckConwayPolynomial_11_3
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 11 [9, 2, 0, 1]) k =
        ([9, 2, 0, 1].toArray.map (fun m => ZMod64.ofNat 11 m)).getD k
          (Zero.zero : ZMod64 11) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_11_3]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

/-- The committed `C(11, 4)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_11_4 : FpPoly 11 :=
  { coeffs := #[(2 : ZMod64 11), 10, 8, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(11, 4)` entry is monic. -/
theorem luebeckConwayPolynomial_11_4_monic :
    DensePoly.Monic luebeckConwayPolynomial_11_4 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_11_4 :
    luebeckConwayPolynomial? 11 4 = some luebeckConwayPolynomial_11_4 := by
  show some (luebeckConwayPolynomialOfCoeffs 11 [2, 10, 8, 0, 1]) = some luebeckConwayPolynomial_11_4
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 11 [2, 10, 8, 0, 1]) k =
        ([2, 10, 8, 0, 1].toArray.map (fun m => ZMod64.ofNat 11 m)).getD k
          (Zero.zero : ZMod64 11) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_11_4]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | _ + 5 => rfl

/-- The committed `C(11, 5)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_11_5 : FpPoly 11 :=
  { coeffs := #[(9 : ZMod64 11), 0, 10, 0, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(11, 5)` entry is monic. -/
theorem luebeckConwayPolynomial_11_5_monic :
    DensePoly.Monic luebeckConwayPolynomial_11_5 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_11_5 :
    luebeckConwayPolynomial? 11 5 = some luebeckConwayPolynomial_11_5 := by
  show some (luebeckConwayPolynomialOfCoeffs 11 [9, 0, 10, 0, 0, 1]) = some luebeckConwayPolynomial_11_5
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 11 [9, 0, 10, 0, 0, 1]) k =
        ([9, 0, 10, 0, 0, 1].toArray.map (fun m => ZMod64.ofNat 11 m)).getD k
          (Zero.zero : ZMod64 11) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_11_5]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | _ + 6 => rfl

/-- The committed `C(11, 6)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_11_6 : FpPoly 11 :=
  { coeffs := #[(2 : ZMod64 11), 7, 6, 4, 3, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(11, 6)` entry is monic. -/
theorem luebeckConwayPolynomial_11_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_11_6 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_11_6 :
    luebeckConwayPolynomial? 11 6 = some luebeckConwayPolynomial_11_6 := by
  show some (luebeckConwayPolynomialOfCoeffs 11 [2, 7, 6, 4, 3, 0, 1]) = some luebeckConwayPolynomial_11_6
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 11 [2, 7, 6, 4, 3, 0, 1]) k =
        ([2, 7, 6, 4, 3, 0, 1].toArray.map (fun m => ZMod64.ofNat 11 m)).getD k
          (Zero.zero : ZMod64 11) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_11_6]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | _ + 7 => rfl

/-- The committed `C(13, 1)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_13_1 : FpPoly 13 :=
  { coeffs := #[(11 : ZMod64 13), 1]
    normalized := by
      right
      decide }

/-- The committed `C(13, 1)` entry is monic. -/
theorem luebeckConwayPolynomial_13_1_monic :
    DensePoly.Monic luebeckConwayPolynomial_13_1 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_13_1 :
    luebeckConwayPolynomial? 13 1 = some luebeckConwayPolynomial_13_1 := by
  show some (luebeckConwayPolynomialOfCoeffs 13 [11, 1]) = some luebeckConwayPolynomial_13_1
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 13 [11, 1]) k =
        ([11, 1].toArray.map (fun m => ZMod64.ofNat 13 m)).getD k
          (Zero.zero : ZMod64 13) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_13_1]
  match k with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- The committed `C(13, 2)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_13_2 : FpPoly 13 :=
  { coeffs := #[(2 : ZMod64 13), 12, 1]
    normalized := by
      right
      decide }

/-- The committed `C(13, 2)` entry is monic. -/
theorem luebeckConwayPolynomial_13_2_monic :
    DensePoly.Monic luebeckConwayPolynomial_13_2 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_13_2 :
    luebeckConwayPolynomial? 13 2 = some luebeckConwayPolynomial_13_2 := by
  show some (luebeckConwayPolynomialOfCoeffs 13 [2, 12, 1]) = some luebeckConwayPolynomial_13_2
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 13 [2, 12, 1]) k =
        ([2, 12, 1].toArray.map (fun m => ZMod64.ofNat 13 m)).getD k
          (Zero.zero : ZMod64 13) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_13_2]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

/-- The committed `C(13, 3)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_13_3 : FpPoly 13 :=
  { coeffs := #[(11 : ZMod64 13), 2, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(13, 3)` entry is monic. -/
theorem luebeckConwayPolynomial_13_3_monic :
    DensePoly.Monic luebeckConwayPolynomial_13_3 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_13_3 :
    luebeckConwayPolynomial? 13 3 = some luebeckConwayPolynomial_13_3 := by
  show some (luebeckConwayPolynomialOfCoeffs 13 [11, 2, 0, 1]) = some luebeckConwayPolynomial_13_3
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 13 [11, 2, 0, 1]) k =
        ([11, 2, 0, 1].toArray.map (fun m => ZMod64.ofNat 13 m)).getD k
          (Zero.zero : ZMod64 13) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_13_3]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

/-- The committed `C(13, 4)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_13_4 : FpPoly 13 :=
  { coeffs := #[(2 : ZMod64 13), 12, 3, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(13, 4)` entry is monic. -/
theorem luebeckConwayPolynomial_13_4_monic :
    DensePoly.Monic luebeckConwayPolynomial_13_4 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_13_4 :
    luebeckConwayPolynomial? 13 4 = some luebeckConwayPolynomial_13_4 := by
  show some (luebeckConwayPolynomialOfCoeffs 13 [2, 12, 3, 0, 1]) = some luebeckConwayPolynomial_13_4
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 13 [2, 12, 3, 0, 1]) k =
        ([2, 12, 3, 0, 1].toArray.map (fun m => ZMod64.ofNat 13 m)).getD k
          (Zero.zero : ZMod64 13) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_13_4]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | _ + 5 => rfl

/-- The committed `C(13, 5)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_13_5 : FpPoly 13 :=
  { coeffs := #[(11 : ZMod64 13), 4, 0, 0, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(13, 5)` entry is monic. -/
theorem luebeckConwayPolynomial_13_5_monic :
    DensePoly.Monic luebeckConwayPolynomial_13_5 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_13_5 :
    luebeckConwayPolynomial? 13 5 = some luebeckConwayPolynomial_13_5 := by
  show some (luebeckConwayPolynomialOfCoeffs 13 [11, 4, 0, 0, 0, 1]) = some luebeckConwayPolynomial_13_5
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 13 [11, 4, 0, 0, 0, 1]) k =
        ([11, 4, 0, 0, 0, 1].toArray.map (fun m => ZMod64.ofNat 13 m)).getD k
          (Zero.zero : ZMod64 13) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_13_5]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | _ + 6 => rfl

/-- The committed `C(13, 6)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_13_6 : FpPoly 13 :=
  { coeffs := #[(2 : ZMod64 13), 11, 11, 10, 0, 0, 1]
    normalized := by
      right
      decide }

/-- The committed `C(13, 6)` entry is monic. -/
theorem luebeckConwayPolynomial_13_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_13_6 := by
  rfl

@[simp] theorem luebeckConwayPolynomial?_hit_13_6 :
    luebeckConwayPolynomial? 13 6 = some luebeckConwayPolynomial_13_6 := by
  show some (luebeckConwayPolynomialOfCoeffs 13 [2, 11, 11, 10, 0, 0, 1]) = some luebeckConwayPolynomial_13_6
  congr 1
  apply DensePoly.ext_coeff
  intro k
  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs 13 [2, 11, 11, 10, 0, 0, 1]) k =
        ([2, 11, 11, 10, 0, 0, 1].toArray.map (fun m => ZMod64.ofNat 13 m)).getD k
          (Zero.zero : ZMod64 13) from
      DensePoly.coeff_ofCoeffs _ k]
  simp [List.toArray, Array.map, DensePoly.coeff, luebeckConwayPolynomial_13_6]
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | _ + 7 => rfl

/-- Rabin irreducibility certificate for the committed `C(2, 2)` entry. -/
private def cert_2_2 : Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 2
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 2), 1], FpPoly.ofCoeffs #[(1 : ZMod64 2), 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs (#[] : Array (ZMod64 2)), right := FpPoly.ofCoeffs #[(1 : ZMod64 2)] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_2_2_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_2_2 luebeckConwayPolynomial_2_2_monic cert_2_2 = true := by
  decide

/-- The committed `C(2, 2)` entry is irreducible. -/
theorem luebeckConwayPolynomial_2_2_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_2_2 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_2_2
    luebeckConwayPolynomial_2_2_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_2_2 luebeckConwayPolynomial_2_2_monic cert_2_2 cert_2_2_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(2, 3)` entry. -/
private def cert_2_3 : Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 3
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 2), 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 0, 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 1, 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(1 : ZMod64 2)], right := FpPoly.ofCoeffs #[(1 : ZMod64 2), 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_2_3_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_2_3 luebeckConwayPolynomial_2_3_monic cert_2_3 = true := by
  decide

/-- The committed `C(2, 3)` entry is irreducible. -/
theorem luebeckConwayPolynomial_2_3_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_2_3 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_2_3
    luebeckConwayPolynomial_2_3_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_2_3 luebeckConwayPolynomial_2_3_monic cert_2_3 cert_2_3_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(2, 4)` entry. -/
private def cert_2_4 : Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 4
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 2), 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 0, 1], FpPoly.ofCoeffs #[(1 : ZMod64 2), 1], FpPoly.ofCoeffs #[(1 : ZMod64 2), 0, 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs (#[] : Array (ZMod64 2)), right := FpPoly.ofCoeffs #[(1 : ZMod64 2)] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_2_4_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_2_4 luebeckConwayPolynomial_2_4_monic cert_2_4 = true := by
  decide

/-- The committed `C(2, 4)` entry is irreducible. -/
theorem luebeckConwayPolynomial_2_4_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_2_4 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_2_4
    luebeckConwayPolynomial_2_4_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_2_4 luebeckConwayPolynomial_2_4_monic cert_2_4 cert_2_4_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(2, 5)` entry. -/
private def cert_2_5 : Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 5
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 2), 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 0, 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 0, 0, 0, 1], FpPoly.ofCoeffs #[(1 : ZMod64 2), 0, 1, 1], FpPoly.ofCoeffs #[(1 : ZMod64 2), 1, 0, 1, 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(1 : ZMod64 2)], right := FpPoly.ofCoeffs #[(0 : ZMod64 2), 1, 1, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_2_5_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_2_5 luebeckConwayPolynomial_2_5_monic cert_2_5 = true := by
  decide

/-- The committed `C(2, 5)` entry is irreducible. -/
theorem luebeckConwayPolynomial_2_5_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_2_5 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_2_5
    luebeckConwayPolynomial_2_5_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_2_5 luebeckConwayPolynomial_2_5_monic cert_2_5 cert_2_5_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(2, 6)` entry. -/
private def cert_2_6 : Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 6
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 2), 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 0, 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 0, 0, 0, 1], FpPoly.ofCoeffs #[(1 : ZMod64 2), 1, 1, 0, 1, 1], FpPoly.ofCoeffs #[(1 : ZMod64 2), 1, 0, 0, 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 1, 0, 0, 1, 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(1 : ZMod64 2)], right := FpPoly.ofCoeffs #[(1 : ZMod64 2), 0, 1] }, { left := FpPoly.ofCoeffs #[(1 : ZMod64 2), 0, 1, 1], right := FpPoly.ofCoeffs #[(0 : ZMod64 2), 1, 1, 0, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_2_6_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_2_6 luebeckConwayPolynomial_2_6_monic cert_2_6 = true := by
  decide

/-- The committed `C(2, 6)` entry is irreducible. -/
theorem luebeckConwayPolynomial_2_6_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_2_6 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_2_6
    luebeckConwayPolynomial_2_6_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_2_6 luebeckConwayPolynomial_2_6_monic cert_2_6 cert_2_6_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(3, 1)` entry. -/
private def cert_3_1 : Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 1
  powChain := #[FpPoly.ofCoeffs #[(2 : ZMod64 3)], FpPoly.ofCoeffs #[(2 : ZMod64 3)]]
  bezout := #[]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_3_1_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_3_1 luebeckConwayPolynomial_3_1_monic cert_3_1 = true := by
  decide

/-- The committed `C(3, 1)` entry is irreducible. -/
theorem luebeckConwayPolynomial_3_1_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_3_1 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_3_1
    luebeckConwayPolynomial_3_1_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_3_1 luebeckConwayPolynomial_3_1_monic cert_3_1 cert_3_1_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(3, 2)` entry. -/
private def cert_3_2 : Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 2
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 3), 1], FpPoly.ofCoeffs #[(1 : ZMod64 3), 2], FpPoly.ofCoeffs #[(0 : ZMod64 3), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(1 : ZMod64 3)], right := FpPoly.ofCoeffs #[(2 : ZMod64 3), 2] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_3_2_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_3_2 luebeckConwayPolynomial_3_2_monic cert_3_2 = true := by
  decide

/-- The committed `C(3, 2)` entry is irreducible. -/
theorem luebeckConwayPolynomial_3_2_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_3_2 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_3_2
    luebeckConwayPolynomial_3_2_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_3_2 luebeckConwayPolynomial_3_2_monic cert_3_2 cert_3_2_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(3, 3)` entry. -/
private def cert_3_3 : Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 3
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 3), 1], FpPoly.ofCoeffs #[(2 : ZMod64 3), 1], FpPoly.ofCoeffs #[(1 : ZMod64 3), 1], FpPoly.ofCoeffs #[(0 : ZMod64 3), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs (#[] : Array (ZMod64 3)), right := FpPoly.ofCoeffs #[(2 : ZMod64 3)] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_3_3_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_3_3 luebeckConwayPolynomial_3_3_monic cert_3_3 = true := by
  decide

/-- The committed `C(3, 3)` entry is irreducible. -/
theorem luebeckConwayPolynomial_3_3_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_3_3 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_3_3
    luebeckConwayPolynomial_3_3_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_3_3 luebeckConwayPolynomial_3_3_monic cert_3_3 cert_3_3_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(3, 4)` entry. -/
private def cert_3_4 : Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 4
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 3), 1], FpPoly.ofCoeffs #[(0 : ZMod64 3), 0, 0, 1], FpPoly.ofCoeffs #[(0 : ZMod64 3), 2, 1, 1], FpPoly.ofCoeffs #[(1 : ZMod64 3), 0, 2, 1], FpPoly.ofCoeffs #[(0 : ZMod64 3), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(2 : ZMod64 3), 1, 2], right := FpPoly.ofCoeffs #[(1 : ZMod64 3), 1, 0, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_3_4_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_3_4 luebeckConwayPolynomial_3_4_monic cert_3_4 = true := by
  decide

/-- The committed `C(3, 4)` entry is irreducible. -/
theorem luebeckConwayPolynomial_3_4_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_3_4 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_3_4
    luebeckConwayPolynomial_3_4_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_3_4 luebeckConwayPolynomial_3_4_monic cert_3_4 cert_3_4_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(3, 5)` entry. -/
private def cert_3_5 : Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 5
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 3), 1], FpPoly.ofCoeffs #[(0 : ZMod64 3), 0, 0, 1], FpPoly.ofCoeffs #[(2 : ZMod64 3), 1, 0, 0, 2], FpPoly.ofCoeffs #[(2 : ZMod64 3), 0, 2, 0, 2], FpPoly.ofCoeffs #[(2 : ZMod64 3), 1, 1, 2, 2], FpPoly.ofCoeffs #[(0 : ZMod64 3), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(1 : ZMod64 3)], right := FpPoly.ofCoeffs #[(2 : ZMod64 3), 0, 2] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_3_5_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_3_5 luebeckConwayPolynomial_3_5_monic cert_3_5 = true := by
  decide

/-- The committed `C(3, 5)` entry is irreducible. -/
theorem luebeckConwayPolynomial_3_5_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_3_5 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_3_5
    luebeckConwayPolynomial_3_5_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_3_5 luebeckConwayPolynomial_3_5_monic cert_3_5 cert_3_5_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(3, 6)` entry. -/
private def cert_3_6 : Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 6
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 3), 1], FpPoly.ofCoeffs #[(0 : ZMod64 3), 0, 0, 1], FpPoly.ofCoeffs #[(0 : ZMod64 3), 1, 1, 0, 1], FpPoly.ofCoeffs #[(1 : ZMod64 3), 2, 0, 0, 2, 2], FpPoly.ofCoeffs #[(0 : ZMod64 3), 0, 0, 2, 2, 2], FpPoly.ofCoeffs #[(2 : ZMod64 3), 2, 2, 0, 1, 2], FpPoly.ofCoeffs #[(0 : ZMod64 3), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(2 : ZMod64 3), 1, 1, 2], right := FpPoly.ofCoeffs #[(0 : ZMod64 3), 2, 0, 0, 2, 1] }, { left := FpPoly.ofCoeffs #[(1 : ZMod64 3), 2, 1, 0, 1], right := FpPoly.ofCoeffs #[(2 : ZMod64 3), 1, 1, 1, 2, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_3_6_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_3_6 luebeckConwayPolynomial_3_6_monic cert_3_6 = true := by
  decide

/-- The committed `C(3, 6)` entry is irreducible. -/
theorem luebeckConwayPolynomial_3_6_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_3_6 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_3_6
    luebeckConwayPolynomial_3_6_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_3_6 luebeckConwayPolynomial_3_6_monic cert_3_6 cert_3_6_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(5, 1)` entry. -/
private def cert_5_1 : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 1
  powChain := #[FpPoly.ofCoeffs #[(2 : ZMod64 5)], FpPoly.ofCoeffs #[(2 : ZMod64 5)]]
  bezout := #[]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_5_1_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_5_1 luebeckConwayPolynomial_5_1_monic cert_5_1 = true := by
  decide

/-- The committed `C(5, 1)` entry is irreducible. -/
theorem luebeckConwayPolynomial_5_1_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_5_1 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_5_1
    luebeckConwayPolynomial_5_1_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_5_1 luebeckConwayPolynomial_5_1_monic cert_5_1 cert_5_1_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(5, 2)` entry. -/
private def cert_5_2 : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 2
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 5), 1], FpPoly.ofCoeffs #[(1 : ZMod64 5), 4], FpPoly.ofCoeffs #[(0 : ZMod64 5), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(2 : ZMod64 5)], right := FpPoly.ofCoeffs #[(2 : ZMod64 5), 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_5_2_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_5_2 luebeckConwayPolynomial_5_2_monic cert_5_2 = true := by
  decide

/-- The committed `C(5, 2)` entry is irreducible. -/
theorem luebeckConwayPolynomial_5_2_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_5_2 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_5_2
    luebeckConwayPolynomial_5_2_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_5_2 luebeckConwayPolynomial_5_2_monic cert_5_2 cert_5_2_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(5, 3)` entry. -/
private def cert_5_3 : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 3
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 5), 1], FpPoly.ofCoeffs #[(4 : ZMod64 5), 4, 2], FpPoly.ofCoeffs #[(1 : ZMod64 5), 0, 3], FpPoly.ofCoeffs #[(0 : ZMod64 5), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(3 : ZMod64 5), 3], right := FpPoly.ofCoeffs #[(3 : ZMod64 5), 2, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_5_3_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_5_3 luebeckConwayPolynomial_5_3_monic cert_5_3 = true := by
  decide

/-- The committed `C(5, 3)` entry is irreducible. -/
theorem luebeckConwayPolynomial_5_3_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_5_3 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_5_3
    luebeckConwayPolynomial_5_3_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_5_3 luebeckConwayPolynomial_5_3_monic cert_5_3 cert_5_3_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(5, 4)` entry. -/
private def cert_5_4 : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 4
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 5), 1], FpPoly.ofCoeffs #[(0 : ZMod64 5), 3, 1, 1], FpPoly.ofCoeffs #[(0 : ZMod64 5), 0, 1, 1], FpPoly.ofCoeffs #[(0 : ZMod64 5), 1, 3, 3], FpPoly.ofCoeffs #[(0 : ZMod64 5), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(3 : ZMod64 5), 3, 1], right := FpPoly.ofCoeffs #[(3 : ZMod64 5), 4, 3, 4] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_5_4_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_5_4 luebeckConwayPolynomial_5_4_monic cert_5_4 = true := by
  decide

/-- The committed `C(5, 4)` entry is irreducible. -/
theorem luebeckConwayPolynomial_5_4_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_5_4 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_5_4
    luebeckConwayPolynomial_5_4_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_5_4 luebeckConwayPolynomial_5_4_monic cert_5_4 cert_5_4_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(5, 5)` entry. -/
private def cert_5_5 : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 5
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 5), 1], FpPoly.ofCoeffs #[(2 : ZMod64 5), 1], FpPoly.ofCoeffs #[(4 : ZMod64 5), 1], FpPoly.ofCoeffs #[(1 : ZMod64 5), 1], FpPoly.ofCoeffs #[(3 : ZMod64 5), 1], FpPoly.ofCoeffs #[(0 : ZMod64 5), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs (#[] : Array (ZMod64 5)), right := FpPoly.ofCoeffs #[(3 : ZMod64 5)] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_5_5_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_5_5 luebeckConwayPolynomial_5_5_monic cert_5_5 = true := by
  decide

/-- The committed `C(5, 5)` entry is irreducible. -/
theorem luebeckConwayPolynomial_5_5_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_5_5 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_5_5
    luebeckConwayPolynomial_5_5_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_5_5 luebeckConwayPolynomial_5_5_monic cert_5_5 cert_5_5_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(5, 6)` entry. -/
private def cert_5_6 : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 6
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 5), 1], FpPoly.ofCoeffs #[(0 : ZMod64 5), 0, 0, 0, 0, 1], FpPoly.ofCoeffs #[(4 : ZMod64 5), 4, 0, 3, 4, 2], FpPoly.ofCoeffs #[(3 : ZMod64 5), 0, 3, 2, 4, 1], FpPoly.ofCoeffs #[(1 : ZMod64 5), 0, 0, 2, 1, 3], FpPoly.ofCoeffs #[(2 : ZMod64 5), 0, 2, 3, 1, 3], FpPoly.ofCoeffs #[(0 : ZMod64 5), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(0 : ZMod64 5), 4, 0, 1, 1], right := FpPoly.ofCoeffs #[(4 : ZMod64 5), 0, 0, 3, 3, 2] }, { left := FpPoly.ofCoeffs #[(4 : ZMod64 5), 2, 1, 4, 3], right := FpPoly.ofCoeffs #[(1 : ZMod64 5), 4, 0, 0, 3, 2] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_5_6_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_5_6 luebeckConwayPolynomial_5_6_monic cert_5_6 = true := by
  decide

/-- The committed `C(5, 6)` entry is irreducible. -/
theorem luebeckConwayPolynomial_5_6_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_5_6 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_5_6
    luebeckConwayPolynomial_5_6_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_5_6 luebeckConwayPolynomial_5_6_monic cert_5_6 cert_5_6_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(7, 1)` entry. -/
private def cert_7_1 : Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 1
  powChain := #[FpPoly.ofCoeffs #[(3 : ZMod64 7)], FpPoly.ofCoeffs #[(3 : ZMod64 7)]]
  bezout := #[]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_7_1_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_7_1 luebeckConwayPolynomial_7_1_monic cert_7_1 = true := by
  decide

/-- The committed `C(7, 1)` entry is irreducible. -/
theorem luebeckConwayPolynomial_7_1_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_7_1 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_7_1
    luebeckConwayPolynomial_7_1_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_7_1 luebeckConwayPolynomial_7_1_monic cert_7_1 cert_7_1_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(7, 2)` entry. -/
private def cert_7_2 : Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 2
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 7), 1], FpPoly.ofCoeffs #[(1 : ZMod64 7), 6], FpPoly.ofCoeffs #[(0 : ZMod64 7), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(1 : ZMod64 7)], right := FpPoly.ofCoeffs #[(5 : ZMod64 7), 4] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_7_2_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_7_2 luebeckConwayPolynomial_7_2_monic cert_7_2 = true := by
  decide

/-- The committed `C(7, 2)` entry is irreducible. -/
theorem luebeckConwayPolynomial_7_2_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_7_2 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_7_2
    luebeckConwayPolynomial_7_2_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_7_2 luebeckConwayPolynomial_7_2_monic cert_7_2 cert_7_2_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(7, 3)` entry. -/
private def cert_7_3 : Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 3
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 7), 1], FpPoly.ofCoeffs #[(0 : ZMod64 7), 5, 3], FpPoly.ofCoeffs #[(1 : ZMod64 7), 1, 4], FpPoly.ofCoeffs #[(0 : ZMod64 7), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(2 : ZMod64 7)], right := FpPoly.ofCoeffs #[(0 : ZMod64 7), 4] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_7_3_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_7_3 luebeckConwayPolynomial_7_3_monic cert_7_3 = true := by
  decide

/-- The committed `C(7, 3)` entry is irreducible. -/
theorem luebeckConwayPolynomial_7_3_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_7_3 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_7_3
    luebeckConwayPolynomial_7_3_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_7_3 luebeckConwayPolynomial_7_3_monic cert_7_3 cert_7_3_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(7, 4)` entry. -/
private def cert_7_4 : Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 4
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 7), 1], FpPoly.ofCoeffs #[(5 : ZMod64 7), 3, 5, 1], FpPoly.ofCoeffs #[(0 : ZMod64 7), 0, 3, 1], FpPoly.ofCoeffs #[(2 : ZMod64 7), 3, 6, 5], FpPoly.ofCoeffs #[(0 : ZMod64 7), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(5 : ZMod64 7), 3, 5], right := FpPoly.ofCoeffs #[(1 : ZMod64 7), 6, 5, 2] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_7_4_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_7_4 luebeckConwayPolynomial_7_4_monic cert_7_4 = true := by
  decide

/-- The committed `C(7, 4)` entry is irreducible. -/
theorem luebeckConwayPolynomial_7_4_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_7_4 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_7_4
    luebeckConwayPolynomial_7_4_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_7_4 luebeckConwayPolynomial_7_4_monic cert_7_4 cert_7_4_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(7, 5)` entry. -/
private def cert_7_5 : Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 5
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 7), 1], FpPoly.ofCoeffs #[(0 : ZMod64 7), 0, 3, 6], FpPoly.ofCoeffs #[(6 : ZMod64 7), 3, 0, 2, 4], FpPoly.ofCoeffs #[(4 : ZMod64 7), 2, 4, 4, 5], FpPoly.ofCoeffs #[(4 : ZMod64 7), 1, 0, 2, 5], FpPoly.ofCoeffs #[(0 : ZMod64 7), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(2 : ZMod64 7)], right := FpPoly.ofCoeffs #[(2 : ZMod64 7), 6, 2] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_7_5_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_7_5 luebeckConwayPolynomial_7_5_monic cert_7_5 = true := by
  decide

/-- The committed `C(7, 5)` entry is irreducible. -/
theorem luebeckConwayPolynomial_7_5_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_7_5 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_7_5
    luebeckConwayPolynomial_7_5_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_7_5 luebeckConwayPolynomial_7_5_monic cert_7_5 cert_7_5_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(7, 6)` entry. -/
private def cert_7_6 : Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 6
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 7), 1], FpPoly.ofCoeffs #[(0 : ZMod64 7), 4, 1, 3, 2, 6], FpPoly.ofCoeffs #[(1 : ZMod64 7), 3, 4, 5, 5], FpPoly.ofCoeffs #[(6 : ZMod64 7), 4, 5, 6, 0, 4], FpPoly.ofCoeffs #[(3 : ZMod64 7), 2, 5, 0, 5, 3], FpPoly.ofCoeffs #[(4 : ZMod64 7), 0, 6, 0, 2, 1], FpPoly.ofCoeffs #[(0 : ZMod64 7), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(6 : ZMod64 7), 0, 2, 2], right := FpPoly.ofCoeffs #[(4 : ZMod64 7), 5, 0, 3, 0, 1] }, { left := FpPoly.ofCoeffs #[(1 : ZMod64 7), 1, 0, 2, 3], right := FpPoly.ofCoeffs #[(2 : ZMod64 7), 1, 2, 3, 3, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_7_6_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_7_6 luebeckConwayPolynomial_7_6_monic cert_7_6 = true := by
  decide

/-- The committed `C(7, 6)` entry is irreducible. -/
theorem luebeckConwayPolynomial_7_6_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_7_6 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_7_6
    luebeckConwayPolynomial_7_6_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_7_6 luebeckConwayPolynomial_7_6_monic cert_7_6 cert_7_6_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(11, 1)` entry. -/
private def cert_11_1 : Berlekamp.IrreducibilityCertificate where
  p := 11
  n := 1
  powChain := #[FpPoly.ofCoeffs #[(2 : ZMod64 11)], FpPoly.ofCoeffs #[(2 : ZMod64 11)]]
  bezout := #[]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_11_1_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_11_1 luebeckConwayPolynomial_11_1_monic cert_11_1 = true := by
  decide

/-- The committed `C(11, 1)` entry is irreducible. -/
theorem luebeckConwayPolynomial_11_1_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_11_1 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_11_1
    luebeckConwayPolynomial_11_1_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_11_1 luebeckConwayPolynomial_11_1_monic cert_11_1 cert_11_1_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(11, 2)` entry. -/
private def cert_11_2 : Berlekamp.IrreducibilityCertificate where
  p := 11
  n := 2
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 11), 1], FpPoly.ofCoeffs #[(4 : ZMod64 11), 10], FpPoly.ofCoeffs #[(0 : ZMod64 11), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(5 : ZMod64 11)], right := FpPoly.ofCoeffs #[(6 : ZMod64 11), 8] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_11_2_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_11_2 luebeckConwayPolynomial_11_2_monic cert_11_2 = true := by
  decide

/-- The committed `C(11, 2)` entry is irreducible. -/
theorem luebeckConwayPolynomial_11_2_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_11_2 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_11_2
    luebeckConwayPolynomial_11_2_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_11_2 luebeckConwayPolynomial_11_2_monic cert_11_2 cert_11_2_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(11, 3)` entry. -/
private def cert_11_3 : Berlekamp.IrreducibilityCertificate where
  p := 11
  n := 3
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 11), 1], FpPoly.ofCoeffs #[(6 : ZMod64 11), 9, 10], FpPoly.ofCoeffs #[(5 : ZMod64 11), 1, 1], FpPoly.ofCoeffs #[(0 : ZMod64 11), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(10 : ZMod64 11), 1], right := FpPoly.ofCoeffs #[(9 : ZMod64 11), 7, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_11_3_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_11_3 luebeckConwayPolynomial_11_3_monic cert_11_3 = true := by
  decide

/-- The committed `C(11, 3)` entry is irreducible. -/
theorem luebeckConwayPolynomial_11_3_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_11_3 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_11_3
    luebeckConwayPolynomial_11_3_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_11_3 luebeckConwayPolynomial_11_3_monic cert_11_3 cert_11_3_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(11, 4)` entry. -/
private def cert_11_4 : Berlekamp.IrreducibilityCertificate where
  p := 11
  n := 4
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 11), 1], FpPoly.ofCoeffs #[(9 : ZMod64 11), 2, 7, 7], FpPoly.ofCoeffs #[(2 : ZMod64 11), 6, 10, 3], FpPoly.ofCoeffs #[(0 : ZMod64 11), 2, 5, 1], FpPoly.ofCoeffs #[(0 : ZMod64 11), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(5 : ZMod64 11), 5, 3], right := FpPoly.ofCoeffs #[(1 : ZMod64 11), 6, 9, 10] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_11_4_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_11_4 luebeckConwayPolynomial_11_4_monic cert_11_4 = true := by
  decide

/-- The committed `C(11, 4)` entry is irreducible. -/
theorem luebeckConwayPolynomial_11_4_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_11_4 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_11_4
    luebeckConwayPolynomial_11_4_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_11_4 luebeckConwayPolynomial_11_4_monic cert_11_4 cert_11_4_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(11, 5)` entry. -/
private def cert_11_5 : Berlekamp.IrreducibilityCertificate where
  p := 11
  n := 5
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 11), 1], FpPoly.ofCoeffs #[(2 : ZMod64 11), 4, 1, 4], FpPoly.ofCoeffs #[(9 : ZMod64 11), 2, 7, 7, 2], FpPoly.ofCoeffs #[(1 : ZMod64 11), 9, 1, 2, 6], FpPoly.ofCoeffs #[(10 : ZMod64 11), 6, 2, 9, 3], FpPoly.ofCoeffs #[(0 : ZMod64 11), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(6 : ZMod64 11), 10, 8], right := FpPoly.ofCoeffs #[(1 : ZMod64 11), 3, 6, 9, 9] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 20000000 in
private theorem cert_11_5_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_11_5 luebeckConwayPolynomial_11_5_monic cert_11_5 = true := by
  decide

/-- The committed `C(11, 5)` entry is irreducible. -/
theorem luebeckConwayPolynomial_11_5_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_11_5 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_11_5
    luebeckConwayPolynomial_11_5_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_11_5 luebeckConwayPolynomial_11_5_monic cert_11_5 cert_11_5_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(11, 6)` entry. -/
private def cert_11_6 : Berlekamp.IrreducibilityCertificate where
  p := 11
  n := 6
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 11), 1], FpPoly.ofCoeffs #[(10 : ZMod64 11), 7, 6, 3, 4, 1], FpPoly.ofCoeffs #[(5 : ZMod64 11), 10, 3, 2, 8, 9], FpPoly.ofCoeffs #[(9 : ZMod64 11), 2, 9, 6, 6, 3], FpPoly.ofCoeffs #[(10 : ZMod64 11), 3, 10, 10, 9, 3], FpPoly.ofCoeffs #[(10 : ZMod64 11), 10, 5, 1, 6, 6], FpPoly.ofCoeffs #[(0 : ZMod64 11), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(9 : ZMod64 11), 6, 7, 8, 2], right := FpPoly.ofCoeffs #[(1 : ZMod64 11), 3, 5, 1, 8, 1] }, { left := FpPoly.ofCoeffs #[(5 : ZMod64 11), 9, 6, 8], right := FpPoly.ofCoeffs #[(10 : ZMod64 11), 4, 6, 7, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 20000000 in
private theorem cert_11_6_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_11_6 luebeckConwayPolynomial_11_6_monic cert_11_6 = true := by
  decide

/-- The committed `C(11, 6)` entry is irreducible. -/
theorem luebeckConwayPolynomial_11_6_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_11_6 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_11_6
    luebeckConwayPolynomial_11_6_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_11_6 luebeckConwayPolynomial_11_6_monic cert_11_6 cert_11_6_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(13, 1)` entry. -/
private def cert_13_1 : Berlekamp.IrreducibilityCertificate where
  p := 13
  n := 1
  powChain := #[FpPoly.ofCoeffs #[(2 : ZMod64 13)], FpPoly.ofCoeffs #[(2 : ZMod64 13)]]
  bezout := #[]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_13_1_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_13_1 luebeckConwayPolynomial_13_1_monic cert_13_1 = true := by
  decide

/-- The committed `C(13, 1)` entry is irreducible. -/
theorem luebeckConwayPolynomial_13_1_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_13_1 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_13_1
    luebeckConwayPolynomial_13_1_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_13_1 luebeckConwayPolynomial_13_1_monic cert_13_1 cert_13_1_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(13, 2)` entry. -/
private def cert_13_2 : Berlekamp.IrreducibilityCertificate where
  p := 13
  n := 2
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 13), 1], FpPoly.ofCoeffs #[(1 : ZMod64 13), 12], FpPoly.ofCoeffs #[(0 : ZMod64 13), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(8 : ZMod64 13)], right := FpPoly.ofCoeffs #[(11 : ZMod64 13), 4] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_13_2_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_13_2 luebeckConwayPolynomial_13_2_monic cert_13_2 = true := by
  decide

/-- The committed `C(13, 2)` entry is irreducible. -/
theorem luebeckConwayPolynomial_13_2_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_13_2 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_13_2
    luebeckConwayPolynomial_13_2_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_13_2 luebeckConwayPolynomial_13_2_monic cert_13_2 cert_13_2_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(13, 3)` entry. -/
private def cert_13_3 : Berlekamp.IrreducibilityCertificate where
  p := 13
  n := 3
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 13), 1], FpPoly.ofCoeffs #[(11 : ZMod64 13), 7, 5], FpPoly.ofCoeffs #[(2 : ZMod64 13), 5, 8], FpPoly.ofCoeffs #[(0 : ZMod64 13), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(6 : ZMod64 13), 10], right := FpPoly.ofCoeffs #[(0 : ZMod64 13), 9, 11] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_13_3_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_13_3 luebeckConwayPolynomial_13_3_monic cert_13_3 = true := by
  decide

/-- The committed `C(13, 3)` entry is irreducible. -/
theorem luebeckConwayPolynomial_13_3_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_13_3 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_13_3
    luebeckConwayPolynomial_13_3_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_13_3 luebeckConwayPolynomial_13_3_monic cert_13_3 cert_13_3_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(13, 4)` entry. -/
private def cert_13_4 : Berlekamp.IrreducibilityCertificate where
  p := 13
  n := 4
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 13), 1], FpPoly.ofCoeffs #[(12 : ZMod64 13), 2, 7, 11], FpPoly.ofCoeffs #[(5 : ZMod64 13), 9, 1, 4], FpPoly.ofCoeffs #[(9 : ZMod64 13), 1, 5, 11], FpPoly.ofCoeffs #[(0 : ZMod64 13), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(10 : ZMod64 13), 1, 4], right := FpPoly.ofCoeffs #[(4 : ZMod64 13), 3, 0, 12] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem cert_13_4_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_13_4 luebeckConwayPolynomial_13_4_monic cert_13_4 = true := by
  decide

/-- The committed `C(13, 4)` entry is irreducible. -/
theorem luebeckConwayPolynomial_13_4_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_13_4 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_13_4
    luebeckConwayPolynomial_13_4_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_13_4 luebeckConwayPolynomial_13_4_monic cert_13_4 cert_13_4_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(13, 5)` entry. -/
private def cert_13_5 : Berlekamp.IrreducibilityCertificate where
  p := 13
  n := 5
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 13), 1], FpPoly.ofCoeffs #[(6 : ZMod64 13), 1, 0, 4, 10], FpPoly.ofCoeffs #[(2 : ZMod64 13), 8, 3, 0, 12], FpPoly.ofCoeffs #[(1 : ZMod64 13), 11, 6, 6, 6], FpPoly.ofCoeffs #[(4 : ZMod64 13), 5, 4, 3, 11], FpPoly.ofCoeffs #[(0 : ZMod64 13), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(9 : ZMod64 13), 5, 0, 7], right := FpPoly.ofCoeffs #[(1 : ZMod64 13), 0, 1, 6, 11] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 20000000 in
private theorem cert_13_5_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_13_5 luebeckConwayPolynomial_13_5_monic cert_13_5 = true := by
  decide

/-- The committed `C(13, 5)` entry is irreducible. -/
theorem luebeckConwayPolynomial_13_5_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_13_5 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_13_5
    luebeckConwayPolynomial_13_5_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_13_5 luebeckConwayPolynomial_13_5_monic cert_13_5 cert_13_5_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(13, 6)` entry. -/
private def cert_13_6 : Berlekamp.IrreducibilityCertificate where
  p := 13
  n := 6
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 13), 1], FpPoly.ofCoeffs #[(2 : ZMod64 13), 10, 8, 11, 10, 3], FpPoly.ofCoeffs #[(1 : ZMod64 13), 5, 10, 9, 9, 1], FpPoly.ofCoeffs #[(9 : ZMod64 13), 2, 7, 4, 6, 7], FpPoly.ofCoeffs #[(1 : ZMod64 13), 4, 3, 12, 5, 8], FpPoly.ofCoeffs #[(0 : ZMod64 13), 4, 11, 3, 9, 7], FpPoly.ofCoeffs #[(0 : ZMod64 13), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(10 : ZMod64 13), 1, 9, 7, 1], right := FpPoly.ofCoeffs #[(7 : ZMod64 13), 3, 0, 8, 2, 12] }, { left := FpPoly.ofCoeffs #[(11 : ZMod64 13), 10, 11, 12, 4], right := FpPoly.ofCoeffs #[(2 : ZMod64 13), 0, 5, 10, 7, 5] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 20000000 in
private theorem cert_13_6_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_13_6 luebeckConwayPolynomial_13_6_monic cert_13_6 = true := by
  decide

/-- The committed `C(13, 6)` entry is irreducible. -/
theorem luebeckConwayPolynomial_13_6_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_13_6 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_13_6
    luebeckConwayPolynomial_13_6_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_13_6 luebeckConwayPolynomial_13_6_monic cert_13_6 cert_13_6_incremental_check)

private theorem luebeckConwayPolynomialOfCoeffs_2_1_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 2 [1, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_1
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 1]) =
    some luebeckConwayPolynomial_2_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 1] =
      luebeckConwayPolynomial_2_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_1_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_2_2_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_2
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 1]) =
    some luebeckConwayPolynomial_2_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 1, 1] =
      luebeckConwayPolynomial_2_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_2_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_2_3_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_3
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1]) =
    some luebeckConwayPolynomial_2_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1] =
      luebeckConwayPolynomial_2_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_3_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_2_4_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_4
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 0, 1]) =
    some luebeckConwayPolynomial_2_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 0, 1] =
      luebeckConwayPolynomial_2_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_4_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_2_5_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 2 [1, 0, 1, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_5
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 0, 1, 0, 0, 1]) =
    some luebeckConwayPolynomial_2_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 0, 1, 0, 0, 1] =
      luebeckConwayPolynomial_2_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_5_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_2_6_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1, 1, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_6
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1, 1, 0, 1]) =
    some luebeckConwayPolynomial_2_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1, 1, 0, 1] =
      luebeckConwayPolynomial_2_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_6_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_3_1_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 3 [1, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_1
  change some (luebeckConwayPolynomialOfCoeffs 3 [1, 1]) =
    some luebeckConwayPolynomial_3_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [1, 1] =
      luebeckConwayPolynomial_3_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_1_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_3_2_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_2
  change some (luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1]) =
    some luebeckConwayPolynomial_3_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1] =
      luebeckConwayPolynomial_3_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_2_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_3_3_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_3
  change some (luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 1]) =
    some luebeckConwayPolynomial_3_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 1] =
      luebeckConwayPolynomial_3_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_3_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_3_4_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 3 [2, 0, 0, 2, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_4
  change some (luebeckConwayPolynomialOfCoeffs 3 [2, 0, 0, 2, 1]) =
    some luebeckConwayPolynomial_3_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [2, 0, 0, 2, 1] =
      luebeckConwayPolynomial_3_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_4_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_3_5_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_5
  change some (luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 0, 0, 1]) =
    some luebeckConwayPolynomial_3_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 0, 0, 1] =
      luebeckConwayPolynomial_3_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_5_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_3_6_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1, 0, 2, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_6
  change some (luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1, 0, 2, 0, 1]) =
    some luebeckConwayPolynomial_3_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1, 0, 2, 0, 1] =
      luebeckConwayPolynomial_3_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_6_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_5_1_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 5 [3, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_1
  change some (luebeckConwayPolynomialOfCoeffs 5 [3, 1]) =
    some luebeckConwayPolynomial_5_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [3, 1] =
      luebeckConwayPolynomial_5_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_1_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_5_2_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 5 [2, 4, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_2
  change some (luebeckConwayPolynomialOfCoeffs 5 [2, 4, 1]) =
    some luebeckConwayPolynomial_5_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [2, 4, 1] =
      luebeckConwayPolynomial_5_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_2_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_5_3_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 5 [3, 3, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_3
  change some (luebeckConwayPolynomialOfCoeffs 5 [3, 3, 0, 1]) =
    some luebeckConwayPolynomial_5_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [3, 3, 0, 1] =
      luebeckConwayPolynomial_5_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_3_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_5_4_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 5 [2, 4, 4, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_4
  change some (luebeckConwayPolynomialOfCoeffs 5 [2, 4, 4, 0, 1]) =
    some luebeckConwayPolynomial_5_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [2, 4, 4, 0, 1] =
      luebeckConwayPolynomial_5_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_4_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_5_5_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 5 [3, 4, 0, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_5
  change some (luebeckConwayPolynomialOfCoeffs 5 [3, 4, 0, 0, 0, 1]) =
    some luebeckConwayPolynomial_5_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [3, 4, 0, 0, 0, 1] =
      luebeckConwayPolynomial_5_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_5_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_5_6_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 5 [2, 0, 1, 4, 1, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_6
  change some (luebeckConwayPolynomialOfCoeffs 5 [2, 0, 1, 4, 1, 0, 1]) =
    some luebeckConwayPolynomial_5_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [2, 0, 1, 4, 1, 0, 1] =
      luebeckConwayPolynomial_5_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_6_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_7_1_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 7 [4, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_1
  change some (luebeckConwayPolynomialOfCoeffs 7 [4, 1]) =
    some luebeckConwayPolynomial_7_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [4, 1] =
      luebeckConwayPolynomial_7_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_1_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_7_2_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 7 [3, 6, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_2
  change some (luebeckConwayPolynomialOfCoeffs 7 [3, 6, 1]) =
    some luebeckConwayPolynomial_7_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [3, 6, 1] =
      luebeckConwayPolynomial_7_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_2_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_7_3_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 7 [4, 0, 6, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_3
  change some (luebeckConwayPolynomialOfCoeffs 7 [4, 0, 6, 1]) =
    some luebeckConwayPolynomial_7_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [4, 0, 6, 1] =
      luebeckConwayPolynomial_7_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_3_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_7_4_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 7 [3, 4, 5, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_4
  change some (luebeckConwayPolynomialOfCoeffs 7 [3, 4, 5, 0, 1]) =
    some luebeckConwayPolynomial_7_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [3, 4, 5, 0, 1] =
      luebeckConwayPolynomial_7_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_4_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_7_5_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 7 [4, 1, 0, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_5
  change some (luebeckConwayPolynomialOfCoeffs 7 [4, 1, 0, 0, 0, 1]) =
    some luebeckConwayPolynomial_7_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [4, 1, 0, 0, 0, 1] =
      luebeckConwayPolynomial_7_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_5_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_7_6_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 7 [3, 6, 4, 5, 1, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_6
  change some (luebeckConwayPolynomialOfCoeffs 7 [3, 6, 4, 5, 1, 0, 1]) =
    some luebeckConwayPolynomial_7_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [3, 6, 4, 5, 1, 0, 1] =
      luebeckConwayPolynomial_7_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_6_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_11_1_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 11 [9, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_1
  change some (luebeckConwayPolynomialOfCoeffs 11 [9, 1]) =
    some luebeckConwayPolynomial_11_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [9, 1] =
      luebeckConwayPolynomial_11_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_1_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_11_2_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 11 [2, 7, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_2
  change some (luebeckConwayPolynomialOfCoeffs 11 [2, 7, 1]) =
    some luebeckConwayPolynomial_11_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [2, 7, 1] =
      luebeckConwayPolynomial_11_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_2_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_11_3_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 11 [9, 2, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_3
  change some (luebeckConwayPolynomialOfCoeffs 11 [9, 2, 0, 1]) =
    some luebeckConwayPolynomial_11_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [9, 2, 0, 1] =
      luebeckConwayPolynomial_11_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_3_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_11_4_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 11 [2, 10, 8, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_4
  change some (luebeckConwayPolynomialOfCoeffs 11 [2, 10, 8, 0, 1]) =
    some luebeckConwayPolynomial_11_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [2, 10, 8, 0, 1] =
      luebeckConwayPolynomial_11_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_4_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_11_5_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 11 [9, 0, 10, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_5
  change some (luebeckConwayPolynomialOfCoeffs 11 [9, 0, 10, 0, 0, 1]) =
    some luebeckConwayPolynomial_11_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [9, 0, 10, 0, 0, 1] =
      luebeckConwayPolynomial_11_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_5_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_11_6_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 11 [2, 7, 6, 4, 3, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_6
  change some (luebeckConwayPolynomialOfCoeffs 11 [2, 7, 6, 4, 3, 0, 1]) =
    some luebeckConwayPolynomial_11_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [2, 7, 6, 4, 3, 0, 1] =
      luebeckConwayPolynomial_11_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_6_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_13_1_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 13 [11, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_1
  change some (luebeckConwayPolynomialOfCoeffs 13 [11, 1]) =
    some luebeckConwayPolynomial_13_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [11, 1] =
      luebeckConwayPolynomial_13_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_1_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_13_2_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 13 [2, 12, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_2
  change some (luebeckConwayPolynomialOfCoeffs 13 [2, 12, 1]) =
    some luebeckConwayPolynomial_13_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [2, 12, 1] =
      luebeckConwayPolynomial_13_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_2_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_13_3_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 13 [11, 2, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_3
  change some (luebeckConwayPolynomialOfCoeffs 13 [11, 2, 0, 1]) =
    some luebeckConwayPolynomial_13_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [11, 2, 0, 1] =
      luebeckConwayPolynomial_13_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_3_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_13_4_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 13 [2, 12, 3, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_4
  change some (luebeckConwayPolynomialOfCoeffs 13 [2, 12, 3, 0, 1]) =
    some luebeckConwayPolynomial_13_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [2, 12, 3, 0, 1] =
      luebeckConwayPolynomial_13_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_4_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_13_5_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 13 [11, 4, 0, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_5
  change some (luebeckConwayPolynomialOfCoeffs 13 [11, 4, 0, 0, 0, 1]) =
    some luebeckConwayPolynomial_13_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [11, 4, 0, 0, 0, 1] =
      luebeckConwayPolynomial_13_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_5_irreducible

private theorem luebeckConwayPolynomialOfCoeffs_13_6_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 13 [2, 11, 11, 10, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_6
  change some (luebeckConwayPolynomialOfCoeffs 13 [2, 11, 11, 10, 0, 0, 1]) =
    some luebeckConwayPolynomial_13_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [2, 11, 11, 10, 0, 0, 1] =
      luebeckConwayPolynomial_13_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_6_irreducible

/-- Every committed imported entry in the current Tier 1 slice comes with
an irreducibility witness. -/
theorem luebeckConwayPolynomial?_irreducible
    {p n : Nat} [ZMod64.Bounds p] {f : FpPoly p}
    (h : luebeckConwayPolynomial? p n = some f) :
    FpPoly.Irreducible f := by
  unfold luebeckConwayPolynomial? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨coeffs, hcoeffs, hf⟩ := h
  subst hf
  unfold luebeckConwayCoeffs? at hcoeffs
  split at hcoeffs
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_1_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_2_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_3_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_4_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_5_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_6_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_1_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_2_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_3_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_4_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_5_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_6_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_1_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_2_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_3_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_4_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_5_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_6_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_1_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_2_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_3_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_4_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_5_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_6_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_1_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_2_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_3_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_4_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_5_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_6_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_1_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_2_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_3_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_4_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_5_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_6_irreducible
  · cases hcoeffs

/-- A committed Conway entry packages the current Tier 1 lookup hit for a
supported `(p, n)` pair. -/
structure SupportedEntry (p n : Nat) [ZMod64.Bounds p] where
  poly : FpPoly p
  prime : Hex.Nat.Prime p
  isSupported : luebeckConwayPolynomial? p n = some poly

/-- The current committed table supports `C(2, 1)`. -/
def supportedEntry_2_1 : SupportedEntry 2 1 :=
  ⟨luebeckConwayPolynomial_2_1, by
    constructor
    · decide
    · intro m hm
      have hmle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
      have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      rcases hcases with rfl | rfl | rfl
      · simp at hm
      · exact Or.inl rfl
      · exact Or.inr rfl,
    luebeckConwayPolynomial?_hit_2_1⟩

/-- The current committed table supports `C(2, 2)`. -/
def supportedEntry_2_2 : SupportedEntry 2 2 :=
  ⟨luebeckConwayPolynomial_2_2,
    supportedEntry_2_1.prime,
    luebeckConwayPolynomial?_hit_2_2⟩

/-- The current committed table supports `C(2, 3)`. -/
def supportedEntry_2_3 : SupportedEntry 2 3 :=
  ⟨luebeckConwayPolynomial_2_3,
    supportedEntry_2_1.prime,
    luebeckConwayPolynomial?_hit_2_3⟩

/-- The current committed table supports `C(2, 4)`. -/
def supportedEntry_2_4 : SupportedEntry 2 4 :=
  ⟨luebeckConwayPolynomial_2_4,
    supportedEntry_2_1.prime,
    luebeckConwayPolynomial?_hit_2_4⟩

/-- The current committed table supports `C(2, 5)`. -/
def supportedEntry_2_5 : SupportedEntry 2 5 :=
  ⟨luebeckConwayPolynomial_2_5,
    supportedEntry_2_1.prime,
    luebeckConwayPolynomial?_hit_2_5⟩

/-- The current committed table supports `C(2, 6)`. -/
def supportedEntry_2_6 : SupportedEntry 2 6 :=
  ⟨luebeckConwayPolynomial_2_6,
    supportedEntry_2_1.prime,
    luebeckConwayPolynomial?_hit_2_6⟩

/-- Recover the committed Conway modulus for a supported entry. -/
def conwayPoly (p n : Nat) [ZMod64.Bounds p] (h : SupportedEntry p n) : FpPoly p :=
  h.poly

@[simp] theorem luebeckConwayPolynomial?_conwayPoly
    {p n : Nat} [ZMod64.Bounds p] (h : SupportedEntry p n) :
    luebeckConwayPolynomial? p n = some (conwayPoly p n h) :=
  h.isSupported

private theorem zmod64_one_ne_zero_of_one_lt
    {p : Nat} [ZMod64.Bounds p] (hp : 1 < p) : (1 : ZMod64 p) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := p) 1 0).mp h
  rw [Nat.zero_mod, Nat.mod_eq_of_lt hp] at hm
  exact Nat.one_ne_zero hm

private theorem ofCoeffs_degree_pos_of_back_ne_zero
    {R : Type u} [Zero R] [DecidableEq R]
    (arr : Array R) (hsize : 2 ≤ arr.size)
    (hback : arr[arr.size - 1]'(by omega) ≠ Zero.zero) :
    0 < (DensePoly.ofCoeffs arr).degree?.getD 0 := by
  have hgetd_eq :
      arr.getD (arr.size - 1) (Zero.zero : R) = arr[arr.size - 1]'(by omega) :=
    (Array.getElem_eq_getD (Zero.zero : R)).symm
  have hcoeff_ne : (DensePoly.ofCoeffs arr).coeff (arr.size - 1) ≠ Zero.zero := by
    rw [DensePoly.coeff_ofCoeffs, hgetd_eq]; exact hback
  have hpoly_size : arr.size - 1 < (DensePoly.ofCoeffs arr).size := by
    rcases Nat.lt_or_ge (arr.size - 1) (DensePoly.ofCoeffs arr).size with hlt | hge
    · exact hlt
    · exact False.elim (hcoeff_ne (DensePoly.coeff_eq_zero_of_size_le _ hge))
  rw [show (DensePoly.ofCoeffs arr).degree? =
        if _h : (DensePoly.ofCoeffs arr).size = 0 then none
        else some ((DensePoly.ofCoeffs arr).size - 1) from rfl]
  rw [dif_neg (by omega : (DensePoly.ofCoeffs arr).size ≠ 0)]
  simp only [Option.getD_some]
  omega

/-- Every committed Tier 1 Conway entry in the current table is nonconstant. -/
theorem luebeckConwayPolynomial?_degree_pos
    {p n : Nat} [ZMod64.Bounds p] {f : FpPoly p}
    (h : luebeckConwayPolynomial? p n = some f) :
    0 < FpPoly.degree f := by
  unfold luebeckConwayPolynomial? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨coeffs, hcoeffs, hf⟩ := h
  subst hf
  unfold luebeckConwayCoeffs? at hcoeffs
  split at hcoeffs
  all_goals
    (cases hcoeffs
     all_goals
       (refine ofCoeffs_degree_pos_of_back_ne_zero _ ?_ ?_
        · simp
        · intro hzero
          simp at hzero
          exact absurd hzero (zmod64_one_ne_zero_of_one_lt (by decide))))

/-- Supported Conway entries produce nonconstant moduli. -/
theorem conwayPoly_nonconstant
    (p n : Nat) [ZMod64.Bounds p] (h : SupportedEntry p n) :
    0 < FpPoly.degree (conwayPoly p n h) := by
  exact luebeckConwayPolynomial?_degree_pos
    (f := conwayPoly p n h) (luebeckConwayPolynomial?_conwayPoly h)

/-- Supported Conway entries carry the imported irreducibility witness. -/
theorem conwayPoly_irreducible
    (p n : Nat) [ZMod64.Bounds p] (h : SupportedEntry p n) :
    FpPoly.Irreducible (conwayPoly p n h) := by
  exact luebeckConwayPolynomial?_irreducible
    (f := conwayPoly p n h) (luebeckConwayPolynomial?_conwayPoly h)

end Conway

end Hex
