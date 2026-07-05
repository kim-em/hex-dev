/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekamp.RabinSoundness
import HexGFqRing.Basic

/-!
Tier 1 Conway-polynomial table and dispatcher: the imported coefficient
table `luebeckConwayCoeffs?`, the `luebeckConwayPolynomialOfCoeffs` /
`luebeckConwayPolynomial?` lookup, the prime-modulus instances, and the
per-entry polynomial literals with their monic/degree/table-hit lemmas.
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

/-- `1 ≠ 0` in `ZMod64 2`, the nondegeneracy fact that certifies the leading
coefficient of the committed `C(2, 1)` literal is nonzero. -/
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
      decide }

/-- Tier 1 imported-table lookup for committed Luebeck Conway entries.

This is only the imported-table surface: unsupported pairs return `none`
rather than triggering Tier 2 compatibility checks or Tier 3 search. -/
def luebeckConwayPolynomial? (p n : Nat) [ZMod64.Bounds p] : Option (FpPoly p) :=
  (luebeckConwayCoeffs? p n).map (luebeckConwayPolynomialOfCoeffs p)

/-- `luebeckConwayPolynomial? 2 1` resolves to the committed `C(2, 1)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_2_1` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_2_1 :
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

/-- Degree `0` over `p = 2` is outside the committed table, so the lookup
returns `none`. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_miss_two_zero :
    luebeckConwayPolynomial? 2 0 = (none : Option (FpPoly 2)) :=
  rfl

/-- Degree `7` over `p = 2` is outside the committed table, so the lookup
returns `none`. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_miss_two_seven :
    luebeckConwayPolynomial? 2 7 = (none : Option (FpPoly 2)) :=
  rfl

/-- Degree `7` over `p = 3` is outside the committed table, so the lookup
returns `none`. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_miss_three_seven :
    luebeckConwayPolynomial? 3 7 = (none : Option (FpPoly 3)) :=
  rfl

/-- The committed `C(2, 1)` entry is monic, so it can be fed to the
executable Rabin checker. -/
@[simp, grind .] theorem luebeckConwayPolynomial_2_1_monic :
    DensePoly.Monic luebeckConwayPolynomial_2_1 := by
  rfl

/-- The committed `C(2, 1)` entry has positive degree. -/
@[simp, grind .] theorem luebeckConwayPolynomial_2_1_degree_pos :
    0 < FpPoly.degree luebeckConwayPolynomial_2_1 := by
  decide

/-- `Hex.Nat.Prime` witness for `p = 2`, the smallest committed Conway prime. -/
theorem prime_two : Hex.Nat.Prime 2 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- Registers `2` as a `ZMod64.PrimeModulus`, the witness derived from
`prime_two`. -/
instance instPrimeModulusTwo : ZMod64.PrimeModulus 2 :=
  ZMod64.primeModulusOfPrime prime_two

/-- `Hex.Nat.Prime` witness for `p = 3`, the first committed odd Conway prime. -/
theorem prime_three : Hex.Nat.Prime 3 := by
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

/-- Registers `3` as a `ZMod64.PrimeModulus`, the witness derived from
`prime_three`. -/
instance instPrimeModulus3 : ZMod64.PrimeModulus 3 :=
  ZMod64.primeModulusOfPrime prime_three

/-- `Hex.Nat.Prime` witness for `p = 5`, a committed odd Conway prime. -/
theorem prime_five : Hex.Nat.Prime 5 := by
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

/-- Registers `5` as a `ZMod64.PrimeModulus`, the witness derived from
`prime_five`. -/
instance instPrimeModulus5 : ZMod64.PrimeModulus 5 :=
  ZMod64.primeModulusOfPrime prime_five

/-- `Hex.Nat.Prime` witness for `p = 7`, a committed odd Conway prime. -/
theorem prime_seven : Hex.Nat.Prime 7 := by
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

/-- Registers `7` as a `ZMod64.PrimeModulus`, the witness derived from
`prime_seven`. -/
instance instPrimeModulus7 : ZMod64.PrimeModulus 7 :=
  ZMod64.primeModulusOfPrime prime_seven

/-- `Hex.Nat.Prime` witness for `p = 11`, a committed odd Conway prime. -/
theorem prime_eleven : Hex.Nat.Prime 11 := by
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

/-- Registers `11` as a `ZMod64.PrimeModulus`, the witness derived from
`prime_eleven`. -/
instance instPrimeModulus11 : ZMod64.PrimeModulus 11 :=
  ZMod64.primeModulusOfPrime prime_eleven

/-- `Hex.Nat.Prime` witness for `p = 13`, a committed odd Conway prime. -/
theorem prime_thirteen : Hex.Nat.Prime 13 := by
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

/-- Registers `13` as a `ZMod64.PrimeModulus`, the witness derived from
`prime_thirteen`. -/
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
/-- The executable linear irreducibility-certificate checker accepts `cert_2_1`
for the committed `C(2, 1)` entry, the evidence feeding
`luebeckConwayPolynomial_2_1_irreducible`. -/
private theorem cert_2_1_linear_check :
    Berlekamp.checkIrreducibilityCertificateLinear
        luebeckConwayPolynomial_2_1 luebeckConwayPolynomial_2_1_monic cert_2_1 = true := by
  decide

/-- The committed `C(2, 1)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_2_1_irreducible :
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
@[simp, grind .] theorem luebeckConwayPolynomial_2_2_monic :
    DensePoly.Monic luebeckConwayPolynomial_2_2 := by
  rfl

/-- The committed `C(2, 2)` entry has positive degree. -/
@[simp, grind .] theorem luebeckConwayPolynomial_2_2_degree_pos :
    0 < FpPoly.degree luebeckConwayPolynomial_2_2 := by
  decide

/-- `luebeckConwayPolynomial? 2 2` resolves to the committed `C(2, 2)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_2_2` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_2_2 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_2_3_monic :
    DensePoly.Monic luebeckConwayPolynomial_2_3 := by
  rfl

/-- The committed `C(2, 3)` entry has positive degree. -/
@[simp, grind .] theorem luebeckConwayPolynomial_2_3_degree_pos :
    0 < FpPoly.degree luebeckConwayPolynomial_2_3 := by
  decide

/-- `luebeckConwayPolynomial? 2 3` resolves to the committed `C(2, 3)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_2_3` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_2_3 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_2_4_monic :
    DensePoly.Monic luebeckConwayPolynomial_2_4 := by
  rfl

/-- The committed `C(2, 4)` entry has positive degree. -/
@[simp, grind .] theorem luebeckConwayPolynomial_2_4_degree_pos :
    0 < FpPoly.degree luebeckConwayPolynomial_2_4 := by
  decide

/-- `luebeckConwayPolynomial? 2 4` resolves to the committed `C(2, 4)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_2_4` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_2_4 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_2_5_monic :
    DensePoly.Monic luebeckConwayPolynomial_2_5 := by
  rfl

/-- The committed `C(2, 5)` entry has positive degree. -/
@[simp, grind .] theorem luebeckConwayPolynomial_2_5_degree_pos :
    0 < FpPoly.degree luebeckConwayPolynomial_2_5 := by
  decide

/-- `luebeckConwayPolynomial? 2 5` resolves to the committed `C(2, 5)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_2_5` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_2_5 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_2_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_2_6 := by
  rfl

/-- The committed `C(2, 6)` entry has positive degree. -/
@[simp, grind .] theorem luebeckConwayPolynomial_2_6_degree_pos :
    0 < FpPoly.degree luebeckConwayPolynomial_2_6 := by
  decide

/-- `luebeckConwayPolynomial? 2 6` resolves to the committed `C(2, 6)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_2_6` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_2_6 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_3_1_monic :
    DensePoly.Monic luebeckConwayPolynomial_3_1 := by
  rfl

/-- `luebeckConwayPolynomial? 3 1` resolves to the committed `C(3, 1)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_3_1` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_3_1 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_3_2_monic :
    DensePoly.Monic luebeckConwayPolynomial_3_2 := by
  rfl

/-- `luebeckConwayPolynomial? 3 2` resolves to the committed `C(3, 2)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_3_2` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_3_2 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_3_3_monic :
    DensePoly.Monic luebeckConwayPolynomial_3_3 := by
  rfl

/-- `luebeckConwayPolynomial? 3 3` resolves to the committed `C(3, 3)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_3_3` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_3_3 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_3_4_monic :
    DensePoly.Monic luebeckConwayPolynomial_3_4 := by
  rfl

/-- `luebeckConwayPolynomial? 3 4` resolves to the committed `C(3, 4)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_3_4` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_3_4 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_3_5_monic :
    DensePoly.Monic luebeckConwayPolynomial_3_5 := by
  rfl

/-- `luebeckConwayPolynomial? 3 5` resolves to the committed `C(3, 5)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_3_5` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_3_5 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_3_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_3_6 := by
  rfl

/-- `luebeckConwayPolynomial? 3 6` resolves to the committed `C(3, 6)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_3_6` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_3_6 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_5_1_monic :
    DensePoly.Monic luebeckConwayPolynomial_5_1 := by
  rfl

/-- `luebeckConwayPolynomial? 5 1` resolves to the committed `C(5, 1)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_5_1` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_5_1 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_5_2_monic :
    DensePoly.Monic luebeckConwayPolynomial_5_2 := by
  rfl

/-- `luebeckConwayPolynomial? 5 2` resolves to the committed `C(5, 2)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_5_2` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_5_2 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_5_3_monic :
    DensePoly.Monic luebeckConwayPolynomial_5_3 := by
  rfl

/-- `luebeckConwayPolynomial? 5 3` resolves to the committed `C(5, 3)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_5_3` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_5_3 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_5_4_monic :
    DensePoly.Monic luebeckConwayPolynomial_5_4 := by
  rfl

/-- `luebeckConwayPolynomial? 5 4` resolves to the committed `C(5, 4)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_5_4` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_5_4 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_5_5_monic :
    DensePoly.Monic luebeckConwayPolynomial_5_5 := by
  rfl

/-- `luebeckConwayPolynomial? 5 5` resolves to the committed `C(5, 5)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_5_5` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_5_5 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_5_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_5_6 := by
  rfl

/-- `luebeckConwayPolynomial? 5 6` resolves to the committed `C(5, 6)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_5_6` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_5_6 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_7_1_monic :
    DensePoly.Monic luebeckConwayPolynomial_7_1 := by
  rfl

/-- `luebeckConwayPolynomial? 7 1` resolves to the committed `C(7, 1)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_7_1` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_7_1 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_7_2_monic :
    DensePoly.Monic luebeckConwayPolynomial_7_2 := by
  rfl

/-- `luebeckConwayPolynomial? 7 2` resolves to the committed `C(7, 2)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_7_2` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_7_2 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_7_3_monic :
    DensePoly.Monic luebeckConwayPolynomial_7_3 := by
  rfl

/-- `luebeckConwayPolynomial? 7 3` resolves to the committed `C(7, 3)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_7_3` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_7_3 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_7_4_monic :
    DensePoly.Monic luebeckConwayPolynomial_7_4 := by
  rfl

/-- `luebeckConwayPolynomial? 7 4` resolves to the committed `C(7, 4)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_7_4` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_7_4 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_7_5_monic :
    DensePoly.Monic luebeckConwayPolynomial_7_5 := by
  rfl

/-- `luebeckConwayPolynomial? 7 5` resolves to the committed `C(7, 5)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_7_5` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_7_5 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_7_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_7_6 := by
  rfl

/-- `luebeckConwayPolynomial? 7 6` resolves to the committed `C(7, 6)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_7_6` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_7_6 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_11_1_monic :
    DensePoly.Monic luebeckConwayPolynomial_11_1 := by
  rfl

/-- `luebeckConwayPolynomial? 11 1` resolves to the committed `C(11, 1)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_11_1` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_11_1 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_11_2_monic :
    DensePoly.Monic luebeckConwayPolynomial_11_2 := by
  rfl

/-- `luebeckConwayPolynomial? 11 2` resolves to the committed `C(11, 2)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_11_2` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_11_2 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_11_3_monic :
    DensePoly.Monic luebeckConwayPolynomial_11_3 := by
  rfl

/-- `luebeckConwayPolynomial? 11 3` resolves to the committed `C(11, 3)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_11_3` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_11_3 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_11_4_monic :
    DensePoly.Monic luebeckConwayPolynomial_11_4 := by
  rfl

/-- `luebeckConwayPolynomial? 11 4` resolves to the committed `C(11, 4)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_11_4` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_11_4 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_11_5_monic :
    DensePoly.Monic luebeckConwayPolynomial_11_5 := by
  rfl

/-- `luebeckConwayPolynomial? 11 5` resolves to the committed `C(11, 5)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_11_5` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_11_5 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_11_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_11_6 := by
  rfl

/-- `luebeckConwayPolynomial? 11 6` resolves to the committed `C(11, 6)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_11_6` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_11_6 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_13_1_monic :
    DensePoly.Monic luebeckConwayPolynomial_13_1 := by
  rfl

/-- `luebeckConwayPolynomial? 13 1` resolves to the committed `C(13, 1)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_13_1` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_13_1 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_13_2_monic :
    DensePoly.Monic luebeckConwayPolynomial_13_2 := by
  rfl

/-- `luebeckConwayPolynomial? 13 2` resolves to the committed `C(13, 2)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_13_2` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_13_2 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_13_3_monic :
    DensePoly.Monic luebeckConwayPolynomial_13_3 := by
  rfl

/-- `luebeckConwayPolynomial? 13 3` resolves to the committed `C(13, 3)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_13_3` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_13_3 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_13_4_monic :
    DensePoly.Monic luebeckConwayPolynomial_13_4 := by
  rfl

/-- `luebeckConwayPolynomial? 13 4` resolves to the committed `C(13, 4)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_13_4` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_13_4 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_13_5_monic :
    DensePoly.Monic luebeckConwayPolynomial_13_5 := by
  rfl

/-- `luebeckConwayPolynomial? 13 5` resolves to the committed `C(13, 5)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_13_5` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_13_5 :
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
@[simp, grind .] theorem luebeckConwayPolynomial_13_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_13_6 := by
  rfl

/-- `luebeckConwayPolynomial? 13 6` resolves to the committed `C(13, 6)` literal,
rewriting the table lookup to the direct `luebeckConwayPolynomial_13_6` form. -/
@[simp, grind =] theorem luebeckConwayPolynomial?_hit_13_6 :
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


end Conway

end Hex
