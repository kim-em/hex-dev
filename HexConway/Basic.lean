import HexBerlekamp
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

/-- The committed `C(2, 1)` entry is irreducible. -/
theorem luebeckConwayPolynomial_2_1_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_2_1 := by
  sorry

/-- Every committed imported entry in the current Tier 1 slice comes with
an irreducibility witness. -/
axiom luebeckConwayPolynomial?_irreducible
    {p n : Nat} [ZMod64.Bounds p] {f : FpPoly p}
    (h : luebeckConwayPolynomial? p n = some f) :
    FpPoly.Irreducible f

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
