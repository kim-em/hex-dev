/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.PrimeSelection
public import HexPolyZ.Decomposition
import all HexPolyZ.Core
import all HexPolyZ.Rational
import all HexPolyZ.Decomposition
import all HexBerlekampZassenhaus.PrimeSelection

public section

/-!
Soundness of a modular square-freeness certificate.

The classical Berlekamp-Zassenhaus square-free-core extraction runs an exact
`gcd(f, f')` over `ℚ`, whose rational coefficient blow-up dominates
`normalizeForFactor`.  For the common (square-free) input the whole computation
collapses to a trivial decomposition; a cheap machine-word modular test decides
square-freeness far faster.

`separableModP f p` reduces `f` and its (integer) derivative modulo a prime `p`
and checks that their `𝔽_p` gcd is a unit.  When `p` is prime and does not
divide the leading coefficient of `f` (admissible), passing this test is a
*sufficient* condition for `f` to be square-free over `ℚ`
(`squareFreeRat_of_separableModP`): a nontrivial rational gcd of `f, f'` clears
via Gauss's lemma to a positive-degree primitive integer common factor, whose
modular image is a positive-degree common factor of `modP f, modP f'`,
contradicting the unit gcd.  This is the soundness the modular fast path rests
on; failing the test simply falls back to the exact computation.
-/

namespace Hex

namespace ZPoly

/-- `toRatPoly` commutes with the formal derivative. -/
theorem toRatPoly_derivative (f : ZPoly) :
    toRatPoly (DensePoly.derivative f) = DensePoly.derivative (toRatPoly f) := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_toRatPoly, DensePoly.coeff_derivative f n (Lean.Grind.Semiring.mul_zero _),
      DensePoly.coeff_derivative (toRatPoly f) n (Lean.Grind.Semiring.mul_zero _), coeff_toRatPoly]
  exact_mod_cast rfl

/-- Reduction modulo `p` preserves divisibility of integer polynomials. -/
theorem modP_dvd_of_dvd {p : Nat} [ZMod64.Bounds p] {a b : ZPoly} (h : a ∣ b) :
    ZPoly.modP p a ∣ ZPoly.modP p b := by
  rcases h with ⟨c, hc⟩
  exact ⟨ZPoly.modP p c, by rw [hc, modP_mul]⟩

/-- Reduction modulo `p` never increases the dense size. -/
private theorem size_modP_le (p : Nat) [ZMod64.Bounds p] (f : ZPoly) :
    (ZPoly.modP p f).size ≤ f.size := by
  show (ZPoly.modP p f).coeffs.size ≤ f.size
  unfold ZPoly.modP FpPoly.ofCoeffs
  have h := DensePoly.size_ofCoeffs_le (R := ZMod64 p)
    ((List.range f.size).map
      (fun i => ZMod64.ofNat p (ZPoly.intModNat (f.coeff i) p))).toArray
  have hlen : ((List.range f.size).map
      (fun i => ZMod64.ofNat p (ZPoly.intModNat (f.coeff i) p))).toArray.size = f.size := by simp
  simpa [DensePoly.size, hlen] using h

/-- Divisibility of rational polynomials is transitive. -/
private theorem rat_dvd_trans {a b c : DensePoly Rat} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  rcases hab with ⟨x, hx⟩
  rcases hbc with ⟨y, hy⟩
  exact ⟨x * y, by rw [hy, hx, DensePoly.mul_assoc_poly]⟩

/-- Divisibility of rational polynomials is reflexive. -/
private theorem rat_dvd_refl (a : DensePoly Rat) : a ∣ a :=
  ⟨1, (DensePoly.mul_one_right_poly a).symm⟩

/-- The `𝔽_p`-separability certificate: the reduction of `f` and of its integer
derivative are coprime over `𝔽_p`. -/
@[expose]
def separableModP (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : Bool :=
  gcdIsUnit (DensePoly.gcd (ZPoly.modP p f) (ZPoly.modP p (DensePoly.derivative f)))

/-- Admissibility is inherited by an integer factor: if `p` does not divide the
leading coefficient of `f = r * s`, the modular image of `r` keeps its full
degree. -/
private theorem size_modP_eq_of_factor
    {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (f r s : ZPoly) (hf : f = r * s) (hr_ne : r ≠ 0) (hs_ne : s ≠ 0)
    (hadm : leadingCoeffAdmissible f p) :
    (ZPoly.modP p r).size = r.size := by
  have hr_pos : 0 < r.size := size_pos_of_ne_zero r hr_ne
  have hs_pos : 0 < s.size := size_pos_of_ne_zero s hs_ne
  have hf_size : f.size = r.size + s.size - 1 := by
    rw [hf]; exact mul_size_eq_top_succ_of_nonzero r s hr_pos hs_pos
  have hmodf_ne : ZPoly.modP p f ≠ 0 := modP_ne_zero_of_leadingCoeffAdmissible f p hadm
  have hmodf_size : (ZPoly.modP p f).size = f.size :=
    size_modP_eq_of_leadingCoeffAdmissible f p hadm
  have hmodf_mul : ZPoly.modP p f = ZPoly.modP p r * ZPoly.modP p s := by
    rw [hf, modP_mul]
  have hmodr_ne : ZPoly.modP p r ≠ 0 := by
    intro h0
    apply hmodf_ne
    rw [hmodf_mul, h0]
    exact DensePoly.zero_mul _
  have hmods_ne : ZPoly.modP p s ≠ 0 := by
    intro h0
    apply hmodf_ne
    rw [hmodf_mul, h0]
    exact (DensePoly.mul_comm_poly _ _).trans (DensePoly.zero_mul _)
  have hmodf_prod_size :
      (ZPoly.modP p f).size = (ZPoly.modP p r).size + (ZPoly.modP p s).size - 1 := by
    rw [hmodf_mul]
    exact FpPoly.size_mul_eq_add_sub_one _ _ hmodr_ne hmods_ne
  have hmodr_le : (ZPoly.modP p r).size ≤ r.size := size_modP_le p r
  have hmods_le : (ZPoly.modP p s).size ≤ s.size := size_modP_le p s
  have hmodr_pos : 0 < (ZPoly.modP p r).size := FpPoly.size_pos_of_ne_zero hmodr_ne
  have hmods_pos : 0 < (ZPoly.modP p s).size := FpPoly.size_pos_of_ne_zero hmods_ne
  omega

/-- **Modular square-freeness certificate soundness.**  For a prime `p` not
dividing the leading coefficient of `f`, if `modP f` and `modP f'` are coprime
over `𝔽_p`, then `f` is square-free over `ℚ`. -/
theorem squareFreeRat_of_separableModP
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p] (hp : Hex.Nat.Prime p)
    (hadm : leadingCoeffAdmissible f p)
    (hsep : separableModP f p = true) :
    SquareFreeRat f := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  -- Contrapositive: a positive-degree rational gcd yields a positive-degree
  -- modular common factor, contradicting the unit gcd.
  apply Classical.byContradiction
  intro hnsq
  unfold SquareFreeRat at hnsq
  -- Name the rational gcd `g`.
  obtain ⟨g, hg_eq⟩ :
      ∃ g, g = DensePoly.gcd (toRatPoly f) (DensePoly.derivative (toRatPoly f)) := ⟨_, rfl⟩
  rw [← hg_eq] at hnsq
  have hgt : 1 < g.size := Nat.lt_of_not_ge hnsq
  have hg_dvd_f : g ∣ toRatPoly f := hg_eq ▸ DensePoly.gcd_dvd_left _ _
  have hg_dvd_df : g ∣ DensePoly.derivative (toRatPoly f) := hg_eq ▸ DensePoly.gcd_dvd_right _ _
  have hg_ne : g ≠ 0 := by
    intro h0
    rw [h0, DensePoly.size_zero] at hgt
    omega
  -- `f ≠ 0` (else the gcd would be `gcd 0 0 = 0`).
  have hderiv0 : DensePoly.derivative (0 : DensePoly Rat) = 0 := by
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_derivative _ n (Lean.Grind.Semiring.mul_zero _), DensePoly.coeff_zero,
        DensePoly.coeff_zero]
    exact Lean.Grind.Semiring.mul_zero _
  have hf_ne : f ≠ 0 := by
    intro h0
    apply hg_ne
    rw [hg_eq, h0, toRatPoly_zero, hderiv0, DensePoly.gcd_zero_zero]
  -- The primitive integer clearing `r` of `g`.
  rcases ratPolyPrimitivePart_rational_associate g with ⟨u, hu⟩
  have hr_prim : Primitive (ratPolyPrimitivePart g) :=
    ratPolyPrimitivePart_primitive g
      (content_ne_zero_of_ne_zero _ (ratPolyPrimitivePart_ne_zero_of_ne_zero g hg_ne))
  have hr_ne : ratPolyPrimitivePart g ≠ 0 := ratPolyPrimitivePart_ne_zero_of_ne_zero g hg_ne
  have hu_ne : u ≠ 0 := by
    intro h0
    apply hg_ne
    rw [hu, h0, rat_scale_zero]
  -- `size (ratPolyPrimitivePart g) = size g ≥ 2`.
  have hr_size : 2 ≤ (ratPolyPrimitivePart g).size := by
    have hscale := rat_scale_size_of_ne_zero hu_ne (toRatPoly (ratPolyPrimitivePart g))
    rw [← hu] at hscale
    rw [← size_toRatPoly (ratPolyPrimitivePart g)]
    omega
  -- `toRatPoly (ratPolyPrimitivePart g) ∣ g`, hence `∣ toRatPoly f` and `∣ toRatPoly f'`.
  have htoR_dvd_g : toRatPoly (ratPolyPrimitivePart g) ∣ g := by
    have hd := rat_dvd_scale_of_dvd u (rat_dvd_refl (toRatPoly (ratPolyPrimitivePart g)))
    rw [← hu] at hd
    exact hd
  have htoR_dvd_f : toRatPoly (ratPolyPrimitivePart g) ∣ toRatPoly f :=
    rat_dvd_trans htoR_dvd_g hg_dvd_f
  have htoR_dvd_df : toRatPoly (ratPolyPrimitivePart g) ∣ DensePoly.derivative (toRatPoly f) :=
    rat_dvd_trans htoR_dvd_g hg_dvd_df
  -- Descend to integer divisibility via Gauss.
  have hr_dvd_f : ratPolyPrimitivePart g ∣ f :=
    dvd_of_toRatPoly_dvd_of_primitive hr_prim htoR_dvd_f
  have hr_dvd_df : ratPolyPrimitivePart g ∣ DensePoly.derivative f := by
    apply dvd_of_toRatPoly_dvd_of_primitive hr_prim
    rw [toRatPoly_derivative]
    exact htoR_dvd_df
  -- `f = r * s`.
  obtain ⟨s, hs⟩ := hr_dvd_f
  have hr_dvd_f : ratPolyPrimitivePart g ∣ f := ⟨s, hs⟩
  have hs_ne : s ≠ 0 := by
    intro h0
    apply hf_ne
    rw [hs, h0]
    exact (DensePoly.mul_comm_poly _ _).trans (DensePoly.zero_mul _)
  -- The modular image of `r` keeps its full degree.
  have hmodr_size : (ZPoly.modP p (ratPolyPrimitivePart g)).size = (ratPolyPrimitivePart g).size :=
    size_modP_eq_of_factor f (ratPolyPrimitivePart g) s hs hr_ne hs_ne hadm
  -- `modP r` is a common divisor of `modP f` and `modP f'`.
  have hmodr_dvd_f : ZPoly.modP p (ratPolyPrimitivePart g) ∣ ZPoly.modP p f :=
    modP_dvd_of_dvd hr_dvd_f
  have hmodr_dvd_df :
      ZPoly.modP p (ratPolyPrimitivePart g) ∣ ZPoly.modP p (DensePoly.derivative f) :=
    modP_dvd_of_dvd hr_dvd_df
  have hmodr_dvd_gcd :
      ZPoly.modP p (ratPolyPrimitivePart g) ∣
        DensePoly.gcd (ZPoly.modP p f) (ZPoly.modP p (DensePoly.derivative f)) :=
    DensePoly.dvd_gcd _ _ _ hmodr_dvd_f hmodr_dvd_df
  -- The gcd is nonzero (it divides the nonzero `modP f`).
  have hmodf_ne : ZPoly.modP p f ≠ 0 := modP_ne_zero_of_leadingCoeffAdmissible f p hadm
  have hgcd_ne :
      DensePoly.gcd (ZPoly.modP p f) (ZPoly.modP p (DensePoly.derivative f)) ≠ 0 := by
    intro h0
    apply hmodf_ne
    rcases DensePoly.gcd_dvd_left (ZPoly.modP p f) (ZPoly.modP p (DensePoly.derivative f)) with
      ⟨c, hc⟩
    rw [h0] at hc
    rw [show (0 : FpPoly p) * c = 0 from DensePoly.zero_mul c] at hc
    exact hc
  -- Its size is at least the (≥ 2) size of `modP r`, so it is not a unit.
  have hgcd_size :
      (ZPoly.modP p (ratPolyPrimitivePart g)).size ≤
        (DensePoly.gcd (ZPoly.modP p f) (ZPoly.modP p (DensePoly.derivative f))).size :=
    FpPoly.size_le_of_dvd_of_ne_zero hmodr_dvd_gcd hgcd_ne
  have hgcd_ge_two :
      2 ≤ (DensePoly.gcd (ZPoly.modP p f) (ZPoly.modP p (DensePoly.derivative f))).size := by
    omega
  -- Contradiction with the unit gcd hypothesis.
  unfold separableModP gcdIsUnit at hsep
  have : (DensePoly.gcd (ZPoly.modP p f) (ZPoly.modP p (DensePoly.derivative f))).size = 1 :=
    beq_iff_eq.mp hsep
  omega

end ZPoly
end Hex
