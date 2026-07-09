/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus
public import HexBerlekampMathlib.Basic
public import HexBerlekampZassenhausMathlib.HenselFactorProps
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.HenselFactorProps

public section
set_option backward.proofsInPublic true

/-!
The semantic mod-p factorization bundle (#8625).

`ModPFactorization f data` collects every fact the Berlekamp-Zassenhaus
certification cone actually consumes about a `PrimeChoiceData`: primality,
the good-prime condition for the lift target `f`, the recorded modular image,
and the semantic invariants of the factor array (monic, irreducible, nodup,
pairwise coprime, nonempty, product congruent to `f` mod `p`).

Historically the cone was keyed on the SELECTION witness
`ZPoly.toMonicPrimeData? core = some data`, whose `factorsModPBerlekampForm`
component records that `data.factorsModP` is the LITERAL `berlekampFactor`
output. No consumer needs that literal form (nor any selection-walk fact):
they extract exactly the fields below, via the
`…_of_factorsModPBerlekampForm` family. Keying the cone on this bundle
instead lets the recursive per-remainder re-lift certify pieces whose factor
arrays are dilated tracked sublists of the parent's — semantically valid
factorizations that no Berlekamp run ever produced.

`modPFactorization_of_choosePrimeData` recovers the bundle from the
selection witness, so existing entry points discharge it for free.
-/

namespace HexBerlekampZassenhausMathlib

open Polynomial

/-- Semantic validity of `data` as a mod-p factorization package for the
monic lift target `f`: everything the certification cone consumes about a
`PrimeChoiceData`, with no reference to how it was produced. -/
structure ModPFactorization (f : Hex.ZPoly) (data : Hex.PrimeChoiceData) : Prop where
  prime : Hex.Nat.Prime data.p
  good :
    letI := data.bounds
    Hex.isGoodPrime f data.p = true
  fModP_eq :
    letI := data.bounds
    data.fModP = Hex.ZPoly.modP data.p f
  monic :
    letI := data.bounds
    ∀ g ∈ data.factorsModP, Hex.DensePoly.Monic g
  ne_nil : data.factorsModP.toList ≠ []
  nodup : data.factorsModP.toList.Nodup
  coprime :
    letI := data.bounds
    Hex.ZPoly.QuadraticMultifactorCoprimeSplits data.p data.factorsModP.toList
  irreducible :
    ∀ i : ModPFactorIndex data,
      Irreducible
        (@HexBerlekampMathlib.toMathlibPolynomial data.p data.bounds
          (modPFactor data i))
  product :
    letI := data.bounds
    Hex.ZPoly.congr
      (Array.polyProduct (data.factorsModP.map Hex.FpPoly.liftToZ))
      (Hex.FpPoly.liftToZ
        (Hex.monicModularImage (Hex.ZPoly.modP data.p f)))
      data.p
  natDegree_pos :
    letI := data.bounds
    ∀ g ∈ data.factorsModP,
      0 < (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ g)).natDegree

/-- The `modP`/`liftToZ` roundtrip on an `FpPoly` product: reducing the
integer product of the lifts recovers the `FpPoly` fold product. -/
theorem modP_polyProduct_map_liftToZ {p : Nat} [Hex.ZMod64.Bounds p]
    (arr : Array (Hex.FpPoly p)) :
    Hex.ZPoly.modP p (Array.polyProduct (arr.map Hex.FpPoly.liftToZ)) =
      arr.toList.foldl (· * ·) 1 := by
  cases arr with
  | mk l =>
      suffices h : ∀ acc : Hex.ZPoly,
          Hex.ZPoly.modP p ((l.map Hex.FpPoly.liftToZ).foldl (· * ·) acc) =
            l.foldl (· * ·) (Hex.ZPoly.modP p acc) by
        simpa [Array.polyProduct, Hex.ZPoly.modP_one] using h 1
      intro acc
      induction l generalizing acc with
      | nil => simp
      | cons x xs ih =>
          simp only [List.map_cons, List.foldl_cons]
          rw [ih, modP_mul, Hex.FpPoly.modP_liftToZ]

/-- The selection witness yields the semantic bundle: assemble the fields
from the `choosePrimeData?` extraction lemmas and the
`…_of_factorsModPBerlekampForm` family. The lift target must be monic of
positive degree (which `(toMonic core).monic` always is at the use sites). -/
theorem modPFactorization_of_choosePrimeData
    {f : Hex.ZPoly} {data : Hex.PrimeChoiceData}
    (hchoose : Hex.choosePrimeData? f = some data)
    (hprim : Hex.ZPoly.Primitive f)
    (hlc_pos : 0 < Hex.DensePoly.leadingCoeff f)
    (hpos : 0 < f.degree?.getD 0) :
    ModPFactorization f data := by
  have hprime := Hex.choosePrimeData?_prime f data hchoose
  have hgood := Hex.choosePrimeData?_isGoodPrime f data hchoose
  have hform : Hex.factorsModPBerlekampForm f data := by
    obtain ⟨hzero, heq⟩ :=
      Hex.choosePrimeData?_factorsModP_berlekamp_form f data hchoose
    exact ⟨hprime, hzero, heq⟩
  refine
    { prime := hprime
      good := hgood
      fModP_eq := ?_
      monic := factorsModP_monic_of_factorsModPBerlekampForm f data hform
      ne_nil := factorsModP_ne_nil_of_factorsModPBerlekampForm f data hform
      nodup := factorsModP_nodup_of_factorsModPBerlekampForm f data hform hgood
      coprime := factorsModP_coprime_of_factorsModPBerlekampForm f data hform hgood
      irreducible :=
        factors_irreducible_of_factorsModPBerlekampForm f data hform hgood hpos
      product := ?_
      natDegree_pos :=
        factorsModP_natDegree_pos_of_factorsModPBerlekampForm f data hform
          hgood hpos }
  · exact Hex.choosePrimeData?_fModP_eq f data hchoose
  · exact
      factorsModP_polyProduct_congr_of_factorsModPBerlekampForm_of_primitive_pos_lc_core
        f data hprim hlc_pos hform hgood

/-- Monic-target form of the bundle producer: primitivity and the positive
leading coefficient come from monicity. -/
theorem modPFactorization_of_choosePrimeData_of_monic
    {f : Hex.ZPoly} {data : Hex.PrimeChoiceData}
    (hchoose : Hex.choosePrimeData? f = some data)
    (hmonic : Hex.DensePoly.Monic f)
    (hpos : 0 < f.degree?.getD 0) :
    ModPFactorization f data :=
  modPFactorization_of_choosePrimeData hchoose
    (zpoly_primitive_of_monic hmonic)
    (by rw [show Hex.DensePoly.leadingCoeff f = 1 from hmonic]; exact Int.one_pos)
    hpos

/-- Plain-form product congruence for a monic lift target: the
`monicModularImage` layer collapses, landing at `≡ f (mod p)` (the shape the
`QuadraticMultifactorLiftInvariant` boundary hypotheses consume). -/
theorem ModPFactorization.product_congr_target
    {f : Hex.ZPoly} {data : Hex.PrimeChoiceData}
    (h : ModPFactorization f data)
    (hmonic : Hex.DensePoly.Monic f) :
    letI := data.bounds
    Hex.ZPoly.congr
      (Array.polyProduct (data.factorsModP.map Hex.FpPoly.liftToZ)) f data.p := by
  letI := data.bounds
  letI : Hex.ZMod64.PrimeModulus data.p :=
    Hex.ZMod64.primeModulusOfPrime h.prime
  have hp : 1 < data.p := by have := h.prime.two_le; omega
  have hzero : (Hex.ZPoly.modP data.p f).isZero = false :=
    Hex.isGoodPrime_modP_isZero_false f data.p h.good
  have hcollapse :
      Hex.monicModularImage (Hex.ZPoly.modP data.p f) =
        Hex.ZPoly.modP data.p f :=
    monicModularImage_modP_eq_of_monic f hmonic h.prime hp hzero
  have hprod := h.product
  rw [hcollapse] at hprod
  exact Hex.ZPoly.congr_trans _ _ _ data.p hprod
    (Hex.FpPoly.congr_liftToZ_modP f)

/-- The `toMonicPrimeData?` form of the bundle producer. -/
theorem modPFactorization_of_toMonicPrimeData
    {core : Hex.ZPoly} {data : Hex.PrimeChoiceData}
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some data)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0) :
    ModPFactorization (Hex.ZPoly.toMonic core).monic data := by
  have hpos : 0 < (Hex.ZPoly.toMonic core).monic.degree?.getD 0 := by
    rw [Hex.ZPoly.toMonic_monic_degree_eq_of_pos_degree core hcore_lc_pos hcore_pos]
    exact hcore_pos
  have hmonic : Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
  exact modPFactorization_of_choosePrimeData_of_monic hselected hmonic hpos


/-! ### Piece transport (#8625): dilated tracked factors

`Hex.piecePrimeData?` builds a piece's prime data by undilating the tracked
seed factors; its executable guards verify monicity, positive degree, the
product identity against the piece's monic image, the good-prime condition,
and that the undilation scalar is a genuine unit. The lemmas below transport
irreducibility along `FpPoly.monicDilate` (a unit substitution composed with
a unit scaling) and assemble the piece's `ModPFactorization` from the guards
plus per-seed irreducibility inherited from the parent bundle. -/

section PieceTransport

open Polynomial

variable {q : Nat} [Hex.ZMod64.Bounds q]

private theorem list_getD_map_range {α : Type} [Zero α] (size n : Nat) (f : Nat → α) :
    ((List.range size).map f).getD n (Zero.zero : α) =
      if n < size then f n else (Zero.zero : α) := by
  by_cases hn : n < size
  · simp [hn, List.getD]
  · simp [hn, List.getD]

/-- Coefficientwise description of `FpPoly.monicDilate`. -/
theorem coeff_monicDilate (c : Hex.ZMod64 q) (u : Hex.FpPoly q) (i : Nat) :
    (Hex.FpPoly.monicDilate c u).coeff i =
      if i < u.size then u.coeff i * c ^ (u.size - 1 - i) else 0 := by
  unfold Hex.FpPoly.monicDilate Hex.FpPoly.ofCoeffs
  rw [Hex.DensePoly.coeff_ofCoeffs_list, list_getD_map_range]
  rfl

/-- Coefficient of a composition with a scaled variable. -/
private theorem coeff_comp_C_mul_X {K : Type} [Field K]
    (pl : Polynomial K) (e : K) (j : Nat) :
    (pl.comp (Polynomial.C e * Polynomial.X)).coeff j = pl.coeff j * e ^ j := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, Polynomial.finsetSum_coeff]
  have hterm : ∀ i ∈ pl.support,
      (Polynomial.C (pl.coeff i) * (Polynomial.C e * Polynomial.X) ^ i).coeff j =
        if i = j then pl.coeff i * e ^ i else 0 := by
    intro i _
    rw [mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hij : i = j
    · simp [hij]
    · simp only [if_neg hij, if_neg (fun h : j = i => hij h.symm)]
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' pl.support j
    (fun i => pl.coeff i * e ^ i)]
  by_cases hj : j ∈ pl.support
  · simp [hj]
  · have : pl.coeff j = 0 := Polynomial.notMem_support_iff.mp hj
    simp [hj, this]

/-- `monicDilate c u` transported to `ZMod q` is a unit scalar times a unit
substitution of `u`. -/
theorem toMathlibPolynomial_monicDilate
    (hprime : Hex.Nat.Prime q) (c : Hex.ZMod64 q)
    (hc : HexModArithMathlib.ZMod64.toZMod c ≠ 0) (u : Hex.FpPoly q) :
    haveI : Fact (_root_.Nat.Prime q) := ⟨natPrime_of_hexNatPrime hprime⟩
    HexBerlekampMathlib.toMathlibPolynomial (Hex.FpPoly.monicDilate c u) =
      Polynomial.C (HexModArithMathlib.ZMod64.toZMod c ^ (u.size - 1)) *
        (HexBerlekampMathlib.toMathlibPolynomial u).comp
          (Polynomial.C (HexModArithMathlib.ZMod64.toZMod c)⁻¹ * Polynomial.X) := by
  haveI : Fact (_root_.Nat.Prime q) := ⟨natPrime_of_hexNatPrime hprime⟩
  set e := HexModArithMathlib.ZMod64.toZMod c with he_def
  ext j
  rw [HexBerlekampMathlib.coeff_toMathlibPolynomial, coeff_monicDilate,
    Polynomial.coeff_C_mul, coeff_comp_C_mul_X,
    HexBerlekampMathlib.coeff_toMathlibPolynomial]
  by_cases hj : j < u.size
  · rw [if_pos hj, HexModArithMathlib.ZMod64.toZMod_mul,
      HexModArithMathlib.ZMod64.toZMod_pow]
    rw [inv_pow]
    rw [show u.size - 1 - j = u.size - 1 - j from rfl]
    have hle : j ≤ u.size - 1 := by omega
    rw [show e ^ (u.size - 1) * (HexModArithMathlib.ZMod64.toZMod (u.coeff j) * (e ^ j)⁻¹) =
        HexModArithMathlib.ZMod64.toZMod (u.coeff j) * (e ^ (u.size - 1) * (e ^ j)⁻¹) by ring]
    congr 1
    rw [← pow_sub₀ e hc hle]
  · rw [if_neg hj]
    have hzero : u.coeff j = 0 :=
      Hex.DensePoly.coeff_eq_zero_of_size_le u (Nat.le_of_not_lt hj)
    rw [hzero, HexModArithMathlib.ZMod64.toZMod_zero]
    ring

/-- Irreducibility transports along `monicDilate` by a unit. -/
theorem irreducible_toMathlibPolynomial_monicDilate
    (hprime : Hex.Nat.Prime q) (c : Hex.ZMod64 q)
    (hc : HexModArithMathlib.ZMod64.toZMod c ≠ 0) (u : Hex.FpPoly q)
    (hirr :
      haveI : Fact (_root_.Nat.Prime q) := ⟨natPrime_of_hexNatPrime hprime⟩
      Irreducible (HexBerlekampMathlib.toMathlibPolynomial u)) :
    haveI : Fact (_root_.Nat.Prime q) := ⟨natPrime_of_hexNatPrime hprime⟩
    Irreducible
      (HexBerlekampMathlib.toMathlibPolynomial (Hex.FpPoly.monicDilate c u)) := by
  haveI : Fact (_root_.Nat.Prime q) := ⟨natPrime_of_hexNatPrime hprime⟩
  set e := HexModArithMathlib.ZMod64.toZMod c with he_def
  haveI : Invertible (e⁻¹) := invertibleOfNonzero (inv_ne_zero hc)
  rw [toMathlibPolynomial_monicDilate hprime c hc u]
  have hcomp :
      (HexBerlekampMathlib.toMathlibPolynomial u).comp
          (Polynomial.C e⁻¹ * Polynomial.X) =
        (Polynomial.algEquivCMulXAddC e⁻¹ (0 : ZMod q))
          (HexBerlekampMathlib.toMathlibPolynomial u) := by
    rw [Polynomial.algEquivCMulXAddC_apply, ← Polynomial.comp_eq_aeval]
    simp
  have hirr_comp :
      Irreducible ((Polynomial.algEquivCMulXAddC e⁻¹ (0 : ZMod q))
        (HexBerlekampMathlib.toMathlibPolynomial u)) := by
    exact (MulEquiv.irreducible_iff
      (Polynomial.algEquivCMulXAddC e⁻¹ (0 : ZMod q)).toMulEquiv).mpr hirr
  rw [hcomp]
  have hunit : IsUnit (Polynomial.C (e ^ (u.size - 1)) : Polynomial (ZMod q)) :=
    Polynomial.isUnit_C.mpr (IsUnit.pow _ (Ne.isUnit hc))
  have hassoc :
      Associated
        ((HexBerlekampMathlib.toMathlibPolynomial u).comp
          (Polynomial.C e⁻¹ * Polynomial.X))
        (Polynomial.C (e ^ (u.size - 1)) *
          (HexBerlekampMathlib.toMathlibPolynomial u).comp
            (Polynomial.C e⁻¹ * Polynomial.X)) :=
    ⟨hunit.unit, by rw [IsUnit.unit_spec, mul_comm]⟩
  rw [hcomp] at hassoc
  exact hassoc.irreducible (hcomp ▸ hirr_comp)

end PieceTransport

end HexBerlekampZassenhausMathlib
