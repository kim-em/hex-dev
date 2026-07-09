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

/-- Positive `toPolynomial` degree of an integer lift, from positive
executable degree of the `FpPoly` source (the bridge inside
`factorsModP_natDegree_pos_of_factorsModPBerlekampForm`, extracted). -/
theorem natDegree_toPolynomial_liftToZ_pos {g : Hex.FpPoly q}
    (hg_pos : 0 < g.degree?.getD 0) :
    0 < (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ g)).natDegree := by
  have hg_size_pos : 0 < g.size := by
    unfold Hex.DensePoly.degree? at hg_pos
    by_cases hgz : g.size = 0
    · simp [hgz] at hg_pos
    · exact Nat.pos_of_ne_zero hgz
  have hg_lead_ne : g.coeff (g.size - 1) ≠ (0 : Hex.ZMod64 q) :=
    Hex.DensePoly.coeff_last_ne_zero_of_pos_size g hg_size_pos
  have hg_lead_toNat_ne : (g.coeff (g.size - 1)).toNat ≠ 0 := by
    intro h
    apply hg_lead_ne
    have heq_zero : g.coeff (g.size - 1) = Hex.ZMod64.zero := by
      apply (Hex.ZMod64.eq_iff_toNat_eq _ _).mpr
      rw [Hex.ZMod64.toNat_zero, h]
    exact heq_zero
  have hlift_coeff_ne :
      (Hex.FpPoly.liftToZ g).coeff (g.size - 1) ≠ (0 : Int) := by
    rw [Hex.FpPoly.coeff_liftToZ]
    intro h
    exact hg_lead_toNat_ne (by simpa [Int.ofNat_eq_zero] using h)
  have hlift_size_le : (Hex.FpPoly.liftToZ g).size ≤ g.size := by
    unfold Hex.FpPoly.liftToZ
    have := Hex.DensePoly.size_ofCoeffs_le
      (((List.range g.size).map fun i => Int.ofNat (g.coeff i).toNat).toArray)
    simpa using this
  have hlift_size_ge : g.size ≤ (Hex.FpPoly.liftToZ g).size := by
    by_contra h
    have hlt : (Hex.FpPoly.liftToZ g).size < g.size := Nat.not_le.mp h
    have hle : (Hex.FpPoly.liftToZ g).size ≤ g.size - 1 := Nat.le_pred_of_lt hlt
    exact hlift_coeff_ne
      (Hex.DensePoly.coeff_eq_zero_of_size_le (Hex.FpPoly.liftToZ g) hle)
  have hlift_size_eq : (Hex.FpPoly.liftToZ g).size = g.size :=
    Nat.le_antisymm hlift_size_le hlift_size_ge
  have hlift_degree_eq :
      (Hex.FpPoly.liftToZ g).degree? = g.degree? := by
    unfold Hex.DensePoly.degree?
    rw [hlift_size_eq]
  have hnatDeg_eq :
      (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ g)).natDegree =
        (Hex.FpPoly.liftToZ g).degree?.getD 0 :=
    HexPolyMathlib.natDegree_toPolynomial _
  rw [hnatDeg_eq, hlift_degree_eq]
  exact hg_pos

/-- A factor list of positive-degree factors whose product has no squared
nontrivial divisor has no duplicates: a repeated factor would contribute a
square. -/
theorem nodup_of_factorProduct_no_squared
    (hprime : Hex.Nat.Prime q)
    {factors : List (Hex.FpPoly q)} {mg : Hex.FpPoly q}
    (hprod : Hex.Berlekamp.factorProduct factors = mg)
    (h_no_squared :
      ∀ d : Hex.FpPoly q, d * d ∣ mg → ¬ (0 < d.degree?.getD 0))
    (hdeg : ∀ v ∈ factors, 0 < v.degree?.getD 0) :
    factors.Nodup := by
  haveI : Fact (_root_.Nat.Prime q) := ⟨natPrime_of_hexNatPrime hprime⟩
  by_contra hdup
  obtain ⟨v, hv⟩ := List.exists_duplicate_iff_not_nodup.mpr hdup
  have hv_mem : v ∈ factors := hv.mem
  have hsub : List.Sublist [v, v] factors := List.duplicate_iff_sublist.mp hv
  have hdvd :
      HexBerlekampMathlib.toMathlibPolynomial v *
          HexBerlekampMathlib.toMathlibPolynomial v ∣
        HexBerlekampMathlib.toMathlibPolynomial mg := by
    have hsub_m := Multiset.coe_le.mpr
      (hsub.map HexBerlekampMathlib.toMathlibPolynomial).subperm
    have hdvd_prod := Multiset.prod_dvd_prod_of_le hsub_m
    have hprod_eq :
        ((factors.map HexBerlekampMathlib.toMathlibPolynomial : List _) :
            Multiset _).prod =
          HexBerlekampMathlib.toMathlibPolynomial mg := by
      rw [Multiset.prod_coe, ← toMathlibPolynomial_listFoldlMul_one]
      show HexBerlekampMathlib.toMathlibPolynomial
        (Hex.Berlekamp.factorProduct factors) = _
      rw [hprod]
    rw [hprod_eq] at hdvd_prod
    simpa [Multiset.prod_coe] using hdvd_prod
  -- Pull the divisibility back through the ring equivalence.
  have hdvd_fp : v * v ∣ mg := by
    obtain ⟨w, hw⟩ := hdvd
    refine ⟨(HexBerlekampMathlib.fpPolyEquiv (p := q)).symm w, ?_⟩
    have h1 := congrArg (HexBerlekampMathlib.fpPolyEquiv (p := q)).symm hw
    rw [map_mul, map_mul] at h1
    simpa [← HexBerlekampMathlib.fpPolyEquiv_apply,
      RingEquiv.symm_apply_apply] using h1
  exact h_no_squared v hdvd_fp (hdeg v hv_mem)

/-- `modP` of a monic integer polynomial is monic (for `1 < p`). Extracted
from the interior of `monicModularImage_modP_eq_of_monic`. -/
theorem monic_modP_of_monic
    (core : Hex.ZPoly) (hcore_monic : Hex.DensePoly.Monic core)
    (hp : 1 < q) :
    Hex.DensePoly.Monic (Hex.ZPoly.modP q core) := by
  have hcore_size_pos : 0 < core.size := zpoly_size_pos_of_monic hcore_monic
  have hcore_lead_one : core.coeff (core.size - 1) = 1 := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last core hcore_size_pos]
    exact hcore_monic
  have hmod1 : 1 % q = 1 := Nat.mod_eq_of_lt hp
  have htoNat_one : (1 : Hex.ZMod64 q).toNat = 1 := by
    show Hex.ZMod64.one.toNat = 1
    rw [Hex.ZMod64.toNat_one, hmod1]
  have hone_ne_zero_zmod : (1 : Hex.ZMod64 q) ≠ 0 := by
    intro h
    have hnat := congrArg Hex.ZMod64.toNat h
    rw [htoNat_one, show (0 : Hex.ZMod64 q) = Hex.ZMod64.zero from rfl,
        Hex.ZMod64.toNat_zero] at hnat
    exact (by decide : (1 : Nat) ≠ 0) hnat
  have hmodP_coeff_lead :
      (Hex.ZPoly.modP q core).coeff (core.size - 1) = (1 : Hex.ZMod64 q) := by
    rw [Hex.ZPoly.coeff_modP, hcore_lead_one]
    have hintModNat : Hex.ZPoly.intModNat (1 : Int) q = 1 := by
      show Int.toNat ((1 : Int) % Int.ofNat q) = 1
      have hppos : (1 : Int) < Int.ofNat q := Int.ofNat_lt.mpr hp
      have h0 : (0 : Int) ≤ 1 := by decide
      rw [Int.emod_eq_of_lt h0 hppos]
      rfl
    rw [hintModNat]
    rfl
  have hmodP_size_le : (Hex.ZPoly.modP q core).size ≤ core.size := by
    unfold Hex.ZPoly.modP Hex.FpPoly.ofCoeffs
    have := Hex.DensePoly.size_ofCoeffs_le
      (((List.range core.size).map fun i =>
          Hex.ZMod64.ofNat q (Hex.ZPoly.intModNat (core.coeff i) q)).toArray)
    simpa using this
  have hmodP_size_ge : core.size ≤ (Hex.ZPoly.modP q core).size := by
    by_contra hneg
    have hlt : (Hex.ZPoly.modP q core).size < core.size := Nat.not_le.mp hneg
    have hle : (Hex.ZPoly.modP q core).size ≤ core.size - 1 := Nat.le_pred_of_lt hlt
    have hzero_coeff :
        (Hex.ZPoly.modP q core).coeff (core.size - 1) = 0 :=
      Hex.DensePoly.coeff_eq_zero_of_size_le _ hle
    rw [hzero_coeff] at hmodP_coeff_lead
    exact hone_ne_zero_zmod hmodP_coeff_lead.symm
  have hmodP_size_eq : (Hex.ZPoly.modP q core).size = core.size :=
    Nat.le_antisymm hmodP_size_le hmodP_size_ge
  have hmodP_size_pos : 0 < (Hex.ZPoly.modP q core).size := by
    rw [hmodP_size_eq]; exact hcore_size_pos
  show Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP q core) = 1
  rw [Hex.FpPoly.leadingCoeff_eq_coeff_pred _ hmodP_size_pos, hmodP_size_eq]
  exact hmodP_coeff_lead

/-- **The fresh per-remainder partition producer (#8625).** A successful
`piecePrimeData?` yields a semantic bundle for the piece's monic transform:
`good`, `fModP_eq`, `monic`, `ne_nil`, `natDegree_pos`, and `product` read
off the executable guards; `nodup` and `coprime` follow from squarefreeness
of the piece's image; and `irreducible` transports from the parent's tracked
seeds along the unit undilation. -/
theorem modPFactorization_of_piecePrimeData
    (hprime : Hex.Nat.Prime q)
    {piece : Hex.ZPoly} {cofLc : Int} {seeds : List (Hex.FpPoly q)}
    {pd' : Hex.PrimeChoiceData}
    (hmonicT : Hex.DensePoly.Monic (Hex.ZPoly.toMonic piece).monic)
    (hirr_seeds :
      haveI : Fact (_root_.Nat.Prime q) := ⟨natPrime_of_hexNatPrime hprime⟩
      ∀ u ∈ seeds, Irreducible (HexBerlekampMathlib.toMathlibPolynomial u))
    (h : Hex.piecePrimeData? piece cofLc seeds = some pd') :
    ModPFactorization (Hex.ZPoly.toMonic piece).monic pd' := by
  haveI : Fact (_root_.Nat.Prime q) := ⟨natPrime_of_hexNatPrime hprime⟩
  letI : Hex.ZMod64.PrimeModulus q := Hex.ZMod64.primeModulusOfPrime hprime
  have hp1 : 1 < q := by have := hprime.two_le; omega
  simp only [Hex.piecePrimeData?] at h
  set c := Hex.ZMod64.ofNat q (Hex.ZPoly.intModNat cofLc q) with hc_def
  set f := (Hex.ZPoly.toMonic piece).monic with hf_def
  set factors := seeds.map (Hex.FpPoly.monicDilate c⁻¹) with hfactors_def
  set mg := Hex.ZPoly.modP q f with hmg_def
  split at h
  · exact absurd h (by simp)
  · rename_i hguard1
    split at h
    · rename_i hguard2
      -- Unpack the unit/nonempty guard.
      rw [Bool.or_eq_true, not_or] at hguard1
      obtain ⟨hunit_b, hempty_b⟩ := hguard1
      have hunit : c⁻¹ * c = 1 := by
        simpa [bne_iff_ne] using hunit_b
      have hseeds_ne : seeds ≠ [] := by
        simpa [List.isEmpty_iff] using hempty_b
      -- Unpack the factor guards.
      rw [Bool.and_eq_true, Bool.and_eq_true] at hguard2
      obtain ⟨⟨hall_b, hprod_b⟩, hgood_b⟩ := hguard2
      have hprod : factors.foldl (· * ·) 1 = mg := by
        simpa using hprod_b
      have hall : ∀ v ∈ factors,
          Hex.DensePoly.leadingCoeff v = 1 ∧ 1 ≤ v.degree?.getD 0 := by
        intro v hv
        have := (List.all_eq_true.mp hall_b) v hv
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
        exact this
      have hfactorProduct : Hex.Berlekamp.factorProduct factors = mg := hprod
      -- The undilation scalar is a unit on the `ZMod q` side.
      have htoZ_inv_ne : HexModArithMathlib.ZMod64.toZMod c⁻¹ ≠ 0 := by
        intro h0
        have := congrArg HexModArithMathlib.ZMod64.toZMod hunit
        rw [HexModArithMathlib.ZMod64.toZMod_mul, h0, zero_mul,
          HexModArithMathlib.ZMod64.toZMod_one] at this
        exact zero_ne_one this
      -- Squarefreeness data for the piece's image.
      have hmg_monic : Hex.DensePoly.Monic mg :=
        monic_modP_of_monic f hmonicT hp1
      have hzero : mg.isZero = false :=
        Hex.isGoodPrime_modP_isZero_false f q hgood_b
      have hmg_ne : mg ≠ 0 := by
        intro h0
        rw [h0] at hzero
        exact Bool.noConfusion hzero
      have hsf := squareFree_common_of_squareFreeModP f
        (Hex.isGoodPrime_squareFreeModP f q hgood_b)
      have h_no_squared :
          ∀ d : Hex.FpPoly q, d * d ∣ mg → ¬ (0 < d.degree?.getD 0) := by
        intro d hdd hpos
        have hunit_d : Hex.Berlekamp.isUnitPolynomial d = true :=
          Hex.Berlekamp.isUnitPolynomial_of_squareFree_of_squared_dvd hsf hdd
        have hdeg : Hex.DensePoly.degree? d = some 0 := by
          unfold Hex.Berlekamp.isUnitPolynomial at hunit_d
          cases hd : Hex.DensePoly.degree? d with
          | none => rw [hd] at hunit_d; simp at hunit_d
          | some k =>
              rw [hd] at hunit_d
              cases k with
              | zero => rfl
              | succ _ => simp at hunit_d
        rw [hdeg] at hpos
        simp at hpos
      have hdeg_each : ∀ v ∈ factors, 0 < v.degree?.getD 0 := by
        intro v hv
        have := (hall v hv).2
        omega
      have hnodup : factors.Nodup :=
        nodup_of_factorProduct_no_squared hprime hfactorProduct h_no_squared
          hdeg_each
      -- Assemble the record and the bundle.
      rw [Option.some.injEq] at h
      subst h
      refine
        { prime := hprime
          good := hgood_b
          fModP_eq := rfl
          monic := ?_
          ne_nil := ?_
          nodup := ?_
          coprime := ?_
          irreducible := ?_
          product := ?_
          natDegree_pos := ?_ }
      · intro g hg
        have hg' : g ∈ factors := by simpa using hg
        exact (hall g hg').1
      · show factors.toArray.toList ≠ []
        intro hnil
        have : factors = [] := by simpa using hnil
        rw [hfactors_def] at this
        exact hseeds_ne (List.map_eq_nil_iff.mp this)
      · simpa using hnodup
      · have := quadraticMultifactorCoprimeSplits_of_factorProduct_no_squared
          mg hmg_ne h_no_squared factors
          (by rw [hfactorProduct]; exact Hex.DensePoly.dvd_refl_poly mg)
        simpa using this
      · intro i
        have hmem : modPFactor
            { p := q, fModP := mg, factorsModP := factors.toArray } i ∈
              factors := by
          have : modPFactor
              { p := q, fModP := mg, factorsModP := factors.toArray } i ∈
                factors.toArray := by
            simp [modPFactor]
          simpa using this
        obtain ⟨u, hu_mem, hu_eq⟩ := List.mem_map.mp hmem
        rw [← hu_eq]
        exact irreducible_toMathlibPolynomial_monicDilate hprime c⁻¹
          htoZ_inv_ne u (hirr_seeds u hu_mem)
      · -- product congruence, through the roundtrip and the guard equality
        have hA : Hex.ZPoly.modP q
            (Array.polyProduct (factors.toArray.map Hex.FpPoly.liftToZ)) = mg := by
          rw [modP_polyProduct_map_liftToZ]
          simpa using hprod
        have hcollapse :
            Hex.monicModularImage (Hex.ZPoly.modP q f) = Hex.ZPoly.modP q f :=
          monicModularImage_modP_eq_of_monic f hmonicT hprime hp1 hzero
        show Hex.ZPoly.congr _ _ q
        rw [hcollapse, ← hmg_def, ← hA]
        exact Hex.ZPoly.congr_symm _ _ _
          (Hex.FpPoly.congr_liftToZ_modP _)
      · intro g hg
        have hg' : g ∈ factors := by simpa using hg
        exact natDegree_toPolynomial_liftToZ_pos (by
          have := (hall g hg').2
          omega)
    · exact absurd h (by simp)

end PieceTransport

end HexBerlekampZassenhausMathlib
