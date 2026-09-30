/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexOrderedFn.Infinitesimal
public import HexOrderedFnMathlib.Hahn
public import HexRationalFnMathlib.Correspondence
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.HahnSeries.Lex
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Algebra.Order.Ring.InjSurj

public section

/-!
The lowest-coefficient sign agrees with the ordered Laurent-series interpretation.
This gives the field order, positive infinitesimals and successive-level embeddings.
-/

namespace Hex.OrderedFn.Infinitesimal

attribute [local instance 2000] Field.toGrindField

open HexPolyMathlib
open scoped LaurentSeries RatFunc

variable {K : Type u} [Field K] [DecidableEq K]

/-- The first nonzero coefficient has index `natTrailingDegree`. -/
theorem lowestIndex_eq (p : DensePoly K) :
    lowestIndex p = (toPolynomial p).natTrailingDegree := by
  by_cases hp : p = 0
  · subst p
    rw [toPolynomial_zero, Polynomial.natTrailingDegree_zero]
    exact Array.findIdx_empty
  have hp' : toPolynomial p ≠ 0 := fun h => hp (equiv.injective (h.trans toPolynomial_zero.symm))
  have hn := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp'
  rw [coeff_toPolynomial] at hn
  have hi : (toPolynomial p).natTrailingDegree < p.coeffs.size := by
    by_contra h
    exact hn (DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt h))
  apply (Array.findIdx_eq hi).mpr
  constructor
  · simpa only [bne_iff_ne, DensePoly.coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some] using hn
  · intro j hj
    have h := Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj
    rw [coeff_toPolynomial] at h
    simpa only [bne_eq_false_iff_eq, DensePoly.coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (hj.trans hi), Option.getD_some] using h

/-- The scanned coefficient agrees with the mathematical trailing coefficient. -/
theorem lowestCoeff_eq (p : DensePoly K) :
    lowestCoeff p = (toPolynomial p).trailingCoeff := by
  rw [lowestCoeff, lowestIndex_eq, Polynomial.trailingCoeff, coeff_toPolynomial]

section

/-- Interpret canonical fractions as lexicographically ordered Laurent series. -/
@[expose] noncomputable def embed : RationalFn K →+* Lex (HahnSeries ℤ K) :=
  let wrap : HahnSeries ℤ K →+* Lex (HahnSeries ℤ K) :=
    { toFun := toLex, map_one' := rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl, map_mul' := fun _ _ => rfl }
  wrap.comp ((algebraMap (RatFunc K) K⸨X⸩).comp HexRationalFnMathlib.equiv.toRingHom)

theorem embed_injective : Function.Injective (embed (K := K)) := embed.injective

@[simp] theorem embed_C (a : K) :
    embed (RationalFn.C a) = toLex (HahnSeries.single 0 a) := by
  change toLex (algebraMap (RatFunc K) K⸨X⸩ (HexRationalFnMathlib.toRatFunc _)) = _
  rw [HexRationalFnMathlib.toRatFunc_C]
  change toLex (algebraMap (RatFunc K) K⸨X⸩ (RatFunc.C a)) = _
  rw [← RatFunc.algebraMap_C, ← IsScalarTower.algebraMap_apply]
  simp [HahnSeries.C]

@[simp] theorem embed_X :
    embed (RationalFn.X : RationalFn K) = toLex (HahnSeries.single 1 1) := by
  change toLex (algebraMap (RatFunc K) K⸨X⸩ (HexRationalFnMathlib.toRatFunc _)) = _
  rw [HexRationalFnMathlib.toRatFunc_X]
  exact congrArg toLex RatFunc.coe_X

omit [DecidableEq K] in
private theorem poly_coeff (p : Polynomial K) (i : ℤ) :
    (algebraMap (Polynomial K) K⸨X⸩ p).coeff i =
      if i < 0 then 0 else p.coeff i.natAbs := by
  rw [Polynomial.algebraMap_hahnSeries_apply]
  exact (PowerSeries.coeff_coe (p : PowerSeries K) i).trans (by simp)

omit [DecidableEq K] in
/-- Polynomial order in Laurent series is its lowest nonzero exponent. -/
theorem poly_order {p : Polynomial K} (hp : p ≠ 0) :
    (algebraMap (Polynomial K) K⸨X⸩ p).orderTop = (p.natTrailingDegree : ℤ) := by
  apply HahnSeries.orderTop_eq_of_le
  · simp [HahnSeries.mem_support, hp]
  · intro i hi
    rw [HahnSeries.mem_support, poly_coeff] at hi
    split at hi
    · exact (hi rfl).elim
    · have hn := Polynomial.natTrailingDegree_le_of_ne_zero hi
      omega

omit [DecidableEq K] in
/-- The Laurent-series leading coefficient is the polynomial trailing coefficient. -/
theorem poly_leadingCoeff (p : Polynomial K) :
    (algebraMap (Polynomial K) K⸨X⸩ p).leadingCoeff = p.trailingCoeff := by
  by_cases hp : p = 0
  · simp [hp]
  have ho := poly_order hp
  have hne : algebraMap (Polynomial K) K⸨X⸩ p ≠ 0 :=
    fun h => hp (Polynomial.algebraMap_hahnSeries_injective ℤ (h.trans (map_zero _).symm))
  rw [HahnSeries.leadingCoeff_of_ne_zero hne,
    (WithTop.untop_eq_iff _).mpr ho, poly_coeff]
  simp [Polynomial.trailingCoeff]

/-- The interpretation uses exactly the stored numerator and denominator. -/
theorem embed_eq (f : RationalFn K) :
    embed f = toLex (algebraMap (Polynomial K) K⸨X⸩ (toPolynomial f.num)) /
      toLex (algebraMap (Polynomial K) K⸨X⸩ (toPolynomial f.den)) := by
  change toLex (algebraMap (RatFunc K) K⸨X⸩
    (algebraMap (Polynomial K) (RatFunc K) (toPolynomial f.num) /
      algebraMap (Polynomial K) (RatFunc K) (toPolynomial f.den))) = _
  exact congrArg toLex (RatFunc.algebraMap_apply_div _ _)

/-- Every fraction presentation with nonzero denominator has the same interpretation. -/
theorem embed_fraction {f : RationalFn K} {p q : DensePoly K}
    (hf : RationalFn.Represents f p q) (hq : q ≠ 0) :
    embed f = toLex (algebraMap (Polynomial K) K⸨X⸩ (toPolynomial p)) /
      toLex (algebraMap (Polynomial K) K⸨X⸩ (toPolynomial q)) := by
  change toLex (algebraMap (RatFunc K) K⸨X⸩ (HexRationalFnMathlib.toRatFunc f)) = _
  rw [HexRationalFnMathlib.toRatFunc_eq hf hq]
  exact congrArg toLex (RatFunc.algebraMap_apply_div _ _)

omit [DecidableEq K] in
private theorem poly_ne_zero {p : Polynomial K} (hp : p ≠ 0) :
    algebraMap (Polynomial K) K⸨X⸩ p ≠ 0 :=
  fun h => hp (Polynomial.algebraMap_hahnSeries_injective ℤ (h.trans (map_zero _).symm))

/-- The leading coefficient of a fraction is the quotient of its trailing coefficients. -/
theorem embed_leadingCoeff (f : RationalFn K) :
    (ofLex (embed f)).leadingCoeff = lowestCoeff f.num / lowestCoeff f.den := by
  rw [embed_eq, lowestCoeff_eq, lowestCoeff_eq]
  change (algebraMap (Polynomial K) K⸨X⸩ (toPolynomial f.num) /
    algebraMap (Polynomial K) K⸨X⸩ (toPolynomial f.den)).leadingCoeff = _
  have hd : toPolynomial f.den ≠ 0 :=
    fun h => f.den_ne_zero (equiv.injective (h.trans toPolynomial_zero.symm))
  have h := HahnSeries.leadingCoeff_mul
    (algebraMap (Polynomial K) K⸨X⸩ (toPolynomial f.num) /
      algebraMap (Polynomial K) K⸨X⸩ (toPolynomial f.den))
    (algebraMap (Polynomial K) K⸨X⸩ (toPolynomial f.den))
  rw [div_mul_cancel₀ _ (poly_ne_zero hd), poly_leadingCoeff, poly_leadingCoeff] at h
  apply (eq_div_iff (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hd)).mpr
  exact h.symm

/-- A nonzero fraction has order equal to the difference of its lowest exponents. -/
theorem embed_order (f : RationalFn K) (hf : f ≠ 0) :
    (ofLex (embed f)).order = (lowestIndex f.num : ℤ) - (lowestIndex f.den : ℤ) := by
  have hn : toPolynomial f.num ≠ 0 := by
    intro h
    apply hf
    exact (RationalFn.num_eq_zero f).mp (equiv.injective (h.trans toPolynomial_zero.symm))
  have hd : toPolynomial f.den ≠ 0 :=
    fun h => f.den_ne_zero (equiv.injective (h.trans toPolynomial_zero.symm))
  have orders (p : Polynomial K) (hp : p ≠ 0) :
      (algebraMap (Polynomial K) K⸨X⸩ p).order = (p.natTrailingDegree : ℤ) := by
    apply WithTop.coe_injective
    rw [HahnSeries.order_eq_orderTop_of_ne_zero (poly_ne_zero hp)]
    exact poly_order hp
  rw [embed_eq, lowestIndex_eq, lowestIndex_eq]
  change (algebraMap (Polynomial K) K⸨X⸩ (toPolynomial f.num) /
    algebraMap (Polynomial K) K⸨X⸩ (toPolynomial f.den)).order = _
  have h := HahnSeries.order_mul
    (div_ne_zero (poly_ne_zero hn) (poly_ne_zero hd)) (poly_ne_zero hd)
  rw [div_mul_cancel₀ _ (poly_ne_zero hd), orders _ hn, orders _ hd] at h
  omega

variable [LinearOrder K] [IsStrictOrderedRing K]

omit [IsStrictOrderedRing K] in
/-- Integer-valued sign agrees with Mathlib's three-valued sign. -/
theorem orderSign_eq (a : K) : orderSign a = (SignType.sign a : Int) := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · simp [orderSign, ha]
  · simp [orderSign]
  · simp [orderSign, ha, ha.ne', ha.not_gt]

omit [DecidableEq K] [IsStrictOrderedRing K] in
private theorem sign_poly (p : Polynomial K) :
    SignType.sign (toLex (algebraMap (Polynomial K) K⸨X⸩ p)) =
      SignType.sign p.trailingCoeff := by
  rw [← poly_leadingCoeff p]
  have hp := HahnSeries.leadingCoeff_pos_iff (x := toLex (algebraMap (Polynomial K) K⸨X⸩ p))
  have hn := HahnSeries.leadingCoeff_neg_iff (x := toLex (algebraMap (Polynomial K) K⸨X⸩ p))
  simp only [ofLex_toLex] at hp hn
  simp only [sign_apply, hp, hn]

/-- Any correct predecessor sign gives the Hahn sign of the canonical fraction. -/
theorem sign_eq (baseSign : K → Int)
    (hs : ∀ a, baseSign a = (SignType.sign a : Int)) (f : RationalFn K) :
    sign baseSign f = (SignType.sign (embed f) : Int) := by
  by_cases hz : f = 0
  · subst f
    simp
  have hn : f.num ≠ 0 := fun h => hz ((RationalFn.num_eq_zero f).mp h)
  rw [sign, ite_eq_right hn, hs, hs, lowestCoeff_eq, lowestCoeff_eq, embed_eq,
    div_eq_mul_inv, sign_mul]
  have hi (x : Lex K⸨X⸩) : SignType.sign x⁻¹ = SignType.sign x := by
    simp only [sign_apply, inv_pos, inv_lt_zero]
  rw [hi, sign_poly, sign_poly, SignType.coe_mul]

/-- The infinitesimal sign agrees with the sign in the Hahn field. -/
theorem sign_orderSign (f : RationalFn K) :
    sign orderSign f = (SignType.sign (embed f) : Int) := sign_eq _ orderSign_eq f

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem lowestIndex_map {L : Type v} [Field L] [DecidableEq L]
    (f : K →+* L) (p : DensePoly K) :
    lowestIndex (DensePoly.Interpret.map f (HexRationalFnMathlib.coeff_zero_iff f) p) =
      lowestIndex p := by
  unfold lowestIndex
  change (DensePoly.Interpret.map f (HexRationalFnMathlib.coeff_zero_iff f) p).toArray.findIdx
      (fun c => c != 0) = p.toArray.findIdx (fun c => c != 0)
  rw [DensePoly.Interpret.map_array]
  have predicate : (fun c : L => c != 0) ∘ f = (fun c : K => c != 0) := by
    funext c
    simp only [Function.comp_apply, Lean.Grind.bne_eq_decide_not_eq]
    by_cases h : c = 0 <;> simp [h]
  unfold Array.findIdx
  rw [Array.findIdx?_map, predicate]
  simp

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem lowestCoeff_map {L : Type v} [Field L] [DecidableEq L]
    (f : K →+* L) (p : DensePoly K) :
    lowestCoeff (DensePoly.Interpret.map f (HexRationalFnMathlib.coeff_zero_iff f) p) =
      f (lowestCoeff p) := by
  simp only [lowestCoeff, lowestIndex_map, DensePoly.Interpret.map_coeff]

omit [IsStrictOrderedRing K] in
/-- Coefficient-field embeddings preserve the selected infinitesimal sign. -/
theorem mapHom_sign {L : Type v} [Field L] [DecidableEq L]
    [LinearOrder L] [IsStrictOrderedRing L]
    (f : K →+* L) (ordered : StrictMono f) (q : RationalFn K) :
    sign orderSign (HexRationalFnMathlib.mapHom f q) = sign orderSign q := by
  change sign orderSign (HexRationalFnMathlib.coeffMap f q) = _
  unfold sign
  simp only [HexRationalFnMathlib.coeffMap, RationalFn.mapCoeffs_num,
    RationalFn.mapCoeffs_den, DensePoly.Interpret.map_eq_zero,
    lowestCoeff_map]
  have hsign (a : K) : orderSign (f a) = orderSign a := by
    rw [orderSign_eq, orderSign_eq, ordered.sign_comp]
  simp only [hsign]

/-- The sign does not depend on the choice of numerator and denominator. -/
theorem sign_fraction (baseSign : K → Int)
    (hs : ∀ a, baseSign a = (SignType.sign a : Int))
    {f : RationalFn K} {p q : DensePoly K}
    (hf : RationalFn.Represents f p q) (hq : q ≠ 0) :
    sign baseSign f = baseSign (lowestCoeff p) * baseSign (lowestCoeff q) := by
  rw [sign_eq _ hs, embed_fraction hf hq, hs, hs, lowestCoeff_eq, lowestCoeff_eq,
    div_eq_mul_inv, _root_.sign_mul]
  have hi (x : Lex K⸨X⸩) : SignType.sign x⁻¹ = SignType.sign x := by
    simp only [sign_apply, inv_pos, inv_lt_zero]
  rw [hi, sign_poly, sign_poly, SignType.coe_mul]

/-- Normalization and cancellation preserve the lowest-coefficient sign. -/
theorem sign_normalize (plan : DensePoly.MulPlan K) (p q : DensePoly K) (hq : q ≠ 0) :
    sign orderSign (RationalFn.normalizeWith plan p q hq) =
      orderSign (lowestCoeff p) * orderSign (lowestCoeff q) :=
  sign_fraction _ orderSign_eq (RationalFn.normalizeWith_spec plan p q hq) hq

/-- The infinitesimal sign changes sign under negation. -/
theorem sign_neg (f : RationalFn K) : sign orderSign (-f) = -sign orderSign f := by
  rw [sign_orderSign, sign_orderSign, map_neg, Left.sign_neg, SignType.coe_neg]

/-- The infinitesimal sign is multiplicative. -/
theorem sign_mul (f g : RationalFn K) :
    sign orderSign (f * g) = sign orderSign f * sign orderSign g := by
  rw [sign_orderSign, sign_orderSign, sign_orderSign, map_mul, _root_.sign_mul,
    SignType.coe_mul]

/-- The sign vanishes exactly at the zero rational function. -/
theorem sign_eq_zero_iff (f : RationalFn K) : sign orderSign f = 0 ↔ f = 0 := by
  rw [sign_orderSign]
  have hz : (SignType.sign (embed f) : Int) = 0 ↔ embed f = 0 := by
    rcases lt_trichotomy (embed f) 0 with h | h | h
    · simp [h, h.ne]
    · simp [h]
    · simp [h, h.ne']
  rw [hz, ← map_zero embed, embed_injective.eq_iff]

/-- Comparison agrees with the order in the Hahn field. -/
theorem compare_eq (f g : RationalFn K) :
    compare orderSign f g = compareOfLessAndEq (embed f) (embed g) := by
  unfold compare
  rw [sign_orderSign, map_sub embed f g]
  rcases lt_trichotomy (embed f) (embed g) with h | h | h
  · simp [compareOfLessAndEq, sub_neg.mpr h, h]
  · simp [compareOfLessAndEq, h]
  · simp [compareOfLessAndEq, sub_pos.mpr h, h.not_gt, h.ne']

open scoped Hex.OrderedFn.Infinitesimal

private theorem cast_sign_neg {L : Type*} [Zero L] [LinearOrder L] (a : L) :
    (SignType.sign a : Int) < 0 ↔ a < 0 := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · simp [ha]
  · simp
  · simp [ha, ha.not_gt]

private theorem cast_sign_nonpos {L : Type*} [Zero L] [LinearOrder L] (a : L) :
    (SignType.sign a : Int) ≤ 0 ↔ a ≤ 0 := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · simp [ha, ha.le]
  · simp
  · simp [ha, ha.not_ge]

/-- Strict comparison is the pullback of the ordered Hahn model. -/
theorem embed_lt (f g : RationalFn K) : f < g ↔ embed f < embed g := by
  change sign orderSign (f - g) < 0 ↔ _
  rw [sign_orderSign, cast_sign_neg, map_sub embed f g, sub_neg]

/-- Nonstrict comparison is the pullback of the ordered Hahn model. -/
theorem embed_le (f g : RationalFn K) : f ≤ g ↔ embed f ≤ embed g := by
  change sign orderSign (f - g) ≤ 0 ↔ _
  rw [sign_orderSign, cast_sign_nonpos, map_sub embed f g, sub_nonpos]

/-- The infinitesimal order is a linear order. -/
scoped instance linearOrder : LinearOrder (RationalFn K) where
  le_refl f := (embed_le f f).mpr le_rfl
  le_trans f g h hfg hgh := (embed_le f h).mpr
    ((embed_le f g).mp hfg |>.trans ((embed_le g h).mp hgh))
  le_antisymm f g hfg hgf := embed_injective
    (le_antisymm ((embed_le f g).mp hfg) ((embed_le g f).mp hgf))
  le_total f g := (le_total (embed f) (embed g)).imp
    (embed_le f g).mpr (embed_le g f).mpr
  lt_iff_le_not_ge f g := by rw [embed_lt, embed_le, embed_le, lt_iff_le_not_ge]
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance
  toDecidableEq := inferInstance

/-- The infinitesimal order makes the rational-function field an ordered field. -/
scoped instance strictOrderedRing : IsStrictOrderedRing (RationalFn K) :=
  Function.Injective.isStrictOrderedRing embed (map_zero _) (map_one _)
    (map_add _) (map_mul _) (fun {_ _} => (embed_le _ _).symm)
    (fun {_ _} => (embed_lt _ _).symm)

/-- Ordered-ring laws for the core rational-function field structure. -/
scoped instance orderedRing : Lean.Grind.OrderedRing (RationalFn K) where
  add_le_left_iff := fun c => (add_le_add_iff_right c).symm
  zero_lt_one := zero_lt_one
  mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := mul_lt_mul_of_pos_right

/-- A negative rational function has sign minus one. -/
theorem sign_of_neg {f : RationalFn K} (hf : f < 0) : sign orderSign f = -1 := by
  have h := (embed_lt f 0).mp hf
  rw [map_zero] at h
  simp [sign_orderSign, h]

/-- A positive rational function has sign one. -/
theorem sign_of_pos {f : RationalFn K} (hf : 0 < f) : sign orderSign f = 1 := by
  have h := (embed_lt 0 f).mp hf
  rw [map_zero] at h
  simp [sign_orderSign, h]

/-- Constants retain the predecessor field's order. -/
theorem C_lt (a b : K) : RationalFn.C a < RationalFn.C b ↔ a < b := by
  rw [embed_lt, embed_C, embed_C, ← sub_pos]
  change 0 < toLex (HahnSeries.single (0 : ℤ) b - HahnSeries.single 0 a) ↔ _
  rw [← HahnSeries.single_sub]
  rw [← HahnSeries.leadingCoeff_pos_iff]
  simp only [ofLex_toLex, HahnSeries.leadingCoeff_of_single, sub_pos]

/-- The indeterminate is positive. -/
theorem X_pos : (0 : RationalFn K) < RationalFn.X := by
  rw [embed_lt, map_zero, embed_X, ← HahnSeries.leadingCoeff_pos_iff]
  simp

/-- The indeterminate is smaller than every positive coefficient. -/
theorem X_lt_C (a : K) (ha : 0 < a) : RationalFn.X < RationalFn.C a := by
  rw [embed_lt, embed_X, embed_C, HahnSeries.lt_iff]
  refine ⟨0, ?_, ?_⟩
  · intro j hj
    simp [ne_of_lt hj, show j ≠ (1 : ℤ) by omega]
  · simpa using ha

/-- The reciprocal of the indeterminate exceeds every coefficient. -/
theorem C_lt_inv_X (a : K) : RationalFn.C a < (RationalFn.X : RationalFn K)⁻¹ := by
  rw [embed_lt, map_inv₀, embed_X, embed_C]
  change toLex (HahnSeries.single (0 : ℤ) a) < toLex ((HahnSeries.single (1 : ℤ) (1 : K))⁻¹)
  rw [HahnSeries.inv_single, inv_one, HahnSeries.lt_iff]
  refine ⟨-1, ?_, ?_⟩
  · intro j hj
    simp [ne_of_lt hj, show j ≠ (0 : ℤ) by omega]
  · simp

/-- The reciprocal of the indeterminate is larger than every integer. -/
theorem intCast_lt_inv_X (n : ℤ) : (n : RationalFn K) < RationalFn.X⁻¹ := by
  have h := C_lt_inv_X (n : K)
  have hc : RationalFn.C (n : K) = (n : RationalFn K) :=
    map_intCast (HexRationalFnMathlib.constantHom (K := K)) n
  rwa [hc] at h

/-- A new infinitesimal is below every power of the preceding infinitesimal. -/
theorem X_lt_pow (n : ℕ) :
    (RationalFn.X : RationalFn (RationalFn K)) < RationalFn.C (RationalFn.X ^ n) :=
  X_lt_C _ (pow_pos X_pos n)

/-- The embedding of the infinitesimal field into Hahn series is strictly monotone. -/
theorem embed_strictMono : StrictMono (embed (K := K)) := fun _ _ h => (embed_lt _ _).mp h

/-- Mapping coefficients through an ordered field embedding preserves the
infinitesimal rational-function order. -/
theorem mapHom_strictMono {L : Type v} [Field L] [DecidableEq L]
    [LinearOrder L] [IsStrictOrderedRing L]
    (f : K →+* L) (ordered : StrictMono f) :
    StrictMono (HexRationalFnMathlib.mapHom f) := by
  intro p q hpq
  change sign orderSign (p - q) < 0 at hpq
  change sign orderSign
    (HexRationalFnMathlib.mapHom f p - HexRationalFnMathlib.mapHom f q) < 0
  rw [← map_sub, mapHom_sign f ordered]
  exact hpq

/-- Interpret two successive infinitesimals in the iterated Hahn field. -/
noncomputable def towerEmbed : RationalFn (RationalFn K) →+* Lex (HahnSeries ℤ (Lex (HahnSeries ℤ K))) :=
  (Hahn.mapHom (embed (K := K))).comp (embed (K := RationalFn K))

/-- The two-level interpretation preserves and reflects order. -/
theorem towerEmbed_lt (f g : RationalFn (RationalFn K)) :
    towerEmbed f < towerEmbed g ↔ f < g := by
  exact (Hahn.map_lt _ embed_strictMono _ _).trans (embed_lt f g).symm

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The two-level interpretation commutes with constant embeddings. -/
theorem towerEmbed_C (a : RationalFn K) :
    towerEmbed (RationalFn.C a) = toLex (HahnSeries.single 0 (embed a)) := by
  change Hahn.mapHom embed (embed (RationalFn.C a)) = _
  rw [embed_C, Hahn.map_C]

end
end Hex.OrderedFn.Infinitesimal
