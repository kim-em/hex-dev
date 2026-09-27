/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SelectedRoot
public import HexRealClosure.Canonical
public import HexRealAlgebraicMathlib.IntegerRoots
public import HexRealAlgebraicMathlib.Field
public import HexSturmMathlib.Rational

public section

namespace Hex.RealClosure

/-- The executable Horner loop agrees with the existing polynomial
interpretation at a canonical real-algebraic argument. -/
theorem evalCanonical_real (p : DensePoly Rat) (x : Hex.RealAlgebraicNumber) :
    (evalCanonical p x).toReal = (realPoly p).eval x.toReal := by
  classical
  have hz (q : Rat) : Hex.RealAlgebraicNumber.ofRat q = 0 ↔ q = 0 := by
    constructor
    · intro h
      have hr := congrArg Hex.RealAlgebraicNumber.toReal h
      have hcast : (q : ℝ) = 0 := by simpa using hr
      exact_mod_cast hcast
    · intro h
      subst q
      apply Hex.RealAlgebraicNumber.toReal_injective
      simp
  let mapped := DensePoly.Interpret.map Hex.RealAlgebraicNumber.ofRat hz p
  have heval : evalCanonical p x = mapped.eval x := by
    simp [evalCanonical, DensePoly.eval, mapped, DensePoly.toList]
  have hpoly : (HexPolyMathlib.toPolynomial mapped).map
      Hex.RealAlgebraicNumber.toRealHom = realPoly p := by
    ext i
    simp [mapped, realPoly, ratCast, Hex.RealAlgebraicNumber.toRealHom]
  rw [heval, ← HexPolyMathlib.eval_toPolynomial]
  rw [← hpoly]
  change Hex.RealAlgebraicNumber.toRealHom
    ((HexPolyMathlib.toPolynomial mapped).eval x) =
      ((HexPolyMathlib.toPolynomial mapped).map
        Hex.RealAlgebraicNumber.toRealHom).eval
        (Hex.RealAlgebraicNumber.toRealHom x)
  rw [Polynomial.eval_map_apply]

theorem evalCanonical_sign (p : DensePoly Rat) (x : Hex.RealAlgebraicNumber) :
    (evalCanonical p x).sign =
      (SignType.sign ((realPoly p).eval x.toReal) : Int) := by
  rw [Hex.RealAlgebraicNumber.sign_eq, evalCanonical_real]
  by_cases hn : (realPoly p).eval x.toReal < 0
  · simp [hn, sign_eq_neg_one_iff.mpr hn]
  · by_cases hz : (realPoly p).eval x.toReal = 0
    · simp [hz]
    · have hp : 0 < (realPoly p).eval x.toReal :=
        lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      simp [hn, hz, sign_eq_one_iff.mpr hp]

theorem lowerMatches_iff (lower : Endpoint Rat) (x : Hex.RealAlgebraicNumber) :
    lowerMatches lower x = true ↔
      (match lower.map ratCast with
       | .negInf => True
       | .finite q => q < x.toReal
       | .posInf => False) := by
  cases lower <;>
    simp [lowerMatches, Endpoint.map, Hex.RealAlgebraicNumber.lt_iff,
      Hex.RealAlgebraicNumber.ofRat_toReal, ratCast]

theorem upperMatches_iff (upper : Endpoint Rat) (x : Hex.RealAlgebraicNumber) :
    upperMatches upper x = true ↔
      (match upper.map ratCast with
       | .posInf => True
       | .finite q => x.toReal < q
       | .negInf => False) := by
  cases upper <;>
    simp [upperMatches, Endpoint.map, Hex.RealAlgebraicNumber.lt_iff,
      Hex.RealAlgebraicNumber.ofRat_toReal, ratCast]

/-- The executable root-selection filter checks exactly the semantic
interval and derivative-sign conditions of the descriptor. -/
theorem Root.matches_iff {context : Nat} (d : Root context)
    (x : Hex.RealAlgebraicNumber) :
    d.matches x = true ↔
      HexRealRootsMathlib.Tarski.InInterval
        (d.raw.lower.map ratCast) (d.raw.upper.map ratCast) x.toReal ∧
      SignDet.signsAt ratCast ratZero d.raw.queries x.toReal = d.raw.signs := by
  have hsign : d.raw.queries.map (fun q => (evalCanonical q x).sign) =
      SignDet.signsAt ratCast ratZero d.raw.queries x.toReal := by
    simp [SignDet.signsAt, evalCanonical_sign, realPoly]
  rw [HexRealRootsMathlib.Tarski.inInterval_iff]
  simp [Root.matches, Bool.and_eq_true, lowerMatches_iff, upperMatches_iff,
    hsign]
  intro _
  cases hL : d.raw.lower.map ratCast <;>
    cases hU : d.raw.upper.map ratCast <;> simp_all

/-- The canonical integer-root list contains exactly the canonical real
values at which the rational descriptor's defining polynomial vanishes. -/
theorem Root.mem_canonical_roots_iff {context : Nat} (d : Root context)
    (x : Hex.RealAlgebraicNumber) :
    x ∈ (Hex.ZPoly.clearDenominators d.raw.head).2.realAlgebraicRoots ↔
      (realPoly d.raw.head).eval x.toReal = 0 := by
  let p := (Hex.ZPoly.clearDenominators d.raw.head).2
  have hscale : HexRealRootsMathlib.toPolyℝ p =
      Polynomial.C ((Hex.ZPoly.clearDenominators d.raw.head).1 : ℝ) *
        realPoly d.raw.head :=
    HexSturmMathlib.toPolyℝ_clearDenominators d.raw.head
  have hc : ((Hex.ZPoly.clearDenominators d.raw.head).1 : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Hex.ZPoly.clearDenominators_pos d.raw.head)
  have hne : HexRealRootsMathlib.toPolyℝ p ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hc) (d.head_ne_zero ratCast ratZero)
  have hp : p ≠ 0 := by
    intro hz
    exact hne (by simp [hz])
  have hcomp : (algebraMap ℝ ℂ).comp (Int.castRingHom ℝ) = Int.castRingHom ℂ :=
    RingHom.ext_int _ _
  have hmap : HexRootsMathlib.toPolyℂ p =
      (HexRealRootsMathlib.toPolyℝ p).map (algebraMap ℝ ℂ) := by
    show (HexPolyZMathlib.toPolynomial p).map (Int.castRingHom ℂ) =
      ((HexPolyZMathlib.toPolynomial p).map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ)
    rw [Polynomial.map_map, hcomp]
  rw [Hex.ZPoly.mem_realAlgebraicRoots_iff p hp x]
  rw [hmap, Polynomial.IsRoot.def]
  change ((HexRealRootsMathlib.toPolyℝ p).map (algebraMap ℝ ℂ)).eval
      ((algebraMap ℝ ℂ) x.toReal) = 0 ↔ _
  rw [Polynomial.eval_map_apply]
  change (((HexRealRootsMathlib.toPolyℝ p).eval x.toReal : ℝ) : ℂ) = 0 ↔ _
  norm_cast
  rw [hscale, Polynomial.eval_mul, Polynomial.eval_C]
  simp [hc]

/-- Every checked rational selected root has the value of a canonical real
algebraic number. Denominator clearing and the existing integer root list
handle reducible rational defining polynomials. -/
theorem Root.exists_canonical {context : Nat} (d : Root context) :
    ∃ a : Hex.RealAlgebraicNumber,
      a ∈ (Hex.ZPoly.clearDenominators d.raw.head).2.realAlgebraicRoots ∧
      a.toReal = d.real := by
  let p := (Hex.ZPoly.clearDenominators d.raw.head).2
  have hvalue : (realPoly d.raw.head).eval d.real = 0 := by
    simpa using Expression.denote_head (d := d)
  have hscale : (HexRealRootsMathlib.toPolyℝ p) =
      Polynomial.C ((Hex.ZPoly.clearDenominators d.raw.head).1 : ℝ) *
        realPoly d.raw.head := by
    exact HexSturmMathlib.toPolyℝ_clearDenominators d.raw.head
  have hne : HexRealRootsMathlib.toPolyℝ p ≠ 0 := by
    rw [hscale]
    apply mul_ne_zero
    · exact Polynomial.C_ne_zero.mpr (by
        exact_mod_cast ne_of_gt (Hex.ZPoly.clearDenominators_pos d.raw.head))
    · exact d.head_ne_zero ratCast ratZero
  have hp : p ≠ 0 := by
    intro hz
    apply hne
    simp [hz]
  have hroot : (HexRealRootsMathlib.toPolyℝ p).IsRoot d.real := by
    rw [Polynomial.IsRoot.def, hscale, Polynomial.eval_mul, hvalue, mul_zero]
  have hcomp : (algebraMap ℝ ℂ).comp (Int.castRingHom ℝ) = Int.castRingHom ℂ :=
    RingHom.ext_int _ _
  have hmap : HexRootsMathlib.toPolyℂ p =
      (HexRealRootsMathlib.toPolyℝ p).map (algebraMap ℝ ℂ) := by
    show (HexPolyZMathlib.toPolynomial p).map (Int.castRingHom ℂ) =
      ((HexPolyZMathlib.toPolynomial p).map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ)
    rw [Polynomial.map_map, hcomp]
  have hcomplex : (HexRootsMathlib.toPolyℂ p).IsRoot (d.real : ℂ) := by
    rw [hmap]
    simpa using hroot.map (f := algebraMap ℝ ℂ)
  obtain ⟨a, _, ha⟩ :=
    (Hex.ZPoly.mem_algebraicRoots_iff p hp (d.real : ℂ)).mpr hcomplex
  have hreal : a.isReal = true := by
    rw [Hex.AlgebraicNumber.isReal_iff, ha]
    simp
  let b := Hex.RealAlgebraicNumber.ofAlgebraic a hreal
  have hb : b.toReal = d.real := by
    change a.toComplex.re = d.real
    rw [ha]
    simp
  refine ⟨b, ?_, hb⟩
  apply (Hex.ZPoly.mem_realAlgebraicRoots_iff p hp b).mpr
  rw [hb]
  exact hcomplex

/-- A semantic canonical witness for the selected root. The executable
conversion still has to select the matching entry of the finite root list. -/
noncomputable def Root.canonical {context : Nat} (d : Root context) :
    Hex.RealAlgebraicNumber := d.exists_canonical.choose

theorem Root.canonical_real {context : Nat} (d : Root context) :
    d.canonical.toReal = d.real := d.exists_canonical.choose_spec.2

theorem Root.canonical_mem {context : Nat} (d : Root context) :
    d.canonical ∈ (Hex.ZPoly.clearDenominators d.raw.head).2.realAlgebraicRoots :=
  d.exists_canonical.choose_spec.1

/-- The matching canonical algebraic value is independent of the semantic
choice used to witness it. -/
theorem Root.canonical_unique {context : Nat} (d : Root context)
    (a : Hex.RealAlgebraicNumber) (h : a.toReal = d.real) :
    a = d.canonical :=
  Hex.RealAlgebraicNumber.toReal_injective (h.trans d.canonical_real.symm)

theorem Rebinding.canonical_eq_source {context version : Nat} {source : Root context}
    (r : Rebinding source version) :
    r.target.canonical = source.canonical := by
  apply source.canonical_unique
  rw [r.target.canonical_real, r.real_eq_source]

/-- A canonical root returned by the executable filter is the one selected
by the checked descriptor. -/
theorem Root.canonical?_sound {context : Nat} (d : Root context)
    (x : Hex.RealAlgebraicNumber) (h : d.canonical? = some x) :
    x.toReal = d.real := by
  have hfind :
      ((Hex.ZPoly.clearDenominators d.raw.head).2.realAlgebraicRoots.toList).find?
        d.matches = some x := h
  have hmem : x ∈ (Hex.ZPoly.clearDenominators d.raw.head).2.realAlgebraicRoots := by
    exact Array.mem_toList_iff.mp (List.mem_of_find?_eq_some hfind)
  have hmatch : d.matches x = true := List.find?_some hfind
  obtain ⟨hint, hsign⟩ := (d.matches_iff x).mp hmatch
  have hroot := (d.mem_canonical_roots_iff x).mp hmem
  have hne : realPoly d.raw.head ≠ 0 := d.head_ne_zero ratCast ratZero
  have hrootIn : x.toReal ∈ HexRealRootsMathlib.Tarski.rootsIn
      (realPoly d.raw.head) (d.raw.lower.map ratCast) (d.raw.upper.map ratCast) :=
    (HexRealRootsMathlib.Tarski.mem_rootsIn_iff _ hne _ _ _).mpr ⟨hroot, hint⟩
  exact d.real_unique x.toReal hrootIn hsign

/-- The independent canonical root enumeration always contains a match for a
validated rational selected-root descriptor. -/
theorem Root.canonical?_isSome {context : Nat} (d : Root context) :
    d.canonical?.isSome := by
  obtain ⟨x, hmem, hreal⟩ := d.exists_canonical
  apply List.find?_isSome.mpr
  refine ⟨x, ?_, ?_⟩
  · exact Array.mem_toList_iff.mpr hmem
  · apply (d.matches_iff x).mpr
    rw [hreal]
    have hs := d.real_spec
    have hne : realPoly d.raw.head ≠ 0 := d.head_ne_zero ratCast ratZero
    have hint := (HexRealRootsMathlib.Tarski.mem_rootsIn_iff _ hne _ _ _).mp hs.1 |>.2
    exact ⟨hint, hs.2⟩

theorem Root.toCanonical_real {context : Nat} (d : Root context) :
    d.toCanonical.toReal = d.real := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp d.canonical?_isSome
  simpa [Root.toCanonical, hx] using d.canonical?_sound x hx

theorem Root.toCanonical_eq_canonical {context : Nat} (d : Root context) :
    d.toCanonical = d.canonical :=
  d.canonical_unique d.toCanonical d.toCanonical_real

namespace Expression

/-- The executable canonical evaluation denotes the selected real value. -/
theorem toCanonical_real {context : Nat} {d : Root context}
    (a : Expression d) : a.toCanonical.toReal = a.denote := by
  rw [Expression.toCanonical, evalCanonical_real, d.toCanonical_real]
  rfl

/-- Interpret a rational expression with the existing canonical algebraic
field operations at the matching selected root. -/
noncomputable def canonicalValue {context : Nat} {d : Root context}
    (a : Expression d) : Hex.RealAlgebraicNumber :=
  (HexPolyMathlib.toPolynomial a.polynomial).eval₂
    (algebraMap Rat Hex.RealAlgebraicNumber) d.canonical

/-- The canonical arithmetic and checked selected-root expression have the
same real interpretation, even for a reducible defining polynomial. -/
theorem canonicalValue_real {context : Nat} {d : Root context}
    (a : Expression d) : a.canonicalValue.toReal = a.denote := by
  have hpoly : realPoly a.polynomial =
      (HexPolyMathlib.toPolynomial a.polynomial).map (Rat.castHom ℝ) := by
    ext i
    simp [realPoly, ratCast]
  have hcomp : Hex.RealAlgebraicNumber.toRealHom.comp
      (algebraMap Rat Hex.RealAlgebraicNumber) = Rat.castHom ℝ := by
    ext q
    simp [Hex.RealAlgebraicNumber.toRealHom]
  change Hex.RealAlgebraicNumber.toRealHom
      ((HexPolyMathlib.toPolynomial a.polynomial).eval₂
        (algebraMap Rat Hex.RealAlgebraicNumber) d.canonical) = _
  rw [Polynomial.hom_eval₂, hcomp]
  rw [show Hex.RealAlgebraicNumber.toRealHom d.canonical = d.real from d.canonical_real]
  simp [denote, hpoly, Polynomial.eval_map]

/-- The executable conversion is the canonical value chosen semantically
from the complete real-root list. -/
theorem toCanonical_eq_canonicalValue {context : Nat} {d : Root context}
    (a : Expression d) : a.toCanonical = a.canonicalValue := by
  apply Hex.RealAlgebraicNumber.toReal_injective
  rw [toCanonical_real, canonicalValue_real]

/-- Equality of canonical values is precisely equality of selected real
values; raw rational polynomials need not be structurally equal. -/
theorem canonicalValue_eq_iff {context : Nat} {d : Root context}
    (a b : Expression d) :
    a.canonicalValue = b.canonicalValue ↔ a.denote = b.denote := by
  constructor
  · intro h
    simpa [canonicalValue_real] using congrArg Hex.RealAlgebraicNumber.toReal h
  · intro h
    apply Hex.RealAlgebraicNumber.toReal_injective
    simpa [canonicalValue_real] using h

theorem canonicalValue_zero {context : Nat} {d : Root context} :
    (zero (d := d)).canonicalValue = 0 := by
  apply Hex.RealAlgebraicNumber.toReal_injective
  simp [canonicalValue_real]

theorem canonicalValue_one {context : Nat} {d : Root context} :
    (one (d := d)).canonicalValue = 1 := by
  apply Hex.RealAlgebraicNumber.toReal_injective
  simp [canonicalValue_real]

theorem canonicalValue_add {context : Nat} {d : Root context}
    (a b : Expression d) :
    (add a b).canonicalValue = a.canonicalValue + b.canonicalValue := by
  apply Hex.RealAlgebraicNumber.toReal_injective
  simp only [canonicalValue_real, denote_add, Hex.RealAlgebraicNumber.add_toReal]

theorem canonicalValue_mul {context : Nat} {d : Root context}
    (a b : Expression d) :
    (mul a b).canonicalValue = a.canonicalValue * b.canonicalValue := by
  apply Hex.RealAlgebraicNumber.toReal_injective
  simp only [canonicalValue_real, denote_mul, Hex.RealAlgebraicNumber.mul_toReal]

theorem canonicalValue_neg {context : Nat} {d : Root context}
    (a : Expression d) :
    (neg a).canonicalValue = -a.canonicalValue := by
  apply Hex.RealAlgebraicNumber.toReal_injective
  simp only [canonicalValue_real, denote_neg, Hex.RealAlgebraicNumber.neg_toReal]

theorem canonicalValue_sub {context : Nat} {d : Root context}
    (a b : Expression d) :
    (sub a b).canonicalValue = a.canonicalValue - b.canonicalValue := by
  apply Hex.RealAlgebraicNumber.toReal_injective
  simp only [canonicalValue_real, denote_sub, Hex.RealAlgebraicNumber.sub_toReal]

theorem canonicalValue_inverse? {context : Nat} {d : Root context}
    (a b : Expression d) (h : a.inverse? = .ok (some b)) :
    b.canonicalValue = a.canonicalValue⁻¹ := by
  apply Hex.RealAlgebraicNumber.toReal_injective
  rw [canonicalValue_real, Hex.RealAlgebraicNumber.inv_toReal, canonicalValue_real]
  exact eq_inv_of_mul_eq_one_right (inverse?_sound a b h)

theorem canonicalValue_inverse?_none {context : Nat} {d : Root context}
    (a : Expression d) (h : a.inverse? = .ok none) :
    a.canonicalValue = 0 := by
  apply Hex.RealAlgebraicNumber.toReal_injective
  simpa [canonicalValue_real] using inverse?_none_denote a h

/-- Checked cofactor splitting and context rebinding retain the same
canonical algebraic value for every transported expression. -/
theorem canonicalValue_refine {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version) (a : Expression d) :
    (refine r a).canonicalValue = a.canonicalValue := by
  apply Hex.RealAlgebraicNumber.toReal_injective
  rw [canonicalValue_real, canonicalValue_real, denote_refine]

/-- A returned selected-root sign agrees with exact canonical algebraic
comparison at the matching root. -/
theorem canonicalValue_sign? {context : Nat} {d : Root context}
    (a : Expression d) (value : Int) (h : a.sign? = .ok value) :
    value = a.canonicalValue.sign := by
  rw [a.sign?_sound value h, Hex.RealAlgebraicNumber.sign_eq, canonicalValue_real]
  by_cases hn : a.denote < 0
  · simp [hn, sign_eq_neg_one_iff.mpr hn]
  · by_cases hz : a.denote = 0
    · simp [hz]
    · have hp : 0 < a.denote := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      simp [hn, hz, sign_eq_one_iff.mpr hp]

theorem toCanonical_add {context : Nat} {d : Root context}
    (a b : Expression d) :
    (add a b).toCanonical = a.toCanonical + b.toCanonical := by
  rw [toCanonical_eq_canonicalValue, canonicalValue_add,
    a.toCanonical_eq_canonicalValue, b.toCanonical_eq_canonicalValue]

theorem toCanonical_mul {context : Nat} {d : Root context}
    (a b : Expression d) :
    (mul a b).toCanonical = a.toCanonical * b.toCanonical := by
  rw [toCanonical_eq_canonicalValue, canonicalValue_mul,
    a.toCanonical_eq_canonicalValue, b.toCanonical_eq_canonicalValue]

theorem toCanonical_inverse? {context : Nat} {d : Root context}
    (a b : Expression d) (h : a.inverse? = .ok (some b)) :
    b.toCanonical = a.toCanonical⁻¹ := by
  rw [b.toCanonical_eq_canonicalValue, a.toCanonical_eq_canonicalValue]
  exact canonicalValue_inverse? a b h

theorem toCanonical_sign? {context : Nat} {d : Root context}
    (a : Expression d) (value : Int) (h : a.sign? = .ok value) :
    value = a.toCanonical.sign := by
  rw [a.toCanonical_eq_canonicalValue]
  exact canonicalValue_sign? a value h

theorem toCanonical_refine {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version) (a : Expression d) :
    (refine r a).toCanonical = a.toCanonical := by
  rw [(refine r a).toCanonical_eq_canonicalValue,
    a.toCanonical_eq_canonicalValue]
  exact canonicalValue_refine r a

end Expression

end Hex.RealClosure

/- The inherited `sorryAx` is `HexRealRootsMathlib.Tarski.check_rootSum` (#10389). -/
/-- info: 'Hex.RealClosure.Root.exists_canonical' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Root.exists_canonical
/-- info: 'Hex.RealClosure.Expression.canonicalValue_inverse?' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Expression.canonicalValue_inverse?
/-- info: 'Hex.RealClosure.Root.toCanonical_real' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Root.toCanonical_real
/-- info: 'Hex.RealClosure.Expression.toCanonical_eq_canonicalValue' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Expression.toCanonical_eq_canonicalValue
