/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealFormulaMathlib.Semantics
public import HexPolyZMathlib.PolynomialEquivalence
public import HexRealClosureMathlib.SelectedRoot
public section
/-! Translate checked selected-root constraints into the shared integer schema.
Positive denominator clearing preserves all comparisons and generator-coordinate
relations. The descriptor owner's count-one theorem supplies uniqueness.
This builds a source-selection formula, not frozen context replay or coverage. -/
namespace Hex.RCF.RealCoefficients.NativeSelection
open Hex Hex.RealClosure Hex.RealFormula
open scoped HexMvPolyMathlib

@[expose] def polynomial (i : Fin n) (p : ZPoly) : RealFormula.Poly n :=
  p.toArray.toList.foldr (fun c acc => MvPoly.C c + MvPoly.X i * acc) 0

theorem polynomial_eval (i : Fin n) (p : ZPoly) (values : Fin n → ℝ) :
    (polynomial i p).eval values =
      (HexPolyMathlib.toPolynomial p).eval₂ (Int.castRingHom ℝ) (values i) := by
  rw [HexPolyMathlib.eval₂_horner]
  unfold polynomial RealFormula.Poly.eval
  rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
  change MvPolynomial.eval₂ (Int.castRingHom ℝ) values
    (HexMvPolyMathlib.toMvPolynomial (p.coeffs.toList.foldr
      (fun c acc => MvPoly.C c + MvPoly.X i * acc) 0)) = _
  induction p.coeffs.toList with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldr_cons]
    rw [HexMvPolyMathlib.toMvPolynomial_add, HexMvPolyMathlib.toMvPolynomial_mul,
      HexMvPolyMathlib.toMvPolynomial_C, HexMvPolyMathlib.toMvPolynomial_X]
    simpa only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
      MvPolynomial.eval₂_X] using congrArg (fun x => (Int.castRingHom ℝ) c + values i * x) ih

@[expose] def atom (i : Fin n) (p : DensePoly Rat) (comparison : RealFormula.Cmp) : RealFormula.QF n :=
  .atom ⟨polynomial i (ZPoly.clearDenominators p).2, comparison⟩

theorem cleared_eval (p : DensePoly Rat) (x : ℝ) :
    (HexPolyMathlib.toPolynomial (ZPoly.clearDenominators p).2).eval₂ (Int.castRingHom ℝ) x =
      ((ZPoly.clearDenominators p).1 : ℝ) * (realPoly p).eval x := by
  have mapped := congrArg (fun q : Polynomial Rat => q.map (Rat.castHom ℝ))
    (HexPolyZMathlib.toPolynomial_clearDenominators p)
  have casted : (realPoly p) = (HexPolyMathlib.toPolynomial p).map (Rat.castHom ℝ) := by
    ext k
    simp [realPoly, HexPolyMathlib.Interpret.coeff_interpret, Polynomial.coeff_map,
      HexPolyMathlib.coeff_toPolynomial, ratCast]
  rw [Polynomial.map_mul, Polynomial.map_C, ← casted, Polynomial.map_map] at mapped
  have same : (Rat.castHom ℝ).comp (Int.castRingHom Rat) = Int.castRingHom ℝ := by
    ext k
    simp
  rw [same] at mapped
  have result := congrArg (fun q : Polynomial ℝ => q.eval x) mapped
  simpa only [Polynomial.eval_map, Polynomial.eval_mul, Polynomial.eval_C,
    Rat.coe_castHom, Rat.cast_natCast] using result
theorem atom_correct (i : Fin n) (p : DensePoly Rat) (comparison : RealFormula.Cmp)
    (values : Fin n → ℝ) :
    (atom i p comparison).toProp values ↔ comparison.toProp ((realPoly p).eval (values i)) := by
  change comparison.toProp ((polynomial i (ZPoly.clearDenominators p).2).eval values) ↔ _
  rw [polynomial_eval, cleared_eval]
  have positive : (0 : ℝ) < ((ZPoly.clearDenominators p).1 : ℝ) := by
    exact_mod_cast ZPoly.clearDenominators_pos p
  cases comparison with
  | eq | ne => simp [RealFormula.Cmp.toProp, mul_eq_zero, ne_of_gt positive]
  | lt =>
    simpa [RealFormula.Cmp.toProp] using
      (mul_lt_mul_iff_of_pos_left positive :
        ((ZPoly.clearDenominators p).1 : ℝ) * (realPoly p).eval (values i) <
          ((ZPoly.clearDenominators p).1 : ℝ) * 0 ↔ (realPoly p).eval (values i) < 0)
  | le =>
    simpa [RealFormula.Cmp.toProp] using
      (mul_le_mul_iff_of_pos_left positive :
        ((ZPoly.clearDenominators p).1 : ℝ) * (realPoly p).eval (values i) ≤
          ((ZPoly.clearDenominators p).1 : ℝ) * 0 ↔ (realPoly p).eval (values i) ≤ 0)
  | gt =>
    simpa [RealFormula.Cmp.toProp] using
      (mul_lt_mul_iff_of_pos_left positive :
        ((ZPoly.clearDenominators p).1 : ℝ) * 0 <
          ((ZPoly.clearDenominators p).1 : ℝ) * (realPoly p).eval (values i) ↔
          0 < (realPoly p).eval (values i))
  | ge =>
    simpa [RealFormula.Cmp.toProp] using
      (mul_le_mul_iff_of_pos_left positive :
        ((ZPoly.clearDenominators p).1 : ℝ) * 0 ≤
          ((ZPoly.clearDenominators p).1 : ℝ) * (realPoly p).eval (values i) ↔
          0 ≤ (realPoly p).eval (values i))
/-- A fixed-field polynomial coefficient is related to its selected generator
in the same shared schema. Positive denominator clearing retains the equality. -/
@[expose] def relation (generator coordinate : Fin n) (p : DensePoly Rat) : RealFormula.QF n :=
  let cleared := ZPoly.clearDenominators p
  .atom ⟨MvPoly.C (cleared.1 : Int) * MvPoly.X coordinate - polynomial generator cleared.2, .eq⟩

theorem relation_correct (generator coordinate : Fin n) (p : DensePoly Rat)
    (values : Fin n → ℝ) :
    (relation generator coordinate p).toProp values ↔
      values coordinate = (realPoly p).eval (values generator) := by
  change RealFormula.Poly.eval (MvPoly.C ((ZPoly.clearDenominators p).1 : Int) * MvPoly.X coordinate -
    polynomial generator (ZPoly.clearDenominators p).2) values = 0 ↔ _
  unfold RealFormula.Poly.eval
  rw [← HexMvPolyMathlib.eval₂_toMvPolynomial, HexMvPolyMathlib.toMvPolynomial_sub,
    HexMvPolyMathlib.toMvPolynomial_mul, HexMvPolyMathlib.toMvPolynomial_C,
    HexMvPolyMathlib.toMvPolynomial_X, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, HexMvPolyMathlib.eval₂_toMvPolynomial]
  simp only [Int.coe_castRingHom, Int.cast_natCast]
  change ((ZPoly.clearDenominators p).1 : ℝ) * values coordinate -
    (polynomial generator (ZPoly.clearDenominators p).2).eval values = 0 ↔ _
  rw [polynomial_eval, cleared_eval, sub_eq_zero]
  have positive : (0 : ℝ) < ((ZPoly.clearDenominators p).1 : ℝ) := by
    exact_mod_cast ZPoly.clearDenominators_pos p
  simp only [mul_eq_mul_left_iff, ne_of_gt positive, or_false]

@[expose] def signAtom (i : Fin n) (p : DensePoly Rat) (requested : Int) : RealFormula.QF n :=
  if requested = -1 then atom i p .lt
  else if requested = 0 then atom i p .eq
  else if requested = 1 then atom i p .gt
  else .ff

theorem signAtom_correct (i : Fin n) (p : DensePoly Rat) (requested : Int)
    (values : Fin n → ℝ) :
    (signAtom i p requested).toProp values ↔
      (SignType.sign ((realPoly p).eval (values i)) : Int) = requested := by
  let x := (realPoly p).eval (values i)
  have hn : ((SignType.sign x : Int) = -1) ↔ x < 0 := by
    have same : ((SignType.sign x : Int) = -1) ↔ SignType.sign x = -1 := by
      generalize SignType.sign x = s
      cases s <;> decide
    exact same.trans sign_eq_neg_one_iff
  have hz : ((SignType.sign x : Int) = 0) ↔ x = 0 := by
    have same : ((SignType.sign x : Int) = 0) ↔ SignType.sign x = 0 := by
      generalize SignType.sign x = s
      cases s <;> decide
    exact same.trans sign_eq_zero_iff
  have hp : ((SignType.sign x : Int) = 1) ↔ 0 < x := by
    have same : ((SignType.sign x : Int) = 1) ↔ SignType.sign x = 1 := by
      generalize SignType.sign x = s
      cases s <;> decide
    exact same.trans sign_eq_one_iff
  by_cases negative : requested = -1
  · subst requested
    simpa [signAtom, atom_correct, RealFormula.Cmp.toProp, x] using hn.symm
  by_cases zero : requested = 0
  · subst requested
    simpa [signAtom, atom_correct, RealFormula.Cmp.toProp, x] using hz.symm
  by_cases positive : requested = 1
  · subst requested
    simpa [signAtom, atom_correct, RealFormula.Cmp.toProp, x] using hp.symm
  have absent : (SignType.sign x : Int) ≠ requested := by
    generalize SignType.sign x = s
    cases s <;> simp_all [eq_comm]
  simpa [signAtom, negative, zero, positive, RealFormula.QF.toProp, x] using absent
@[expose] def signs (i : Fin n) : List (DensePoly Rat) → List Int → RealFormula.QF n
  | [], [] => .tt
  | p :: ps, s :: ss => .and (signAtom i p s) (signs i ps ss)
  | _, _ => .ff

theorem signs_correct (i : Fin n) (qs : List (DensePoly Rat)) (requested : List Int)
    (values : Fin n → ℝ) :
    (signs i qs requested).toProp values ↔
      SignDet.signsAt ratCast ratZero qs (values i) = requested := by
  induction qs generalizing requested with
  | nil => cases requested <;> simp [signs, RealFormula.QF.toProp, SignDet.signsAt]
  | cons q qs ih =>
    cases requested <;>
      simp [signs, RealFormula.QF.toProp, signAtom_correct, SignDet.signsAt, ih, realPoly]

section Projection
variable {E : Type u} [Zero E] [DecidableEq E]
variable (f : E → Rat) (zero : ∀ a, f a = 0 ↔ a = 0)

/-- Rational projection changes coefficient representation, retaining actual
polynomial evaluation. It requires zero reflection, not a field on raw syntax. -/
theorem projected_real (p : DensePoly E) :
    realPoly (DensePoly.Interpret.map f zero p) =
      HexPolyMathlib.Interpret.interpret (ratCast ∘ f)
        (fun a => (ratZero (f a)).trans (zero a)) p := by
  ext k
  simp [realPoly, HexPolyMathlib.Interpret.coeff_interpret, DensePoly.Interpret.map_coeff,
    Function.comp_def]

@[expose] def translate (i : Fin n) (qs : List (DensePoly E)) (requested : List Int) :
    RealFormula.QF n :=
  signs i (qs.map (DensePoly.Interpret.map f zero)) requested

theorem translate_correct (i : Fin n) (qs : List (DensePoly E)) (requested : List Int)
    (values : Fin n → ℝ) :
    (translate f zero i qs requested).toProp values ↔
      SignDet.signsAt (ratCast ∘ f) (fun a => (ratZero (f a)).trans (zero a))
        qs (values i) = requested := by
  unfold translate
  rw [signs_correct]
  have same : SignDet.signsAt ratCast ratZero (qs.map (DensePoly.Interpret.map f zero))
      (values i) = SignDet.signsAt (ratCast ∘ f)
        (fun a => (ratZero (f a)).trans (zero a)) qs (values i) := by
    simp only [SignDet.signsAt, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro q _
    change (SignType.sign ((realPoly (DensePoly.Interpret.map f zero q)).eval (values i)) : Int) = _
    rw [projected_real]
    rfl
  rw [same]
end Projection

@[expose] def selection (i : Fin n) (raw : SignDet.RawDescriptor Rat Ctx) : RealFormula.QF n :=
  signs i raw.constraints raw.constraintSigns

theorem identity {context : Nat} (d : Root context) (i : Fin n) (values : Fin n → ℝ) :
    (selection i d.raw).toProp values ↔ values i = d.real := by
  exact (signs_correct i d.raw.constraints d.raw.constraintSigns values).trans
    (d.constraints_iff ratCast ratZero ratOne ratAdd ratSub ratMul ratNat ratSign _)

theorem selected {context : Nat} (d : Root context) :
    (selection (0 : Fin 1) d.raw).toProp (fun _ => d.real) :=
  (identity d 0 _).mpr rfl

theorem unique {context : Nat} (d : Root context) (values : Fin 1 → ℝ)
    (meaning : (selection 0 d.raw).toProp values) : values = fun _ => d.real := by
  have same := (identity d 0 values).mp meaning
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa [hi] using same

/-- info: 'Hex.RCF.RealCoefficients.NativeSelection.polynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polynomial_eval
/-- info: 'Hex.RCF.RealCoefficients.NativeSelection.cleared_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cleared_eval
/-- info: 'Hex.RCF.RealCoefficients.NativeSelection.atom_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms atom_correct
/-- info: 'Hex.RCF.RealCoefficients.NativeSelection.signAtom_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signAtom_correct
/-- info: 'Hex.RCF.RealCoefficients.NativeSelection.projected_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms projected_real
/-- info: 'Hex.RCF.RealCoefficients.NativeSelection.translate_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms translate_correct
/-- info: 'Hex.RCF.RealCoefficients.NativeSelection.relation_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relation_correct
/-- info: 'Hex.RCF.RealCoefficients.NativeSelection.signs_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signs_correct
/-- info: 'Hex.RCF.RealCoefficients.NativeSelection.identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms identity
/-- info: 'Hex.RCF.RealCoefficients.NativeSelection.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selected
/-- info: 'Hex.RCF.RealCoefficients.NativeSelection.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unique
end Hex.RCF.RealCoefficients.NativeSelection
