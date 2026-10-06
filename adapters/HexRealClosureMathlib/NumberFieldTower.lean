/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.NumberFieldTower
public import HexRealClosureMathlib.NumberField
public import HexRealClosureMathlib.TrivialTower
public import HexRealClosureMathlib.LocalSample
public import HexRealClosureMathlib.Canonical

public section

namespace Hex.RealClosure.NumberField

open HexPolyMathlib.Interpret

/-- The canonical real interpretation of the native rational predecessor. -/
noncomputable def rationalModel (registry : BaseContext.Registry) :
    Tower.Model (base registry) ℝ :=
  Tower.Model.base (BaseContext.rational registry) (Rat.castHom ℝ) ratSign

/-- The native minimal polynomial retains every original integer coefficient. -/
theorem defining_value (generator : RealAlgebraicNumber) (registry : BaseContext.Registry) :
    interpret
      (Tower.Model.base (BaseContext.rational registry) (Rat.castHom ℝ) ratSign).value
      (Tower.Model.base (BaseContext.rational registry) (Rat.castHom ℝ) ratSign).zero_iff
      (defining generator registry) =
    (HexPolyMathlib.toPolynomial generator.toAlgebraic.p).map (Int.castRingHom ℝ) := by
  ext i
  rw [coeff_interpret]
  apply (Tower.Model.base_value (BaseContext.rational registry) (Rat.castHom ℝ) ratSign
    ((defining generator registry).coeff i)).trans
  rw [defining, DensePoly.coeff_ofCoeffs]
  erw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases hi : generator.toAlgebraic.p.coeffs[i]? with
  | none =>
    erw [DensePoly.toArray, hi, Option.map_none, Option.getD_none]
    simp only [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial,
      DensePoly.coeff, Array.getD_eq_getD_getElem?, hi, Option.getD_none]
    have zero : (0 : (base registry).Value).stored = 0 :=
      (BaseContext.Element.stored_eq_zero _).mpr rfl
    erw [zero]
    norm_num
  | some z =>
    erw [DensePoly.toArray, hi, Option.map_some, Option.getD_some]
    simp [DensePoly.coeff, Array.getD_eq_getD_getElem?, hi]

private theorem defining_complex (generator : RealAlgebraicNumber) (registry : BaseContext.Registry) :
    (interpret (rationalModel registry).value (rationalModel registry).zero_iff
      (defining generator registry)).map Complex.ofRealHom =
    HexRootsMathlib.toPolyℂ generator.toAlgebraic.p := by
  unfold rationalModel
  rw [defining_value, Polynomial.map_map]
  have same : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ :=
    RingHom.ext_int _ _
  rw [same]

private theorem defining_nonzero (generator : RealAlgebraicNumber) (registry : BaseContext.Registry) :
    interpret (rationalModel registry).value (rationalModel registry).zero_iff
      (defining generator registry) ≠ 0 := by
  intro zero
  have complexZero : HexRootsMathlib.toPolyℂ generator.toAlgebraic.p = 0 := by
    rw [← defining_complex generator registry, zero, Polynomial.map_zero]
  have positive := generator.toAlgebraic.pos_degree
  rw [← HexRootsMathlib.natDegree_toPolyℂ, complexZero, Polynomial.natDegree_zero] at positive
  exact Nat.lt_irrefl 0 positive

private theorem defining_root (generator : RealAlgebraicNumber) (registry : BaseContext.Registry) :
    (interpret (rationalModel registry).value (rationalModel registry).zero_iff
      (defining generator registry)).IsRoot generator.toReal := by
  let p := interpret (rationalModel registry).value (rationalModel registry).zero_iff
    (defining generator registry)
  have root := AlgebraicRoot.toComplex_isRoot generator.toAlgebraic.toRoot
  change (HexRootsMathlib.toPolyℂ generator.toAlgebraic.p).eval generator.toAlgebraic.toComplex = 0 at root
  have agreement : ((p.eval generator.toReal : ℝ) : ℂ) =
      (HexRootsMathlib.toPolyℂ generator.toAlgebraic.p).eval generator.toAlgebraic.toComplex := by
    calc
      ((p.eval generator.toReal : ℝ) : ℂ) =
          (p.map Complex.ofRealHom).eval (generator.toReal : ℂ) :=
        (Polynomial.eval_map_apply Complex.ofRealHom generator.toReal).symm
      _ = _ := by rw [defining_complex, generator.ofReal_toReal]
  apply Complex.ofReal_injective
  exact agreement.trans root

/-- Every checked real algebraic generator has a native presentation at its original embedding. -/
theorem present?_success (generator : RealAlgebraicNumber) (registry : BaseContext.Registry) :
    ∃ source, present? generator registry = some source := by
  refine Option.isSome_iff_exists.mp ?_
  obtain ⟨entries, returned, entry, member, value⟩ :=
    (rationalModel registry).root_exists (defining generator registry)
      (defining_nonzero generator registry) generator.toReal (defining_root generator registry)
  rw [present?, returned]
  apply List.findSome?_isSome_iff.mpr
  refine ⟨entry, member, ?_⟩
  apply (Presentation.ofRoot?_isSome generator registry entry.root).mpr
  apply (RealAlgebraicNumber.beq_iff _ _).mpr
  apply RealAlgebraicNumber.toReal_injective
  exact ((Trivial.Map.rational_model registry).root entry.root).trans value

namespace Presentation

variable {generator : RealAlgebraicNumber} {registry : BaseContext.Registry}

/-- The actual native coefficient conversion determines this field's real model. -/
noncomputable def model (source : Presentation generator registry) :
    Tower.Model source.context ℝ :=
  (source.root.conversionModel (rationalModel registry)).target

/-- The retained generator has the original selected embedding. -/
theorem generator_value (source : Presentation generator registry) :
    source.model.value source.root.convertedValue = generator.toReal := by
  rw [model, Tower.Root.convertedValue_value]
  have same := (RealAlgebraicNumber.beq_iff _ _).mp source.checked
  exact ((Trivial.Map.rational_model registry).root source.root).symm.trans
    (congrArg RealAlgebraicNumber.toReal same)

private theorem rat_value (source : Presentation generator registry) (q : Rat) :
    source.model.value (source.root.conversion.value ⟨q⟩) = (q : ℝ) := by
  exact ((source.root.conversionModel (rationalModel registry)).value
    (⟨q⟩ : (base registry).Value)).trans
    (Tower.Model.base_value (BaseContext.rational registry) (Rat.castHom ℝ) ratSign ⟨q⟩)

private theorem coordinates (source : Presentation generator registry) (coefficients : List Rat) :
    source.model.value (DensePoly.evalCoeffList
      (coefficients.map fun q => source.root.conversion.value ⟨q⟩)
      source.root.convertedValue) =
    DensePoly.evalCoeffList (coefficients.map fun (q : Rat) => (q : ℝ)) generator.toReal := by
  induction coefficients with
  | nil => exact (source.model.zero_iff 0).mpr rfl
  | cons q rest ih =>
    change source.model.value (_ * source.root.convertedValue + _) = _ * generator.toReal + _
    rw [source.model.add, source.model.mul, ih, generator_value, rat_value]

private theorem canonical_coordinates (coefficients : List Rat) (x : RealAlgebraicNumber) :
    (DensePoly.evalCoeffList (coefficients.map RealAlgebraicNumber.ofRat) x).toReal =
    DensePoly.evalCoeffList (coefficients.map fun (q : Rat) => (q : ℝ)) x.toReal := by
  induction coefficients with
  | nil => exact RealAlgebraicNumber.zero_toReal
  | cons q rest ih =>
    change RealAlgebraicNumber.toRealHom (_ * x + RealAlgebraicNumber.ofRat q) = _
    rw [map_add, map_mul]
    change (DensePoly.evalCoeffList (rest.map RealAlgebraicNumber.ofRat) x).toReal *
      x.toReal + (RealAlgebraicNumber.ofRat q).toReal = _
    rw [ih, RealAlgebraicNumber.ofRat_toReal]
    rfl

private theorem value_eval (a : QAdjoin generator.toAlgebraic) :
    value generator a = (realPoly a.coeffs).eval generator.toReal := by
  have mapped : (realPoly a.coeffs).map Complex.ofRealHom =
      (HexPolyMathlib.toPolynomial a.coeffs).map (algebraMap Rat ℂ) := by
    ext i
    simp [realPoly, ratCast]
  have agreement : (((realPoly a.coeffs).eval generator.toReal : ℝ) : ℂ) =
      PolyQuot.toComplex a generator.toAlgebraic.rep generator.toAlgebraic.rep_mk := by
    rw [PolyQuot.toComplex, Polynomial.eval₂_eq_eval_map, ← mapped]
    rw [show generator.toAlgebraic.rep.root = (generator.toReal : ℂ) from
      generator.ofReal_toReal.symm]
    exact (Polynomial.eval_map_apply Complex.ofRealHom generator.toReal).symm
  apply Complex.ofReal_injective
  rw [value_complex]
  exact agreement.symm

/-- Original fixed-field coordinates preserve their selected real value when packed. -/
theorem pack_value (source : Presentation generator registry)
    (a : QAdjoin generator.toAlgebraic) :
    source.model.value (source.pack a) = value generator a := by
  rw [pack, coordinates, value_eval]
  exact (canonical_coordinates a.coeffs.toArray.toList generator).symm.trans
    (evalCanonical_real a.coeffs generator)

/-- Packing reflects zero in the original selected field. -/
theorem pack_zero (source : Presentation generator registry)
    (a : QAdjoin generator.toAlgebraic) : source.pack a = 0 ↔ a = 0 := by
  rw [← source.model.zero_iff, pack_value, value_eq_zero]

/-- Packed addition agrees in the native field, whose nonzero storage is unreduced. -/
theorem pack_add (source : Presentation generator registry)
    (a b : QAdjoin generator.toAlgebraic) :
    source.pack (a+b) - (source.pack a + source.pack b) = 0 := by
  apply (source.model.zero_iff _).mp
  rw [source.model.sub, source.model.add, pack_value, pack_value, pack_value, value_add]
  exact sub_self _

/-- Packed multiplication agrees in the native field. -/
theorem pack_mul (source : Presentation generator registry)
    (a b : QAdjoin generator.toAlgebraic) :
    source.pack (a*b) - source.pack a * source.pack b = 0 := by
  apply (source.model.zero_iff _).mp
  rw [source.model.sub, source.model.mul, pack_value, pack_value, pack_value, value_mul]
  exact sub_self _

/-- Packed inversion agrees, including the original field's total zero inverse. -/
theorem pack_inv (source : Presentation generator registry)
    (a : QAdjoin generator.toAlgebraic) : source.pack a⁻¹ - (source.pack a)⁻¹ = 0 := by
  apply (source.model.zero_iff _).mp
  rw [source.model.sub, source.model.inv, pack_value, pack_value, value_inv]
  exact sub_self _

/-- Native packed signs use the original field's selected real embedding. -/
theorem pack_sign (source : Presentation generator registry)
    (a : QAdjoin generator.toAlgebraic) :
    source.context.sign (source.pack a) = generator.signField a := by
  rw [source.model.sign, pack_value, sign_spec]

private theorem polynomial_map (source : Presentation generator registry)
    (p : DensePoly (QAdjoin generator.toAlgebraic)) :
    source.polynomial p = DensePoly.Interpret.map source.pack source.pack_zero p := by
  have mapped := DensePoly.Interpret.map_ofCoeffs source.pack source.pack_zero p.toArray
  rw [DensePoly.ofCoeffs_toArray] at mapped
  exact mapped.symm

/-- Polynomial packing preserves every original coefficient and its selected embedding. -/
theorem polynomial_value (source : Presentation generator registry)
    (p : DensePoly (QAdjoin generator.toAlgebraic)) :
    interpret source.model.value source.model.zero_iff (source.polynomial p) =
      NumberField.polynomial generator p := by
  ext i
  rw [NumberField.polynomial_coeff, coeff_interpret,
    polynomial_map, DensePoly.Interpret.map_coeff, pack_value]

/-- The diagnostic producer succeeds for every original number-field polynomial. -/
theorem roots_success (source : Presentation generator registry)
    (p : DensePoly (QAdjoin generator.toAlgebraic)) :
    source.roots? p = .ok (source.roots p) :=
  Tower.Context.roots?_success source.model (source.polynomial p)

/-- Universal root output is retained exactly for the original zero polynomial. -/
theorem roots_all (source : Presentation generator registry)
    (p : DensePoly (QAdjoin generator.toAlgebraic)) :
    source.roots p = .all ↔ NumberField.polynomial generator p = 0 := by
  simpa only [roots, source.polynomial_value] using
    Tower.Context.roots_all source.model (source.polynomial p)

/-- The complete native roots are strictly ordered at the original selected embedding. -/
theorem roots_sorted (source : Presentation generator registry)
    (p : DensePoly (QAdjoin generator.toAlgebraic))
    {entries : List (Tower.RootEntry source.context)}
    (returned : source.roots p = .finite entries) :
    (entries.map (fun entry => entry.denote source.model)).Pairwise (· < ·) :=
  Tower.Context.roots_sorted source.model (source.polynomial p) returned

/-- Complete tower roots retain the original number-field polynomial's exact multiplicities. -/
theorem roots_spec (source : Presentation generator registry)
    (p : DensePoly (QAdjoin generator.toAlgebraic))
    {entries : List (Tower.RootEntry source.context)}
    (returned : source.roots p = .finite entries) (x : ℝ) (label : Nat) :
    (∃ entry ∈ entries, entry.denote source.model = x ∧ entry.multiplicity = label) ↔
      (NumberField.polynomial generator p).IsRoot x ∧
      label = (NumberField.polynomial generator p).rootMultiplicity x := by
  simpa only [source.polynomial_value] using
    Tower.Context.roots_spec source.model (source.polynomial p) returned x label

/-- The shared sample family has exactly the roots of the original nonzero polynomials. -/
theorem family_coverage (source : Presentation generator registry)
    (polynomials : List (DensePoly (QAdjoin generator.toAlgebraic))) (x : ℝ) :
    x ∈ (source.family polynomials).boundaries.map (fun root => root.denote source.model) ↔
      ∃ p ∈ polynomials, NumberField.polynomial generator p ≠ 0 ∧
        (NumberField.polynomial generator p).IsRoot x := by
  rw [Tower.Sample.Family.coverage (source.family polynomials) source.model]
  constructor
  · rintro ⟨q, member, nonzero, root⟩
    obtain ⟨p, originalMember, rfl⟩ := List.mem_map.mp member
    exact ⟨p, originalMember, by simpa only [source.polynomial_value] using nonzero,
      by simpa only [source.polynomial_value] using root⟩
  · rintro ⟨p, member, nonzero, root⟩
    exact ⟨source.polynomial p, List.mem_map.mpr ⟨p, member, rfl⟩,
      by simpa only [source.polynomial_value] using nonzero,
      by simpa only [source.polynomial_value] using root⟩

/-- Every original real point belongs to exactly one shared section or sector. -/
theorem cells_unique (source : Presentation generator registry)
    (polynomials : List (DensePoly (QAdjoin generator.toAlgebraic))) (x : ℝ) :
    ∃! region, region ∈ (source.family polynomials).cells ∧ region.Mem source.model x :=
  Tower.Sample.Family.cells_unique (source.family polynomials) source.model x

/-- Boundary handles are strictly ordered at the original number-field embedding. -/
theorem family_sorted (source : Presentation generator registry)
    (polynomials : List (DensePoly (QAdjoin generator.toAlgebraic))) :
    (source.family polynomials).boundaries.Pairwise
      (fun a b => a.denote source.model < b.denote source.model) :=
  Tower.Sample.Family.sorted (source.family polynomials) source.model

/-- Each sector's actual sample context retains its original real interval and signs. -/
theorem region_signs (source : Presentation generator registry)
    (polynomials : List (DensePoly (QAdjoin generator.toAlgebraic)))
    (region : Tower.Sample.Region source.context)
    (present : region ∈ (source.family polynomials).regions) :
    ∃ realization : Tower.Conversion.Model region.sample.input source.model,
      region.sample.cell.contains region.sample.value = true ∧
      (∀ x, region.sample.cell.Mem realization.target x ↔ region.Mem source.model x) ∧
      ∀ x, region.Mem source.model x →
        region.sample.signs (polynomials.map source.polynomial) = polynomials.map (fun p =>
          (SignType.sign ((NumberField.polynomial generator p).eval x) : Int)) := by
  simpa only [List.map_map, Function.comp_def, source.polynomial_value] using
    Tower.Sample.Family.region_signs (source.family polynomials) source.model region present

/-- Every actual section is the selected original boundary with its complete sign vector. -/
theorem section_signs (source : Presentation generator registry)
    (polynomials : List (DensePoly (QAdjoin generator.toAlgebraic)))
    (sample : Tower.Sample source.context)
    (present : sample ∈ (source.family polynomials).sections) :
    ∃ root ∈ (source.family polynomials).boundaries,
      sample = Tower.Sample.ofRoot root ∧ sample.cell.contains sample.value = true ∧
      sample.signs (polynomials.map source.polynomial) = polynomials.map (fun p =>
        (SignType.sign ((NumberField.polynomial generator p).eval (root.denote source.model)) : Int)) := by
  simpa only [List.map_map, Function.comp_def, source.polynomial_value] using
    Tower.Sample.Family.sections_correct (source.family polynomials) source.model sample present

/-- Every actual number-field sector has one real interpretation with its complete sign vector. -/
theorem sector_signs (source : Presentation generator registry)
    (polynomials : List (DensePoly (QAdjoin generator.toAlgebraic)))
    (sample : Tower.Sample source.context)
    (present : sample ∈ (source.family polynomials).sectors) :
    ∃ realization : Tower.Conversion.Model sample.input source.model,
      sample.cell.contains sample.value = true ∧ ∀ x,
        sample.cell.Mem realization.target x →
        sample.signs (polynomials.map source.polynomial) = polynomials.map (fun p =>
          (SignType.sign ((NumberField.polynomial generator p).eval x) : Int)) := by
  obtain ⟨realization, inside, signs⟩ :=
    Tower.Sample.Family.sector_signs (source.family polynomials) source.model sample present
  refine ⟨realization, inside, ?_⟩
  intro x contained
  simpa only [List.map_map, Function.comp_def, source.polynomial_value] using signs x contained

end Presentation
end Hex.RealClosure.NumberField

/-- info: 'Hex.RealClosure.NumberField.Presentation.generator_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.Presentation.generator_value

/-- info: 'Hex.RealClosure.NumberField.Presentation.pack_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.Presentation.pack_value

/-- info: 'Hex.RealClosure.NumberField.Presentation.roots_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.Presentation.roots_spec

/-- info: 'Hex.RealClosure.NumberField.Presentation.family_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.Presentation.family_coverage

/-- info: 'Hex.RealClosure.NumberField.Presentation.sector_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.Presentation.sector_signs

/-- info: 'Hex.RealClosure.NumberField.Presentation.cells_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.Presentation.cells_unique

/-- info: 'Hex.RealClosure.NumberField.Presentation.region_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.Presentation.region_signs

/-- info: 'Hex.RealClosure.NumberField.Presentation.roots_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.Presentation.roots_all

/-- info: 'Hex.RealClosure.NumberField.Presentation.roots_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.Presentation.roots_sorted

/-- info: 'Hex.RealClosure.NumberField.Presentation.section_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.Presentation.section_signs

/-- info: 'Hex.RealClosure.NumberField.Presentation.pack_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.Presentation.pack_inv

/-- info: 'Hex.RealClosure.NumberField.Presentation.pack_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.Presentation.pack_sign

/-- info: 'Hex.RealClosure.NumberField.Presentation.roots_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.Presentation.roots_success

/-- info: 'Hex.RealClosure.NumberField.present?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.present?_success
