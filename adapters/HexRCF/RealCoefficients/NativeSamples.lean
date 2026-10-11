/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.NativeSpecialize

public section
namespace Hex.RCF.RealCoefficients.NativeSamples
open Hex Hex.RealFormula Hex.RealClosure Hex.RealClosure.Tower
variable {registry : BaseContext.Registry} {parent : Context registry}
variable {K : Type u} [Field K] [LinearOrder K] [DecidableEq K]

/-- The actual sample coefficient conversion agrees with shared specialization
in the target context. The model field may be non-Archimedean; no ordinary-real
interpretation of the whole parent context is assumed. -/
theorem row_converted (original : Model parent K) (sample : Tower.Sample parent)
    (conversion : Conversion.Model sample.input original)
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n + 1)) :
    sample.signs (RepresentationSpecialize.prepare values formula) =
      NativeSpecialize.row sample.input.context (sample.input.value ∘ values) sample.value formula := by
  rw [Tower.Sample.signs_correct sample original conversion]
  unfold NativeSpecialize.row RepresentationSpecialize.prepare
  simp only [List.map_map]
  apply List.map_congr_left
  intro q _
  dsimp only [Function.comp_def]
  rw [conversion.target.sign,
    ← HexPolyMathlib.Interpret.eval_interpret conversion.target.value conversion.target.zero_iff
      conversion.target.add conversion.target.mul]
  change (SignType.sign (RepresentationSpecialize.evaluate original.value original.zero_iff
    (conversion.target.value sample.value) (RepresentationSpecialize.polynomial values q)) : Int) =
    (SignType.sign (RepresentationSpecialize.evaluate conversion.target.value conversion.target.zero_iff
      (conversion.target.value sample.value)
      (RepresentationSpecialize.polynomial (sample.input.value ∘ values) q)) : Int)
  rw [RepresentationSpecialize.polynomial_eval₂ original.value original.zero_iff original.one
      original.add original.mul original.nat original.neg,
    RepresentationSpecialize.polynomial_eval₂ conversion.target.value conversion.target.zero_iff
      conversion.target.one conversion.target.add conversion.target.mul conversion.target.nat
      conversion.target.neg]
  have same : (fun j => original.value (values j)) =
      (fun j => conversion.target.value ((sample.input.value ∘ values) j)) := by
    funext j
    exact (conversion.value _).symm
  rw [same]

omit [DecidableEq K] in
/-- Every original divisor retains its sign in the sample context. -/
theorem sign_converted (original : Model parent K) (sample : Tower.Sample parent)
    (conversion : Conversion.Model sample.input original) (a : parent.Value) :
    sample.input.context.sign (sample.input.value a) = parent.sign a := by
  rw [conversion.target.sign, conversion.value, original.sign]

section Infinite
variable [Infinite K]

/-- Converted specialization is the same ambient polynomial. -/
theorem polynomial_converted (original : Model parent K) (sample : Tower.Sample parent)
    (conversion : Conversion.Model sample.input original)
    (values : Fin n → parent.Value) (q : RealFormula.Poly (n + 1)) :
    HexPolyMathlib.Interpret.interpret conversion.target.value conversion.target.zero_iff
      (RepresentationSpecialize.polynomial (sample.input.value ∘ values) q) =
    HexPolyMathlib.Interpret.interpret original.value original.zero_iff
      (RepresentationSpecialize.polynomial values q) := by
  apply Polynomial.funext
  intro x
  change RepresentationSpecialize.evaluate conversion.target.value conversion.target.zero_iff x _ =
    RepresentationSpecialize.evaluate original.value original.zero_iff x _
  rw [RepresentationSpecialize.polynomial_eval₂ conversion.target.value conversion.target.zero_iff
      conversion.target.one conversion.target.add conversion.target.mul conversion.target.nat
      conversion.target.neg,
    RepresentationSpecialize.polynomial_eval₂ original.value original.zero_iff original.one
      original.add original.mul original.nat original.neg]
  have same : (fun j => conversion.target.value ((sample.input.value ∘ values) j)) =
      (fun j => original.value (values j)) := by
    funext j
    exact conversion.value _
  rw [same]

/-- Coefficient conversion preserves the actual specialized degree. -/
theorem degree_converted (original : Model parent K) (sample : Tower.Sample parent)
    (conversion : Conversion.Model sample.input original)
    (values : Fin n → parent.Value) (q : RealFormula.Poly (n + 1)) :
    (RepresentationSpecialize.polynomial (sample.input.value ∘ values) q).natDegree =
      (RepresentationSpecialize.polynomial values q).natDegree := by
  rw [← HexPolyMathlib.Interpret.natDegree_interpret conversion.target.value conversion.target.zero_iff,
    polynomial_converted original sample conversion,
    HexPolyMathlib.Interpret.natDegree_interpret]

/-- Conversion preserves normalized size, distinguishing zero from constants. -/
theorem size_converted (original : Model parent K) (sample : Tower.Sample parent)
    (conversion : Conversion.Model sample.input original)
    (values : Fin n → parent.Value) (q : RealFormula.Poly (n + 1)) :
    (RepresentationSpecialize.polynomial (sample.input.value ∘ values) q).size =
      (RepresentationSpecialize.polynomial values q).size := by
  have zero : RepresentationSpecialize.polynomial (sample.input.value ∘ values) q = 0 ↔
      RepresentationSpecialize.polynomial values q = 0 := by
    rw [← HexPolyMathlib.Interpret.interpret_eq_zero conversion.target.value conversion.target.zero_iff,
      polynomial_converted original sample conversion,
      HexPolyMathlib.Interpret.interpret_eq_zero]
  by_cases empty : RepresentationSpecialize.polynomial values q = 0
  · simp only [zero.mpr empty, empty, DensePoly.size_zero]
  · have left := mt (DensePoly.size_eq_zero_iff
      (RepresentationSpecialize.polynomial (sample.input.value ∘ values) q)).mp
      (mt zero.mp empty)
    have right := mt (DensePoly.size_eq_zero_iff (RepresentationSpecialize.polynomial values q)).mp empty
    have degree := degree_converted original sample conversion values q
    rw [DensePoly.natDegree_eq_size_sub_one, DensePoly.natDegree_eq_size_sub_one] at degree
    omega

/-- A true converted sample row has an ordinary-real witness at one finite
reader, retaining every supplied original divisor and authenticated coordinate.
The actual target provider history and source identities remain explicit;
this is native point realization, not frozen replay or complete cell coverage. -/
theorem true_real (original : Model parent K) (sample : Tower.Sample parent)
    (conversion : Conversion.Model sample.input original)
    (following : sample.input.context.origin.base.Realization)
    (values : Fin n → parent.Value) (source : Fin n → ℝ)
    (fixed : ∀ i, sample.input.context.origin.RealValue following
      (sample.input.value (values i)) (source i))
    (formula : RealFormula.QF (n + 1)) (guards : List parent.Value)
    (nonzero : ∀ a ∈ guards, parent.sign a ≠ 0)
    (truth : Samples.Row.eval formula
      (sample.signs (RepresentationSpecialize.prepare values formula)) = some true) :
    ∃ read : sample.input.context.Value → ℝ, ∃ domain : sample.input.context.Value → Prop,
      Transport.Closed read domain ∧
      (∀ a, domain a → domain (-a) ∧ read (-a) = -read a) ∧ domain sample.value ∧
      (∀ q ∈ formula.polys,
        (RepresentationSpecialize.polynomial source q).size =
          (RepresentationSpecialize.polynomial values q).size) ∧
      formula.toProp (RealFormula.append source (read sample.value)) ∧
      (∀ a ∈ guards, domain (sample.input.value a) ∧ read (sample.input.value a) ≠ 0) ∧
      (∀ a r, sample.input.context.origin.RealValue following a r → domain a ∧ read a = r) := by
  rw [row_converted original sample conversion] at truth
  obtain ⟨read, domain, closed, negative, present, sizes, meaning, divisors, real⟩ :=
    NativeSpecialize.true_real sample.input.context following (sample.input.value ∘ values)
      source fixed sample.value formula (guards.map sample.input.value) (by
        intro a ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        rw [sign_converted original sample conversion]
        exact nonzero b hb) truth
  have sourceSizes q hq := (sizes q hq).trans (size_converted original sample conversion values q)
  exact ⟨read, domain, closed, negative, present, sourceSizes, meaning,
    fun a ha => divisors _ (List.mem_map.mpr ⟨a, ha, rfl⟩), real⟩

end Infinite

/-- A false point row yields a universal counterexample, never a false
existential decision or a completeness claim. -/
theorem not_forall (original : Model parent K) (sample : Tower.Sample parent)
    (conversion : Conversion.Model sample.input original)
    (following : sample.input.context.origin.base.Realization)
    (values : Fin n → parent.Value) (source : Fin n → ℝ)
    (fixed : ∀ i, sample.input.context.origin.RealValue following
      (sample.input.value (values i)) (source i))
    (formula : RealFormula.QF (n + 1))
    (falseRow : Samples.Row.eval formula
      (sample.signs (RepresentationSpecialize.prepare values formula)) = some false) :
    ¬ ∀ x : ℝ, formula.toProp (RealFormula.append source x) := by
  rw [row_converted original sample conversion] at falseRow
  exact NativeSpecialize.not_forall sample.input.context following (sample.input.value ∘ values)
    source fixed sample.value formula falseRow

end Hex.RCF.RealCoefficients.NativeSamples
