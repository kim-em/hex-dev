/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerInclusion
public import HexRealClosureMathlib.TowerNaturality

public section

namespace Hex.RealClosure.Tower.Inclusion

variable {registry : BaseContext.Registry} {K : Type u}
variable [Field K] [LinearOrder K]
variable {source destination : Context registry}

/-- The interpretation of the actual conversion underlying a checked
inclusion. Target ownership is fixed by its native context equality. -/
structure Model (inclusion : Inclusion source destination)
    (original : Tower.Model source K) where
  conversion : Conversion.Model inclusion.conversion original

namespace Model

/-- Package a proved value-preserving native inclusion with the specified
source and target interpretations. -/
noncomputable def ofValues (inclusion : Inclusion source destination)
    (original : Tower.Model source K) (target : Tower.Model destination K)
    (preserved : ∀ a, target.value (inclusion.value a) = original.value a) :
    Inclusion.Model inclusion original := by
  rcases inclusion with ⟨conversion, same⟩
  cases same
  exact ⟨⟨target, preserved⟩⟩

variable {inclusion : Inclusion source destination} {original : Tower.Model source K}
variable (model : Model inclusion original)
include model

/-- Interpret the exact returned target, using its checked context equality. -/
noncomputable def target : Tower.Model destination K :=
  inclusion.context_eq ▸ model.conversion.target

/-- The target changes only the context ownership of the conversion model. -/
theorem target_heq : HEq model.target model.conversion.target := by
  unfold target
  exact model.conversion.target.cast_heq inclusion.context_eq

omit model in
private theorem ofValues_target_proof (inclusion : Inclusion source destination)
    (original : Tower.Model source K) (target : Tower.Model destination K)
    (preserved : ∀ a, target.value (inclusion.value a) = original.value a) :
    (ofValues inclusion original target preserved).target = target := by
  rcases inclusion with ⟨conversion, same⟩
  cases same
  rfl

omit model in
/-- The inclusion package retains the supplied target interpretation. -/
theorem ofValues_target (inclusion : Inclusion source destination)
    (original : Tower.Model source K) (target : Tower.Model destination K)
    (preserved : ∀ a, target.value (inclusion.value a) = original.value a) :
    (ofValues inclusion original target preserved).target = target :=
  ofValues_target_proof inclusion original target preserved

/-- Carry a checked inclusion's interpretation into a larger ordered field. -/
noncomputable def map {L : Type v} [Field L] [LinearOrder L]
    (embedding : K →+* L) (ordered : StrictMono embedding) :
    Inclusion.Model inclusion (original.map embedding ordered) where
  conversion :=
    { target := model.conversion.target.map embedding ordered
      value := by
        intro a
        simp only [Tower.Model.map_value, model.conversion.value] }

/-- Lifting an inclusion also lifts its actual target interpretation. -/
theorem map_target {L : Type v} [Field L] [LinearOrder L]
    (embedding : K →+* L) (ordered : StrictMono embedding) :
    (model.map embedding ordered).target = model.target.map embedding ordered := by
  rcases inclusion with ⟨conversion, same⟩
  cases same
  unfold map target
  rfl

/-- Compose the interpretations of the two actual cached inclusions. -/
noncomputable def comp {following : Context registry}
    {next : Inclusion destination following}
    (nextModel : Inclusion.Model next model.target) :
    Inclusion.Model (inclusion.comp next) original := by
  rcases inclusion with ⟨conversion, same⟩
  cases same
  dsimp only [Inclusion.Model.target] at nextModel
  exact ⟨model.conversion.comp nextModel.conversion⟩

/-- The composite inclusion uses the second inclusion's actual target model. -/
theorem comp_target {following : Context registry}
    {next : Inclusion destination following}
    (nextModel : Inclusion.Model next model.target) :
    (model.comp nextModel).target = nextModel.target := by
  apply Tower.Model.value_ext
  intro a
  rcases inclusion with ⟨conversion, same⟩
  cases same
  unfold comp target
  have aligned := model.conversion.comp_target nextModel.conversion
  have second := nextModel.conversion.target.cast_heq next.context_eq
  have first := (model.conversion.comp nextModel.conversion).target.cast_heq
    (Inclusion.comp ⟨conversion, rfl⟩ next).context_eq
  exact congrArg (fun m : Tower.Model following K => m.value a)
    (eq_of_heq (first.trans (aligned.trans second.symm)))

/-- The checked inclusion preserves every original interpreted value. -/
theorem value (a : source.Value) :
    model.target.value (inclusion.value a) = original.value a := by
  unfold Inclusion.value
  exact (Tower.Model.value_cast inclusion.context_eq model.conversion.target model.target
    (model.conversion.target.cast_heq inclusion.context_eq) _).trans
      (model.conversion.value a)

/-- The original canonical zero is the target canonical zero. -/
theorem zero : inclusion.value 0 = 0 :=
  (model.target.zero_iff _).mp ((model.value 0).trans ((original.zero_iff 0).mpr rfl))

/-- Signs use the same interpreted values in the original and shared contexts. -/
theorem sign (a : source.Value) : destination.sign (inclusion.value a) = source.sign a := by
  rw [model.target.sign, model.value, original.sign]

variable [DecidableEq K]

/-- Transport preserves the whole polynomial through the original-owner map. -/
theorem polynomial (p : source.Poly) :
    HexPolyMathlib.Interpret.interpret model.target.value model.target.zero_iff
      (inclusion.polynomial p) =
    HexPolyMathlib.Interpret.interpret original.value original.zero_iff p := by
  apply Polynomial.ext
  intro i
  rw [HexPolyMathlib.Interpret.coeff_interpret, HexPolyMathlib.Interpret.coeff_interpret]
  unfold Inclusion.polynomial
  have coefficient := Transport.polynomial_coeff inclusion.value model.zero p i
  change (DensePoly.ofCoeffs (p.toArray.map inclusion.value)).coeff i =
    inclusion.value (p.coeff i) at coefficient
  rw [coefficient, model.value]

/-- Checked transport preserves and reflects native mathematical equality. -/
theorem equal (a b : source.Value) :
    destination.equal (inclusion.value a) (inclusion.value b) = source.equal a b := by
  rw [model.target.equal_spec, original.equal_spec, model.value, model.value]

variable [IsStrictOrderedRing K]

/-- Checked transport preserves all three native comparison results. -/
theorem compare (a b : source.Value) :
    destination.compare (inclusion.value a) (inclusion.value b) = source.compare a b := by
  rw [model.target.compare_spec, original.compare_spec, model.value, model.value]

end Model
end Hex.RealClosure.Tower.Inclusion

/-- info: 'Hex.RealClosure.Tower.Inclusion.Model.value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusion.Model.value

/-- info: 'Hex.RealClosure.Tower.Inclusion.Model.polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusion.Model.polynomial

/-- info: 'Hex.RealClosure.Tower.Inclusion.Model.compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusion.Model.compare

/-- info: 'Hex.RealClosure.Tower.Inclusion.Model.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusion.Model.comp

/-- info: 'Hex.RealClosure.Tower.Inclusion.Model.comp_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusion.Model.comp_target
