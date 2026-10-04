/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerReuse
public import HexRealClosureMathlib.TowerTransport
public import HexSignDetMathlib.SelectedRoot

public section

namespace Hex.RealClosure.Tower.Conversion.Model

variable {registry : BaseContext.Registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]
variable {source : Context registry} {conversion : Conversion source}
variable {original : Tower.Model source K} (model : Model conversion original)
variable (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
variable (converted : SignDet.Descriptor conversion.context.Value Signature
  conversion.context.sign conversion.context.signature)
variable (binding : converted.raw = source.mapDescriptor conversion.context conversion.value descriptor)
variable (candidate : conversion.context.Value)
variable (selected : converted.raw.constraints.map
  (fun p => conversion.context.sign (p.eval candidate)) = converted.raw.constraintSigns)

include binding selected in
/-- The executable constraints identify the selected root in the unchanged
target field. Derivative signs and interval bounds are checked together. -/
theorem reuseRoot_value :
    model.target.value candidate = descriptor.root original.value original.zero_iff
      original.one original.add original.sub original.mul original.nat original.sign := by
  have equal := (converted.constraints_iff model.target.value model.target.zero_iff
    model.target.one model.target.add model.target.sub model.target.mul model.target.nat
    model.target.sign (model.target.value candidate)).mp (by
      rw [← selected]
      unfold SignDet.signsAt
      apply List.map_congr_left
      intro p hp
      rw [HexPolyMathlib.Interpret.eval_interpret model.target.value model.target.zero_iff
        model.target.add model.target.mul, ← model.target.sign])
  exact equal.trans (model.root descriptor converted binding)

/-- Reusing an existing selected root preserves every source value while
keeping the original target context and its interpretation. -/
@[expose] noncomputable def reuseRoot :
    Model (conversion.reuseRoot descriptor converted binding candidate selected)
      (original.adjoin descriptor) := by
  refine ⟨model.target, ?_⟩
  intro x
  change model.target.value ((DensePoly.ofCoeffs
    ((source.polynomial descriptor x).toArray.map conversion.value)).eval candidate) = _
  rw [← HexPolyMathlib.Interpret.eval_interpret model.target.value model.target.zero_iff
    model.target.add model.target.mul, model.polynomial,
    model.reuseRoot_value descriptor converted binding candidate selected,
    original.adjoin_value descriptor x, original.adjoin_generator]

end Hex.RealClosure.Tower.Conversion.Model

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.reuseRoot_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Conversion.Model.reuseRoot_value

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.reuseRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Conversion.Model.reuseRoot
