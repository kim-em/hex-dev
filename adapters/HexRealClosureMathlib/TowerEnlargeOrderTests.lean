/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TowerEnlargeOrder
public import HexRealClosureMathlib.SelectedRoot

namespace Hex.RealClosure.Tower.EnlargeOrder.Tests

open scoped Hex.OrderedFn.Infinitesimal

private def registry : BaseContext.Registry := fun _ => none
private abbrev rationalBase := BaseContext.rational registry
private abbrev base := Context.base rationalBase
private noncomputable def rational : Model base ℝ :=
  Model.base rationalBase (Rat.castHom ℝ) ratSign

/-- Restriction of an arbitrary old rational tower model retains every value
inside the actual relative algebraic union of its extracted base map. -/
example (suffix : Suffix base) (old : Model suffix.context ℝ) :
    let initial := suffix.restrict rational old
    letI : Field Rat := HexPolyMathlib.fieldOfGrind
    letI : Algebra Rat ℝ := (initial.baseHom rationalBase).toAlgebra
    ∀ a, ((Model.suffixRestrict rationalBase suffix rational old).value a : ℝ) = old.value a :=
  Model.suffixRestrict_value rationalBase suffix rational old

/-- The new infinitesimal ambient is algebraic over the native rational
function base, rather than over the full old ambient ℝ. -/
example (suffix : Suffix base) (old : Model suffix.context ℝ) :
    let initial := suffix.restrict rational old
    letI : Field Rat := HexPolyMathlib.fieldOfGrind
    letI : Algebra Rat ℝ := (initial.baseHom rationalBase).toAlgebra
    let restricted := Model.suffixRestrict rationalBase suffix rational old
    let coefficient := (suffix.restrict rational restricted).baseHom rationalBase
    let ambient := Ambient.infinitesimal (Union.Carrier Rat ℝ)
    letI : Field (Hex.RationalFn Rat) := HexPolyMathlib.fieldOfGrind
    letI : Algebra (Hex.RationalFn Rat) ambient.Carrier :=
      (Ambient.mappedNativeHom HexPolyMathlib.toGrind_fieldOfGrind coefficient ambient).toAlgebra
    Algebra.IsAlgebraic (Hex.RationalFn Rat) ambient.Carrier := by
  exact Model.suffixRestrict_algebraic rationalBase suffix rational old

/-- A selected root's actual enlarged context supplies a native parameter
below every old positive value; callers need no cast or new model witness. -/
example (descriptor : SignDet.Descriptor base.Value Signature base.sign base.signature) :
    let context := (base.adjoin descriptor).context
    ∃ result : Conversion context, context.enlarge? = some result ∧
      ∃ parameter : result.context.Value, result.context.sign parameter = 1 ∧
        ∀ a, context.sign a = 1 → result.context.sign (parameter - result.value a) = -1 := by
  obtain ⟨rebuilt, _, enlarged, _, positive, small⟩ := Context.enlarge?_ordered
    rationalBase (.root descriptor .nil) rfl rational (rational.adjoin descriptor)
    (Ambient.infinitesimal ℝ)
  exact ⟨rebuilt.result.cast rfl, enlarged, _, positive, small⟩

end Hex.RealClosure.Tower.EnlargeOrder.Tests
