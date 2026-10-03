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
  intro initial
  letI : Field Rat := HexPolyMathlib.fieldOfGrind
  letI : Algebra Rat ℝ := (initial.baseHom rationalBase).toAlgebra
  exact Model.suffixRestrict_algebraic rationalBase suffix rational old
    (Ambient.infinitesimal (Union.Carrier Rat ℝ))

/-- Only the initial coefficient inequalities are supplied to the local
algebraic bound; it then applies to every interpreted old tower value. -/
example (suffix : Suffix base) (old : Model suffix.context ℝ) :
    let ambient := Ambient.infinitesimal ℝ
    ∀ a, 0 < old.value a → ambient.inclusion Hex.RationalFn.X <
      Ambient.coefficientHom ambient (old.value a) := by
  let ambient := Ambient.infinitesimal ℝ
  apply Model.suffix_infinitesimal rationalBase suffix rational old
    (Ambient.coefficientHom ambient) (Ambient.coefficientHom_strictMono ambient)
    (ambient.inclusion Hex.RationalFn.X)
  intro b positive
  exact Ambient.X_lt_coefficient ambient _ positive

/-- A selected root's actual enlargement returns its native parameter below
every old positive value, with no second reconstruction or existential scalar. -/
example (descriptor : SignDet.Descriptor base.Value Signature base.sign base.signature) :
    let context := (base.adjoin descriptor).context
    ∃ result : Enlargement context, context.enlargeWithParameter? = some result ∧
      result.conversion.context.sign result.parameter = 1 ∧
        ∀ a, context.sign a = 1 → result.conversion.context.sign
          (result.parameter - result.conversion.value a) = -1 := by
  obtain ⟨rebuilt, enlarged, _, _, _, positive, small⟩ := Context.enlargeWithParameter?_model
    rationalBase (.root descriptor .nil) rfl rational (rational.adjoin descriptor)
    (Ambient.infinitesimal ℝ)
  exact ⟨rebuilt.enlargement rationalBase rfl, enlarged, positive, small⟩

/-- The combined restriction/enlargement theorem supplies the actual returned
parameter and preservation model over the old tower's relative algebraic union. -/
example (suffix : Suffix base) (old : Model suffix.context ℝ) :
    let initial := suffix.restrict rational old
    letI : Field Rat := HexPolyMathlib.fieldOfGrind
    letI : Algebra Rat ℝ := (initial.baseHom rationalBase).toAlgebra
    let restricted := Model.suffixRestrict rationalBase suffix rational old
    let ambient := Ambient.infinitesimal (Union.Carrier Rat ℝ)
    ∃ result : Enlargement suffix.context,
      suffix.context.enlargeWithParameter? = some result ∧
        Nonempty (Conversion.Model result.conversion (restricted.liftInfinitesimal ambient)) ∧
        result.conversion.context.sign result.parameter = 1 ∧
        ∀ a, suffix.context.sign a = 1 → result.conversion.context.sign
          (result.parameter - result.conversion.value a) = -1 := by
  intro initial
  letI : Field Rat := HexPolyMathlib.fieldOfGrind
  letI : Algebra Rat ℝ := (initial.baseHom rationalBase).toAlgebra
  let ambient := Ambient.infinitesimal (Union.Carrier Rat ℝ)
  obtain ⟨_, _, rebuilt, enlarged, model, _, _, positive, small⟩ :=
    Context.enlargeWithParameter?_algebraic rationalBase suffix rational old ambient
  exact ⟨rebuilt.enlargement rationalBase rfl, enlarged, ⟨model⟩, positive, small⟩

private abbrev nestedBase := rationalBase.infinitesimal
private abbrev nested := Context.base nestedBase
private noncomputable def nestedReference : Model nested (Ambient.infinitesimal Rat).Carrier := by
  classical
  let wide := Ambient.infinitesimal Rat
  let f := Ambient.nativeHom HexRationalFnMathlib.ratField_eq wide
  exact Model.base nestedBase f
    (fun q => Ambient.nativeHom_sign HexRationalFnMathlib.ratField_eq wide q)

/-- A lawful reference for the native ℚ(ε) base supplies actual enlargement
and its returned parameter through every validated root over that base. -/
example (suffix : Suffix nested) :
    ∃ result : Enlargement suffix.context,
      suffix.context.enlargeWithParameter? = some result ∧
      result.conversion.context.sign result.parameter = 1 ∧
      ∀ a, suffix.context.sign a = 1 → result.conversion.context.sign
        (result.parameter - result.conversion.value a) = -1 := by
  classical
  exact Context.enlargeWithParameter?_ordered nestedBase suffix rfl nestedReference

/-- Over a non-Archimedean base, inequalities are supplied only for initial
base values. Algebraicity extends them to the selected root and all its values. -/
example (descriptor : SignDet.Descriptor nested.Value Signature nested.sign nested.signature)
    {L : Type} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    (embedding : (Ambient.infinitesimal Rat).Carrier →+* L) (ordered : StrictMono embedding)
    (parameter : L)
    (small : ∀ a : nested.Value, 0 < nestedReference.value a →
      parameter < embedding (nestedReference.value a)) :
    ∀ a, 0 < (nestedReference.adjoin descriptor).value a →
      parameter < embedding ((nestedReference.adjoin descriptor).value a) := by
  classical
  apply Model.suffix_infinitesimal nestedBase (.root descriptor .nil) nestedReference
    (nestedReference.adjoin descriptor) embedding ordered parameter
  intro b positive
  let a : nested.Value := by
    change BaseContext.Element nestedBase
    exact ⟨b⟩
  change parameter < embedding ((nestedReference.adjoin descriptor).value
    ((nested.adjoin descriptor).embed a))
  rw [Model.adjoin_embed]
  apply small
  change 0 < (nestedReference.adjoin descriptor).value
    ((nested.adjoin descriptor).embed a) at positive
  rwa [Model.adjoin_embed] at positive

end Hex.RealClosure.Tower.EnlargeOrder.Tests
