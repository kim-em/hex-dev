/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerCatalog
public import HexRealClosure.BaseSubsequence

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- A cached native base inclusion, tied to the actual checked subsequence factory. -/
structure BaseInclusion (source target : BaseContext.PackedContext registry) where
  private mk ::
  coefficients : BaseContext.FieldEmbedding source.Carrier target.Carrier
  produced : source.subsequence? target = some coefficients

/-- Include an existing real subsequence and retain every earlier infinitesimal.
The check uses actual native predecessors, with their original progress proofs. -/
def BaseInclusion.make? (source target : BaseContext.PackedContext registry) :
    Option (BaseInclusion source target) :=
  match produced : source.subsequence? target with
  | none => none
  | some coefficients => some ⟨coefficients, produced⟩

/-- The checked nominal wrapper has the same compatibility boundary as its
actual native staged-chain producer. -/
theorem BaseInclusion.make?_isSome (source target : BaseContext.PackedContext registry) :
    (BaseInclusion.make? source target).isSome = true ↔
      List.Sublist source.signature.constants target.signature.constants ∧
        source.signature.infinitesimals ≤ target.signature.infinitesimals := by
  have packaged : (BaseInclusion.make? source target).isSome =
      (source.subsequence? target).isSome := by
    unfold BaseInclusion.make?
    split <;> simp_all only [Option.isSome_none, Option.isSome_some]
  rw [packaged]
  exact source.subsequence?_isSome target

/-- Read the stored coefficient in its original nominal base context. -/
@[expose] def Context.baseStored (base : BaseContext.PackedContext registry) :
    (Context.ofBase base).Value → base.Carrier := by
  cases base with
  | pack context => exact BaseContext.Element.stored

/-- Return a coefficient in the declared nominal target context. -/
@[expose] def Context.baseValue (base : BaseContext.PackedContext registry) :
    base.Carrier → (Context.ofBase base).Value := by
  cases base with
  | pack context => exact fun value => ⟨value⟩

/-- Transport a nominal base value through the cached coefficient embedding. -/
@[expose] def BaseInclusion.value {source target : BaseContext.PackedContext registry}
    (inclusion : BaseInclusion source target) (a : (Context.ofBase source).Value) :
    (Context.ofBase target).Value :=
  Context.baseValue target (inclusion.coefficients.value (Context.baseStored source a))

/-- Native base transport preserves and reflects canonical zero. -/
theorem BaseInclusion.zero {source target : BaseContext.PackedContext registry}
    (inclusion : BaseInclusion source target) (a : (Context.ofBase source).Value) :
    inclusion.value a = 0 ↔ a = 0 := by
  cases source with
  | pack source =>
    cases target with
    | pack target =>
      change (⟨inclusion.coefficients.value a.stored⟩ : BaseContext.Element target) = 0 ↔ a = 0
      exact (BaseContext.Element.stored_eq_zero _).symm.trans
        ((inclusion.coefficients.zero a.stored).trans (BaseContext.Element.stored_eq_zero a))

/-- Native base transport retains the actual one. -/
theorem BaseInclusion.one {source target : BaseContext.PackedContext registry}
    (inclusion : BaseInclusion source target) : inclusion.value 1 = 1 := by
  cases source with
  | pack source =>
    cases target with
    | pack target =>
      apply BaseContext.Element.ext
      exact inclusion.coefficients.one

/-- Native base transport follows subtraction in the stored dictionaries. -/
theorem BaseInclusion.sub {source target : BaseContext.PackedContext registry}
    (inclusion : BaseInclusion source target) (a b : (Context.ofBase source).Value) :
    inclusion.value (a - b) = inclusion.value a - inclusion.value b := by
  cases source with
  | pack source =>
    cases target with
    | pack target =>
      apply BaseContext.Element.ext
      exact inclusion.coefficients.sub a.stored b.stored

/-- Native base transport follows multiplication in the stored dictionaries. -/
theorem BaseInclusion.mul {source target : BaseContext.PackedContext registry}
    (inclusion : BaseInclusion source target) (a b : (Context.ofBase source).Value) :
    inclusion.value (a * b) = inclusion.value a * inclusion.value b := by
  cases source with
  | pack source =>
    cases target with
    | pack target =>
      apply BaseContext.Element.ext
      exact inclusion.coefficients.mul a.stored b.stored

/-- Native base transport follows totalized inversion, including zero. -/
theorem BaseInclusion.inv {source target : BaseContext.PackedContext registry}
    (inclusion : BaseInclusion source target) (a : (Context.ofBase source).Value) :
    inclusion.value a⁻¹ = (inclusion.value a)⁻¹ := by
  cases source with
  | pack source =>
    cases target with
    | pack target =>
      apply BaseContext.Element.ext
      exact inclusion.coefficients.inv a.stored

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.BaseInclusion.make?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseInclusion.make?_isSome

/-- info: 'Hex.RealClosure.Tower.BaseInclusion.inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseInclusion.inv

/-- info: 'Hex.RealClosure.BaseContext.FieldEmbedding.rationalFunctions_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.FieldEmbedding.rationalFunctions_sign
