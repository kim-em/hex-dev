/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.NestedTransport.Read
import HexRCF.RealCoefficients.RootTransport
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
open Hex.RCF.RealCoefficients
namespace Hex.RCF.RealCoefficients.NestedTransportTests.Model
open Hex.RCF.RealCoefficients.NestedTransportTests.Context
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
noncomputable def firstMeaning := RootTransport.model RootTransportData.interpretation
  Data.lower RootTransportConformance.checked.converted RootTransportConformance.checked.binding
noncomputable def sourceMeaning : Model Data.parent ℝ := Data.parent_eq ▸ (Data.rational.adjoin Data.lower)
noncomputable def convertedMeaning := firstMeaning.cast Data.parent_eq
private theorem frame_models (left right : Literal)
    (hl : Literal.ofJson (rootData Data.base.codec Data.lower) = some left)
    (hr : Literal.ofJson (rootData Data.base.codec Data.lower) = some right)
    (same : left = right) :
    HEq (Data.rational.root (.base (BaseContext.rational Data.registry)) Data.lower left hl)
      (Data.rational.root (.base (BaseContext.rational Data.registry)) Data.lower right hr) := by
  cases same
  rfl
private theorem original_same : sourceMeaning = Data.original := by
  have original : HEq (Data.rational.adjoin Data.lower) Data.original := by
    change HEq
      (Data.rational.root (.base (BaseContext.rational Data.registry)) Data.lower
        Data.extension.frame Data.extension.encoded)
      (Data.rational.root (.base (BaseContext.rational Data.registry)) Data.lower
        Data.frozenFrame Data.frameEncoded)
    exact frame_models _ _ _ _ Data.frame_eq
  have casted := (Model.cast_heq (Data.rational.adjoin Data.lower) Data.parent_eq).trans original
  exact eq_of_heq casted
private noncomputable def changeModel {left right : Context Data.registry}
    (same : left = right) (m : Model left ℝ) : Model right ℝ := by
  cases same
  exact m
private theorem model_values {left right : Context Data.registry}
    (same : left = right) (m : Model left ℝ)
    (f : Data.parent.Value → left.Value) (g : Data.parent.Value → right.Value)
    (values : HEq g f) (a : Data.parent.Value) :
    (changeModel same m).value (g a) = m.value (f a) := by
  cases same
  cases eq_of_heq values
  rfl
noncomputable def interpretation : Conversion.Model Hex.RCF.RealCoefficients.NestedTransportTests.Conversion.converted Data.original where
  target := changeModel context_eq convertedMeaning.target
  value a :=
    (model_values context_eq convertedMeaning.target conversion.value
      Hex.RCF.RealCoefficients.NestedTransportTests.Conversion.converted.value Hex.RCF.RealCoefficients.NestedTransportTests.Conversion.map_eq.symm a).trans
      ((convertedMeaning.value a).trans
        (congrArg (fun m : Model Data.parent ℝ => m.value a) original_same))
def checked := (Hex.RCF.RealCoefficients.NestedTransportTests.Read.readAt Hex.RCF.RealCoefficients.NestedTransportTests.Facts.facts
  Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts).toOption.get Hex.RCF.RealCoefficients.NestedTransportTests.Read.accepted
noncomputable def point : ℝ := checked.converted.root interpretation.target.value
  interpretation.target.zero_iff interpretation.target.one interpretation.target.add
  interpretation.target.sub interpretation.target.mul interpretation.target.nat interpretation.target.sign
theorem point_eq : point = Upper.root.root Data.original.value Data.original.zero_iff Data.original.one
    Data.original.add Data.original.sub Data.original.mul Data.original.nat Data.original.sign :=
  interpretation.root Upper.root checked.converted checked.binding
#print axioms interpretation
#print axioms point_eq
#print axioms original_same
end Hex.RCF.RealCoefficients.NestedTransportTests.Model
