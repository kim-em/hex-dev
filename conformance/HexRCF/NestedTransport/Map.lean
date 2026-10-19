/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.NestedTransport.Context
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
open Hex.RCF.RealCoefficients
namespace Hex.RCF.RealCoefficients.NestedTransportTests.Map
open Hex.RCF.RealCoefficients.NestedTransportTests.Context
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
private theorem apply_heq {A B C : Type} {f : A → B} {g : A → C}
    (same : B = C) (h : HEq f g) (a : A) : HEq (f a) (g a) := by
  cases same
  cases eq_of_heq h
  rfl
private theorem functions {A B C : Type} {f : A → B} {g : A → C}
    (same : B = C) (h : ∀ a, HEq (f a) (g a)) : HEq f g := by
  cases same
  exact heq_of_eq (funext (fun a => eq_of_heq (h a)))
def mapped (facts : List (Algebraic.SignFact native))
    (prior : List (Algebraic.SignFact Data.native)) : Data.parent.Value → target.Value := fun a =>
  Algebraic.Element.pack native.reduce rfl facts
    (DensePoly.ofCoeffs (a.polynomial.toArray.map (RootTransportData.mapped prior)))
private theorem closure : HEq conversion.value
    (fun a : Data.parent.Value => Algebraic.Element.ofPoly (context := native)
      (DensePoly.ofCoeffs (a.polynomial.toArray.map RootTransportData.conversion.value))) := by
  have castValues := (Conversion.cast_spec first Data.parent_eq).2
  have firstValues := (RootTransport.step_spec RootTransportData.conversion Data.lower descriptor
    RootTransportConformance.checked.binding).2
  have packing := Tower.Context.adjoin_pack chain descriptor
  apply functions (congrArg Context.Value context_eq)
  intro a
  have point := apply_heq (congrArg Context.Value (Conversion.cast_spec first Data.parent_eq).1) castValues a
  have pointFirst := apply_heq (congrArg Context.Value (RootTransport.step_spec RootTransportData.conversion
    Data.lower descriptor RootTransportConformance.checked.binding).1) firstValues
    (_root_.cast (congrArg Context.Value Data.parent_eq.symm) a)
  have pointPack := apply_heq (congrArg Context.Value (Tower.Context.adjoin_native chain descriptor).1) packing
    (DensePoly.ofCoeffs (a.polynomial.toArray.map RootTransportData.conversion.value))
  exact point.trans (pointFirst.trans (by
    rw [Hex.RCF.RealCoefficients.NestedTransportTests.Context.polynomial]
    exact pointPack))
theorem mapped_eq (facts : List (Algebraic.SignFact native))
    (prior : List (Algebraic.SignFact Data.native)) :
    HEq (mapped facts prior) conversion.value := by
  have equality : mapped facts prior = fun a : Data.parent.Value =>
      Algebraic.Element.ofPoly (context := native)
        (DensePoly.ofCoeffs (a.polynomial.toArray.map RootTransportData.conversion.value)) := by
    funext a
    simp only [mapped, RootTransportData.mapped_eq]
    exact Algebraic.Element.pack_eq native.reduce rfl facts _
  exact (heq_of_eq equality).trans closure.symm
end Hex.RCF.RealCoefficients.NestedTransportTests.Map
