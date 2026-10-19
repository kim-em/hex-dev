/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.NestedTransport.Map
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.RealCoefficients.NestedTransportTests.Conversion
open Hex.RCF.RealCoefficients.NestedTransportTests.Context
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
private theorem targetProof {r : BaseContext.Registry} {s t q : Context r}
    {a : s.Value → t.Value} {b : s.Value → q.Value}
    (h : t = q) (v : HEq a b) (proof : Transport s t a) : Transport s q b := by
  cases h
  cases eq_of_heq v
  exact proof
def map : Data.parent.Value → target.Value := fun a =>
  Algebraic.Element.ofPoly (context := native)
    (DensePoly.ofCoeffs (a.polynomial.toArray.map
      Hex.RCF.RealCoefficients.RootTransportData.conversion.value))
theorem map_eq : HEq conversion.value map := by
  have h := Hex.RCF.RealCoefficients.NestedTransportTests.Map.mapped_eq ([] : List (Algebraic.SignFact native))
    ([] : List (Algebraic.SignFact Data.native))
  have same : Hex.RCF.RealCoefficients.NestedTransportTests.Map.mapped [] [] = map := by
    funext a
    simp only [Hex.RCF.RealCoefficients.NestedTransportTests.Map.mapped, Hex.RCF.RealCoefficients.RootTransportData.mapped_eq]
    exact Algebraic.Element.pack_eq native.reduce rfl [] _
  exact h.symm.trans (heq_of_eq same)
def converted : Conversion Data.parent := Conversion.ofTransport map
  (targetProof context_eq map_eq conversion.checked)
theorem supplied_eq (facts : List (Algebraic.SignFact native))
    (prior : List (Algebraic.SignFact Data.native)) :
    Hex.RCF.RealCoefficients.NestedTransportTests.Map.mapped facts prior = converted.value := by
  exact eq_of_heq ((Hex.RCF.RealCoefficients.NestedTransportTests.Map.mapped_eq facts prior).trans map_eq)
end Hex.RCF.RealCoefficients.NestedTransportTests.Conversion
