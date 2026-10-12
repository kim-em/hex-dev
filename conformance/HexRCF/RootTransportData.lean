/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.RealCoefficients.RootTransport
import HexRCF.SelectedRoot.Data
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.RealCoefficients.RootTransportData
private theorem target {r : BaseContext.Registry} {s t q : Context r}
    {a : s.Value → t.Value} {b : s.Value → q.Value}
    (h : t = q) (v : HEq a b) (proof : Transport s t a) : Transport s q b := by
  cases h
  cases eq_of_heq v
  exact proof
private def embedding : Data.base.Value → Data.parent.Value :=
  Algebraic.Element.ofCoeff (context := Data.native)
private theorem embedding_eq : HEq Data.extension.embed embedding :=
  (Context.adjoin_native (.base (BaseContext.rational Data.registry)) Data.lower).2.1
private theorem inclusion : Transport Data.base Data.parent embedding :=
  target Data.parent_eq embedding_eq
    (Transport.inclusion Data.base Data.lower Data.extension rfl)
def conversion : Conversion Data.base := Conversion.ofTransport embedding inclusion
def mapped (facts : List (Algebraic.SignFact Data.native)) : Data.base.Value → Data.parent.Value :=
  fun a => Algebraic.Element.pack Data.reduction Data.reduction_eq facts (DensePoly.C a)
theorem mapped_eq (facts : List (Algebraic.SignFact Data.native)) : mapped facts = conversion.value := by
  funext a
  exact Algebraic.Element.pack_eq Data.reduction Data.reduction_eq facts (DensePoly.C a)
noncomputable def interpretation : Conversion.Model conversion Data.rational where
  target := Data.original
  value a := Data.rational.root_embed (.base (BaseContext.rational Data.registry))
    Data.lower Data.frozenFrame Data.frameEncoded a
#print axioms interpretation
end Hex.RCF.RealCoefficients.RootTransportData
