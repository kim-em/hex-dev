/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.RealCoefficients
import HexRCF.RootTransportConformance
import HexRCF.ProofEvidence
import Lean.Elab.Command
open Hex.RCF.SelectedRootTests.Data
namespace Hex.RCF.RealCoefficients.RootTransportOrdinaryConformance
open Hex.RCF.RealCoefficients.RootTransportConformance
theorem selected : checked.converted.root original.value original.zero_iff original.one
    original.add original.sub original.mul original.nat original.sign = Real.sqrt 2 :=
  (Hex.RCF.RealCoefficients.RootTransportData.interpretation.root lower
    checked.converted checked.binding).trans selectedSqrt
theorem values (a : extension.context.Value) :
    model.target.value ((Hex.RCF.RealCoefficients.RootTransport.step Hex.RCF.RealCoefficients.RootTransportData.conversion
      lower checked.converted checked.binding).value a) =
      (rational.adjoin lower).value a :=
  (Hex.RCF.RealCoefficients.RootTransportData.interpretation.adjoinWith lower checked.converted
    checked.binding
    (Hex.RCF.RealCoefficients.RootTransport.step
      Hex.RCF.RealCoefficients.RootTransportData.conversion lower checked.converted checked.binding)
    rfl HEq.rfl).value a
/-- info: 'Hex.RCF.RealCoefficients.RootTransportOrdinaryConformance.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selected
/-- info: 'Hex.RCF.RealCoefficients.RootTransportOrdinaryConformance.values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms values
open Lean in
run_meta do
  for name in #[``selected, ``values] do
    let proof := Lean.mkConst name
    let _ ← Hex.RCF.checkProof name (← Lean.Meta.inferType proof) proof
    let axioms ← collectAxioms name
    unless axioms.size == 3 && axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "unapproved fresh root transport axiom"
  for (name, law) in #[(``selected, ``Hex.RealClosure.Tower.Conversion.Model.root),
      (``values, ``Hex.RealClosure.Tower.Conversion.Model.adjoinWith)] do
    unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf law) do
      throwError "fresh root transport omitted owner law"
    for producer in #[``Hex.SignDet.Descriptor.validate, ``Hex.RealClosure.Algebraic.Element.ofPoly,
        ``Hex.SignDet.buildPrepared, ``Hex.RCF.RealCoefficients.ScalarPacket.build] do
      if ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf producer) then
        throwError "fresh transport retained producer"
end Hex.RCF.RealCoefficients.RootTransportOrdinaryConformance
