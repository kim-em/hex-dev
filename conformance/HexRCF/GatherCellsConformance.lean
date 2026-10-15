/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.GatherCells
import HexRCF.ProofEvidence
import HexRCF.Tactic
namespace Hex.RCF.RealCoefficients.GatherCellsConformance
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula
private def registry : BaseContext.Registry := fun _ => none
private abbrev parent := Context.base (BaseContext.rational registry)

#eval (show IO Unit from do
  let x : parent.Poly := DensePoly.ofCoeffs #[0,1]
  let first ← match Hex.SignDet.Descriptor.validate parent.sign parent.signature
      {context := parent.signature, head := x*x - DensePoly.C (1+1),
        lower := .finite 1, upper := .finite (1+1), indices := [], signs := []} with
    | none => throw (IO.userError "first selected generator failed")
    | some root => pure root
  let second ← match Hex.SignDet.Descriptor.validate parent.sign parent.signature
      {context := parent.signature, head := x*x - DensePoly.C (1+1+1),
        lower := .finite 1, upper := .finite (1+1), indices := [], signs := []} with
    | none => throw (IO.userError "second selected generator failed")
    | some root => pure root
  let a := parent.adjoin first
  let b := parent.adjoin second
  let owners := [a.context,b.context]
  let alpha : GatherCells.Source owners := ⟨⟨0,by simp [owners]⟩,a.generator⟩
  let beta : GatherCells.Source owners := ⟨⟨1,by simp [owners]⟩,b.generator⟩
  let coefficients : Fin 3 → GatherCells.Source owners := fun i =>
    if i.val = 1 then beta else alpha
  let original : List (GatherCells.Source owners) :=
    [⟨⟨1,by simp [owners]⟩,b.generator-(1 : b.context.Value)⟩, ⟨⟨0,by simp [owners]⟩,a.generator-(1 : a.context.Value)⟩,
      ⟨⟨1,by simp [owners]⟩,-b.generator⟩]
  let boundVar : Poly 4 := MvPoly.X 3
  let positive : QF 4 := .atom ⟨boundVar^2 + MvPoly.X 1 - MvPoly.X 0,.gt⟩
  let cancelled : QF 4 := .atom
    ⟨(MvPoly.X 0 - MvPoly.X 2)*boundVar^4 + boundVar^2,.ge⟩
  let formula := QF.and positive cancelled
  match GatherCells.build (.pack (BaseContext.rational registry)) coefficients original formula with
  | .error cause => throw (IO.userError s!"cross-owner production failed: {repr cause}")
  | .ok ⟨shared,packet⟩ => do
    let input := packet.family.collection.input
    let values := input.value ∘ GatherCells.values shared coefficients
    let guards := (GatherCells.guards shared original).map input.value
    unless packet.roots.roots.length == 1 do
      throw (IO.userError "leading cancellation or repeated zero root changed")
    for quantifier in [Quantifier.existsReal,.forallReal] do
      unless (CompleteReplay.check input.context.codec values formula guards packet.radical
          quantifier packet.rootGraph packet.cells).toOption == some true do
        throw (IO.userError "independent-owner source values changed after complete replay")
    let swapped : Fin 3 → input.context.Value := fun i =>
      if i.val = 0 then values 1 else if i.val = 1 then values 0 else values i
    match CompleteReplay.check input.context.codec swapped formula guards packet.radical
        .forallReal packet.rootGraph packet.cells with
    | .error .binding => pure ()
    | .error .evidence => pure ()
    | _ => throw (IO.userError "complete replay accepted a swapped source coordinate order")
    let empty := fun i : Fin 0 => i.elim0
    let constantFormula : QF 1 := .ff
    match GatherCells.buildWith shared empty original constantFormula with
    | .error cause => throw (IO.userError s!"guard-only constant construction failed: {repr cause}")
    | .ok constantPacket => do
      let point := constantPacket.family.collection.input
      for quantifier in [Quantifier.existsReal,.forallReal] do
        unless (CompleteReplay.check point.context.codec (fun i : Fin 0 => i.elim0)
            constantFormula ((GatherCells.guards shared original).map point.value) constantPacket.radical
            quantifier constantPacket.rootGraph constantPacket.cells).toOption == some false do
          throw (IO.userError "guard-only false constant changed its strict verdict")
      let zero : GatherCells.Source owners := ⟨⟨1,by simp [owners]⟩,0⟩
      match GatherCells.build (.pack (BaseContext.rational registry)) empty
          (original ++ [zero]) constantFormula with
      | .error .divisor => pure ()
      | _ => throw (IO.userError "late original zero guard was lost with an empty coefficient tuple")
      IO.println "independent owners, repeated coordinates, leading cancellation, guard-only constants and source-order refusal pass")

run_meta do
  for name in #[``GatherCells.values_real,``GatherCells.guards_nonzero,
      ``GatherCells.buildWith_complete,``GatherCells.build_complete,
      ``GatherCells.build_zero,``GatherCells.build_domains] do
    let .thmInfo declaration ← Lean.getConstInfo name | throwError "expected actual gathering theorem"
    let _ ← Hex.RCF.checkProof name declaration.type declaration.value
    let axioms ← Lean.collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "unexpected cross-owner packet axiom: {name}"
  let seen ← Hex.RCF.ProofEvidence.projectDependencies #[``GatherCells.build_complete]
  for required in #[``Shared.gather?_models,``CellDiscover.run_complete,
      ``GatherCells.values_real,``GatherCells.guards_nonzero,``CompleteReplay.check_covered,
      ``Inclusions.Models.value] do
    unless seen.contains required do throwError "cross-owner progress omitted actual law: {required}"
  Lean.logInfo "six cross-owner packet proof bodies checked with actual gathering and complete replay laws"
end Hex.RCF.RealCoefficients.GatherCellsConformance
