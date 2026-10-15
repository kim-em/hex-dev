/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.NumberFieldCells
import HexRCF.ProofEvidence
import HexRCF.Tactic
open Hex Hex.RealClosure Hex.RCF.RealCoefficients
namespace Hex.RCF.NumberFieldCellsConformance
private def registry : BaseContext.Registry := fun _ => none
private def selected (coefficients : List Int) (lower upper : Rat) : Option RealAlgebraicNumber := do
  let d ← Root.validate 7
    { context := 7, head := DensePoly.ofList coefficients,
      lower := .finite lower, upper := .finite upper, indices := [], signs := [] }
  pure d.handle.canonical
private def formula : RealFormula.QF 2 :=
  .atom ⟨MvPoly.X 1 ^ 2 - MvPoly.X 0, .eq⟩
private def trial (coefficients : List Int) (lower upper : Rat)
    (computed expected : Bool) : IO Unit :=
  match selected coefficients lower upper with
  | none => throw (IO.userError "source root construction failed")
  | some generator =>
    let g := generator.toAlgebraic.toQAdjoin
    let values := fun _ : Fin 1 => if computed then g*g-1 else g
    let g := values 0
    let guards := [g,g-1,-g]
    match NumberField.cells generator registry values guards formula with
    | .error cause => throw (IO.userError s!"number-field cells failed: {repr cause}")
    | .ok ⟨source,packet⟩ => do
      let input := packet.family.collection.input
      let converted := input.value ∘ (source.pack ∘ values)
      let original := (guards.map source.pack).map input.value
      let data ← match CellRead.read input.context.codec original packet.roots converted formula packet.cells with
        | .error cause => throw (IO.userError s!"literal replay failed: {repr cause}")
        | .ok data => pure data
      unless (CellReplay.check converted formula original packet.radical packet.roots data .existsReal).toOption == some expected do
        throw (IO.userError "original selected-field existential verdict changed")
      unless (CellReplay.check converted formula original packet.radical packet.roots data .forallReal).toOption == some false do
        throw (IO.userError "original selected-field universal verdict changed")
      let _ : Hashable input.context.Value := RowEncode.hashable input.context.codec
      let _ : Hashable Tower.Signature := RowEncode.hashable Tower.Signature.codec
      let rootGraph := Hex.SignDet.Codec.graph input.context.codec Tower.Signature.codec
        (Hex.SignDet.Dag.encode packet.roots.replay)
      for (quantifier,verdict) in [(RealFormula.Quantifier.existsReal,expected),(.forallReal,false)] do
        unless (CompleteReplay.check input.context.codec converted formula original packet.radical
            quantifier rootGraph packet.cells).toOption == some verdict do
          throw (IO.userError "complete packet changed the selected-field source verdict")
      match NumberField.cells generator registry values [0] .ff with
      | .error .divisor => pure ()
      | _ => throw (IO.userError "zero original guard bypassed preflight")
      IO.println s!"original selected embedding {lower},{upper}: both frozen verdicts and guard preflight passed"
#eval trial [-2,0,1] 1 2 false true
#eval trial [-2,0,1] (-2) (-1) false false
#eval trial [-2,0,0,1] 1 2 true true
run_meta do
  for name in #[``NumberField.cellsWith_spec, ``NumberField.cells_success, ``NumberField.cells_zero,
      ``NumberField.cellsWith_complete, ``NumberField.cells_complete] do
    let .thmInfo info ← Lean.getConstInfo name | throwError "expected theorem"
    let _ ← Hex.RCF.checkProof name info.type info.value
    let axioms ← Lean.collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "unexpected axiom in original-field cell construction: {name}"
  let deps ← Hex.RCF.ProofEvidence.projectDependencies #[``NumberField.cellsWith_spec,``NumberField.cells_success,
    ``NumberField.cellsWith_complete,``NumberField.cells_complete]
  for required in #[``CellDiscover.run_complete, ``CompleteReplay.check_covered,
      ``CellDiscover.run_success, ``Hex.RealClosure.NumberField.present?_success,
      ``Hex.RealClosure.NumberField.Presentation.pack_value,
      ``Hex.RealClosure.NumberField.Presentation.pack_zero, ``NumberField.value_eq_ofField] do
    unless deps.contains required do throwError "original selected-source law missing: {required}"
  Lean.logInfo "actual factory/source/cell proof bodies kernel checked with original selected-field laws"
end Hex.RCF.NumberFieldCellsConformance
