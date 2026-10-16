/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.AlgebraicCells
import HexRCF.ProofEvidence
import HexRCF.Tactic
open Hex Hex.RealClosure Hex.RealFormula Hex.RCF.RealCoefficients
namespace Hex.RCF.AlgebraicCellsConformance
private def registry : BaseContext.Registry := fun _ => none
private def selected (coefficients : List Int) (lower upper : Rat) : Option RealAlgebraicNumber := do
  let d ← Root.validate 7
    {context := 7,head := DensePoly.ofList coefficients,
      lower := .finite lower,upper := .finite upper,indices := [],signs := []}
  pure d.handle.canonical

#eval (show IO Unit from do
  for q in ([0,1,-1,7/3] : List Rat) do
    let generator := RealAlgebraicNumber.ofRat q
    let some source := AlgebraicCells.presentation generator registry
      | throw (IO.userError "recognized rational presentation was rejected")
    match source.root with
    | .point value =>
      unless value.stored == q do
        throw (IO.userError "rational point changed its original value")
    | .selected .. => throw (IO.userError "rational coefficient added a selected-root extension")
    unless (Hex.RealClosure.NumberField.Presentation.ofRoot? generator registry
        (.point ⟨q+1⟩)).isNone do
      throw (IO.userError "checked point factory accepted a different rational")
  let coordinates : Fin 3 → Rat := fun i => if i.val = 1 then -1 else 7/3
  let some sources := AlgebraicCells.presentations registry (RealAlgebraicNumber.ofRat ∘ coordinates)
    | throw (IO.userError "repeated rational coordinates were rejected")
  for i in List.finRange 3 do
    match (sources i).root with
    | .point value =>
      unless value.stored == coordinates i do
        throw (IO.userError "rational tuple changed its coordinate order")
    | .selected .. => throw (IO.userError "rational tuple added a selected-root extension")
  let original : List (Fin 3) := [2,0,2,1]
  unless ((AlgebraicCells.guards sources original).map (fun guard => guard.1.val)) == [2,0,2,1] do
    throw (IO.userError "rational tuple changed repeated original guard indices")
  IO.println "checked rational points preserve values, repeated coordinates and original guards; wrong points reject")

private def trial (negative : Bool) : IO Unit := do
  let a ← match selected [-2,0,1] (if negative then -2 else 1) (if negative then -1 else 2) with
    | none => throw (IO.userError "original selected square root failed")
    | some value => pure value
  let b ← match selected [-3,0,1] 1 2 with
    | none => throw (IO.userError "second original selected square root failed")
    | some value => pure value
  let inputs : Fin 4 → RealAlgebraicNumber := fun i =>
    if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then .ofRat 1 else 0
  let indices : Fin 2 → Fin 4 := fun i => ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩
  let original : List (Fin 4) := [2,1,0,1]
  let x : Poly 3 := MvPoly.X 2
  let formula : QF 3 := .and (.atom ⟨x^2 + MvPoly.X 1 - MvPoly.X 0,.gt⟩)
    (.and (.atom ⟨x^2,.ge⟩) (.atom ⟨MvPoly.X 0,.gt⟩))
  match AlgebraicCells.build registry inputs indices original formula with
  | .error cause => throw (IO.userError s!"automatic algebraic production failed: {repr cause}")
  | .ok ⟨sources,shared,packet⟩ => do
    let input := packet.family.collection.input
    let values := input.value ∘ GatherCells.values shared (AlgebraicCells.coefficients sources indices)
    let guards := (GatherCells.guards shared (AlgebraicCells.guards sources original)).map input.value
    unless packet.roots.roots.length == 1 do
      throw (IO.userError "automatic coefficient production changed the repeated zero root")
    for (quantifier,expected) in [(Quantifier.existsReal,!negative),(.forallReal,!negative)] do
      unless (CompleteReplay.check input.context.codec values formula guards packet.radical
          quantifier packet.rootGraph packet.cells).toOption == some expected do
        throw (IO.userError "original selected generator changed after automatic presentation and replay")
    match AlgebraicCells.build registry inputs indices (original ++ [3]) formula with
    | .error .divisor => pure ()
    | _ => throw (IO.userError "automatic presentations lost a late original zero guard")
    IO.println s!"automatic original algebraic inputs, negative={negative}: both verdicts and zero preflight pass"

#eval trial false
#eval trial true

private def linearTrial (negative : Bool) : IO Unit := do
  let a ← match selected [-2,0,1] (if negative then -2 else 1) (if negative then -1 else 2) with
    | none => throw (IO.userError "linear source root construction failed")
    | some value => pure value
  let inputs := fun _ : Fin 1 => a
  let indices := fun i : Fin 1 => i
  let x : Poly 2 := MvPoly.X 1
  let formula : QF 2 := .and (.atom ⟨x-MvPoly.X 0,.gt⟩) (.atom ⟨x-1,.lt⟩)
  match AlgebraicCells.build registry inputs indices [0] formula with
  | .error cause => throw (IO.userError s!"linear source production failed: {repr cause}")
  | .ok ⟨sources,shared,packet⟩ => do
    let input := packet.family.collection.input
    let values := input.value ∘ GatherCells.values shared (AlgebraicCells.coefficients sources indices)
    let guards := (GatherCells.guards shared (AlgebraicCells.guards sources [0])).map input.value
    unless packet.roots.roots.length == 2 do
      throw (IO.userError "linear conjugate constraints changed their exact two roots")
    for (quantifier,expected) in [(Quantifier.existsReal,negative),(.forallReal,false)] do
      unless (CompleteReplay.check input.context.codec values formula guards packet.radical
          quantifier packet.rootGraph packet.cells).toOption == some expected do
        throw (IO.userError "linear constraints lost the variable's selected embedding or quantifier")
    IO.println s!"linear original source negative={negative}: exists={negative}, forall=false"

#eval linearTrial false
#eval linearTrial true

#eval (show IO Unit from do
  let inputs : Fin 0 → RealAlgebraicNumber := fun i => i.elim0
  let indices : Fin 0 → Fin 0 := fun i => i.elim0
  let formulas : List (QF 1 × Bool) := [(.tt,true),(.ff,false)]
  for (formula,expected) in formulas do
    match AlgebraicCells.build registry inputs indices [] formula with
    | .error cause => throw (IO.userError s!"empty automatic presentation failed: {repr cause}")
    | .ok ⟨sources,shared,packet⟩ => do
      let input := packet.family.collection.input
      for quantifier in [Quantifier.existsReal,.forallReal] do
        unless (CompleteReplay.check input.context.codec
            (input.value ∘ GatherCells.values shared (AlgebraicCells.coefficients sources indices)) formula []
            packet.radical quantifier packet.rootGraph packet.cells).toOption == some expected do
          throw (IO.userError "empty automatic presentation changed a constant verdict")
  IO.println "empty automatic presentation preserves both strict constant verdicts")

run_meta do
  for name in #[``AlgebraicCells.presentation_success,``AlgebraicCells.presentations_success,``AlgebraicCells.original_base,
      ``AlgebraicCells.owner_eq,``AlgebraicCells.stored_heq,``AlgebraicCells.build_domains,``AlgebraicCells.build_sound,
      ``AlgebraicCells.entry_real,``AlgebraicCells.compatible,``AlgebraicCells.entry_nonzero,
      ``AlgebraicCells.buildWith_complete,``AlgebraicCells.build_complete,``AlgebraicCells.build_zero] do
    let .thmInfo declaration ← Lean.getConstInfo name | throwError "expected actual algebraic-input theorem"
    let _ ← Hex.RCF.checkProof name declaration.type declaration.value
    let axioms ← Lean.collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "unexpected original algebraic-input axiom: {name}"
  let seen ← Hex.RCF.ProofEvidence.projectDependencies #[``AlgebraicCells.build_complete,``AlgebraicCells.build_sound]
  for required in #[``Hex.RealClosure.NumberField.present?_success,``AlgebraicCells.build_domains,
      ``Hex.RealClosure.NumberField.Presentation.ofRoot?_isSome,``RealAlgebraicNumber.toRat?_eq_some,
      ``Hex.RealClosure.NumberField.Presentation.generator_value,``NumberField.model_read,
      ``Hex.RealClosure.Tower.Shared.Model.value_of_model,``GatherCells.build_complete,
      ``CellDiscover.run_complete,``CompleteReplay.check_covered] do
    unless seen.contains required do throwError "automatic algebraic input omitted owner law: {required}"
  Lean.logInfo "thirteen automatic algebraic-input proof bodies and actual owner dependencies checked"
end Hex.RCF.AlgebraicCellsConformance
