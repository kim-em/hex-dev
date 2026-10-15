/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.CellDiscover
import HexRCF.RealCoefficients.CompleteReplay
import HexRCF.CellReplay.Algebraic.Schema
namespace Hex.RCF.RealCoefficients.CellDiscoverAlgebraic
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula
open Hex.RCF.RealCoefficients Hex.RCF.SelectedRootTests
abbrev parent := CellReplayTests.Algebraic.Schema.parent
def values : Fin 1 → parent.Value := CellReplayTests.Algebraic.Schema.values
def originalGuards : List parent.Value := [values 0, values 0 - 1, -(values 0)]
def atom : RealFormula.Poly 2 := MvPoly.X 1 ^ 2 - MvPoly.X 0
def formula : QF 2 := .and (.atom ⟨atom,.ge⟩) (.and (.atom ⟨atom,.le⟩) (.atom ⟨0,.eq⟩))
#eval (show IO Unit from match CellDiscover.run values originalGuards formula with
  | .error cause => throw (IO.userError s!"discovery failed: {repr cause}")
  | .ok packet => do
    let input := packet.family.collection.input
    unless parent.signature.roots.length < input.context.signature.roots.length do
      throw (IO.userError "nonlinear discovery did not extend the coefficient context")
    let converted := input.value ∘ values
    let guards := originalGuards.map input.value
    for (quantifier,expected) in [(RealFormula.Quantifier.existsReal,true),(.forallReal,false)] do
      unless (CompleteReplay.check input.context.codec converted formula guards packet.radical
          quantifier packet.rootGraph packet.cells).toOption == some expected do
        throw (IO.userError "emitted complete root/cell packets changed the strict verdict")
    let data ← match CellRead.read input.context.codec guards packet.roots converted formula packet.cells with
      | .error cause => throw (IO.userError s!"replay failed: {repr cause}")
      | .ok data => pure data
    unless (CellReplay.check converted formula guards packet.radical packet.roots data .existsReal).toOption == some true do
      throw (IO.userError "true existential changed")
    unless (CellReplay.check converted formula guards packet.radical packet.roots data .forallReal).toOption == some false do
      throw (IO.userError "false universal changed")
    unless packet.roots.roots.length == 2 do throw (IO.userError "root union not deduplicated")
    unless packet.family.values.length+1 == 3 do throw (IO.userError "sector discovery incomplete")
    match CellDiscover.run values [0] formula with
    | .error .divisor => pure ()
    | _ => throw (IO.userError "original zero guard accepted")
    let old ← match CellBuild.prepare values originalGuards formula with
      | .error cause => throw (IO.userError s!"old-context control preparation failed: {repr cause}")
      | .ok old => pure old
    match CellRead.read parent.codec originalGuards old.2 values formula packet.cells with
    | .error .evidence => IO.println "new-context cells refused in the old context with exact evidence tag"
    | .error cause => throw (IO.userError s!"wrong stale-context diagnostic: {repr cause}")
    | .ok _ => throw (IO.userError "new-context packet accepted under the old context")
    IO.println "automatically discovered common-context sectors, transported the original guard, replayed all rows and checked both verdicts")
end Hex.RCF.RealCoefficients.CellDiscoverAlgebraic
