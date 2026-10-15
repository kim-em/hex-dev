/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.CellDiscover
import HexRCF.SelectedRoot.Data
namespace Hex.RCF.RealCoefficients.CellDiscoverLinear
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula
open Hex.RCF.RealCoefficients Hex.RCF.SelectedRootTests
abbrev parent := Data.base
def values : Fin 0 → parent.Value := Fin.elim0
def atom : RealFormula.Poly 1 := MvPoly.X 0 - 1
def formula : QF 1 := .and (.atom ⟨atom,.ge⟩) (.and (.atom ⟨atom,.le⟩) (.atom ⟨0,.eq⟩))
#eval (show IO Unit from match CellDiscover.run values [-1] formula with
  | .error cause => throw (IO.userError s!"discovery failed: {repr cause}")
  | .ok packet => do
    let input := packet.family.collection.input
    let converted := input.value ∘ values
    let guards := ([-1] : List parent.Value).map input.value
    let data ← match CellRead.read input.context.codec guards packet.roots converted formula packet.cells with
      | .error cause => throw (IO.userError s!"replay failed: {repr cause}")
      | .ok data => pure data
    unless (CellReplay.check converted formula guards packet.radical packet.roots data .existsReal).toOption == some true do
      throw (IO.userError "true existential changed")
    unless (CellReplay.check converted formula guards packet.radical packet.roots data .forallReal).toOption == some false do
      throw (IO.userError "false universal changed")
    unless packet.roots.roots.length == 1 do throw (IO.userError "root union not deduplicated")
    unless (CellDiscover.points packet.family).length == 2 do throw (IO.userError "sector discovery incomplete")
    match CellDiscover.run values [0] formula with
    | .error .divisor => pure ()
    | _ => throw (IO.userError "original zero guard accepted")
    IO.println "automatically discovered common-context sectors, transported the original guard, replayed all rows and checked both verdicts")
end Hex.RCF.RealCoefficients.CellDiscoverLinear
