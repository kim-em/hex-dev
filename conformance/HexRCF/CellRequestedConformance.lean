/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.CellDecision
import HexRCF.CellReplay.Algebraic.Schema
import HexRCF.ProofEvidence
import HexRCF.Tactic
namespace Hex.RCF.RealCoefficients.CellRequestedConformance
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula
open Hex.RCF.RealCoefficients
abbrev parent := CellReplayTests.Algebraic.Schema.parent
def values : Fin 1 → parent.Value := CellReplayTests.Algebraic.Schema.values
def atom : RealFormula.Poly 2 := MvPoly.X 1 ^ 2 - MvPoly.X 0
def equation : QF 2 := .atom ⟨atom,.eq⟩
def constant : QF 2 := .atom ⟨0,.eq⟩

def test (formula : QF 2) (rootCount : Nat) (existential universal : Bool) : IO Unit := do
  let packet ← match CellDiscover.run values [values 0] formula with
    | .error error => throw (IO.userError s!"discovery failed: {repr error}")
    | .ok packet => pure packet
  let input := packet.family.collection.input
  let converted := input.value ∘ values
  let guards := [input.value (values 0)]
  unless packet.roots.roots.length == rootCount do throw (IO.userError "wrong root count")
  let data ← match CellRead.read input.context.codec guards packet.roots converted formula packet.cells with
    | .error error => throw (IO.userError s!"cell replay failed: {repr error}")
    | .ok data => pure data
  unless (CellReplay.check converted formula guards packet.radical packet.roots data .existsReal).toOption == some existential do
    throw (IO.userError "wrong existential verdict")
  unless (CellReplay.check converted formula guards packet.radical packet.roots data .forallReal).toOption == some universal do
    throw (IO.userError "wrong universal verdict")

#eval (show IO Unit from do
  test equation 2 true false
  test constant 0 true true
  test (.atom ⟨0,.gt⟩) 0 false false
  test (.and equation equation) 2 true false
  let x : RealFormula.Poly 2 := MvPoly.X 1
  let guards : QF 2 := .and (.atom ⟨x-1,.gt⟩) (.atom ⟨2-x,.ge⟩)
  test (.and guards (.atom ⟨x-1,.eq⟩)) 2 false false
  test (.and guards (.atom ⟨x-2,.eq⟩)) 2 true false
  IO.println "indexed proved boundary requests produce all algebraic sectors and the empty-root whole line; repeated/common roots and half-open endpoint matrices retain strict true/false verdicts")

end Hex.RCF.RealCoefficients.CellRequestedConformance
