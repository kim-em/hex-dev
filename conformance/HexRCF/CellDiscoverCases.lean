/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.CellDiscover
import HexRCF.RealCoefficients.CompleteReplay
import HexRCF.CellReplay.Algebraic.Schema
namespace Hex.RCF.RealCoefficients.CellDiscoverCases
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula
open Hex.RCF.RealCoefficients Hex.RCF.SelectedRootTests
abbrev parent := CellReplayTests.Algebraic.Schema.parent
def positive : Fin 1 → parent.Value := CellReplayTests.Algebraic.Schema.values
def atom : RealFormula.Poly 2 := MvPoly.X 1 ^ 2 - MvPoly.X 0
def zero : RealFormula.Poly 2 := 0
def equation : QF 2 := .and (.atom ⟨atom,.eq⟩) (.atom ⟨zero,.eq⟩)
def disjunction : QF 2 := .and (.or (.atom ⟨atom,.lt⟩) (.atom ⟨atom,.ge⟩)) (.atom ⟨zero,.eq⟩)
def constant (comparison : RealFormula.Cmp) : QF 2 := .atom ⟨zero,comparison⟩

def xPoly : RealFormula.Poly 2 := MvPoly.X 1
def guard (lower upper : Int) : QF 2 :=
  .and (.atom ⟨xPoly - MvPoly.C lower,.gt⟩)
    (.atom ⟨MvPoly.C upper - xPoly,.ge⟩)
def upper : QF 2 := .atom ⟨xPoly - 2,.eq⟩
def lower : QF 2 := .atom ⟨xPoly - 1,.eq⟩

def test (values : Fin 1 → parent.Value) (formula : QF 2)
    (count : Nat) (existential universal : Bool) : IO Unit :=
  match CellDiscover.run values [positive 0] formula with
  | .error cause => throw (IO.userError s!"discovery failed: {repr cause}")
  | .ok packet => do
    let input := packet.family.collection.input
    let converted := input.value ∘ values
    let guards := [input.value (positive 0)]
    for (quantifier,expected) in [(RealFormula.Quantifier.existsReal,existential),(.forallReal,universal)] do
      unless (CompleteReplay.check input.context.codec converted formula guards packet.radical
          quantifier packet.rootGraph packet.cells).toOption == some expected do
        throw (IO.userError "emitted complete root/cell packets changed the strict verdict")
    let data ← match CellRead.read input.context.codec guards packet.roots converted formula packet.cells with
      | .error cause => throw (IO.userError s!"replay failed: {repr cause}")
      | .ok data => pure data
    unless packet.roots.roots.length == count do throw (IO.userError "wrong complete root count")
    unless (CellReplay.check converted formula guards packet.radical packet.roots data .existsReal).toOption == some existential do
      throw (IO.userError "wrong strict existential verdict")
    unless (CellReplay.check converted formula guards packet.radical packet.roots data .forallReal).toOption == some universal do
      throw (IO.userError "wrong strict universal verdict")
    match CellDiscover.run values [0] formula with
    | .error .divisor => pure ()
    | _ => throw (IO.userError "original zero guard accepted")

#eval (show IO Unit from do
  test positive equation 2 true false
  test (fun i => -(positive i)) equation 0 false false
  test positive disjunction 2 true true
  test positive (constant .eq) 0 true true
  test positive (constant .gt) 0 false false
  test positive (.and (guard 1 2) upper) 2 true false
  test positive (.and (guard 1 2) lower) 2 false false
  test positive (.and (guard 2 2) upper) 1 false false
  test positive (.or (.not (guard 2 2)) upper) 1 true true
  test positive (.and (guard 3 2) upper) 2 false false
  test positive (.or (.not (guard 3 2)) upper) 2 true true
  IO.println "automatic discovery: selected conjugates, Boolean tautology constant true/false and upper/lower/equal/reversed guard cases retain complete roots, strict folds and original guards")
end Hex.RCF.RealCoefficients.CellDiscoverCases
