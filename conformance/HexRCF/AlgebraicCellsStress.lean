/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.AlgebraicCells
import HexRCF.ProofEvidence
import HexRCF.Tactic
open Hex Hex.RealClosure Hex.RealFormula Hex.RCF.RealCoefficients
namespace Hex.RCF.AlgebraicCellsStress
private def registry : BaseContext.Registry := fun _ => none
private def selected (coefficients : List Int) (lower upper : Rat) : Option RealAlgebraicNumber := do
  let d ← Root.validate 7
    {context := 7,head := DensePoly.ofList coefficients,
      lower := .finite lower,upper := .finite upper,indices := [],signs := []}
  pure d.handle.canonical

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
  let formula : QF 3 := .and (.atom ⟨x^2 - MvPoly.X 0,.eq⟩)
    (.and (.atom ⟨x-1,.gt⟩) (.atom ⟨x - MvPoly.X 1,.lt⟩))
  match AlgebraicCells.build registry inputs indices original formula with
  | .error cause => throw (IO.userError s!"automatic algebraic production failed: {repr cause}")
  | .ok ⟨sources,shared,packet⟩ => do
    let input := packet.family.collection.input
    let values := input.value ∘ GatherCells.values shared (AlgebraicCells.coefficients sources indices)
    let guards := (GatherCells.guards shared (AlgebraicCells.guards sources original)).map input.value
    for (quantifier,expected) in [(Quantifier.existsReal,!negative),(.forallReal,false)] do
      unless (CompleteReplay.check input.context.codec values formula guards packet.radical
          quantifier packet.rootGraph packet.cells).toOption == some expected do
        throw (IO.userError "original selected generator changed after automatic presentation and replay")
    match AlgebraicCells.build registry inputs indices (original ++ [3]) formula with
    | .error .divisor => pure ()
    | _ => throw (IO.userError "automatic presentations lost a late original zero guard")
    IO.println s!"automatic original algebraic inputs, negative={negative}: both verdicts and zero preflight pass"

#eval trial false
#eval trial true

end Hex.RCF.AlgebraicCellsStress
