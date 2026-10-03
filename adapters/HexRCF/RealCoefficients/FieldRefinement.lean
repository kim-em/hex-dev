/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FieldBuildBudget
public import HexRoots.IsolateAll
public section

namespace Hex.RCF.RealCoefficients.FieldBuild

private def refineLoop (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (table : LiteralSign.Table (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (checked : Field.checkSignTable p s hw hp table = true)
    (rep : RefinedIsolation p) : Nat →
    Except BuildError {result : LiteralSign.Table (PolyQuot p (SimpleRoot.ofSquare p s hw hp)) //
      Field.checkSignTable p s hw hp result = true}
  | 0 => .ok ⟨table, checked⟩
  | remaining + 1 =>
      if table.entries.all (fun entry =>
          (IntervalSign.sign? entry.key.coeffs table.interval.lower table.interval.upper).isSome) then .ok ⟨table, checked⟩
      else match rep.refineTo? (rep.1.square.prec + 8) with
      | none => .ok ⟨table, checked⟩
      | some refined =>
          let square := refined.val.1.square
          let lower := (square.re - square.radiusHi).toRat
          let upper := (square.re + square.radiusHi).toRat
          -- An unavailable contained/tighter presentation declines this optional
          -- optimization. The already checked exact query evidence remains.
          if table.lower ≤ lower && upper ≤ table.upper &&
              upper - lower < table.interval.upper - table.interval.lower then
            match table.refine lower upper PolyQuot.coeffs with
            | none => .error .invalidReplay
            | some result =>
                if valid : Field.checkSignTable p s hw hp result = true then
                  refineLoop p s hw hp result valid refined.val remaining
                else .error .invalidReplay
          else .ok ⟨table, checked⟩

/-- Propose tighter generator windows only for inconclusive Horner signs.
Each step uses the owner's root refinement. The frozen inner count and exact
containment are independently checked against the unchanged original interval.
Resource exhaustion or an absent window retains checked full-query evidence;
malformed proposed evidence is terminal. No replay search is introduced. -/
def refineSigns (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (table : LiteralSign.Table (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (steps : Nat) :
    Except BuildError {result : LiteralSign.Table (PolyQuot p (SimpleRoot.ofSquare p s hw hp)) //
      Field.checkSignTable p s hw hp result = true} :=
  if checked : Field.checkSignTable p s hw hp table = true then
    refineLoop p s hw hp table checked (Field.literalRep p s hw hp) steps
  else .error .invalidReplay

end Hex.RCF.RealCoefficients.FieldBuild
