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

private theorem checkRefinement (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (table result : LiteralSign.Table (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (checked : Field.checkSignTable p s hw hp table = true) (lower upper : Rat)
    (produced : table.refine lower upper PolyQuot.coeffs = some result) :
    Field.checkSignTable p s hw hp result = true := by
  have binding := table.refine_bindings lower upper PolyQuot.coeffs result produced
  have accepted := table.refine_checked lower upper PolyQuot.coeffs result produced
  simp only [Field.checkSignTable, Bool.and_eq_true] at checked ⊢
  rw [binding.1, binding.2.1, binding.2.2.1]
  exact ⟨checked.1, accepted⟩

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
            match produced : table.refine lower upper PolyQuot.coeffs with
            | none => .error .invalidReplay
            | some result =>
                let valid := checkRefinement p s hw hp table result checked lower upper produced
                refineLoop p s hw hp result valid refined.val remaining
          else .ok ⟨table, checked⟩

/-- Propose tighter generator windows only for inconclusive Horner signs.
Each step uses the owner's root refinement. The frozen inner count and exact
containment are independently checked against the unchanged original interval.
Resource exhaustion, an absent window or no reduction in full queries retains
the original checked evidence; malformed proposed evidence is terminal. No replay search is introduced. -/
def refineSigns (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (table : LiteralSign.Table (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (steps : Nat) :
    Except BuildError {result : LiteralSign.Table (PolyQuot p (SimpleRoot.ofSquare p s hw hp)) //
      Field.checkSignTable p s hw hp result = true} :=
  if checked : Field.checkSignTable p s hw hp table = true then
    match refineLoop p s hw hp table checked (Field.literalRep p s hw hp) steps with
    | .error error => .error error
    | .ok result =>
        if (result.val.entries.filter (·.evidence.isSome)).length <
            (table.entries.filter (·.evidence.isSome)).length then .ok result
        else .ok ⟨table, checked⟩
  else .error .invalidReplay

end Hex.RCF.RealCoefficients.FieldBuild
