/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.RealFormula

/-!
Oracle: none. Mode: always.

Covered operations: polynomial, comparison, formula and sentence translations;
half-open guards; partial reverse translation; existing RCF decision and proof API.
Covered properties: polynomial round trips, pointwise interpretation equivalence,
and transport of checked certificates to shared sentences.
Covered edge cases: zero, constants, missing coefficients, all six comparisons,
negative dyadic bounds, included upper/excluded lower endpoints, reversed bounds,
degree-three residues, and rejection of zero or multiple remaining quantifiers.
-/

namespace Hex.RCF.RealFormulaConformance

open Hex.RealFormula Hex.RCF.RealFormula

private def cubic : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), -1, 0, 1]
private def sparse : Poly 1 := MvPoly.X 0 ^ 7 - MvPoly.C 3 * MvPoly.X 0 + MvPoly.C 2

#guard toPoly (ofPoly cubic) == cubic
#guard toPoly (ofPoly (0 : ZPoly)) == 0
#guard toPoly (ofPoly (DensePoly.C (-17))) == DensePoly.C (-17)
#guard ofPoly (toPoly sparse) == sparse
#guard ofPoly (toPoly (0 : Poly 1)) == 0
#guard ofPoly (toPoly (MvPoly.X 0 ^ 9 - MvPoly.X 0 ^ 9 : Poly 1)) == 0
#guard [Hex.RCF.Cmp.eq, .ne, .lt, .le, .gt, .ge].all fun c =>
  Decidable.decide (toCmp (ofCmp c) = c)

private def φ : Formula := .imp (.atom ⟨cubic, .le⟩) (.not (.atom ⟨cubic, .gt⟩))
#guard Decidable.decide (toFormula (ofFormula φ) =
  .or (.not (.atom ⟨cubic, .le⟩)) (.not (.atom ⟨cubic, .gt⟩)))
#guard Decidable.decide (toFormula (ofFormula .ff) = .ff)
#guard Decidable.decide (toFormula (ofFormula (.or φ φ)) = .or (toFormula (ofFormula φ))
  (toFormula (ofFormula φ)))

private def lo : Dyadic := Dyadic.ofInt (-3) >>> (1 : Int)
private def hi : Dyadic := Dyadic.ofInt 1 >>> (1 : Int)
#guard !(guard lo hi).evalRat (fun _ => -3/2)
#guard (guard lo hi).evalRat (fun _ => 1/2)
#guard (guard lo hi).evalRat (fun _ => -1/2)
#guard !(guard hi lo).evalRat (fun _ => 0)
#guard !(guard hi hi).evalRat (fun _ => 1/2)

example (ρ : Fin 0 → ℝ) :
    (ofSentence (.forallIoc lo hi φ)).toProp ρ ↔
      (Hex.RCF.Sentence.forallIoc lo hi φ).toProp := ofSentence_correct _ _
example (ρ : Fin 0 → ℝ) :
    (ofSentence (.existsIoc lo hi φ)).toProp ρ ↔
      (Hex.RCF.Sentence.existsIoc lo hi φ).toProp := ofSentence_correct _ _

#guard (toSentence? (ofSentence (.existsReal (.atom ⟨cubic, .eq⟩)))).isSome
#guard toSentence? (.matrix .tt) == none
#guard toSentence? (.quant .existsReal (.quant .forallReal (.matrix .tt))) == none
#guard decide? (ofSentence (.forallReal .tt)) == some true
#guard decide? (ofSentence (.existsReal .ff)) == some false

private def unused : QF 3 := .atom ⟨MvPoly.X 2 ^ 3 - MvPoly.C 2, .eq⟩
private def symbolic : QF 2 := .atom ⟨MvPoly.X 0 * MvPoly.X 1 + MvPoly.C 1, .eq⟩
#guard (residue? .existsReal unused).isSome
#guard residue? .existsReal symbolic == none
#guard univariate? (QF.tt : QF 4) == some .tt
#guard univariate? (QF.atom ⟨MvPoly.X 1 - MvPoly.X 0, .eq⟩ : QF 2) == none

example (ρ : Fin 2 → ℝ) :
    (Hex.RCF.Sentence.existsReal (.atom ⟨DensePoly.ofCoeffs #[(-2 : Int), 0, 0, 1], .eq⟩)).toProp ↔
      (Prenex.quant .existsReal (.matrix unused)).toProp ρ :=
  residue_correct (by decide +kernel) ρ

private def inequality : QF 2 := .atom ⟨MvPoly.X 1 ^ 2 +
  MvPoly.C 2 * MvPoly.X 0 * MvPoly.X 1 - MvPoly.C 3, .le⟩
private def specialized : QF 2 := inequality.map (MvPoly.subst fun i =>
  if i == 0 then MvPoly.C 1 else MvPoly.X 1)
#guard residue? .existsReal inequality == none
#guard residue? .existsReal specialized ==
  some (.existsReal (.atom ⟨DensePoly.ofCoeffs #[(-3 : Int), 2, 1], .le⟩))

example (ρ : Fin 0 → ℝ) :
    (ofSentence (.forallReal .tt)).toProp ρ :=
  RealFormula.check_sound (t := .forallReal .tt) (by decide) .constants (by decide) ρ

end Hex.RCF.RealFormulaConformance
