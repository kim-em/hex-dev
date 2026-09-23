/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Formula
public meta import HexRCF.RealCoefficients.Formula
public meta import HexRealFormula.Syntax

public section

/-!
Oracle: none. Mode: always.

Covered operations: evaluation of shared quantifier-free formulas from supplied signs.
Covered properties: exact truth at real valuations and propagation of missing signs.
Covered edge cases: repeated atoms, every comparison and sign, constants, one
variable, false formulas, and missing signs in either Boolean connective.
-/

namespace Hex.RCF.RealCoefficients.FormulaTests

open Hex.RealFormula

/-- Two comparisons of the same constant exercise sign reuse and negation. -/
@[expose] def phi : Hex.RealFormula.QF 0 :=
  .and (.atom ⟨MvPoly.C 1, .gt⟩) (.not (.atom ⟨MvPoly.C 1, .eq⟩))

example : QF.evalSigns (fun _ => some .pos) phi = some true := rfl

#guard [Hex.RealFormula.Cmp.eq, .ne, .lt, .le, .gt, .ge].all fun cmp =>
  [(-1 : Int), 0, 1].all fun value =>
    QF.evalSigns (fun _ => some (Hex.RCF.Sign.ofInt value))
      (.atom ⟨MvPoly.C value, cmp⟩ : QF 0) == some (cmp.evalRat value)

/-- Boolean short circuits must not conceal a missing sign certificate. -/
example : QF.evalSigns (fun _ => none) (.or .tt phi) = none := rfl
example : QF.evalSigns (fun _ => none) (.and .ff phi) = none := rfl
example : QF.evalSigns (fun _ => none) (.atom ⟨MvPoly.C 1, .gt⟩ : QF 0) = none := rfl
example : QF.evalSigns (fun _ => some .pos) (.not phi) = some false := rfl

/-- The formula result follows from signs checked at the actual real point. -/
theorem phi_correct : phi.toProp (fun _ => 0) := by
  obtain ⟨value, hvalue, hsemantic⟩ := QF.evalSigns_spec
    (formula := phi) (signOf := fun _ => some .pos) (ρ := fun _ => 0) (by
      intro p hp
      have he : p = (MvPoly.C 1 : Hex.RealFormula.Poly 0) := by
        simpa only [phi, Hex.RealFormula.QF.polys,
          Hex.RealFormula.QF.polys.go, List.mem_cons, List.not_mem_nil,
          or_false, or_self] using hp
      subst p
      refine ⟨.pos, rfl, ?_⟩
      simp only [Sign.toInt, Hex.RealFormula.Poly.eval,
        ← HexMvPolyMathlib.eval₂_toMvPolynomial,
        HexMvPolyMathlib.toMvPolynomial_C,
        map_one]
      norm_num)
  apply hsemantic.mp
  exact Option.some.inj (hvalue.symm.trans (by rfl))

/-- The sign of a nonconstant polynomial is evaluated at the given valuation. -/
theorem variable_correct :
    (QF.atom ⟨MvPoly.X 0, .gt⟩ : QF 1).toProp (fun _ => (2 : ℝ)) := by
  apply (QF.evalSigns_eq_true_iff (signOf := fun _ => some .pos)
    (ρ := fun _ => (2 : ℝ)) (by
      intro p hp
      have he : p = (MvPoly.X 0 : Hex.RealFormula.Poly 1) := by
        simpa using hp
      subst p
      refine ⟨.pos, rfl, ?_⟩
      simp only [Hex.RCF.Sign.toInt, Hex.RealFormula.Poly.eval,
        ← HexMvPolyMathlib.eval₂_toMvPolynomial,
        HexMvPolyMathlib.toMvPolynomial_X, MvPolynomial.eval₂_X]
      norm_num)).mp rfl

/-- info: 'Hex.RCF.RealCoefficients.FormulaTests.variable_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms variable_correct

/-- info: 'Hex.RCF.RealCoefficients.FormulaTests.phi_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phi_correct

end Hex.RCF.RealCoefficients.FormulaTests
