/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Formula

public section

namespace Hex.RCF.RealCoefficients.FormulaTests

open Hex.RealFormula

/-- Two comparisons of the same constant exercise sign reuse and negation. -/
@[expose] def phi : Hex.RealFormula.QF 0 :=
  .and (.atom ⟨MvPoly.C 1, .gt⟩) (.not (.atom ⟨MvPoly.C 1, .eq⟩))

example : QF.evalSigns (fun _ => some .pos) phi = some true := rfl

/-- Boolean short circuits must not conceal a missing sign certificate. -/
example : QF.evalSigns (fun _ => none) (.or .tt phi) = none := rfl

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

/-- info: 'Hex.RCF.RealCoefficients.FormulaTests.phi_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phi_correct

end Hex.RCF.RealCoefficients.FormulaTests
