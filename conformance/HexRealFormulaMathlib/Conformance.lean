/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealFormulaMathlib

/-! Scoped-normalization regressions and proved real-binder examples. -/

namespace Hex.RealFormula.MathlibConformance

private def free : QF 1 := .atom ⟨MvPoly.X 0, .lt⟩
private def bound : QF 2 := .atom ⟨MvPoly.X 1, .ge⟩
private def nested : Scoped 1 := .and (.matrix free) (.quant .existsReal (.matrix bound))
private def negated : Scoped 1 := .not (.quant .existsReal (.matrix bound))

#guard nested.toPrenex == .quant .existsReal (.matrix (.and free.lift bound))
#guard negated.toPrenex == .quant .forallReal
  (.matrix (.atom ⟨MvPoly.X 1, .lt⟩))
#guard (Scoped.not (.not nested)).toPrenex == nested.toPrenex
#guard (nested.iff nested).toPrenex.toView.prefix ==
  [.forallReal, .existsReal, .forallReal, .existsReal]
#guard ((Scoped.matrix free).imp (.quant .forallReal (.matrix bound))).toPrenex ==
  .quant .forallReal (.matrix (.or (.atom ⟨MvPoly.X 0, .ge⟩) bound))

private def equal : QF 2 := .atom ⟨MvPoly.X 0 - MvPoly.X 1, .eq⟩

private theorem equal_correct (ρ : Fin 2 → ℝ) : equal.toProp ρ ↔ ρ 0 = ρ 1 := by
  change MvPoly.eval₂ (Int.castRingHom ℝ) ρ (MvPoly.X 0 - MvPoly.X 1 : Poly 2) = 0 ↔ _
  rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
  simp [sub_eq_zero]

-- Choosing the inner coordinate after the outer coordinate is essential.
example : (Prenex.quant .forallReal (.quant .existsReal (.matrix equal))).toProp Fin.elim0 := by
  intro x
  refine ⟨x, ?_⟩
  change equal.toProp _
  rw [equal_correct]
  rfl

example : ¬(Prenex.quant .existsReal (.quant .forallReal (.matrix equal))).toProp Fin.elim0 := by
  rintro ⟨x, hx⟩
  have h := (equal_correct _).mp (hx (x + 1))
  change x = x + 1 at h
  have hzero : (0 : ℝ) = 1 := add_left_cancel (show x + 0 = x + 1 by simpa using h)
  exact zero_ne_one hzero

-- The free coordinate remains arbitrary in the normalization theorem.
example (ρ : Fin 1 → ℝ) : nested.toPrenex.toProp ρ ↔ nested.toProp ρ :=
  nested.toPrenex_correct ρ

end Hex.RealFormula.MathlibConformance
