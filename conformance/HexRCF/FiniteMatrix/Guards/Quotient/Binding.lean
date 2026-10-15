/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Quotient.Source
open Hex Hex.RealClosure Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Hex.RCF.RealCoefficients Hex.RCF.RealCoefficients.FiniteMatrixTests
open HexPolyTheory.Interpret
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Binding
open Semantics
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
theorem argument_eq : Records.inverse.argument = Reader.argument :=
  Reader.read_argument Records.inverse.read_eq

theorem inverse : read Reader.entry.value = 1 / (Real.sqrt 2 - 1) := by
  have identity := Records.inverse.denote_inv rational zero_iff unit add sub mul nat sign
  change read Reader.entry.value = (read Records.inverse.argument)⁻¹ at identity
  rw [argument_eq] at identity
  have coefficient : read Reader.argument = Real.sqrt 2 - 1 := Guards.Data.first
  simpa only [coefficient, one_div] using identity

noncomputable def valuation : Fin 1 → ℝ := fun i => read (Source.values i)

theorem same_queries : Source.queries Records.entries =
    Guards.Schema.queries Packings.facts := by
  have checked : Source.queries Records.entries =
      Guards.Schema.queries Records.entries :=
    of_decide_eq_true Source.computed
  exact checked.trans ((Guards.Schema.queries_eq _).trans (Guards.Schema.queries_eq _).symm)

private theorem polynomial (p : DensePoly (Element FiniteTower.first)) :
    interpret (fun y : ℝ => y) (fun _ => Iff.rfl) (Transport.polynomial read p) =
      interpret read reflect p := by
  ext i
  rw [coeff_interpret, Transport.polynomial_coeff _ zero, coeff_interpret]

theorem bind (x : ℝ) :
    (Guards.Schema.queries Packings.facts).map (fun q =>
      (interpret (fun y : ℝ => y) (fun _ => Iff.rfl) (Transport.polynomial read q)).eval x) =
    Source.formula.polys.map (fun q => q.eval (RealFormula.append valuation x)) := by
  rw [← same_queries, Source.queries_eq]
  simp only [polynomial]
  exact RepresentationSpecialize.prepare_eval read reflect closed.read_one
    (fun a b => closed.read_add a b trivial trivial)
    (fun a b => closed.read_mul a b trivial trivial) closed.read_natCast negative
    Source.values Source.formula x

theorem valuation_eq : valuation = RealFormula.append Fin.elim0 (1 / (Real.sqrt 2 - 1)) := by
  funext i
  rcases i with ⟨_ | i, hi⟩
  · change read Reader.entry.value = _
    exact inverse
  · omega

end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Binding
