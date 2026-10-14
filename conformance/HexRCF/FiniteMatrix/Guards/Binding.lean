/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Schema
import HexRCF.FiniteMatrix.Guards.Meaning
import HexRCF.FiniteMatrix.Semantics
open Hex Hex.RealClosure Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open HexPolyMathlib.Interpret
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Binding
open Hex.RCF.RealCoefficients Hex.RCF.RealCoefficients.FiniteMatrixTests
open Semantics
noncomputable def valuation : Fin 2 → ℝ := fun i => read (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.values i)
private theorem polynomial (p : DensePoly (Element FiniteTower.first)) :
    interpret (fun y : ℝ => y) (fun _ => Iff.rfl) (Transport.polynomial read p) =
      interpret read reflect p := by
  ext i
  rw [coeff_interpret, Transport.polynomial_coeff _ zero, coeff_interpret]

theorem bind (entries : List (Packing FiniteTower.first)) (x : ℝ) :
    (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.queries entries).map (fun q =>
      (interpret (fun y : ℝ => y) (fun _ => Iff.rfl) (Transport.polynomial read q)).eval x) =
    Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.formula.polys.map (fun q => q.eval (RealFormula.append valuation x)) := by
  rw [Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.queries_eq]
  simp only [polynomial]
  exact RepresentationSpecialize.prepare_eval read reflect closed.read_one
    (fun a b => closed.read_add a b trivial trivial)
    (fun a b => closed.read_mul a b trivial trivial) closed.read_natCast negative
    Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.values Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.formula x

theorem valuation_eq : valuation = RealFormula.append
    (RealFormula.append Fin.elim0 (Real.sqrt 2)) (0 / (Real.sqrt 2 - 1)) := by
  funext i
  rcases i with ⟨_ | _ | i, hi⟩
  · change read FiniteTower.generator = Real.sqrt 2
    exact Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Meaning.generator
  · change read 0 = 0 / (Real.sqrt 2 - 1)
    rw [zero, zero_div]
  · omega
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Binding
