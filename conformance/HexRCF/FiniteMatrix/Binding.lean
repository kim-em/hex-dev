/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.FiniteMatrix.Schema
public import HexRCF.FiniteMatrix.Semantics
public section
open Hex Hex.RealClosure Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open HexPolyMathlib.Interpret
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Binding
open Hex.RCF.RealCoefficients Semantics
noncomputable def valuation : Fin 1 → ℝ := fun i => read (Schema.values i)
private theorem polynomial (p : DensePoly (Element FiniteTower.first)) :
    interpret (fun y : ℝ => y) (fun _ => Iff.rfl) (Transport.polynomial read p) =
      interpret read reflect p := by
  ext i
  rw [coeff_interpret, Transport.polynomial_coeff _ zero, coeff_interpret]

theorem bind (entries : List (Packing FiniteTower.first)) (x : ℝ) :
    (Schema.queries entries).map (fun q =>
      (interpret (fun y : ℝ => y) (fun _ => Iff.rfl) (Transport.polynomial read q)).eval x) =
    Schema.formula.polys.map (fun q => q.eval (RealFormula.append valuation x)) := by
  rw [Schema.queries_eq]
  simp only [polynomial]
  exact RepresentationSpecialize.prepare_eval read reflect closed.read_one
    (fun a b => closed.read_add a b trivial trivial)
    (fun a b => closed.read_mul a b trivial trivial) closed.read_natCast negative
    Schema.values Schema.formula x

theorem valuation_eq : valuation = RealFormula.append Fin.elim0 (Real.sqrt 2) := by
  funext i
  have index : i = 0 := Fin.eq_zero i
  subst i
  change read FiniteTower.generator = Real.sqrt 2
  rw [read_eq]
  exact (FiniteJoint.read_generator FiniteJoint.alpha).trans Semantics.alpha_sqrt
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Binding
