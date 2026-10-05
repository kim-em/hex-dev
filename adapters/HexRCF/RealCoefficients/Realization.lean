/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Samples
public import HexRealClosureMathlib.SpecializeSample

public section

/-! Ordinary real witnesses for shared formulas from one-infinitesimal replay.
The fixed coefficient field has its supplied ordered real embedding. Internal
root data may use one infinitesimal; every source atom is lifted from the fixed
field, including domain guards. This does not reconstruct tower contexts or
authenticate source coefficients and original divisors. -/

namespace Hex.RCF.RealCoefficients.Realization
open Hex Hex.RealClosure Hex.RealFormula HexPolyMathlib.Interpret
attribute [local instance 2500] Field.toGrindField

variable {F : Type} [Field F] [DecidableEq F]
variable {Ctx : Type} [DecidableEq Ctx]

/-- Lift an actual fixed-field atom without introducing parameter dependence. -/
@[expose] def lift (p : DensePoly F) : DensePoly (RationalFn F) :=
  DensePoly.Interpret.map RationalFn.C RationalFn.C_eq_zero_iff p

/-- Constant lifting preserves evaluation at every ordinary parameter. -/
theorem lift_eval (embedding : F →+* ℝ) (p : DensePoly F) (t x : ℝ) :
    (interpret (fun a : ℝ => a) (fun _ => Iff.rfl)
      (Specialize.polynomial embedding (lift p) t)).eval x =
      (interpret embedding
        (fun _ => embedding.injective.eq_iff' (map_zero embedding)) p).eval x := by
  congr 1
  ext i
  simp [coeff_interpret, Specialize.polynomial_coeff, lift, DensePoly.Interpret.map_coeff,
    Specialize.evalMapped_C]

/-- Retain the exact source atom order, including repeated and domain atoms. -/
@[expose] def queries (values : Fin n → F) (formula : QF (n + 1)) :
    List (DensePoly (RationalFn F)) :=
  (RepresentationSpecialize.prepare values formula).map lift

/-- The complete specialized row is the source sign vector at one real point. -/
theorem signs (embedding : F →+* ℝ) (values : Fin n → F) (formula : QF (n + 1))
    (t x : ℝ) :
    SignDet.signsAt (fun a : ℝ => a) (fun _ => Iff.rfl)
      ((queries values formula).map (fun q => Specialize.polynomial embedding q t)) x =
      formula.polys.map (fun q =>
        (SignType.sign (q.eval (append (fun i => embedding (values i)) x)) : Int)) := by
  have same := RepresentationSpecialize.prepare_eval embedding
    (fun _ => embedding.injective.eq_iff' (map_zero embedding))
    embedding.map_one embedding.map_add embedding.map_mul (fun n => map_natCast embedding n)
    embedding.map_neg values formula x
  unfold SignDet.signsAt queries
  simp only [List.map_map, Function.comp_def, lift_eval]
  simpa only [List.map_map, Function.comp_def, RepresentationSpecialize.evaluate] using
    congrArg (List.map (fun a : ℝ => (SignType.sign a : Int))) same

/-- An accepted count-one replay and true complete row give an ordinary real
witness for the shared formula. The owner's finite realization theorem supplies
one parameter and root for all signs together; the infinitesimal is not itself
a real witness. No search or convergence premise is used. Frontend quotation
still needs authenticated fixed coefficients, original divisor proofs and the
original-goal reification equivalence. -/
theorem exists_real [LinearOrder F] [IsStrictOrderedRing F]
    (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (context : Ctx) (values : Fin n → F) (formula : QF (n + 1))
    (p : DensePoly (RationalFn F)) (a b : Endpoint (RationalFn F))
    (r : SignDet.Replay (RationalFn F) Ctx)
    (accepted : r.check (OrderedFn.Infinitesimal.sign OrderedFn.orderSign)
      context p a b (queries values formula) = true)
    (condition : List Int) (one : (r.table accepted).count condition = 1)
    (truth : Samples.Row.eval formula condition = some true) :
    ∃ x : ℝ, formula.toProp (append (fun i => embedding (values i)) x) := by
  obtain ⟨t, _, _, x, hx, _⟩ := Specialize.realizeBelow embedding ordered context p a b
    (queries values formula) r accepted condition one 1 (by norm_num)
  have row := hx.2
  rw [signs embedding values formula t x] at row
  exact ⟨x, (Samples.Row.eval_true formula condition _ row.symm).mp truth⟩

end Hex.RCF.RealCoefficients.Realization
