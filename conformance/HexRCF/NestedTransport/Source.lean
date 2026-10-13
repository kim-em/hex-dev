/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.NestedTransport.Model
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.RealCoefficients.NestedTransportTests.Source
open Data
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
def head : parent.Poly := DensePoly.ofList
  [@Neg.neg parent.Value
    (Algebraic.Element.cachedNeg reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts) alpha,
    @Zero.zero parent.Value (Tower.instZeroValue parent),
    @One.one parent.Value
      (Algebraic.Element.cachedOne reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)]
def lower := @One.one parent.Value
  (Algebraic.Element.cachedOne reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
def upper := @NatCast.natCast parent.Value
  (Algebraic.Element.cachedNatCast reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts) 2
meta section
open Lean Meta Elab Command
elab "#suffix_source_fields" : command => liftTermElabM do
  let goal ← Term.elabTerm (← `(Upper.root.raw.head = head ∧
    Upper.root.raw.lower = .finite lower ∧ Upper.root.raw.upper = .finite upper)) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let goal ← instantiateMVars goal
  let dictionary ← synthInstance (mkApp (mkConst ``Decidable) goal)
  let proof := mkAppN (mkConst ``of_decide_eq_true)
    #[goal, dictionary, ← mkEqRefl (mkConst ``Bool.true)]
  KernelCheck.addChecked `Hex.RCF.RealCoefficients.NestedTransportTests.Source.fields goal proof
    #[``Descriptor.validate, ``Descriptor.ofReplay?]
end
#suffix_source_fields
open HexPolyMathlib.Interpret in
theorem interpreted : interpret original.value original.zero_iff head =
    (Polynomial.X ^ 2 - Polynomial.C (Real.sqrt 2) : Polynomial ℝ) := by
  have negative : original.value (@Neg.neg parent.Value
      (Algebraic.Element.cachedNeg reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts) alpha) =
      -Real.sqrt 2 := by
    erw [Algebraic.Element.cachedNeg_eq, original.neg, alpha_value]
  have unit : original.value (@One.one parent.Value
      (Algebraic.Element.cachedOne reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)) = 1 := by
    erw [Algebraic.Element.cachedOne_eq, original.one]
  have zero : original.value (@Zero.zero parent.Value (Tower.instZeroValue parent)) = 0 :=
    (original.zero_iff _).mpr rfl
  ext i
  rcases i with _ | _ | _ | i
  all_goals simp [head, coeff_interpret, DensePoly.ofList, DensePoly.coeff_ofCoeffs,
    Polynomial.coeff_X_pow, Polynomial.coeff_C, negative, unit, zero]
open HexPolyMathlib.Interpret HexRealRootsMathlib in
theorem point : Hex.RCF.RealCoefficients.NestedTransportTests.Model.point ^ 2 = Real.sqrt 2 ∧
    1 < Hex.RCF.RealCoefficients.NestedTransportTests.Model.point ∧ Hex.RCF.RealCoefficients.NestedTransportTests.Model.point < 2 := by
  rw [Hex.RCF.RealCoefficients.NestedTransportTests.Model.point_eq]
  let x := Upper.root.root original.value original.zero_iff original.one original.add original.sub
    original.mul original.nat original.sign
  have member := (Upper.root.root_spec original.value original.zero_iff original.one original.add
    original.sub original.mul original.nat original.sign).1
  have valid := Upper.root.head_ne_zero original.value original.zero_iff
  have data := (Tarski.mem_rootsIn_iff _ valid _ _ x).mp member
  rw [fields.1, interpreted] at data
  have lo : original.value lower = 1 := by
    unfold lower
    erw [Algebraic.Element.cachedOne_eq, original.one]
  have hi : original.value upper = 2 := by
    unfold upper
    have same := congrArg (fun op : NatCast parent.Value => original.value (@NatCast.natCast parent.Value op 2))
      (Algebraic.Element.cachedNatCast_eq reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    exact same.trans (original.nat 2)
  refine ⟨?_, ?_⟩
  · simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] using data.1
  · rw [fields.2.1, fields.2.2] at data
    have bounds := data.2
    change original.value lower < x ∧ x < original.value upper at bounds
    simpa only [lo, hi] using bounds

theorem source : ∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 :=
  ⟨Hex.RCF.RealCoefficients.NestedTransportTests.Model.point, point⟩
#print axioms source
end Hex.RCF.RealCoefficients.NestedTransportTests.Source
