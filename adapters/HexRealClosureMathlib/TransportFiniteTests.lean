/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportSelected
public import HexRealRootsMathlib.RealClosed
public import HexRealClosureMathlib.TransportInventory

public section

namespace Hex.RealClosure.Transport.Finite.Tests

open Hex.SignDet HexRealRootsMathlib HexPolyMathlib.Interpret

/-- A reader that agrees at the reached scalars 0 and 1, but fails addition
at 1 + 1. No closed domain containing the unit can support this reader. -/
def changedTwo (x : Rat) : Rat := if x = 2 then 3 else x

theorem changedTwo_not_closed (S : Rat → Prop) : ¬ Closed changedTwo S := by
  intro closed
  have addition := closed.read_add 1 1 closed.one closed.one
  norm_num [changedTwo] at addition

private theorem changedTwo_product :
    Product changedTwo (1 : Hex.DensePoly Rat) 1 := by
  have coefficient : (1 : Hex.DensePoly Rat).coeff 0 = 1 := by
    rw [← HexPolyMathlib.coeff_toPolynomial, HexPolyMathlib.toPolynomial_one]
    simp
  constructor
  · intro i hi j hj
    have iz : i = 0 := by change i < 1 at hi; omega
    have jz : j = 0 := by change j < 1 at hj; omega
    subst i; subst j
    norm_num [coefficient, changedTwo]
  · intro i hi j hj
    have iz : i = 0 := by change i < 1 at hi; omega
    have jz : j = 0 := by change j < 1 at hj; omega
    subst i; subst j
    norm_num [productPrefix, Hex.DensePoly.coeff_C, changedTwo]

/-- Nontrivial binary-power and product-fold data is inhabited even when no
universal closed-domain interpretation exists for the same reader. -/
theorem changedTwo_moment : MomentData changedTwo [1] [2] := by
  have power : PowerData changedTwo (1 : Hex.DensePoly Rat) 2 := by
    simp only [PowerData, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceDiv, Nat.reduceMod]
    exact ⟨changedTwo_product, trivial, trivial⟩
  constructor
  · intro pair member
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at member
    subst pair
    exact power
  · change FoldData changedTwo [(1 : Hex.DensePoly Rat).natPow 2] 1
    rw [FoldData]
    constructor
    · rw [Hex.DensePoly.natPow_two, Hex.DensePoly.mul_one_right_poly]
      exact changedTwo_product
    · trivial

/-- Consume the actual finite theorem with that nonclosed reader. -/
theorem changedTwo_transport :
    polynomial changedTwo (moment [1] [2]) = moment ([1].map (polynomial changedTwo)) [2] := by
  exact moment_polynomial changedTwo (by norm_num [changedTwo])
    (by norm_num [changedTwo]) [1] [2] changedTwo_moment

variable {E C : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E] [NatCast E]
variable [DecidableEq C]

/-- One ordinary real point satisfies the original descriptor's interpreted
root condition and its entire recorded sign vector. The finite arithmetic
premises are explicit; this does not construct them from a tower inventory. -/
theorem real_point (read : E → ℝ) (zero : read 0 = 0) (unit : read 1 = 1)
    (sourceSign : E → Int) (context : C) (d : Descriptor E C sourceSign context)
    (descriptorData : DescriptorData read sourceSign (fun x : ℝ => (SignType.sign x : Int))
      d.raw d.evidence)
    (qs : List (Hex.DensePoly E)) (s : SelectedSigns d qs)
    (data : ReplayData read sourceSign (fun x : ℝ => (SignType.sign x : Int))
      d.raw.head d.raw.lower d.raw.upper (d.raw.queries ++ qs) s.evidence) :
    ∃! x : ℝ,
      x ∈ Tarski.rootsIn (interpret (fun y : ℝ => y) (fun _ => Iff.rfl) (polynomial read d.raw.head))
        ((endpoint read d.raw.lower).map (fun y : ℝ => y))
        ((endpoint read d.raw.upper).map (fun y : ℝ => y)) ∧
      signsAt (fun y : ℝ => y) (fun _ => Iff.rfl) (d.raw.queries.map (polynomial read)) x = d.raw.signs ∧
      signsAt (fun y : ℝ => y) (fun _ => Iff.rfl) (qs.map (polynomial read)) x = s.values.toList := by
  let mapped := checkedDescriptor read zero unit (fun c : C => c) sourceSign
    (fun x : ℝ => (SignType.sign x : Int)) context d descriptorData
  let point := mapped.root (fun y : ℝ => y) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have raw : mapped.raw = descriptor read (fun c : C => c) d.raw :=
    checkedDescriptor_raw read zero unit (fun c : C => c) sourceSign _ context d descriptorData
  have queries := descriptor_queries read zero (fun c : C => c) d.raw descriptorData.derivatives descriptorData.head
  have spec := mapped.root_spec (fun y : ℝ => y) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  change point ∈ _ ∧ _ at spec
  rw [raw, queries] at spec
  simp only [descriptor] at spec
  refine ⟨point, ⟨spec.1, spec.2, ?_⟩, ?_⟩
  · exact selected_signs read zero unit (fun c : C => c) sourceSign context d descriptorData qs s data
  · intro y conditions
    apply mapped.root_unique (fun z : ℝ => z) (fun _ => Iff.rfl) rfl
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) y
    · rw [raw]
      exact conditions.1
    · rw [raw, queries]
      exact conditions.2.1

/-- An actual total identity interpretation supplies the finite premises from
its retained descriptor/replay inventory; no arithmetic data is assumed here. -/
theorem identity_point (context : C)
    (d : Descriptor ℝ C (fun x : ℝ => (SignType.sign x : Int)) context)
    (qs : List (Hex.DensePoly ℝ)) (s : SelectedSigns d qs) :
    ∃! x : ℝ,
      x ∈ Tarski.rootsIn (interpret (fun y : ℝ => y) (fun _ => Iff.rfl) (polynomial (fun y : ℝ => y) d.raw.head))
        ((endpoint (fun y : ℝ => y) d.raw.lower).map (fun y : ℝ => y))
        ((endpoint (fun y : ℝ => y) d.raw.upper).map (fun y : ℝ => y)) ∧
      signsAt (fun y : ℝ => y) (fun _ => Iff.rfl)
        (d.raw.queries.map (polynomial (fun y : ℝ => y))) x = d.raw.signs ∧
      signsAt (fun y : ℝ => y) (fun _ => Iff.rfl)
        (qs.map (polynomial (fun y : ℝ => y))) x = s.values.toList := by
  let closed : Closed (fun x : ℝ => x) (fun _ => True) :=
    ⟨trivial, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial,
      trivial, fun _ => trivial, rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ _ _ => rfl, rfl, fun _ => rfl⟩
  have agreement (xs : List ℝ) : Inventory.Agreement (fun x : ℝ => x) (fun _ => True)
      (fun x : ℝ => (SignType.sign x : Int)) (fun x : ℝ => (SignType.sign x : Int)) xs :=
    fun _ _ => ⟨trivial, rfl, Iff.rfl⟩
  let descriptorData := Inventory.descriptor_data closed d.raw d.evidence (agreement _)
  let replayData := Inventory.replay_data closed d.raw.head d.raw.lower d.raw.upper
    (d.raw.queries ++ qs) s.evidence (agreement _)
  exact real_point (fun x : ℝ => x) rfl rfl _ context d
    (DescriptorData.of_closed _ _ closed _ _ d.raw d.evidence descriptorData) qs s
    (ReplayData.of_closed _ _ closed _ _ d.raw.head d.raw.lower d.raw.upper
      (d.raw.queries ++ qs) s.evidence replayData)

end Hex.RealClosure.Transport.Finite.Tests

/-- info: 'Hex.RealClosure.Transport.Finite.Tests.real_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.Tests.real_point

/-- info: 'Hex.RealClosure.Transport.Finite.Tests.identity_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.Tests.identity_point

/-- info: 'Hex.RealClosure.Transport.Finite.Tests.changedTwo_not_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.Tests.changedTwo_not_closed
/-- info: 'Hex.RealClosure.Transport.Finite.Tests.changedTwo_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.Tests.changedTwo_moment
/-- info: 'Hex.RealClosure.Transport.Finite.Tests.changedTwo_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.Tests.changedTwo_transport
