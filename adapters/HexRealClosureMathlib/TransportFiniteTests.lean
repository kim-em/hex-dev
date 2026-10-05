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
