/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportSelected
public import HexRealRootsMathlib.RealClosed

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
    ∃ x : ℝ,
      x ∈ Tarski.rootsIn (interpret (fun y : ℝ => y) (fun _ => Iff.rfl) (polynomial read d.raw.head))
        ((endpoint read d.raw.lower).map (fun y : ℝ => y))
        ((endpoint read d.raw.upper).map (fun y : ℝ => y)) ∧
      signsAt (fun y : ℝ => y) (fun _ => Iff.rfl) (qs.map (polynomial read)) x = s.values.toList := by
  let mapped := checkedDescriptor read zero unit (fun c : C => c) sourceSign
    (fun x : ℝ => (SignType.sign x : Int)) context d descriptorData
  let point := mapped.root (fun y : ℝ => y) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  refine ⟨point, ?_, ?_⟩
  · have root := (mapped.root_spec (fun y : ℝ => y) (fun _ => Iff.rfl) rfl
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)).1
    change point ∈ _ at root
    simp only [mapped, checkedDescriptor_raw, descriptor] at root
    exact root
  · exact selected_signs read zero unit (fun c : C => c) sourceSign context d descriptorData qs s data

end Hex.RealClosure.Transport.Finite.Tests

/-- info: 'Hex.RealClosure.Transport.Finite.Tests.real_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.Tests.real_point
