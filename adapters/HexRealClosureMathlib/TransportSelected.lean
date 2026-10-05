/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportDescriptor
public import HexSignDetMathlib.SelectedRoot

public section

namespace Hex.RealClosure.Transport

open Hex.SignDet

variable {E : Type u} {K : Type v} {C : Type w} {D : Type z}
variable [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E] [NatCast E]
variable [CommRing K] [DecidableEq K] [DecidableEq C] [DecidableEq D]

namespace Finite

/-- The complete selected-sign check transports the joint derivative and
additional-query replay, preserving the exact singleton row after filtering. -/
theorem selected_check (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (contextMap : C → D) (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (raw : RawDescriptor E C) (qs : List (Hex.DensePoly E)) (values : Vector Int qs.length)
    (evidence : Replay E C) (derivatives : DerivativeData read raw.head raw.head.natDegree)
    (head : Leading read raw.head)
    (data : ReplayData read sourceSign targetSign raw.head raw.lower raw.upper
      (raw.queries ++ qs) evidence)
    (accepted : raw.checkSigns sourceSign context qs values evidence = true) :
    (descriptor read contextMap raw).checkSigns targetSign (contextMap context)
      (qs.map (polynomial read))
      ⟨values.toArray, by simpa only [List.length_map] using values.size_toArray⟩
      (replay read contextMap evidence) = true := by
  simp only [RawDescriptor.checkSigns, Bool.and_eq_true, decide_eq_true_eq] at accepted ⊢
  refine ⟨⟨⟨(descriptor_wellFormed read zero contextMap raw head).trans accepted.1.1.1,
    congrArg contextMap accepted.1.1.2⟩, ?_⟩, ?_⟩
  · rw [descriptor_queries read zero contextMap raw derivatives head, ← List.map_append]
    exact replay_check read zero unit contextMap sourceSign targetSign context
      raw.head raw.lower raw.upper (raw.queries ++ qs) evidence data accepted.1.2
  · rw [descriptor_queries read zero contextMap raw derivatives head, List.length_map, replay_node]
    exact accepted.2

/-- Transport checked selected-sign evidence to the actual validated target
descriptor, retaining the original sign vector and complete joint replay. -/
@[expose] def selected (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (contextMap : C → D) (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (d : Descriptor E C sourceSign context)
    (descriptorData : DescriptorData read sourceSign targetSign d.raw d.evidence)
    (qs : List (Hex.DensePoly E)) (s : SelectedSigns d qs)
    (data : ReplayData read sourceSign targetSign d.raw.head d.raw.lower d.raw.upper
      (d.raw.queries ++ qs) s.evidence) :
    SelectedSigns (checkedDescriptor read zero unit contextMap sourceSign targetSign context d descriptorData)
      (qs.map (polynomial read)) :=
  { values := ⟨s.values.toArray, by simpa only [List.length_map] using s.values.size_toArray⟩
    evidence := replay read contextMap s.evidence
    accepted := by
      rw [Descriptor.checkSigns, checkedDescriptor_raw]
      exact selected_check read zero unit contextMap sourceSign targetSign context d.raw qs s.values
        s.evidence descriptorData.derivatives descriptorData.head data s.accepted }

/-- The selected-sign vector is retained literally after its length transport. -/
theorem selected_values (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (contextMap : C → D) (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (d : Descriptor E C sourceSign context)
    (descriptorData : DescriptorData read sourceSign targetSign d.raw d.evidence)
    (qs : List (Hex.DensePoly E)) (s : SelectedSigns d qs)
    (data : ReplayData read sourceSign targetSign d.raw.head d.raw.lower d.raw.upper
      (d.raw.queries ++ qs) s.evidence) :
    (selected read zero unit contextMap sourceSign targetSign context d descriptorData qs s data).values.toList =
      s.values.toList := rfl

/-- The selected-sign evidence is the full literal mapped joint replay. -/
theorem selected_evidence (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (contextMap : C → D) (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (d : Descriptor E C sourceSign context)
    (descriptorData : DescriptorData read sourceSign targetSign d.raw d.evidence)
    (qs : List (Hex.DensePoly E)) (s : SelectedSigns d qs)
    (data : ReplayData read sourceSign targetSign d.raw.head d.raw.lower d.raw.upper
      (d.raw.queries ++ qs) s.evidence) :
    (selected read zero unit contextMap sourceSign targetSign context d descriptorData qs s data).evidence =
      replay read contextMap s.evidence := rfl

end Finite

/-- The complete selected-sign check transports the joint derivative and
additional-query replay, preserving the exact singleton row after filtering. -/
theorem selected_check (read : E → K) (S : E → Prop) (closed : Closed read S)
    (contextMap : C → D) (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (raw : RawDescriptor E C) (qs : List (Hex.DensePoly E)) (values : Vector Int qs.length)
    (evidence : Replay E C) (members : ∀ i < raw.head.size, S (raw.head.coeff i))
    (head : Leading read raw.head)
    (data : ReplayData read S sourceSign targetSign raw.head raw.lower raw.upper
      (raw.queries ++ qs) evidence)
    (accepted : raw.checkSigns sourceSign context qs values evidence = true) :
    (descriptor read contextMap raw).checkSigns targetSign (contextMap context)
      (qs.map (polynomial read))
      ⟨values.toArray, by simpa only [List.length_map] using values.size_toArray⟩
      (replay read contextMap evidence) = true := by
  simp only [RawDescriptor.checkSigns, Bool.and_eq_true, decide_eq_true_eq] at accepted ⊢
  refine ⟨⟨⟨(descriptor_wellFormed read closed.read_zero contextMap raw head).trans accepted.1.1.1,
    congrArg contextMap accepted.1.1.2⟩, ?_⟩, ?_⟩
  · rw [descriptor_queries read S closed contextMap raw members head, ← List.map_append]
    exact replay_check read S closed contextMap sourceSign targetSign context
      raw.head raw.lower raw.upper (raw.queries ++ qs) evidence data accepted.1.2
  · rw [descriptor_queries read S closed contextMap raw members head, List.length_map, replay_node]
    exact accepted.2

/-- Transport checked selected-sign evidence to the actual validated target
descriptor, retaining the original sign vector and complete joint replay. -/
@[expose] def selected (read : E → K) (S : E → Prop) (closed : Closed read S)
    (contextMap : C → D) (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (d : Descriptor E C sourceSign context)
    (descriptorData : DescriptorData read S sourceSign targetSign d.raw d.evidence)
    (qs : List (Hex.DensePoly E)) (s : SelectedSigns d qs)
    (data : ReplayData read S sourceSign targetSign d.raw.head d.raw.lower d.raw.upper
      (d.raw.queries ++ qs) s.evidence) :
    SelectedSigns (checkedDescriptor read S closed contextMap sourceSign targetSign context d descriptorData)
      (qs.map (polynomial read)) :=
  { values := ⟨s.values.toArray, by simpa only [List.length_map] using s.values.size_toArray⟩
    evidence := replay read contextMap s.evidence
    accepted := by
      rw [Descriptor.checkSigns, checkedDescriptor_raw]
      exact selected_check read S closed contextMap sourceSign targetSign context d.raw qs s.values
        s.evidence descriptorData.members descriptorData.head data s.accepted }

/-- The selected-sign vector is retained literally after its length transport. -/
theorem selected_values (read : E → K) (S : E → Prop) (closed : Closed read S)
    (contextMap : C → D) (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (d : Descriptor E C sourceSign context)
    (descriptorData : DescriptorData read S sourceSign targetSign d.raw d.evidence)
    (qs : List (Hex.DensePoly E)) (s : SelectedSigns d qs)
    (data : ReplayData read S sourceSign targetSign d.raw.head d.raw.lower d.raw.upper
      (d.raw.queries ++ qs) s.evidence) :
    (selected read S closed contextMap sourceSign targetSign context d descriptorData qs s data).values.toList =
      s.values.toList := rfl

/-- The selected-sign evidence is the full literal mapped joint replay. -/
theorem selected_evidence (read : E → K) (S : E → Prop) (closed : Closed read S)
    (contextMap : C → D) (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (d : Descriptor E C sourceSign context)
    (descriptorData : DescriptorData read S sourceSign targetSign d.raw d.evidence)
    (qs : List (Hex.DensePoly E)) (s : SelectedSigns d qs)
    (data : ReplayData read S sourceSign targetSign d.raw.head d.raw.lower d.raw.upper
      (d.raw.queries ++ qs) s.evidence) :
    (selected read S closed contextMap sourceSign targetSign context d descriptorData qs s data).evidence =
      replay read contextMap s.evidence := rfl

end Hex.RealClosure.Transport

namespace Hex.RealClosure.Transport

open Hex.SignDet

variable {E : Type u} {K : Type v} {C : Type w} {D : Type z}
variable [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E] [NatCast E]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable [DecidableEq C] [DecidableEq D]

namespace Finite

/-- Every original selected sign holds at the root of the actual checked
target descriptor, whose derivative queries come from its interpreted head. -/
theorem selected_signs (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (contextMap : C → D) (sourceSign : E → Int) (context : C)
    (d : Descriptor E C sourceSign context)
    (descriptorData : DescriptorData read sourceSign (fun x : K => (SignType.sign x : Int))
      d.raw d.evidence)
    (qs : List (Hex.DensePoly E)) (s : SelectedSigns d qs)
    (data : ReplayData read sourceSign (fun x : K => (SignType.sign x : Int))
      d.raw.head d.raw.lower d.raw.upper (d.raw.queries ++ qs) s.evidence) :
    signsAt (fun x : K => x) (fun _ => Iff.rfl) (qs.map (polynomial read))
      ((checkedDescriptor read zero unit contextMap sourceSign
        (fun x : K => (SignType.sign x : Int)) context d descriptorData).root
        (fun x : K => x) (fun _ => Iff.rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)) = s.values.toList := by
  have signs := (selected read zero unit contextMap sourceSign
    (fun x : K => (SignType.sign x : Int)) context d descriptorData qs s data).values_at_root
      (fun x : K => x) (fun _ => Iff.rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  exact signs.symm.trans (selected_values read zero unit contextMap sourceSign
    (fun x : K => (SignType.sign x : Int)) context d descriptorData qs s data)

end Finite

/-- Every original selected sign holds at the root of the actual checked
target descriptor, whose derivative queries come from its interpreted head. -/
theorem selected_signs (read : E → K) (S : E → Prop) (closed : Closed read S)
    (contextMap : C → D) (sourceSign : E → Int) (context : C)
    (d : Descriptor E C sourceSign context)
    (descriptorData : DescriptorData read S sourceSign (fun x : K => (SignType.sign x : Int))
      d.raw d.evidence)
    (qs : List (Hex.DensePoly E)) (s : SelectedSigns d qs)
    (data : ReplayData read S sourceSign (fun x : K => (SignType.sign x : Int))
      d.raw.head d.raw.lower d.raw.upper (d.raw.queries ++ qs) s.evidence) :
    signsAt (fun x : K => x) (fun _ => Iff.rfl) (qs.map (polynomial read))
      ((checkedDescriptor read S closed contextMap sourceSign
        (fun x : K => (SignType.sign x : Int)) context d descriptorData).root
        (fun x : K => x) (fun _ => Iff.rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)) = s.values.toList := by
  have signs := (selected read S closed contextMap sourceSign
    (fun x : K => (SignType.sign x : Int)) context d descriptorData qs s data).values_at_root
      (fun x : K => x) (fun _ => Iff.rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  exact signs.symm.trans (selected_values read S closed contextMap sourceSign
    (fun x : K => (SignType.sign x : Int)) context d descriptorData qs s data)

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.selected_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.selected_check

/-- info: 'Hex.RealClosure.Transport.selected_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.selected_values

/-- info: 'Hex.RealClosure.Transport.selected_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.selected_evidence

/-- info: 'Hex.RealClosure.Transport.selected_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.selected_signs

/-- info: 'Hex.RealClosure.Transport.Finite.selected_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.selected_check

/-- info: 'Hex.RealClosure.Transport.Finite.selected_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.selected_values

/-- info: 'Hex.RealClosure.Transport.Finite.selected_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.selected_evidence

/-- info: 'Hex.RealClosure.Transport.Finite.selected_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.selected_signs
