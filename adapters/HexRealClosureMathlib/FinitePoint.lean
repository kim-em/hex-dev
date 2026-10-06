/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.InverseReplay
public import HexRealClosureMathlib.InversePacking
public import HexRealClosureMathlib.ValueSigns
import all HexRealClosureMathlib.Packing

public section

namespace Hex.RealClosure.Algebraic
open Hex.SignDet HexRealRootsMathlib HexPolyMathlib.Interpret

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- The one selected point used for every finite evidence inventory at this
level. It depends on descriptor transport, not on separately chosen roots for
individual packing, inverse or input-sign records. -/
noncomputable def Context.finitePoint (context : Context E Ctx coeffSign parent)
    (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence) : K :=
  (Transport.Finite.checkedDescriptor read zero unit (fun c : Ctx => c)
    coeffSign (fun x : K => (SignType.sign x : Int)) parent context.root descriptorData).root
      (fun y : K => y) (fun _ => Iff.rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-- Every reached joint replay holds at this same named selected point. -/
theorem Context.finitePoint_signs (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (qs : List (DensePoly E)) (signs : SelectedSigns context.root qs)
    (data : Transport.Finite.ReplayData read coeffSign (fun x : K => (SignType.sign x : Int))
      context.root.raw.head context.root.raw.lower context.root.raw.upper
      (context.root.raw.queries ++ qs) signs.evidence) :
    signsAt (fun y : K => y) (fun _ => Iff.rfl) (qs.map (Transport.polynomial read))
      (context.finitePoint read zero unit descriptorData) = signs.values.toList :=
  Transport.Finite.selected_signs read zero unit (fun c : Ctx => c)
    coeffSign parent context.root descriptorData qs signs data

/-- The point lies in the prescribed interval and has the descriptor's full
Thom signs. All inventories can use this proposition without another choice. -/
theorem Context.finitePoint_spec (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence) :
    context.finitePoint read zero unit descriptorData ∈ Tarski.rootsIn
      (interpret (fun y : K => y) (fun _ => Iff.rfl)
        (Transport.polynomial read context.root.raw.head))
      ((Transport.endpoint read context.root.raw.lower).map (fun y : K => y))
      ((Transport.endpoint read context.root.raw.upper).map (fun y : K => y)) ∧
    signsAt (fun y : K => y) (fun _ => Iff.rfl)
      (context.root.raw.queries.map (Transport.polynomial read))
      (context.finitePoint read zero unit descriptorData) = context.root.raw.signs := by
  let mapped := Transport.Finite.checkedDescriptor read zero unit (fun c : Ctx => c)
    coeffSign (fun x : K => (SignType.sign x : Int)) parent context.root descriptorData
  have raw : mapped.raw = Transport.descriptor read (fun c : Ctx => c) context.root.raw :=
    Transport.Finite.checkedDescriptor_raw read zero unit (fun c : Ctx => c)
      coeffSign _ parent context.root descriptorData
  have queries := Transport.Finite.descriptor_queries read zero (fun c : Ctx => c)
    context.root.raw descriptorData.derivatives descriptorData.head
  have spec := mapped.root_spec (fun y : K => y) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have samePoint : mapped.root (fun y : K => y) (fun _ => Iff.rfl) rfl
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) =
      context.finitePoint read zero unit descriptorData := rfl
  rw [samePoint] at spec
  rw [raw, queries] at spec
  simpa only [Transport.descriptor] using spec

/-- Only the ordinary record's reached replay and coefficient differences. -/
structure Packing.Data (entry : Packing context) (read : E → K) : Prop where
  replay : Transport.Finite.ReplayData read coeffSign (fun x : K => (SignType.sign x : Int))
    context.root.raw.head context.root.raw.lower context.root.raw.upper
    (context.root.raw.queries ++ [entry.representative, entry.original - entry.representative])
    entry.signs.evidence
  difference : Transport.Difference read entry.original entry.representative

/-- Ordinary packing equations and signs hold at the common finite point. -/
theorem Packing.atPoint (entry : Packing context) (read : E → K)
    (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (data : Packing.Data entry read) :
    let x := context.finitePoint read zero unit descriptorData
    Packing.eval read x entry.value.polynomial = Packing.eval read x entry.original ∧
      (SignType.sign (Packing.eval read x entry.original) : Int) = entry.value.sign := by
  dsimp only
  have observed := (Context.finitePoint_signs read zero unit descriptorData _ entry.signs
    data.replay).trans entry.observed
  have equal := Packing.eval_original entry read zero _ data.difference observed
  refine ⟨equal, ?_⟩
  rw [← equal]
  exact Packing.eval_sign entry read zero _ observed

/-- An input's cached tag holds at the same point used for arithmetic evidence. -/
theorem ValueSign.atPoint (record : ValueSign context) (read : E → K)
    (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (data : ValueSign.Data record read) :
    (SignType.sign (Packing.eval read (context.finitePoint read zero unit descriptorData)
      record.value.polynomial) : Int) = record.value.sign :=
  record.eval_sign read _ ((Context.finitePoint_signs read zero unit descriptorData _
    record.signs data.replay).trans record.observed)

/-- A nonzero inverse equation holds at that same point; no independent
existential choice is made for its packing and inverse query slices. -/
theorem Packing.Inverse.atPoint {entry : Packing context} (record : Packing.Inverse entry)
    (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (data : Packing.Inverse.Data record read) :
    let x := context.finitePoint read zero unit descriptorData
    Packing.eval read x entry.value.polynomial = Packing.eval read x entry.original ∧
      Packing.eval read x entry.value.polynomial = (Packing.eval read x record.argument.polynomial)⁻¹ ∧
      (SignType.sign (Packing.eval read x entry.value.polynomial) : Int) = entry.value.sign ∧
      (SignType.sign (Packing.eval read x record.argument.polynomial) : Int) = record.argument.sign := by
  dsimp only
  have packing := (Context.finitePoint_signs read zero unit descriptorData _ entry.signs
    data.packing).trans entry.observed
  have inverse := (Context.finitePoint_signs read zero unit descriptorData _ record.signs
    data.inverse).trans record.observed
  have pair : (SignType.sign (Packing.eval read (context.finitePoint read zero unit descriptorData)
      record.argument.polynomial) : Int) = record.argument.sign ∧
      (SignType.sign (Packing.eval read (context.finitePoint read zero unit descriptorData)
        (record.argument.polynomial * entry.value.polynomial - 1)) : Int) = 0 := by
    simpa only [signsAt, List.map_cons, List.map_nil, List.cons.injEq, and_true, Packing.eval]
      using inverse
  exact ⟨Packing.eval_original entry read zero _ data.original packing,
    record.eval_inv read zero unit _ data.product data.difference inverse,
    Packing.eval_sign entry read zero _ packing, pair.1⟩

/-- The typed inverse inventory carries exactly the existing finite replay
and arithmetic obligations of its inner checked inverse operation. -/
abbrev InverseFact.Data (fact : InverseFact context) (read : E → K) : Prop :=
  Packing.Inverse.Data fact.inverse read

/-- Typed inverse records use the same point as the other inventories. -/
theorem InverseFact.atPoint (fact : InverseFact context) (read : E → K)
    (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (data : InverseFact.Data fact read) :
    let x := context.finitePoint read zero unit descriptorData
    Packing.eval read x fact.entry.value.polynomial = Packing.eval read x fact.entry.original ∧
      Packing.eval read x fact.entry.value.polynomial =
        (Packing.eval read x fact.inverse.argument.polynomial)⁻¹ ∧
      (SignType.sign (Packing.eval read x fact.entry.value.polynomial) : Int) = fact.entry.value.sign ∧
      (SignType.sign (Packing.eval read x fact.inverse.argument.polynomial) : Int) =
        fact.inverse.argument.sign :=
  fact.inverse.atPoint read zero unit descriptorData data

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Context.finitePoint_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.finitePoint_spec

/-- info: 'Hex.RealClosure.Algebraic.Packing.atPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.atPoint

/-- info: 'Hex.RealClosure.Algebraic.ValueSign.atPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.ValueSign.atPoint

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inverse.atPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inverse.atPoint

/-- info: 'Hex.RealClosure.Algebraic.InverseFact.atPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.InverseFact.atPoint
