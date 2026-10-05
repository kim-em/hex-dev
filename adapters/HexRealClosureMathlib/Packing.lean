/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Packing
public import HexRealClosureMathlib.TransportSelected

public section

namespace Hex.RealClosure.Algebraic.Packing

open Hex.SignDet HexRealRootsMathlib HexPolyMathlib.Interpret

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Evaluate the original finite coefficient array with an arbitrary reader.
This does not assume a whole-field embedding or a closed interpretation domain. -/
noncomputable def eval (read : E → K) (x : K) (p : Hex.DensePoly E) : K :=
  (interpret (fun y : K => y) (fun _ => Iff.rfl) (Transport.polynomial read p)).eval x

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
private theorem sign_zero {x : K} (h : (SignType.sign x : Int) = 0) : x = 0 := by
  have sign : SignType.sign x = 0 := by
    cases chosen : SignType.sign x <;> simp [chosen] at h ⊢
  exact sign_eq_zero_iff.mp sign

omit [IsStrictOrderedRing K] [IsRealClosed K] in
/-- The same replay authenticates the packed value's retained native sign.
Only preservation of the predecessor's zero is needed for this clause. -/
theorem eval_sign (entry : Algebraic.Packing context) (read : E → K)
    (zero : read 0 = 0) (x : K)
    (observed : signsAt (fun y : K => y) (fun _ => Iff.rfl)
      ([entry.representative, entry.original - entry.representative].map
        (Transport.polynomial read)) x = [entry.sign, 0]) :
    (SignType.sign (eval read x entry.value.polynomial) : Int) = entry.value.sign := by
  have signs : (SignType.sign (eval read x entry.representative) : Int) = entry.sign ∧
      (SignType.sign (eval read x (entry.original - entry.representative)) : Int) = 0 := by
    simpa only [signsAt, List.map_cons, List.map_nil, List.cons.injEq,
      and_true, eval] using observed
  rw [entry.cached, entry.stored]
  by_cases h : entry.sign = 0
  · rw [ite_eq_left h, h]
    have empty : Transport.polynomial read (0 : Hex.DensePoly E) = 0 :=
      (Transport.polynomial_zero read zero 0 (by simp)).mpr rfl
    simp [eval, empty]
  · rw [ite_eq_right h]
    exact signs.1

omit [IsStrictOrderedRing K] [IsRealClosed K] in
/-- The joint representative/difference signs authenticate packing's original
polynomial, including zero outputs. Only the finite coefficient subtractions
used in this actual difference are required of the predecessor reader. -/
theorem eval_original (entry : Algebraic.Packing context) (read : E → K)
    (zero : read 0 = 0) (x : K)
    (difference : Transport.Difference read entry.original entry.representative)
    (observed : signsAt (fun y : K => y) (fun _ => Iff.rfl)
      ([entry.representative, entry.original - entry.representative].map
        (Transport.polynomial read)) x = [entry.sign, 0]) :
    eval read x entry.value.polynomial = eval read x entry.original := by
  have signs : (SignType.sign (eval read x entry.representative) : Int) = entry.sign ∧
      (SignType.sign (eval read x (entry.original - entry.representative)) : Int) = 0 := by
    simpa only [signsAt, List.map_cons, List.map_nil, List.cons.injEq,
      and_true, eval] using observed
  have equal : eval read x entry.original = eval read x entry.representative := by
    have vanished := sign_zero signs.2
    unfold eval at vanished ⊢
    rw [Transport.Ring.polynomial_sub read zero entry.original entry.representative
      difference.differences, interpret_sub (fun y : K => y) (fun _ => Iff.rfl)
        (fun _ _ => rfl), Polynomial.eval_sub] at vanished
    exact sub_eq_zero.mp vanished
  rw [entry.stored]
  by_cases h : entry.sign = 0
  · rw [ite_eq_left h]
    have vanished := sign_zero (signs.1.trans h)
    have empty : Transport.polynomial read (0 : Hex.DensePoly E) = 0 :=
      (Transport.polynomial_zero read zero 0 (by simp)).mpr rfl
    simp only [eval, empty, interpret_zero, Polynomial.eval_zero]
    exact (equal.trans vanished).symm
  · rw [ite_eq_right h]
    exact equal.symm

/-- One actual checked target root realizes the packing record's original
polynomial and retained native value together. Descriptor and replay transport
consume only their finite predecessor operations; no ambient model or global
closed-domain law is a premise. Recursive construction of those finite
predecessor data remains the exporter's responsibility. -/
theorem realize (entry : Algebraic.Packing context) (read : E → K)
    (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (data : Transport.Finite.ReplayData read coeffSign
      (fun x : K => (SignType.sign x : Int))
      context.root.raw.head context.root.raw.lower context.root.raw.upper
      (context.root.raw.queries ++ [entry.representative, entry.original - entry.representative])
      entry.signs.evidence)
    (difference : Transport.Difference read entry.original entry.representative) :
    ∃ x : K,
      x ∈ Tarski.rootsIn
        (interpret (fun y : K => y) (fun _ => Iff.rfl)
          (Transport.polynomial read context.root.raw.head))
        ((Transport.endpoint read context.root.raw.lower).map (fun y : K => y))
        ((Transport.endpoint read context.root.raw.upper).map (fun y : K => y)) ∧
      signsAt (fun y : K => y) (fun _ => Iff.rfl)
        (context.root.raw.queries.map (Transport.polynomial read)) x = context.root.raw.signs ∧
      eval read x entry.value.polynomial = eval read x entry.original := by
  let mapped := Transport.Finite.checkedDescriptor read zero unit (fun c : Ctx => c)
    coeffSign (fun x : K => (SignType.sign x : Int)) parent context.root descriptorData
  let point := mapped.root (fun y : K => y) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have raw : mapped.raw = Transport.descriptor read (fun c : Ctx => c) context.root.raw :=
    Transport.Finite.checkedDescriptor_raw read zero unit (fun c : Ctx => c)
      coeffSign _ parent context.root descriptorData
  have queries := Transport.Finite.descriptor_queries read zero (fun c : Ctx => c)
    context.root.raw descriptorData.derivatives descriptorData.head
  have spec := mapped.root_spec (fun y : K => y) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  change point ∈ _ ∧ _ at spec
  rw [raw, queries] at spec
  simp only [Transport.descriptor] at spec
  refine ⟨point, spec.1, spec.2, ?_⟩
  apply eval_original entry read zero point difference
  exact (Transport.Finite.selected_signs read zero unit (fun c : Ctx => c) coeffSign parent
    context.root descriptorData _ entry.signs data).trans entry.observed

/-- All retained packings in one level use one selected target root. Zero
packings retain their original equations in the same finite conjunction as
nonzero packings. Each lower-level transport premise follows the actual
descriptor and each record's complete replay. -/
theorem realize_many (entries : List (Algebraic.Packing context)) (read : E → K)
    (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (data : ∀ entry ∈ entries,
      Transport.Finite.ReplayData read coeffSign (fun x : K => (SignType.sign x : Int))
        context.root.raw.head context.root.raw.lower context.root.raw.upper
        (context.root.raw.queries ++ [entry.representative, entry.original - entry.representative])
        entry.signs.evidence ∧
      Transport.Difference read entry.original entry.representative) :
    ∃ x : K,
      x ∈ Tarski.rootsIn
        (interpret (fun y : K => y) (fun _ => Iff.rfl)
          (Transport.polynomial read context.root.raw.head))
        ((Transport.endpoint read context.root.raw.lower).map (fun y : K => y))
        ((Transport.endpoint read context.root.raw.upper).map (fun y : K => y)) ∧
      signsAt (fun y : K => y) (fun _ => Iff.rfl)
        (context.root.raw.queries.map (Transport.polynomial read)) x = context.root.raw.signs ∧
      ∀ entry ∈ entries, eval read x entry.value.polynomial = eval read x entry.original ∧
        (SignType.sign (eval read x entry.original) : Int) = entry.value.sign := by
  let mapped := Transport.Finite.checkedDescriptor read zero unit (fun c : Ctx => c)
    coeffSign (fun x : K => (SignType.sign x : Int)) parent context.root descriptorData
  let point := mapped.root (fun y : K => y) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have raw : mapped.raw = Transport.descriptor read (fun c : Ctx => c) context.root.raw :=
    Transport.Finite.checkedDescriptor_raw read zero unit (fun c : Ctx => c)
      coeffSign _ parent context.root descriptorData
  have queries := Transport.Finite.descriptor_queries read zero (fun c : Ctx => c)
    context.root.raw descriptorData.derivatives descriptorData.head
  have spec := mapped.root_spec (fun y : K => y) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  change point ∈ _ ∧ _ at spec
  rw [raw, queries] at spec
  simp only [Transport.descriptor] at spec
  refine ⟨point, spec.1, spec.2, ?_⟩
  intro entry member
  have observed := (Transport.Finite.selected_signs read zero unit (fun c : Ctx => c) coeffSign parent
    context.root descriptorData _ entry.signs (data entry member).1).trans entry.observed
  have equal := eval_original entry read zero point (data entry member).2 observed
  exact ⟨equal, equal ▸ eval_sign entry read zero point observed⟩

end Hex.RealClosure.Algebraic.Packing

/-- info: 'Hex.RealClosure.Algebraic.Packing.realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.realize

/-- info: 'Hex.RealClosure.Algebraic.Packing.realize_many' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.realize_many
