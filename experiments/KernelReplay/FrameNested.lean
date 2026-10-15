/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FrameSource
public import KernelReplay.NativeAssemblyNestedData
import all HexRealClosure.TowerContext
import all HexRealClosure.FrameFormat

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FrameNested
open Hex.SignDet

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat

/-- The original second selected extension: the positive root of Y² minus
its predecessor's actual selected generator. -/
@[expose] def step (parent : Tower.Context FiniteBaseProbe.registry)
    (generator : parent.Value) : Tower.Context FiniteBaseProbe.registry :=
  let raw : RawDescriptor parent.Value Tower.Signature :=
    ⟨parent.signature, DensePoly.ofCoeffs #[-generator, 0, 1], .negInf, .posInf, [1], [1]⟩
  match Descriptor.validate parent.sign parent.signature raw with
  | none => parent
  | some descriptor => (parent.adjoin descriptor).context

private theorem step_congr {left right : Tower.Context FiniteBaseProbe.registry}
    (same : left = right) (a : left.Value) (b : right.Value) (values : HEq a b) :
    step left a = step right b := by
  cases same
  cases values
  rfl

/-- Preserve the actual first descriptor behind one checked constant before
reducing the second producer. This avoids re-expanding the first validation at
all occurrences of its coefficient dictionaries and signature. -/
@[expose, noinline, nospecialize] def extend (first : Descriptor NativeAssemblyStaged.base.Value
    Tower.Signature NativeAssemblyStaged.base.sign NativeAssemblyStaged.base.signature) :
    Tower.Context FiniteBaseProbe.registry :=
  let parent : Tower.Context FiniteBaseProbe.registry :=
    .pack (.root (.base FiniteBaseProbe.base) first
      (FrameEncode.frameData NativeAssemblyStaged.base.codec first) (FrameSource.encoded first))
  let generator : parent.Value := Element.ofPoly
    (context := Context.adjoin first NativeAssemblyStaged.base.isClean)
    (DensePoly.ofCoeffs #[0, 1])
  step parent generator

/-- The actual two-level extension, with its first checked owner retained. -/
@[expose] def context : Tower.Context FiniteBaseProbe.registry :=
  match Descriptor.validate NativeAssemblyStaged.base.sign
      NativeAssemblyStaged.base.signature NativeAssemblyStaged.raw with
  | none => NativeAssemblyStaged.base
  | some first => extend first

/-- Stage the already checked first producer before extracting the second. -/
theorem context_eq_first : context = extend NativeAssemblyStaged.owner.root := by
  unfold context
  rw [NativeAssemblyStaged.validated]

/-- The two-level context is exactly the unmodified native source constructor,
including its actual second validation and selected generator. -/
theorem context_eq : context = NativeAssemblyNested.context := by
  unfold context NativeAssemblyNested.context
  cases h : Descriptor.validate NativeAssemblyStaged.base.sign
      NativeAssemblyStaged.base.signature NativeAssemblyStaged.raw with
  | none => rfl
  | some first =>
    unfold extend
    change step _ _ = step _ _
    exact step_congr (FrameSource.packed_native first) _ _
      (Tower.Context.adjoin_native (.base FiniteBaseProbe.base) first).2.2.symm

end Hex.RealClosure.Algebraic.KernelReplay.FrameNested

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FrameNested.context_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FrameNested.context_eq

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FrameNested.context_eq_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FrameNested.context_eq_first
