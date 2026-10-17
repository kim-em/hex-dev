/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FrameDataProbe
public import HexRealClosure.FrameFormat
import all KernelReplay.FrameData
import all KernelReplay.FrameEncode
import all HexRealClosure.TowerContext
import all HexRealClosure.FrameFormat

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FrameSource
open Hex.SignDet

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat

/-- The original serializer accepts the structurally computed first frame. -/
theorem encoded (descriptor : SignDet.Descriptor NativeAssemblyStaged.base.Value
    Tower.Signature NativeAssemblyStaged.base.sign NativeAssemblyStaged.base.signature) :
    Tower.Literal.ofJson (Tower.rootData NativeAssemblyStaged.base.codec descriptor) =
      some (FrameEncode.frameData NativeAssemblyStaged.base.codec descriptor) := by
  change some (Tower.rootData _ _) = some _
  rw [FrameEncode.frameData_eq]

/-- Changing only an accepted frame presentation preserves the actual context
returned by the original total extension operation. -/
theorem packed_native (descriptor : SignDet.Descriptor NativeAssemblyStaged.base.Value
    Tower.Signature NativeAssemblyStaged.base.sign NativeAssemblyStaged.base.signature) :
    Tower.Context.pack (.root (.base FiniteBaseProbe.base) descriptor
      (FrameEncode.frameData NativeAssemblyStaged.base.codec descriptor) (encoded descriptor)) =
      (NativeAssemblyStaged.base.adjoin descriptor).context := by
  let chain := Tower.Chain.base FiniteBaseProbe.base
  let extension := NativeAssemblyStaged.base.adjoin descriptor
  have same : FrameEncode.frameData NativeAssemblyStaged.base.codec descriptor = extension.frame :=
    (Option.some.inj (encoded descriptor)).symm.trans (Option.some.inj extension.encoded)
  have replace (left right : Tower.Literal)
      (hl : Tower.Literal.ofJson (Tower.rootData NativeAssemblyStaged.base.codec descriptor) = some left)
      (hr : Tower.Literal.ofJson (Tower.rootData NativeAssemblyStaged.base.codec descriptor) = some right)
      (h : left = right) :
      (Tower.Context.pack (.root chain descriptor left hl)) =
        (Tower.Context.pack (.root chain descriptor right hr)) := by
    cases h
    rfl
  exact (replace _ extension.frame (encoded descriptor) extension.encoded same).trans
    (Tower.Context.adjoin_native chain descriptor).1.symm

/-- The original validated constructor, retaining a reducible but exactly equal
first frame. Failure keeps the original base and is rejected by extraction. -/
@[expose] def context : Tower.Context FiniteBaseProbe.registry :=
  match SignDet.Descriptor.validate NativeAssemblyStaged.base.sign
      NativeAssemblyStaged.base.signature NativeAssemblyStaged.raw with
  | none => NativeAssemblyStaged.base
  | some descriptor => .pack (.root (.base FiniteBaseProbe.base) descriptor
      (FrameEncode.frameData NativeAssemblyStaged.base.codec descriptor) (encoded descriptor))

/-- The presentation denotes the exact original native source context. -/
theorem context_eq : context = NativeAssemblyStaged.context := by
  unfold context NativeAssemblyStaged.context
  cases h : SignDet.Descriptor.validate NativeAssemblyStaged.base.sign
      NativeAssemblyStaged.base.signature NativeAssemblyStaged.raw with
  | none => rfl
  | some descriptor => exact packed_native descriptor

end Hex.RealClosure.Algebraic.KernelReplay.FrameSource

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FrameSource.context_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FrameSource.context_eq
