/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerContext
public import KernelReplay.FrameEncode

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FrameEncode
open Hex.SignDet

variable {E : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable {sign : E → Int} {parent : Tower.Signature}

/-- Logical frame serialization uses only structural traversal. -/
@[expose] def frameData (value : ValueCodec E)
    (root : Descriptor E Tower.Signature sign parent) : Codec.Json :=
  letI : Hashable E := ⟨fun a => hash (value.encode a)⟩
  letI : Hashable Tower.Signature := ⟨fun _ => 0⟩
  let ctx := Tower.contextCodec parent
  .arr #[ctx.encode root.raw.context, Codec.poly value root.raw.head,
    Codec.endpoint value root.raw.lower, Codec.endpoint value root.raw.upper,
    Codec.Json.of root.raw.indices, Codec.Json.of root.raw.signs,
    Codec.graph value ctx (encodeLinear root.evidence)]

/-- Every descriptor field and graph entry agrees with the existing serializer. -/
@[csimp] theorem frameData_eq : @frameData = @Tower.rootData := by
  funext E _ _ _ _ _ _ _ _ _ value root
  unfold frameData Tower.rootData
  rw [encodeLinear_eq]

end Hex.RealClosure.Algebraic.KernelReplay.FrameEncode

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FrameEncode.frameData_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FrameEncode.frameData_eq
