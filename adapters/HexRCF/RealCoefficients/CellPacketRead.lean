/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellPackets
public section
namespace Hex.RCF.RealCoefficients.CellPacketRead
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E]
/-- Parse the common sector layout with checked row/descriptor readers.
The linear test carries equality to its canonical polynomial identity; supplied
operations can validate it without changing any root or cut index. -/
@[expose] def readUsing (value : ValueCodec E) (_context : ValueCodec Ctx) (sign : E → Int) (binding : Ctx)
    (guards : List E) (roots : List (Descriptor E Ctx sign binding))
    (cut : Fin (roots.length+1)) (queries : List (DensePoly E)) (packet : Codec.Json)
    (rows : (root : Descriptor E Ctx sign binding) → (queries : List (DensePoly E)) →
      Codec.Json → Except Replay.Error (SelectedSigns root queries))
    (boundary : (root : Descriptor E Ctx sign binding) → (point : E) →
      Codec.Json → Except Replay.Error (SelectedSigns root [Isolation.pointQuery point]))
    (descriptor : Codec.Json → Codec.Json → Except String (Descriptor E Ctx sign binding))
    (linear : (root : Descriptor E Ctx sign binding) → (point : E) →
      {test : Bool // test = (root.raw.head - Isolation.pointQuery point).isZero}) :
    Except Replay.Error (CellPackets.Sector sign binding roots cut queries) := do
  unless guards.all (fun d => Decidable.decide (d ≠ 0)) do throw .divisor
  let fields ← match Codec.tuple 6 packet with
    | .error _ => .error .evidence
    | .ok fields => .ok fields
  let point ← match value.decode fields[0] with
    | .error _ => .error .evidence
    | .ok point => .ok point
  let left : { f : (h : 0 < cut.val) → SelectedSigns
      (roots.get ⟨cut.val-1, by have := cut.isLt; omega⟩) [Isolation.pointQuery point] //
        ∀ h, (f h).value = -1 } ←
    if positive : 0 < cut.val then do
      let signs ← boundary (roots.get ⟨cut.val-1, by have := cut.isLt; omega⟩) point fields[1]
      if observed : signs.value = -1 then pure ⟨fun _ => signs, fun _ => observed⟩
      else throw .binding
    else
      if fields[1] = Codec.Json.Value.null then
        pure ⟨fun h => False.elim (positive h), fun h => False.elim (positive h)⟩
      else throw .binding
  let right : { f : (h : cut.val < roots.length) → SelectedSigns
      (roots.get ⟨cut.val, h⟩) [Isolation.pointQuery point] // ∀ h, (f h).value = 1 } ←
    if bound : cut.val < roots.length then do
      let signs ← boundary (roots.get ⟨cut.val, bound⟩) point fields[2]
      if observed : signs.value = 1 then pure ⟨fun _ => signs, fun _ => observed⟩
      else throw .binding
    else
      if fields[2] = Codec.Json.Value.null then
        pure ⟨fun h => False.elim (bound h), fun h => False.elim (bound h)⟩
      else throw .binding
  let root ← match descriptor fields[3] fields[4] with
    | .error _ => .error .evidence
    | .ok root => .ok root
  if same : (linear root point).val = true then
    let signs ← rows root queries fields[5]
    return ⟨⟨point, left.val, left.property, right.val, right.property⟩, ⟨root, (linear root point).property.symm.trans same, signs⟩⟩
  else throw .binding

/-- Original guard preflight and the canonical checked readers share the
same supplied-sector layout as operation-parametric replay. -/
@[expose] def read (value : ValueCodec E) (context : ValueCodec Ctx) (sign : E → Int) (binding : Ctx)
    (guards : List E) (roots : List (Descriptor E Ctx sign binding))
    (cut : Fin (roots.length+1)) (queries : List (DensePoly E)) (packet : Codec.Json) :
    Except Replay.Error (CellPackets.Sector sign binding roots cut queries) :=
  readUsing value context sign binding guards roots cut queries packet
    (RowOperations.read value context sign binding)
    (fun root point => RowOperations.read value context sign binding root [Isolation.pointQuery point])
    (Algebraic.RootReplay.readDescriptor value context sign binding)
    (fun root point => ⟨(root.raw.head - Isolation.pointQuery point).isZero, rfl⟩)
end Hex.RCF.RealCoefficients.CellPacketRead
