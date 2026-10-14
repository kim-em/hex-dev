/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.SectorSamples
public import HexRCF.RealCoefficients.PointRows
public import HexRCF.RealCoefficients.RowReplay
public import HexRealClosure.RootReplay
public section
namespace Hex.RCF.RealCoefficients.SectorReplay
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable {p : DensePoly parent.Value}

structure Result (roots : RootReplay.Result p .negInf .posInf)
    (cut : Fin (roots.roots.length+1)) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) where
  sector : SectorSamples.Sector roots cut
  row : PointRows.Packet sector.point values formula

/-- All absent endpoints use the literal null marker, so unused supplied
claims are not silently skipped. Present endpoints require strict signs. -/
@[expose] def read (value : ValueCodec parent.Value) (guards : List parent.Value)
    (roots : RootReplay.Result p .negInf .posInf) (cut : Fin (roots.roots.length+1))
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1)) (packet : Codec.Json) :
    Except Replay.Error (Result roots cut values formula) := do
  unless guards.all (fun d => Decidable.decide (d ≠ 0)) do throw .divisor
  let fields ← match Codec.tuple 6 packet with
    | .error _ => .error .evidence
    | .ok fields => .ok fields
  let point ← match value.decode fields[0] with
    | .error _ => .error .evidence
    | .ok point => .ok point
  let left : { f : (h : 0 < cut.val) → SelectedSigns
      (roots.roots.get ⟨cut.val-1, by have := cut.isLt; omega⟩) [Isolation.pointQuery point] //
        ∀ h, (f h).value = -1 } ←
    if positive : 0 < cut.val then do
      let signs ← RowReplay.read value [] (roots.roots.get ⟨cut.val-1, by have := cut.isLt; omega⟩)
        [Isolation.pointQuery point] fields[1]
      if observed : signs.value = -1 then pure ⟨fun _ => signs, fun _ => observed⟩
      else throw .binding
    else
      if fields[1] = Codec.Json.Value.null then
        pure ⟨fun h => False.elim (positive h), fun h => False.elim (positive h)⟩
      else throw .binding
  let right : { f : (h : cut.val < roots.roots.length) → SelectedSigns
      (roots.roots.get ⟨cut.val, h⟩) [Isolation.pointQuery point] // ∀ h, (f h).value = 1 } ←
    if bound : cut.val < roots.roots.length then do
      let signs ← RowReplay.read value [] (roots.roots.get ⟨cut.val, bound⟩)
        [Isolation.pointQuery point] fields[2]
      if observed : signs.value = 1 then pure ⟨fun _ => signs, fun _ => observed⟩
      else throw .binding
    else
      if fields[2] = Codec.Json.Value.null then
        pure ⟨fun h => False.elim (bound h), fun h => False.elim (bound h)⟩
      else throw .binding
  let root ← match Algebraic.RootReplay.readDescriptor value Signature.codec parent.sign
      parent.signature fields[3] fields[4] with
    | .error _ => .error .evidence
    | .ok root => .ok root
  if same : (root.raw.head - Isolation.pointQuery point).isZero = true then
    let signs ← RowReplay.read value [] root (RepresentationSpecialize.prepare values formula) fields[5]
    return ⟨⟨point, left.val, left.property, right.val, right.property⟩, ⟨root, same, signs⟩⟩
  else throw .binding
end Hex.RCF.RealCoefficients.SectorReplay
