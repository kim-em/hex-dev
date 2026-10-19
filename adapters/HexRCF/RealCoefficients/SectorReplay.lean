/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.SectorSamples
public import HexRCF.RealCoefficients.PointRows
public import HexRCF.RealCoefficients.RowReplay
public import HexRCF.RealCoefficients.CellPacketRead
public import HexRCF.RealCoefficients.CellPacketConvert
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

/-- Bind an operation-parametric checked packet to this source formula. -/
@[expose] def fromPacket {roots : RootReplay.Result p .negInf .posInf}
    {cut : Fin (roots.roots.length+1)} {values : Fin n → parent.Value}
    {formula : RealFormula.QF (n+1)}
    (source : CellPackets.Sector parent.sign parent.signature roots.roots cut
      (RepresentationSpecialize.prepare values formula)) : Result roots cut values formula :=
  ⟨source.sector.asSector, source.row.asPacket⟩

/-- Original guard preflight precedes specialization and the shared literal
reader. Absent endpoints require null; present endpoints require strict signs. -/
@[expose] def read (value : ValueCodec parent.Value) (guards : List parent.Value)
    (roots : RootReplay.Result p .negInf .posInf) (cut : Fin (roots.roots.length+1))
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1)) (packet : Codec.Json) :
    Except Replay.Error (Result roots cut values formula) := do
  unless guards.all (fun d => Decidable.decide (d ≠ 0)) do throw .divisor
  let source ← CellPacketRead.read value Signature.codec parent.sign parent.signature []
    roots.roots cut (RepresentationSpecialize.prepare values formula) packet
  return fromPacket source
end Hex.RCF.RealCoefficients.SectorReplay
