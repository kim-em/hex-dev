/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellPackets
public import HexRCF.RealCoefficients.PointRows
public import HexRCF.RealCoefficients.SectorSamples
public section
namespace Hex.RCF.RealCoefficients.CellPackets
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable {p : DensePoly parent.Value}

@[expose] def Point.asPacket {point : parent.Value} {values : Fin n → parent.Value}
    {formula : RealFormula.QF (n+1)}
    (source : Point parent.sign parent.signature point (RepresentationSpecialize.prepare values formula)) :
    PointRows.Packet point values formula := ⟨source.root, source.bound, source.signs⟩

@[expose] def Bounds.asSector {roots : RootReplay.Result p .negInf .posInf}
    {cut : Fin (roots.roots.length+1)}
    (source : Bounds parent.sign parent.signature roots.roots cut) : SectorSamples.Sector roots cut :=
  ⟨source.point, source.left, source.leftSign, source.right, source.rightSign⟩
end Hex.RCF.RealCoefficients.CellPackets
