/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellRead
public import HexRCF.RealCoefficients.SectorEncode
public section
namespace Hex.RCF.RealCoefficients.CellEncode
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable {p : DensePoly parent.Value} {roots : RootReplay.Result p .negInf .posInf}
variable {values : Fin n → parent.Value} {formula : RealFormula.QF (n+1)}

/-- View the existing typed cell data through its operation-parametric reader. -/
@[expose] def sector (data : CellReplay.Evidence roots values formula)
    (cut : Fin (roots.roots.length+1)) : CellPackets.Sector parent.sign parent.signature
      roots.roots cut (RepresentationSpecialize.prepare values formula) :=
  ⟨⟨(data.sectors cut).point, (data.sectors cut).left, (data.sectors cut).leftSign,
    (data.sectors cut).right, (data.sectors cut).rightSign⟩,
    ⟨(data.sectorRows cut).root, (data.sectorRows cut).bound, (data.sectorRows cut).signs⟩⟩

/-- Freeze complete supplied cells without invoking root or sign production.
The coefficient writer is explicit so a partial reader can use the same literal
encoding as native construction. The established packet layout is retained. -/
@[expose] def packet [Hashable parent.Value] [Hashable Signature]
    (value : ValueCodec parent.Value) (data : CellReplay.Evidence roots values formula) : Codec.Json :=
  let sections := (List.finRange roots.roots.length).map fun i =>
    RowEncode.packet value Signature.codec (data.sections i)
  let sectors := (List.finRange (roots.roots.length+1)).map fun cut =>
    SectorEncode.packet value Signature.codec (sector data cut)
  .arr #[.arr sections.toArray,.arr sectors.toArray]

end Hex.RCF.RealCoefficients.CellEncode
