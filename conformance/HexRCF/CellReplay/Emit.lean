/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Quoted
import HexSignDet.Codec.Bytes
import HexSignDet.DagEncode
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open RootReplayConformance Hex.RCF.RealCoefficients.CellReplayTests.Schema Hex.RCF.RealCoefficients.CellReplayTests.Check
namespace Hex.RCF.RealCoefficients.CellReplayTests.Emit
local instance : Hashable Data.base.Value := ⟨fun a => hash a.stored⟩
local instance : Hashable Signature := ⟨fun s => hash (Signature.codec.encode s).writeBytes⟩

def signs (d : Descriptor Data.base.Value Signature Data.base.sign Data.base.signature)
    (queries : List Data.base.Poly) (row : SelectedSigns d queries) : Codec.Json :=
  (Algebraic.SignEvidence.codec Data.base.codec Signature.codec d.raw).encode
    ⟨queries, row.values, Dag.encode row.evidence⟩

def encode {p : Data.base.Poly} (roots : RootReplay.Result p .negInf .posInf)
    (values : Fin n → Data.base.Value) (formula : RealFormula.QF (n+1))
    (evidence : CellReplay.Evidence roots values formula) : Codec.Json := Id.run do
  let queries := RepresentationSpecialize.prepare values formula
  let sections := (List.finRange roots.roots.length).toArray.map fun i =>
    signs (roots.roots.get i) queries (evidence.sections i)
  let sectors := (List.finRange (roots.roots.length+1)).toArray.map fun cut =>
    let sector := evidence.sectors cut
    let row := evidence.sectorRows cut
    let lower := if h : 0 < cut.val then signs _ _ (sector.left h) else Codec.Json.Value.null
    let upper := if h : cut.val < roots.roots.length then signs _ _ (sector.right h) else Codec.Json.Value.null
    Codec.Json.arr #[Data.base.codec.encode sector.point, lower, upper,
      Codec.descriptor Data.base.codec Signature.codec row.root.raw,
      Codec.graph Data.base.codec Signature.codec (Dag.encode row.root.evidence), signs _ queries row.signs]
  return .arr #[.arr sections, .arr sectors]
def packet := encode wholeResult values formula evidence
def zeroPacket := encode constantResult values Zero.matrix Zero.rows
#eval (show IO Unit from do
  unless packet.writeBytes == Check.packet.writeBytes do
    throw (IO.userError "checked complete-cell packet did not round-trip")
  unless zeroPacket.writeBytes == Zero.packet.writeBytes do
    throw (IO.userError "checked zero-cell packet did not round-trip")
  if let some path ← IO.getEnv "HEX_RCF_CELL_OUTPUT" then
    IO.FS.writeBinFile path packet.writeBytes
  if let some path ← IO.getEnv "HEX_RCF_ZERO_OUTPUT" then
    IO.FS.writeBinFile path zeroPacket.writeBytes
  IO.println "complete checked cell and zero packets round-tripped from section/sector evidence")

end Hex.RCF.RealCoefficients.CellReplayTests.Emit
