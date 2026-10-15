/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Quoted
import HexSignDet.Codec.Bytes
import HexSignDet.DagEncode
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Emit
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open Schema Inputs Sections
abbrev hashValue : Hashable parent.Value := ⟨fun a => hash (parent.codec.encode a).writeBytes⟩
abbrev hashSignature : Hashable Signature := ⟨fun s => hash (Signature.codec.encode s).writeBytes⟩

/-- Encoding retains the checked data; it neither prepares nor produces a row. -/
def encodeRaw {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]
    [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Hashable E] [Hashable Ctx]
    (value : ValueCodec E) (context : ValueCodec Ctx) (sign : E → Int) (binding : Ctx)
    (p : DensePoly E) (queries : List (DensePoly E))
    (table : RootTable.Result sign binding p .negInf .posInf)
    (sections : (i : Fin table.roots.length) → SelectedSigns (table.roots.get i) queries)
    (sectors : (cut : Fin (table.roots.length+1)) →
      CellPackets.Sector sign binding table.roots cut queries) : Codec.Json := Id.run do
  let encodeRow (raw : RawDescriptor E Ctx) (qs : List (DensePoly E))
      (vs : Vector Int qs.length) (tree : SignDet.Replay E Ctx) :=
    (Algebraic.SignEvidence.codec value context raw).encode ⟨qs, vs, Dag.encode tree⟩
  let sectionFields := (List.finRange table.roots.length).toArray.map fun i =>
    let row := sections i
    encodeRow (table.roots.get i).raw queries row.values row.evidence
  let sectorFields := (List.finRange (table.roots.length+1)).toArray.map fun cut =>
    let sector := (sectors cut).sector
    let row := (sectors cut).row
    let lower := if h : 0 < cut.val then
      let selected := sector.left h
      encodeRow (table.roots.get ⟨cut.val-1, by have := cut.isLt; omega⟩).raw
        [Isolation.pointQuery sector.point] selected.values selected.evidence
      else Codec.Json.Value.null
    let upper := if h : cut.val < table.roots.length then
      let selected := sector.right h
      encodeRow (table.roots.get ⟨cut.val, h⟩).raw
        [Isolation.pointQuery sector.point] selected.values selected.evidence
      else Codec.Json.Value.null
    Codec.Json.arr #[value.encode sector.point, lower, upper,
      Codec.descriptor value context row.root.raw,
      Codec.graph value context (Dag.encode row.root.evidence),
      encodeRow row.root.raw queries row.signs.values row.signs.evidence]
  return .arr #[Codec.graph value context (Dag.encode table.tree), .arr sectionFields, .arr sectorFields]

def encode (facts : List (Algebraic.SignFact Data.native)) (data : Read.Sectors facts) : Codec.Json :=
  @encodeRaw parent.Value Signature _ _ _
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
    hashValue hashSignature parent.codec Signature.codec parent.sign parent.signature
    (polynomialAt facts) (queriesAt facts) data.1.1 data.1.2 data.2

def packet : Codec.Json := encode Canonical.facts Canonical.data

#eval (show IO Unit from do
  let original := Codec.Json.arr #[Literals.roots, Literals.sections, Literals.sectors]
  unless packet.writeBytes == original.writeBytes do
    throw (IO.userError "checked algebraic cells did not round-trip")
  if let some path ← IO.getEnv "HEX_RCF_ALGEBRAIC_CELL_OUTPUT" then
    IO.FS.writeBinFile path packet.writeBytes
  IO.println "complete algebraic root/section/sector packet round-tripped from checked data")
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Emit
