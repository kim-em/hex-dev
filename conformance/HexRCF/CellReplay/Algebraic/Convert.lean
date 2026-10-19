/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Read
import HexRCF.RealCoefficients.CellPacketTransport
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Convert
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open Schema Inputs Sections
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def sector (facts : List (Algebraic.SignFact Data.native)) (data : Read.Sectors facts)
    (cut : Fin ((rootList facts data.1.1).length+1)) :=
  @CellPackets.Sector.changeOps parent.Value Signature _ _ _
    (Tower.instOneValue parent)
    (Tower.instAddValue parent)
    (Tower.instSubValue parent)
    (Tower.instMulValue parent)
    (Tower.instNatCastValue parent)
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedOne_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast_eq Data.reduction Data.reduction_eq facts)
    parent.sign parent.signature (rootList facts data.1.1) cut (queriesAt facts) (data.2 cut)

def canonicalTable (facts : List (Algebraic.SignFact Data.native)) (data : Read.Sectors facts) :=
  RootTable.changeOps
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedOne_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast_eq Data.reduction Data.reduction_eq facts)
    parent.sign parent.signature (Inputs.polynomialAt facts) .negInf .posInf data.1.1

def roots (facts : List (Algebraic.SignFact Data.native)) (data : Read.Sectors facts) :=
  RootReplay.fromTable (Inputs.polynomialAt facts) .negInf .posInf (canonicalTable facts data)

theorem count (facts : List (Algebraic.SignFact Data.native)) (data : Read.Sectors facts) :
    (roots facts data).roots.length = (rootList facts data.1.1).length := by
  dsimp only [roots, RootReplay.fromTable, canonicalTable, RootTable.changeOps]
  erw [List.length_map]
  rfl

theorem queries_eq (facts : List (Algebraic.SignFact Data.native)) :
    queriesAt facts = RepresentationSpecialize.prepare values formula := by
  unfold queriesAt
  erw [Algebraic.Element.cachedOne_eq, Algebraic.Element.cachedAdd_eq,
    Algebraic.Element.cachedMul_eq, Algebraic.Element.cachedNeg_eq, Algebraic.Element.cachedNatCast_eq]

def canonicalSector (facts : List (Algebraic.SignFact Data.native)) (data : Read.Sectors facts)
    (cut : Fin ((roots facts data).roots.length+1)) :
    CellPackets.Sector parent.sign parent.signature (roots facts data).roots cut
      (RepresentationSpecialize.prepare values formula) := by
  let oldCut := Fin.cast (congrArg (fun n => n+1) (count facts data)) cut
  let converted := sector facts data oldCut
  let queried := CellPackets.Sector.changeQueries parent.sign parent.signature (queries_eq facts) converted
  exact queried
def canonicalRow (facts : List (Algebraic.SignFact Data.native)) (data : Read.Sectors facts)
    (i : Fin (roots facts data).roots.length) :
    SelectedSigns ((roots facts data).roots.get i) (RepresentationSpecialize.prepare values formula) := by
  let j := Fin.cast (count facts data) i
  let rawRoot := (rootList facts data.1.1).get j
  let converted := @RowOperations.changeOps parent.Value Signature _ _ _
    (Tower.instOneValue parent)
    (Tower.instAddValue parent)
    (Tower.instSubValue parent)
    (Tower.instMulValue parent)
    (Tower.instNatCastValue parent)
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedOne_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast_eq Data.reduction Data.reduction_eq facts)
    parent.sign parent.signature rawRoot (queriesAt facts) (data.1.2 j)
  have same : (roots facts data).roots.get i = (@Descriptor.changeOps parent.Value Signature _ _ _
    (Tower.instOneValue parent)
    (Tower.instAddValue parent)
    (Tower.instSubValue parent)
    (Tower.instMulValue parent)
    (Tower.instNatCastValue parent)
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedOne_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast_eq Data.reduction Data.reduction_eq facts)
    parent.sign parent.signature) rawRoot := by
    dsimp only [roots, RootReplay.fromTable, canonicalTable, RootTable.changeOps]
    erw [List.get_eq_getElem, List.getElem_map]
    rfl
  exact RowOperations.retarget parent.sign parent.signature same.symm (queries_eq facts) converted

def sectorResult (facts : List (Algebraic.SignFact Data.native)) (data : Read.Sectors facts)
    (cut : Fin ((roots facts data).roots.length+1)) : SectorReplay.Result (roots facts data) cut values formula :=
  SectorReplay.fromPacket (canonicalSector facts data cut)

def evidence (facts : List (Algebraic.SignFact Data.native)) (data : Read.Sectors facts) :
    CellReplay.Evidence (roots facts data) values formula :=
  ⟨canonicalRow facts data, fun cut => (sectorResult facts data cut).sector,
    fun cut => (sectorResult facts data cut).row⟩
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Convert
