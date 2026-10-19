/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.FiniteMatrix.Schema
public import KernelReplay.FiniteTowerPackets
public import HexRealClosure.SignEvidence
public import HexRealClosure.PackingReplay
public section
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Read
open Hex Hex.SignDet Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
/-- Decode exactly the supplied scalar record; no scalar producer is called. -/
def scalar (packet : Codec.Json) : Option (SignFact FiniteTower.first) := do
  let fields ← packet.getArr? |>.toOption
  if fields.size != 3 then none else do
    let p ← FiniteTower.readPolynomial? fields[0]!
    let sign ← fields[1]!.getInt? |>.toOption
    RationalRoot.readFact? FiniteTower.first p sign fields[2]!
def packing (packet : Codec.Json) : Option (Packing FiniteTower.first) := do
  let fields ← packet.getArr? |>.toOption
  if fields.size != 5 then none else do
    let sign ← fields[2]!.getInt? |>.toOption
    FiniteTowerPackets.readPacking? fields[0]! fields[1]! sign fields[3]! fields[4]!
def sign (facts : List (SignFact FiniteTower.first)) (packet : Codec.Json) :
    Option (ValueSign FiniteTower.first) := do
  let fields ← packet.getArr? |>.toOption
  if fields.size != 2 then none else do
    let value ← (Element.signCodec ValueCodec.rat facts).decode fields[0]! |>.toOption
    FiniteTowerPackets.readSign? value fields[1]!
/-- Bind all guards and atoms to one supplied joint graph at the selected root. -/
def selected (guarded : Bool) (facts : List (SignFact FiniteTower.first))
    (packet : Codec.Json) (entries : List (Packing FiniteTower.first))
    (records : List (ValueSign FiniteTower.first)) :
    Option (SelectedSigns FiniteJoint.next.root (Schema.allQueries guarded entries)) := do
  let evidence ← (SignEvidence.codec (Element.signCodec ValueCodec.rat facts)
    ValueCodec.nat FiniteJoint.next.root.raw).decode packet |>.toOption
  if equal : evidence.queries = Schema.allQueries guarded entries then
    let memo ← Dag.validatePacking? entries records 8 FiniteJoint.next.root.raw.head
      FiniteJoint.next.root.raw.lower FiniteJoint.next.root.raw.upper evidence.graph
    SelectedSigns.readMemo? FiniteJoint.next.root (Schema.allQueries guarded entries)
      (equal ▸ evidence.values) memo evidence.graph.root
  else none
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Read
