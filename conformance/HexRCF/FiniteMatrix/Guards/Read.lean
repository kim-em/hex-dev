/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Schema
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Read
open Hex Hex.SignDet Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
def selected (zero : Bool) (facts : List (SignFact FiniteTower.first)) (packet : Codec.Json)
    (entries : List (Packing FiniteTower.first)) (records : List (ValueSign FiniteTower.first)) :
    Option (SelectedSigns FiniteJoint.next.root (Schema.allQueries zero entries)) := do
  let evidence ← (SignEvidence.codec (Element.signCodec ValueCodec.rat facts)
    ValueCodec.nat FiniteJoint.next.root.raw).decode packet |>.toOption
  if equal : evidence.queries = Schema.allQueries zero entries then
    let memo ← Dag.validatePacking? entries records 8 FiniteJoint.next.root.raw.head
      FiniteJoint.next.root.raw.lower FiniteJoint.next.root.raw.upper evidence.graph
    SelectedSigns.readMemo? FiniteJoint.next.root (Schema.allQueries zero entries)
      (equal ▸ evidence.values) memo evidence.graph.root
  else none
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Read
