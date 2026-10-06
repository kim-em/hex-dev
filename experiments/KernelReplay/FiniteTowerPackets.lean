/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteTower
public meta import KernelReplay.FiniteTower
public meta import KernelReplay.RationalRoot
import all HexRealClosure.Packing
import all HexRealClosure.ValueSigns
import all HexRealClosure.PackingReplay
import all HexRealClosure.SignCodec
import all HexRealClosure.SignRequests
import all HexRealClosure.Algebraic
import all HexSignDet.Descriptor
import all HexSignDet.Dag
import all HexSignDet.Thom
import all HexSignDet.Replay
import all HexSignDet.MomentReplay
import all HexSignDet.QueryReduction
import all HexSignDet.Reduction
import all HexSignDet.Matrix
import all HexRank.Cert
import all HexMatrix.MatrixAlgebra
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Value
import all HexSignDet.Codec.Coefficients
import all HexRealRoots.TarskiShared
import all HexPoly.Dense
import all HexPoly.Euclid.DivGcd
import all Init.Data.Rat.Basic
import all Init.Data.Array.Basic
import all Init.Prelude

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerPackets
open Hex.SignDet FiniteTower

/-- Reconstruct the exact original packing operation from two supplied base
sign graphs. Its representative fact does not cover a different original key. -/
@[expose] def readPacking? (original retained : Codec.Json) (claimed : Int)
    (scalar joint : Codec.Json) : Option (Packing first) := do
  let p ← readPolynomial? original
  let kept ← readPolynomial? retained
  let fact ← RationalRoot.readFact? first kept claimed scalar
  let graph ← (Codec.readGraph ValueCodec.rat ValueCodec.nat 7 first.root.raw.head
    first.root.raw.lower first.root.raw.upper joint).toOption
  let memo ← graph.validate? Sturm.orderSign 7 first.root.raw.head
    first.root.raw.lower first.root.raw.upper
  Packing.readMemo? reduction reduction_eq [fact] p memo graph.root

/-- Read the cached tag of the actual stored operand from supplied base graph
entries; no input is repacked and no producer is invoked by this reader. -/
@[expose] def readSign? (value : Element first) (packet : Codec.Json) : Option (ValueSign first) := do
  let graph ← (Codec.readGraph ValueCodec.rat ValueCodec.nat 7 first.root.raw.head
    first.root.raw.lower first.root.raw.upper packet).toOption
  let memo ← graph.validate? Sturm.orderSign 7 first.root.raw.head
    first.root.raw.lower first.root.raw.upper
  ValueSign.readMemo? value memo graph.root

/-- The higher checker consumes decoded literal coefficients and records;
its Boolean result is the acceptance of the actual selected descriptor. -/
@[expose] def program (facts : List (SignFact first)) (subject packet : Codec.Json)
    (entries : List (Packing first)) (signs : List (ValueSign first)) : Bool :=
  (readNext? facts entries signs subject packet).isSome

public meta section
open Lean Meta

/-- Quote and independently decode a literal base polynomial. -/
def quotePolynomial (p : DensePoly Rat) : MetaM Expr :=
  RationalRoot.checkedRecord (mkApp (mkConst ``readPolynomial?)
    (KernelReplay.jsonExpr (Codec.poly ValueCodec.rat p)))

/-- The native supplier contributes only literal polynomial and graph packets;
all returned packing records are reconstructed and ordinary-kernel checked. -/
unsafe def packing (polynomial : Expr) : MetaM Expr := do
  let polynomial ← withTransparency .all
    (reduce polynomial (explicitOnly := false))
  let p ← try
    evalExpr (DensePoly Rat) (← inferType polynomial) polynomial (checkMeta := false)
    catch error => throwError "packing polynomial evaluation: {error.toMessageData}"
  let kept := reduction p
  let scalar ← match first.buildSigns [first.queryPoly kept] with
    | .ok signs => pure signs
    | .error error => throwError "base scalar production failed: {reprStr error}"
  let joint ← match first.buildSigns [kept, p - kept] with
    | .ok signs => pure signs
    | .error error => throwError "base packing production failed: {reprStr error}"
  RationalRoot.checkedRecord (mkAppN (mkConst ``readPacking?)
    #[KernelReplay.jsonExpr (Codec.poly ValueCodec.rat p),
      KernelReplay.jsonExpr (Codec.poly ValueCodec.rat kept), toExpr scalar.value,
      KernelReplay.jsonExpr (Codec.graph ValueCodec.rat ValueCodec.nat (Dag.encode scalar.evidence)),
      KernelReplay.jsonExpr (Codec.graph ValueCodec.rat ValueCodec.nat (Dag.encode joint.evidence))])

/-- The input-sign supplier similarly returns only a checked literal graph. -/
unsafe def sign (value : Expr) : MetaM Expr := do
  let input ← try
    evalExpr (Element first) (← inferType value) value (checkMeta := false)
    catch error => throwError "input-sign value evaluation: {error.toMessageData}"
  let signs ← match first.buildSigns [input.polynomial] with
    | .ok signs => pure signs
    | .error error => throwError "base input-sign production failed: {reprStr error}"
  RationalRoot.checkedRecord (mkApp2 (mkConst ``readSign?) value
    (KernelReplay.jsonExpr (Codec.graph ValueCodec.rat ValueCodec.nat (Dag.encode signs.evidence))))

/-- Native output consists solely of the upper subject, graph and finite stored
coefficient keys. The root and all scalar proof objects are discarded. -/
structure Packet where
  subject : Codec.Json
  graph : Codec.Json
  coefficients : List (DensePoly Rat)

unsafe def produce : MetaM Packet := do
  let some root := Descriptor.validate Element.sign 8 nextRaw
    | throwError "native nested selected-root production failed"
  let graph := Dag.encode root.evidence
  let values := Codec.Coefficients.graph graph ++ Codec.Coefficients.poly nextRaw.head ++
    Codec.Coefficients.endpoint nextRaw.lower ++ Codec.Coefficients.endpoint nextRaw.upper
  let coefficients := (values.filter (fun value => value.sign != 0)).map Element.polynomial
  return ⟨SignRequests.binding (Element.codec ValueCodec.rat) ValueCodec.nat nextRaw,
    Codec.graph (Element.codec ValueCodec.rat) ValueCodec.nat graph, coefficients.eraseDups⟩

/-- Every supplied literal coefficient obtains an independently checked scalar
fact at the base descriptor, before graph decoding restores the stored value. -/
unsafe def inputFacts (packet : Packet) : MetaM Expr := do
  let owner := mkConst ``first
  let mut facts : List Expr := []
  for polynomial in packet.coefficients do
    let literal ← quotePolynomial polynomial
    facts := facts ++ [← RationalRoot.produceFact owner literal]
  let factType ← mkAppM ``SignFact #[owner]
  mkListLit factType facts

/-- Retain the exact instantiated reader program alongside its inventories. -/
structure Assembly where
  program : Expr
  collection : Collections

/-- Collect exactly the lower packing and input-sign records reached by the
actual higher reader. The final acceptance equation refers to these inventories. -/
unsafe def collect (packet : Packet) : MetaM Assembly := withExporting (isExporting := false) do
  let facts ← inputFacts packet
  let program := mkAppN (mkConst ``program)
    #[facts, KernelReplay.jsonExpr packet.subject, KernelReplay.jsonExpr packet.graph]
  let owner := mkConst ``first
  let entryType ← mkAppM ``Packing #[owner]
  let signType ← mkAppM ``ValueSign #[owner]
  let entries ← mkListLit entryType []
  let signs ← mkListLit signType []
  let simpContext ← Simp.mkContext (simpTheorems := #[])
    (congrTheorems := ← getSimpCongrTheorems)
  let collection ← collectMany 500 program #[⟨entries⟩, ⟨signs⟩] simpContext (fun needed _ => do
    unless ← isDefEq needed.context owner do throwError "unexpected lower context"
    match needed.kind with
    | .coefficient => return some (← packing needed.polynomial)
    | .valueSign =>
      let some value := needed.value | throwError "input-sign request lost its value"
      return some (← sign value)
    | .inverse => throwError "descriptor reader requested a native inverse")
  return ⟨program, collection⟩

end
end Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerPackets
