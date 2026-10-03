/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SignEvidence
public meta import HexRealClosureMathlib.SignEvidence
public import HexRealClosureMathlib.SignFactsConformance
public meta import HexRealClosureMathlib.SignFactsConformance
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexRealClosure.SignCodec
import all HexRealClosure.AlgebraicCodec
import all HexRealClosure.Algebraic
import all HexRealClosure.SignEvidence
import all HexSignDet.Codec.Coefficients
import all HexPoly.Euclid.DivGcd

public section

namespace Hex.RealClosure.Algebraic.SignEvidenceConformance
open SignDet SignDet.Conformance
open CoefficientSignsConformance PackingConformance SignFactsConformance

@[expose] def read (required : List (DensePoly Rat)) (evidence : SignEvidence Rat Nat) :=
  context.readEvidence? (fun q : Rat => (q : ℝ))
    (fun _ => Rat.cast_eq_zero) (by simp)
    (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) rational_sign
    (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _) required evidence

@[expose] def decode (value : ValueCodec Rat) (required : List (DensePoly Rat))
    (bytes : ByteArray) :=
  context.decodeEvidence (fun q : Rat => (q : ℝ))
    (fun _ => Rat.cast_eq_zero) (by simp)
    (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) rational_sign
    (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _)
    value ValueCodec.nat required bytes

/-- This interpretation has no compiled implementation. The byte reader
must erase it along with the semantic proof arguments. -/
noncomputable def rationalModel (x : Rat) : ℝ :=
  Classical.choose (show ∃ y : ℝ, y = (x : ℝ) from ⟨_, rfl⟩)

theorem rationalModel_eq (x : Rat) : rationalModel x = (x : ℝ) := by
  unfold rationalModel
  exact Classical.choose_spec (show ∃ y : ℝ, y = (x : ℝ) from ⟨_, rfl⟩)

@[expose] def decodeModel (required : List (DensePoly Rat)) (bytes : ByteArray) :=
  context.decodeEvidence rationalModel
    (fun _ => by rw [rationalModel_eq]; exact Rat.cast_eq_zero)
    (by rw [rationalModel_eq]; simp)
    (fun _ _ => by simp only [rationalModel_eq]; exact Rat.cast_add _ _)
    (fun _ _ => by simp only [rationalModel_eq]; exact Rat.cast_sub _ _)
    (fun _ _ => by simp only [rationalModel_eq]; exact Rat.cast_mul _ _)
    (fun _ => by rw [rationalModel_eq]; simp)
    (fun x => by rw [rationalModel_eq]; exact rational_sign x)
    (fun _ => by simp only [rationalModel_eq]; exact Rat.cast_neg _)
    (fun _ => by simp only [rationalModel_eq]; exact Rat.cast_inv _)
    ValueCodec.rat ValueCodec.nat required bytes

/-- Repeated original keys share one joint graph, while zero remains a real
requested slot. Tests mutate independently supplied bytes and graph data. -/
def bytesChecks : Option (List (String × Bool)) := do
    let keys : List (DensePoly Rat) := [2 * Sturm.Fixtures.x, 0, 2 * Sturm.Fixtures.x]
    let packet ← (context.buildEvidence keys).toOption
    let codec := SignEvidence.codec ValueCodec.rat ValueCodec.nat source.raw
    let bytes := codec.encodeBytes packet
    let facts ← (decode ValueCodec.rat keys bytes).toOption
    let empty ← (context.buildEvidence []).toOption
    let emptyFacts ← (decode ValueCodec.rat [] (codec.encodeBytes empty)).toOption
    let badSigns := {packet with values := packet.values.map (fun s => -s)}
    let first ← packet.graph.entries[0]?
    let bad := {first with node := {first.node with
      system := {first.node.system with values := first.node.system.values.map (· + 1)}}}
    let extra := {packet with graph :=
      {packet.graph with entries := packet.graph.entries.push bad}}
    let selected ← packet.graph.entries[packet.graph.root]?
    let cyclicEntries := packet.graph.entries.set! packet.graph.root
      {selected with children := some (packet.graph.root, packet.graph.root)}
    let cyclic := {packet with graph := {packet.graph with entries := cyclicEntries}}
    let foreignEntries := packet.graph.entries.set! 0 {first with node := {first.node with context := 8}}
    let foreign := {packet with graph := {packet.graph with entries := foreignEntries}}
    let headEntries := packet.graph.entries.set! 0
      {first with node := {first.node with head := 2 * first.node.head}}
    let changedHead := {packet with graph := {packet.graph with entries := headEntries}}
    let momentEntry := {first with node := {first.node with
      moments := first.node.moments.map fun cert => {cert with context := 8}}}
    let momentPacket := {packet with graph := {packet.graph with
      entries := packet.graph.entries.set! 0 momentEntry}}
    let stale := fun raw => (SignEvidence.codec ValueCodec.rat ValueCodec.nat raw).encodeBytes packet
    pure [
      ("noncomputable interpretation erases",
        (decodeModel keys bytes).toOption.map (fun fs => fs.toList.map SignFact.sign) == some [1, 0, 1]),
      ("ordered signs", facts.toList.map SignFact.sign == [1, 0, 1]),
      ("literal keys", facts.toList.map SignFact.polynomial == keys),
      ("direct rational evaluation", facts.toList.map SignFact.sign == keys.map (fun p => Sturm.orderSign (p.eval 1))),
      ("empty requests", emptyFacts.toList.isEmpty),
      ("shared leaf", packet.graph.entries.size == 4),
      ("nonempty preparation indices", packet.graph.entries.any (fun e =>
        e.node.preparation.any (fun p => !p.steps.isEmpty))),
      ("nonempty reduction indices", packet.graph.entries.any (fun e =>
        e.node.reductions.toArray.any (fun r => r.any (fun p => !p.steps.isEmpty)))),
      ("false signs", (decode ValueCodec.rat keys (codec.encodeBytes badSigns)).toOption.isNone),
      ("missing key", (decode ValueCodec.rat keys.tail bytes).toOption.isNone),
      ("extra key", (decode ValueCodec.rat (keys ++ [0]) bytes).toOption.isNone),
      ("changed order", (decode ValueCodec.rat [0, 2 * Sturm.Fixtures.x, 2 * Sturm.Fixtures.x] bytes).toOption.isNone),
      ("equal value with another polynomial", (decode ValueCodec.rat [stored, 0, 2 * Sturm.Fixtures.x] bytes).toOption.isNone),
      ("corrupt unselected entry", (decode ValueCodec.rat keys (codec.encodeBytes extra)).toOption.isNone),
      ("cyclic references", (decode ValueCodec.rat keys (codec.encodeBytes cyclic)).toOption.isNone),
      ("foreign graph context", (decode ValueCodec.rat keys (codec.encodeBytes foreign)).toOption.isNone),
      ("changed graph head", (decode ValueCodec.rat keys (codec.encodeBytes changedHead)).toOption.isNone),
      ("foreign moment context", (decode ValueCodec.rat keys (codec.encodeBytes momentPacket)).toOption.isNone),
      ("foreign context", (decode ValueCodec.rat keys (stale {source.raw with context := 8})).toOption.isNone),
      ("changed head", (decode ValueCodec.rat keys (stale {source.raw with head := 2 * source.raw.head})).toOption.isNone),
      ("changed endpoint", (decode ValueCodec.rat keys (stale {source.raw with upper := .finite 3})).toOption.isNone),
      ("changed derivative vector", (decode ValueCodec.rat keys (stale {source.raw with indices := [1], signs := [1]})).toOption.isNone),
      ("truncated JSON", (decode ValueCodec.rat keys (bytes.extract 0 (bytes.size - 2))).toOption.isNone)]

def bytesPass : Bool := bytesChecks.map (fun xs => xs.all (·.2)) == some true

#guard bytesPass

@[expose] def decodeUpper (value : ValueCodec (Element context))
    (required : List (DensePoly (Element context)))
    (bytes : ByteArray) : Except String (Vector (SignFact NestedSignsConformance.next) required.length) :=
  NestedSignsConformance.next.decodeEvidence upperEmbedding
    (Element.denote_eq_zero (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_one (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_add (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_sub (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_mul (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_nat (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.sign_spec (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_neg (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_inv (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _)
      (fun _ _ => Rat.cast_div _ _)) value ValueCodec.nat required bytes

/-- Both child packets are decoded and independently checked. The upper
packet uses a strict predecessor reader built only from the lower packet's
proved facts. Omitting a lower literal or upper key rejects at that level. -/
def nestedPass : Bool :=
  (do
    let keys := [stored, 2 * Sturm.Fixtures.x, DensePoly.C (1 : Rat), DensePoly.C (-1 : Rat)]
    let lower ← (context.buildEvidence keys).toOption
    let codec := SignEvidence.codec ValueCodec.rat ValueCodec.nat source.raw
    let lowerFacts ← (decode ValueCodec.rat keys (codec.encodeBytes lower)).toOption
    let reader := Element.signCodec ValueCodec.rat lowerFacts.toList
    let upper : SignEvidence (Element context) Nat :=
      ⟨[NestedSignsConformance.unitPoly], #v[1], NestedSignsConformance.graph⟩
    let wire := SignEvidence.codec reader ValueCodec.nat NestedSignsConformance.root.raw
    let bytes := wire.encodeBytes upper
    let facts ← (decodeUpper reader upper.queries bytes).toOption
    let valueReader := Element.signCodec reader facts.toList
    let literal := Element.ofPoly (context := NestedSignsConformance.next) NestedSignsConformance.unitPoly
    let encoded := (Element.codec (Element.codec ValueCodec.rat)).encode literal
    let restored ← (valueReader.decode encoded).toOption
    let missingLiteral := Element.signCodec ValueCodec.rat
      (lowerFacts.toList.filter fun fact => fact.polynomial != stored)
    let missingEndpoint := Element.signCodec ValueCodec.rat
      (lowerFacts.toList.filter fun fact => fact.polynomial != DensePoly.C (1 : Rat))
    pure (restored == literal && facts.toList.map SignFact.sign == [1] &&
      (decodeUpper missingLiteral upper.queries bytes).toOption.isNone &&
      (decodeUpper missingEndpoint upper.queries bytes).toOption.isNone &&
      (decodeUpper reader [] bytes).toOption.isNone &&
      ((Element.signCodec (context := NestedSignsConformance.next) reader []).decode encoded).toOption.isNone)) == some true

#guard nestedPass

/-- Both levels are actual producer output. The lower request list is
collected from every literal of the produced upper packet, rather than a
handwritten fixture list. Arithmetic during checking still uses native ops. -/
def producedNestedPass : Bool :=
  (do
    let upperSigns ← (NestedSignsConformance.next.buildSigns
      [NestedSignsConformance.unitPoly, NestedSignsConformance.nextQuery,
        0, NestedSignsConformance.unitPoly]).toOption
    let upper := SignEvidence.ofSigns upperSigns
    let coefficients := SignEvidence.coefficients NestedSignsConformance.next.root.raw upper
    let keys := Element.signKeys coefficients
    let lower ← (context.buildEvidence keys).toOption
    let lowerCodec := SignEvidence.codec ValueCodec.rat ValueCodec.nat source.raw
    let facts ← (decode ValueCodec.rat keys (lowerCodec.encodeBytes lower)).toOption
    let reader := Element.signCodec ValueCodec.rat facts.toList
    let wire := SignEvidence.codec reader ValueCodec.nat NestedSignsConformance.next.root.raw
    let decoded ← (decodeUpper reader upper.queries (wire.encodeBytes upper)).toOption
    let literals := coefficients.all fun a =>
      reader.decode (reader.encode a) == .ok a
    let missing := Element.signCodec ValueCodec.rat
      (facts.toList.filter fun fact => fact.polynomial != stored)
    let everyOmission := facts.toList.all fun fact =>
      fact.polynomial == 0 ||
        (decodeUpper (Element.signCodec ValueCodec.rat
          (facts.toList.filter fun other => other.polynomial != fact.polynomial))
          upper.queries (wire.encodeBytes upper)).toOption.isNone
    let prepared := upper.graph.entries.any fun e =>
      e.node.preparation.any fun p => !p.steps.isEmpty
    let reduced := upper.graph.entries.any fun e =>
      e.node.reductions.toArray.any fun r => r.any fun p => !p.steps.isEmpty
    pure (decoded.toList.map SignFact.sign == [1, 1, 0, 1] && literals && everyOmission &&
      prepared && reduced && keys.length < coefficients.length &&
      (decodeUpper missing upper.queries (wire.encodeBytes upper)).toOption.isNone)) == some true

#guard producedNestedPass

@[expose] def upperKernelSigns :
    SelectedSigns NestedSignsConformance.next.root [NestedSignsConformance.unitPoly] :=
  ⟨#v[1], .leaf NestedSignsConformance.queryNode, by
    simpa only [NestedSignsConformance.next, Context.extend, Context.root_adjoin] using
      NestedSignsConformance.query_checked⟩

@[expose] def kernelLowerFacts : List (SignFact context) :=
  literalFacts ++ [SignCodecConformance.oneFact, ⟨DensePoly.C (-1), -1, by
    rw [context.signPoly_const _ (by decide +kernel)]
    decide +kernel⟩]

@[expose] def kernelLowerReader := Element.signCodec ValueCodec.rat kernelLowerFacts

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
/-- The ordinary kernel verifies coverage of every stored literal in this
upper packet, including its scales, quotients and finite endpoints. -/
theorem upper_coverage : kernelLowerReader.Covers
    (SignEvidence.coefficients NestedSignsConformance.next.root.raw
      (SignEvidence.ofSigns upperKernelSigns)) := by
  unfold ValueCodec.Covers
  simp only [NestedSignsConformance.next, Context.extend, Context.root_adjoin,
    NestedSignsConformance.root_raw]
  simp only [SignEvidence.ofSigns, upperKernelSigns, Dag.encode_leaf]
  decide +kernel

/-- The actual partial-reader codec roundtrip is a kernel theorem, with no
global law for the algebraic coefficient decoder. -/
theorem upper_roundtrip :
    (SignEvidence.codec kernelLowerReader ValueCodec.nat NestedSignsConformance.next.root.raw).decode
      ((SignEvidence.codec kernelLowerReader ValueCodec.nat
        NestedSignsConformance.next.root.raw).encode (SignEvidence.ofSigns upperKernelSigns)) =
      .ok (SignEvidence.ofSigns upperKernelSigns) :=
  SignEvidence.codec_ofSigns_covered _ _ _ upperKernelSigns upper_coverage
    (ValueCodec.nat_lawful.covers _)

/-- The child table is checked by the imported ordinary-kernel fixture. -/
@[expose] def kernelSigns : SelectedSigns context.root [NestedSignsConformance.endpointQuery] :=
  ⟨#v[1], .leaf NestedSignsConformance.endpointNode, by
    simpa only [context, Context.root_adjoin] using NestedSignsConformance.endpoint_checked⟩

@[expose] def kernelPacket : SignEvidence Rat Nat := SignEvidence.ofSigns kernelSigns

/-- The actual producer packet roundtrips without caller-supplied dimension
or reduction-index premises, for every checked rational joint row. -/
theorem rational_roundtrip {queries : List (DensePoly Rat)}
    (signs : SelectedSigns context.root queries) :
    (SignEvidence.codec ValueCodec.rat ValueCodec.nat context.root.raw).decode
      ((SignEvidence.codec ValueCodec.rat ValueCodec.nat context.root.raw).encode
        (SignEvidence.ofSigns signs)) = .ok (SignEvidence.ofSigns signs) :=
  SignEvidence.codec_ofSigns _ _ ValueCodec.rat_lawful ValueCodec.nat_lawful context signs

/-- The child fixture survives the real byte codec when its lexical precheck
passes. The compiled guard below checks that premise for the default limits;
this theorem does not measure kernel reduction of the byte codec. -/
theorem kernel_bytes (limits : Codec.Limits)
    (bound : Codec.checkBytes limits
      ((SignEvidence.codec ValueCodec.rat ValueCodec.nat context.root.raw).encodeBytes
        kernelPacket) = .ok ()) :
    (SignEvidence.codec ValueCodec.rat ValueCodec.nat context.root.raw).decodeBytes
      ((SignEvidence.codec ValueCodec.rat ValueCodec.nat context.root.raw).encodeBytes
        kernelPacket) limits = .ok kernelPacket :=
  SignEvidence.bytes_ofSigns _ _ ValueCodec.rat_lawful ValueCodec.nat_lawful
    context kernelSigns limits bound

#guard Codec.checkBytes {}
  ((SignEvidence.codec ValueCodec.rat ValueCodec.nat context.root.raw).encodeBytes
    kernelPacket) == .ok ()

/-- General graph correspondence and scalar correspondence apply to the
actual literal child certificate. No producer availability premise is added. -/
theorem kernel_checked : (read kernelPacket.queries kernelPacket).isSome = true := by
  unfold read
  rw [Context.readEvidence_accept]
  change ((SignEvidence.ofSigns kernelSigns).check? context
    [NestedSignsConformance.endpointQuery]).isSome = true
  rw [SignEvidence.check_ofSigns]
  rfl

end Hex.RealClosure.Algebraic.SignEvidenceConformance

/-- info: 'Hex.RealClosure.Algebraic.SignEvidenceConformance.kernel_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.SignEvidenceConformance.kernel_checked

/-- info: 'Hex.RealClosure.Algebraic.SignEvidenceConformance.kernel_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.SignEvidenceConformance.kernel_bytes

/-- info: 'Hex.RealClosure.Algebraic.SignEvidenceConformance.rational_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.SignEvidenceConformance.rational_roundtrip

/-- info: 'Hex.RealClosure.Algebraic.SignEvidenceConformance.upper_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.SignEvidenceConformance.upper_roundtrip
