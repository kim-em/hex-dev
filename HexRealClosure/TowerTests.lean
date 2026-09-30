/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerCatalog
public meta import HexRealClosure.TowerCatalog

public section

namespace Hex.RealClosure.Tower.Tests
open Lean SignDet

private def registry : BaseContext.Registry := fun _ => none
private def rejected (result : Except String α) : Bool := result.toOption.isNone

private def samePayload (a b : Serialized) : Bool :=
  decide (a.binding = b.binding) &&
    match Literal.ofJson a.value, Literal.ofJson b.value with
    | some x, some y => decide (x = y)
    | _, _ => false

/-- Three actual selected-root levels, explicit predecessor embeddings, and
literal readers for noncanonical coefficients in an immutable prefix catalog. -/
private def sample : Option (Array Bool) :=
  let base := Context.base (BaseContext.rational registry)
  let two : base.Value := 1 + 1
  let three : base.Value := two + 1
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let definition := DensePoly.ofCoeffs #[-two, 0, 1] * (x - DensePoly.C three)
  let raw : RawDescriptor base.Value Signature :=
    { context := base.signature, head := definition,
      lower := .finite 1, upper := .finite two, indices := [], signs := [] }
  (Descriptor.validate base.sign base.signature raw).bind fun d₁ =>
  (base.adjoin? d₁).bind fun first =>
  let a := first.generator
  let below := a - first.embed three
  let semanticOne := below * below⁻¹
  let raw₂ : RawDescriptor first.context.Value Signature :=
    { context := first.context.signature, head := DensePoly.ofCoeffs #[-a, 0, 1],
      lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
  (Descriptor.validate first.context.sign first.context.signature raw₂).bind fun d₂ =>
  (first.context.adjoin? d₂).bind fun second =>
  let b := second.generator
  let raw₃ : RawDescriptor second.context.Value Signature :=
    { context := second.context.signature, head := DensePoly.ofCoeffs #[-b, 0, 1],
      lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
  (Descriptor.validate second.context.sign second.context.signature raw₃).bind fun d₃ =>
  (second.context.adjoin? d₃).bind fun third =>
  let c := third.generator
  ((Catalog.empty registry).insert first.context).bind fun catalog₁ =>
  (catalog₁.insert second.context).bind fun catalog₂ =>
  (catalog₂.insert third.context).bind fun catalog =>
  let unreduced : Serialized := ⟨first.context.signature,
    .arr #[Codec.poly base.codec (definition + DensePoly.C 1), toJson (1 : Int)]⟩
  ((catalog.readElement unreduced).toOption).bind fun unreducedRead =>
  let old := first.context.write semanticOne
  ((catalog.readElement old).toOption).bind fun oldRead =>
  let newest := third.context.write c
  ((catalog.readElement newest).toOption).bind fun newestRead =>
  (newest.value.getArr?.toOption).bind fun fields =>
  let wrongSign : Serialized := ⟨newest.binding, .arr #[fields[0]!, toJson (-1 : Int)]⟩
  let zeroSign : Serialized := ⟨newest.binding, .arr #[fields[0]!, toJson (0 : Int)]⟩
  (fields[0]!.getArr?.toOption).bind fun coefficients =>
  (coefficients[1]!.getArr?.toOption).bind fun nested =>
  (nested[0]!.getArr?.toOption).bind fun nestedCoefficients =>
  let nestedSign : Serialized := ⟨newest.binding, .arr #[
    .arr (coefficients.set! 1 (.arr #[nested[0]!, toJson (-1 : Int)])), fields[1]!]⟩
  let nestedZero : Serialized := ⟨newest.binding, .arr #[
    .arr (coefficients.set! 1 (.arr #[
      .arr (nestedCoefficients.push (first.context.codec.encode 0)), nested[1]!])), fields[1]!]⟩
  let trailingZero : Serialized := ⟨newest.binding,
    .arr #[.arr (coefficients.push (second.context.codec.encode 0)), fields[1]!]⟩
  (Descriptor.validate base.sign base.signature
    { raw with head := DensePoly.scale two definition }).bind fun dOther =>
  (base.adjoin? dOther).bind fun other =>
  let poly : third.context.Poly := DensePoly.ofCoeffs #[-third.embed b, 0, 1]
  let printedPoly := third.context.writePoly poly
  ((catalog.readPolynomial printedPoly).toOption).bind fun readPoly =>
  (printedPoly.value.getArr?.toOption).bind fun polyCoefficients =>
  (base.adjoin? d₁).bind fun sameRoot =>
  some #[
    decide (first.context.sign a = 1), decide (second.context.sign b = 1),
    decide (third.context.sign c = 1),
    decide (first.context.sign (a * a - first.embed two) = 0),
    decide (second.context.sign (b * b - second.embed a) = 0),
    decide (third.context.sign (c * c - third.embed b) = 0),
    decide (third.context.sign (third.embed (second.embed (a * a - first.embed two))) = 0),
    decide (first.context.sign (semanticOne - 1) = 0), decide (semanticOne ≠ 1),
    samePayload unreduced unreducedRead.write,
    decide (!samePayload unreduced (first.context.write (first.embed 1))),
    samePayload old oldRead.write, samePayload newest newestRead.write,
    decide (newestRead.sign = 1), samePayload printedPoly readPoly.write,
    rejected (catalog.readElement wrongSign), rejected (catalog.readElement zeroSign),
    rejected (catalog.readElement trailingZero),
    rejected (catalog.readElement ⟨newest.binding, .bool true⟩),
    rejected (third.context.read old),
    decide (first.context.signature ≠ other.context.signature),
    rejected (catalog.readElement (other.context.write other.generator)),
    (catalog.insert first.context).isNone,
    rejected (catalog₁.readElement newest),
    decide (newestRead.context.signature = third.context.signature),
    rejected (catalog.readElement nestedSign), rejected (catalog.readElement nestedZero),
    rejected (catalog.readElement ⟨newest.binding, .arr #[fields[0]!]⟩),
    rejected (catalog.readElement ⟨newest.binding, .arr #[fields[0]!, fields[1]!, .null]⟩),
    rejected (catalog.readElement ⟨newest.binding, .arr #[fields[0]!, .num ⟨10, 1⟩]⟩),
    rejected (catalog.readElement ⟨newest.binding, .arr #[fields[0]!, .str "1"]⟩),
    rejected (catalog.readPolynomial ⟨printedPoly.binding,
      .arr (polyCoefficients.push (third.context.codec.encode 0))⟩),
    decide (sameRoot.context.signature = first.context.signature),
    (catalog.insert sameRoot.context).isNone,
    decide ((Signature.codec.decode (Signature.codec.encode third.context.signature)).toOption =
      some third.context.signature),
    decide (((contextCodec base.signature).decode
      ((contextCodec base.signature).encode third.context.signature)).toOption = some third.context.signature)]

/--
info: some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
  true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
-/
#guard_msgs in
#eval sample

/-- The parent has one relative encoding, so a full literal copy is rejected. -/
private def duplicateParent : Bool :=
  let parent := (Context.base (BaseContext.rational registry)).signature
  rejected ((contextCodec parent).decode
    (.arr #[.num ⟨1, 0⟩, parent.literal.toJson]))

#guard duplicateParent

/-- Base payload shape is checked independently of algebraic restoration. -/
private def baseSample : Array Bool := Id.run do
  let base := Context.base ((BaseContext.rational registry).infinitesimal)
  let a : base.Value := 1 + 1
  let raw := base.write a
  return #[((base.read raw).toOption.map (fun a => samePayload raw (base.write a))).getD false,
    rejected (base.read ⟨base.signature, (BaseContext.Syntax.rational 2).literal.toJson⟩),
    rejected (base.read ⟨base.signature,
      .arr #[toJson (0 : Nat), toJson (2 : Int), toJson (2 : Nat)]⟩)]

/-- info: #[true, true, true] -/
#guard_msgs in
#eval baseSample

/-- Rational format failures and automatic native-base catalog reconstruction. -/
private def rationalSample : Array Bool :=
  let base := Context.base (BaseContext.rational registry)
  let catalog := Catalog.empty registry
  let bad (j : Json) := rejected (base.read ⟨base.signature, j⟩)
  #[bad (.arr #[toJson (0 : Nat), toJson (2 : Int), toJson (0 : Int)]),
    bad (.arr #[toJson (0 : Nat), toJson (2 : Int), toJson (-1 : Int)]),
    bad (.arr #[toJson (0 : Nat), .num ⟨20, 1⟩, toJson (1 : Nat)]),
    bad .null, bad (.mkObj []),
    (catalog.lookup base.signature).isSome, (catalog.insert base).isNone,
    (catalog.readElement (base.write 1)).toOption.isSome,
    rejected (Signature.codec.decode (.arr #[.arr #[], .num ⟨0, 1⟩, .arr #[]])),
    rejected ((contextCodec base.signature).decode (.arr #[.num ⟨0, 0⟩, .null]))]

/-- info: #[true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval rationalSample

-- Neither unchecked tower/extension construction nor operations across
-- unrelated value types are part of the public interface.
#check_failure Extension.mk
#check_failure (fun (a b : Context registry) (x : a.Value) (y : b.Value) => x + y)

end Hex.RealClosure.Tower.Tests
