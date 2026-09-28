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
  let old := first.context.write semanticOne
  ((catalog.readElement old).toOption).bind fun oldRead =>
  let newest := third.context.write c
  ((catalog.readElement newest).toOption).bind fun newestRead =>
  (newest.value.getArr?.toOption).bind fun fields =>
  let wrongSign : Serialized := ⟨newest.binding, .arr #[fields[0]!, toJson (-1 : Int)]⟩
  let zeroSign : Serialized := ⟨newest.binding, .arr #[fields[0]!, toJson (0 : Int)]⟩
  (fields[0]!.getArr?.toOption).bind fun coefficients =>
  let trailingZero : Serialized := ⟨newest.binding,
    .arr #[.arr (coefficients.push (second.context.codec.encode 0)), fields[1]!]⟩
  (Descriptor.validate base.sign base.signature
    { raw with head := DensePoly.scale two definition }).bind fun dOther =>
  (base.adjoin? dOther).bind fun other =>
  let poly : third.context.Poly := DensePoly.ofCoeffs #[-third.embed b, 0, 1]
  let printedPoly := third.context.writePoly poly
  ((catalog.readPolynomial printedPoly).toOption).bind fun readPoly =>
  some #[
    decide (first.context.sign a = 1), decide (second.context.sign b = 1),
    decide (third.context.sign c = 1),
    decide (first.context.sign (a * a - first.embed two) = 0),
    decide (second.context.sign (b * b - second.embed a) = 0),
    decide (third.context.sign (c * c - third.embed b) = 0),
    decide (third.context.sign (third.embed (second.embed (a * a - first.embed two))) = 0),
    decide (first.context.sign (semanticOne - 1) = 0), decide (semanticOne ≠ 1),
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
    decide (newestRead.context.signature = third.context.signature)]

/--
info: some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
  true, true, true, true]
-/
#guard_msgs in
#eval sample

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

-- Neither unchecked tower/extension construction nor operations across
-- unrelated value types are part of the public interface.
#check_failure Extension.mk
#check_failure (fun (a b : Context registry) (x : a.Value) (y : b.Value) => x + y)

end Hex.RealClosure.Tower.Tests
