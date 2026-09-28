/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerTransport
public import HexRealClosure.TowerCatalog
public import HexRealClosure.TowerOrder
public meta import HexRealClosure.TowerTransport
public meta import HexRealClosure.TowerCatalog
public meta import HexRealClosure.TowerOrder

namespace Hex.RealClosure.Tower.ConversionTests
open SignDet

private def registry : BaseContext.Registry := fun _ => none

/-- Refine a reducible nonmonic definition, reconstruct a later linear root,
and compose its actual value conversion with an identity conversion. -/
private def sample : Option (Array Bool) :=
  let base := Context.base (BaseContext.rational registry)
  let two : base.Value := 1 + 1
  let three : base.Value := two + 1
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let factor := x * x - DensePoly.C two
  let raw : RawDescriptor base.Value Signature :=
    { context := base.signature, head := DensePoly.scale three (factor * (x - DensePoly.C three)),
      lower := .finite 1, upper := .finite two, indices := [], signs := [] }
  (Descriptor.validate base.sign base.signature raw).bind fun descriptor =>
  let first := base.adjoin descriptor
  let below := first.generator - first.embed three
  let one := below * below⁻¹
  let later : RawDescriptor first.context.Value Signature :=
    { context := first.context.signature, head := DensePoly.ofCoeffs #[-first.generator, 1],
      lower := .finite 1, upper := .finite (1 + 1), indices := [1], signs := [1] }
  (Descriptor.validate first.context.sign first.context.signature later).bind fun next =>
  let old := first.context.adjoin next
  ((descriptor.buildReencoding factor (.finite 1) (.finite two)).toOption).bind fun result =>
  result.bind fun encoding =>
  let initial := Conversion.refine base encoding
  let suffix : Suffix first.context := .root next .nil
  (initial.extend? suffix).map fun conversion =>
  let identity := Conversion.identity conversion.context
  let composed := conversion.comp identity
  let value := composed.value old.generator
  let movedOne := composed.value (old.embed one)
  let packet := composed.context.write movedOne
  #[decide (composed.context.signature.roots.length = 2),
    decide (old.context.signature ≠ composed.context.signature),
    composed.context.equal (value * value) (composed.value (old.embed (first.embed two))),
    decide (composed.context.compare value 1 = .gt),
    decide (one ≠ 1), composed.context.equal movedOne 1,
    decide (composed.value (old.embed (first.generator * first.generator - first.embed two)) = 0),
    (composed.context.read packet).toOption.isSome,
    (old.context.read packet).toOption.isNone,
    decide (identity.context.signature = conversion.context.signature),
    identity.context.equal (identity.value (conversion.value old.generator)) (identity.value 1 +
      identity.value (conversion.value old.generator - 1))]

/-- info: some #[true, true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample

#check_failure Conversion.mk

end Hex.RealClosure.Tower.ConversionTests
