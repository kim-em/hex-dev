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
and compose two checked definition changes before rebuilding the later root. -/
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
  ((encoding.target.buildReencoding (DensePoly.scale two factor)
    (.finite 1) (.finite two)).toOption).bind fun result =>
  result.bind fun following =>
  let same := (Conversion.refine_spec base encoding).1.trans
    (congrArg Extension.context (base.refine encoding).canonical)
  let next := (Conversion.refine base following).cast same.symm
  let successive := initial.comp next
  (successive.extend? suffix).map fun composed =>
  let value := composed.value old.generator
  let movedOne := composed.value (old.embed one)
  let packet := composed.context.write movedOne
  let identity := Conversion.identity base
  #[decide (composed.context.signature.roots.length = 2),
    decide (old.context.signature ≠ composed.context.signature),
    composed.context.equal (value * value) (composed.value (old.embed (first.embed two))),
    decide (composed.context.compare value 1 = .gt),
    decide (one ≠ 1), composed.context.equal movedOne 1,
    decide (composed.value (old.embed (first.generator * first.generator - first.embed two)) = 0),
    (composed.context.read packet).toOption.isSome,
    (old.context.read packet).toOption.isNone,
    decide (successive.context.signature ≠ initial.context.signature),
    successive.context.equal (successive.value first.generator * successive.value first.generator)
      (successive.value (first.embed two)),
    identity.context.equal (identity.value two) (1 + 1)]

/-- info: some #[true, true, true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample

#check_failure Conversion.mk
#check_failure (show Conversion (Context.base (BaseContext.rational registry)) from
  ⟨Context.base (BaseContext.rational registry), id, .identity _⟩)

end Hex.RealClosure.Tower.ConversionTests
