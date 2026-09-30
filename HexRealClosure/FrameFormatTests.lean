/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.FrameFormat
public meta import HexRealClosure.FrameFormat

public section

namespace Hex.RealClosure.Tower.FormatTests
open SignDet

private def registry : BaseContext.Registry := fun _ => none

/-- Total construction for a non-monic reducible definition, followed by an
extension whose head contains noncanonical predecessor representatives. -/
private def sample : Option (Array Bool) :=
  let base := Context.base (BaseContext.rational registry)
  let two : base.Value := 1 + 1
  let three : base.Value := two + 1
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let head := DensePoly.scale three
    (DensePoly.ofCoeffs #[-two, 0, 1] * (x - DensePoly.C three))
  let raw : RawDescriptor base.Value Signature :=
    { context := base.signature, head := head, lower := .finite 1,
      upper := .finite two, indices := [], signs := [] }
  (Descriptor.validate base.sign base.signature raw).bind fun descriptor =>
  let first := base.adjoin descriptor
  let a := first.generator
  let divisor := a - first.embed three
  let semanticOne := divisor / divisor
  let raw₂ : RawDescriptor first.context.Value Signature :=
    { context := first.context.signature,
      head := DensePoly.ofCoeffs #[-(a * semanticOne), 0, semanticOne],
      lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
  (Descriptor.validate first.context.sign first.context.signature raw₂).bind fun descriptor₂ =>
  let second := first.context.adjoin descriptor₂
  let b := second.generator
  some #[
    decide (first.context.sign a = 1),
    decide (first.context.sign (a * a - first.embed two) = 0),
    decide (semanticOne ≠ 1), decide (first.context.sign (semanticOne - 1) = 0),
    decide (second.context.sign b = 1),
    decide (second.context.sign (b * b - second.embed a) = 0),
    decide (first.context.signature = base.signature.extend first.frame),
    decide (second.context.signature = first.context.signature.extend second.frame),
    (base.adjoin? descriptor).isSome, (first.context.adjoin? descriptor₂).isSome]

/-- info: some #[true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample

end Hex.RealClosure.Tower.FormatTests
