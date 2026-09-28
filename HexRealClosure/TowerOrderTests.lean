/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.FrameFormat
public import HexRealClosure.TowerOrder
public meta import HexRealClosure.FrameFormat
public meta import HexRealClosure.TowerOrder

namespace Hex.RealClosure.Tower.OrderTests
open SignDet

private def registry : BaseContext.Registry := fun _ => none

/-- Semantic equality and all three comparison results on actual native
extensions, including a non-monic reducible head and noncanonical nonzero one. -/
private def sample : Option (Array Bool) :=
  let base := Context.base (BaseContext.rational registry)
  let two : base.Value := 1 + 1
  let three : base.Value := two + 1
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let head := DensePoly.scale three
    (DensePoly.ofCoeffs #[-two, 0, 1] * (x - DensePoly.C three))
  let raw : RawDescriptor base.Value Signature :=
    { context := base.signature, head, lower := .finite 1,
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
    first.context.equal (a * a) (first.embed two),
    decide (first.context.compare a (first.embed two) = .lt),
    decide (first.context.compare (first.embed two) a = .gt),
    first.context.equal semanticOne 1, decide (semanticOne ≠ 1),
    decide (first.context.compare semanticOne 1 = .eq),
    !first.context.equal a (first.embed two),
    second.context.equal (second.embed semanticOne) (second.embed 1),
    decide (second.context.compare (second.embed a) (second.embed (first.embed two)) = .lt),
    decide (second.context.compare (second.embed (first.embed two)) (second.embed a) = .gt),
    decide (second.context.compare (second.embed semanticOne) (second.embed 1) = .eq),
    second.context.equal (b * b) (second.embed a),
    second.context.equal (b - b) 0,
    decide (second.context.compare (-b) 0 = .lt)]

/-- info: some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample

#check_failure (fun (a b : Context registry) (x : a.Value) (y : b.Value) => a.equal x y)
#check_failure (fun (a b : Context registry) (x : a.Value) (y : b.Value) => a.compare x y)

end Hex.RealClosure.Tower.OrderTests
