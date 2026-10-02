/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.FrameFormat
public import HexRealClosure.TowerOrder
public import HexRealClosure.Yun
public meta import HexRealClosure.FrameFormat
public meta import HexRealClosure.TowerOrder
public meta import HexRealClosure.Yun

namespace Hex.RealClosure.Tower.YunTests
open SignDet

private def registry : BaseContext.Registry := fun _ => none

/-- A repeated nonmonic input with coefficients in two actual native root
levels, including a noncanonical representative of one. -/
private def sample : Option (Array Bool) :=
  let base := Context.base (BaseContext.rational registry)
  let two : base.Value := 1 + 1
  let raw : RawDescriptor base.Value Signature :=
    { context := base.signature, head := DensePoly.ofCoeffs #[-two, 0, 1],
      lower := .finite 1, upper := .finite two, indices := [], signs := [] }
  (Descriptor.validate base.sign base.signature raw).bind fun d₁ =>
  let first := base.adjoin d₁
  let a := first.generator
  let raw₂ : RawDescriptor first.context.Value Signature :=
    { context := first.context.signature, head := DensePoly.scale (1 + 1) (DensePoly.ofCoeffs #[-a, 0, 1]),
      lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
  (Descriptor.validate first.context.sign first.context.signature raw₂).bind fun d₂ =>
  let second := first.context.adjoin d₂
  let b := second.generator
  let divisor := b - second.embed (first.embed (two + 1))
  let one := divisor / divisor
  let y : DensePoly second.context.Value := DensePoly.ofCoeffs #[0, one]
  let linear := y - DensePoly.C b
  let p := DensePoly.scale (1 + 1) (linear * linear * linear)
  match Yun.decomposeRaw p with
  | .zero => none
  | .factors unit entries =>
    if h : entries.size = 1 then
      let e := entries[0]'(by omega)
      let checks := #[second.context.equal unit (1 + 1), decide (e.2 = 3),
        decide (e.1.natDegree = 1), second.context.equal (e.1.eval b) 0,
        second.context.equal e.1.leadingCoeff 1, decide (one ≠ 1),
        second.context.equal one 1]
      let other := y - DensePoly.C (second.embed a)
      match Yun.decomposeRaw (linear * linear * linear * other) with
      | .zero => none
      | .factors unit₂ entries₂ =>
        if h₂ : entries₂.size = 2 then
          let firstFactor := entries₂[0]'(by omega)
          let secondFactor := entries₂[1]'(by omega)
          some (checks ++ #[second.context.equal unit₂ 1,
            decide (firstFactor.2 = 1), decide (secondFactor.2 = 3),
            decide (firstFactor.1.natDegree = 1 ∧ secondFactor.1.natDegree = 1),
            second.context.equal (firstFactor.1.eval (second.embed a)) 0,
            second.context.equal (secondFactor.1.eval b) 0,
            decide ((DensePoly.gcd firstFactor.1 secondFactor.1).natDegree = 0)])
        else none
    else none

/-- info: some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample

end Hex.RealClosure.Tower.YunTests
