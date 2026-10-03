/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerPresentation
public import HexRealClosure.TowerOrder
public import HexRealClosure.TowerCatalog
public meta import HexRealClosure.TowerPresentation
public meta import HexRealClosure.TowerOrder
public meta import HexRealClosure.TowerCatalog

namespace Hex.RealClosure.Tower.PresentationTests
open SignDet

private def registry : BaseContext.Registry := fun _ => none

/-- Refine the second root in a three-level tower and reconstruct its later
dependent root. The original prefix remains, and the returned native value
retains its equation, order and inverse while rejecting the old packet. -/
private def sample : Option (Array Bool) := do
  let base := Context.base (BaseContext.rational registry)
  let two : base.Value := 1 + 1
  let before ← Descriptor.validate base.sign base.signature
    { context := base.signature, head := DensePoly.ofCoeffs #[-1, 1],
      lower := .finite 0, upper := .finite two, indices := [], signs := [] }
  let first : Suffix base := .root before .nil
  let parent := first.context
  let two : parent.Value := 1 + 1
  let three : parent.Value := two + 1
  let x : DensePoly parent.Value := DensePoly.ofCoeffs #[0, 1]
  let factor := x * x - DensePoly.C two
  let middle ← Descriptor.validate parent.sign parent.signature
    { context := parent.signature, head := DensePoly.scale three (factor * (x - DensePoly.C three)),
      lower := .finite 1, upper := .finite two, indices := [], signs := [] }
  let extension := parent.adjoin middle
  let last ← Descriptor.validate extension.context.sign extension.context.signature
    { context := extension.context.signature, head := DensePoly.ofCoeffs #[-extension.generator, 1],
      lower := .finite 1, upper := .finite (1 + 1), indices := [1], signs := [1] }
  let later : Suffix extension.context := .root last .nil
  let old := extension.context.adjoin last
  let some encoding ← (middle.buildReencoding factor (.finite 1) (.finite two)).toOption
    | none
  (Presentation.refine? first encoding later old.generator).map fun result =>
  let target := result.suffix.context
  let value := result.value
  #[decide (result.suffix.length = 3),
    decide (target.signature.roots.length = 3),
    decide (target.signature.roots.take 1 = old.context.signature.roots.take 1),
    decide (target.signature ≠ old.context.signature),
    target.equal (value * value) (1 + 1),
    decide (target.compare 1 value = .lt),
    decide (target.compare value (1 + 1) = .lt),
    target.equal (value * value⁻¹) 1,
    (target.read (old.context.write old.generator)).toOption.isNone]

/-- info: some #[true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample

end Hex.RealClosure.Tower.PresentationTests
