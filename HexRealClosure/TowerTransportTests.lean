/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerTransport
public import HexRealClosure.TowerSuffix
public import HexRealClosure.TowerEnlarge
public import HexRealClosure.TowerCatalog
public import HexRealClosure.TowerOrder
public meta import HexRealClosure.TowerTransport
public meta import HexRealClosure.TowerSuffix
public meta import HexRealClosure.TowerEnlarge
public meta import HexRealClosure.TowerCatalog
public meta import HexRealClosure.TowerOrder

namespace Hex.RealClosure.Tower.TransportTests
open SignDet

private def registry : BaseContext.Registry := fun _ => none

private def rebuildOrigin {target : Context registry} (origin : Origin target) : Bool := by
  cases origin with
  | pack base suffix eq =>
    exact ((Conversion.infinitesimal base).rebuild? suffix).isSome

private def sixteenth {E : Type} [Mul E] (x : E) : E :=
  let square := x * x
  let fourth := square * square
  let eighth := fourth * fourth
  eighth * eighth

/-- Adding an infinitesimal preserves an old base value, gives the new base
its own signature, and rejects its packet in the old context. -/
private def baseSample : Array Bool :=
  let old := Context.base (BaseContext.rational registry)
  let conversion := Conversion.infinitesimal (BaseContext.rational registry)
  let two : old.Value := 1 + 1
  let moved := conversion.value two
  let target := conversion.context
  let eps : target.Value := by
    change (Conversion.infinitesimal (BaseContext.rational registry)).context.Value
    rw [(Conversion.infinitesimal_spec (BaseContext.rational registry)).1]
    exact BaseContext.Element.infinitesimal (BaseContext.rational registry)
  #[decide (old.signature.base.infinitesimals = 0),
    decide (old.origin.length = 0),
    old.enlarge?.isSome,
    decide (target.signature.base.infinitesimals = 1),
    (target.enlarge?.map (fun next => next.context.signature.base.infinitesimals)) == some 2,
    target.equal moved (1 + 1),
    ((target.read (target.write moved)).toOption.map (target.equal moved)) == some true,
    decide (target.compare 0 eps = .lt),
    decide (target.compare eps (conversion.value 1) = .lt),
    (old.read (target.write moved)).toOption.isNone]

#guard baseSample == #[true, true, true, true, true, true, true, true, true, true]

/-- Revalidate one selected square root over the new rational-function base. -/
private def rootSample : Option (Array Bool) :=
  let base := Context.base (BaseContext.rational registry)
  let two : base.Value := 1 + 1
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let raw : RawDescriptor base.Value Signature :=
    { context := base.signature, head := x * x - DensePoly.C two,
      lower := .finite 1, upper := .finite two, indices := [], signs := [] }
  (Descriptor.validate base.sign base.signature raw).bind fun descriptor =>
  let original := base.adjoin descriptor
  let suffix : Suffix base := .root descriptor .nil
  let conversion := Conversion.infinitesimal (BaseContext.rational registry)
  (conversion.rebuild? suffix).map fun rebuilt =>
  let result := rebuilt.result
  let root := result.value original.generator
  let automatic := original.context.enlarge?
  let eps : conversion.context.Value := by
    change (Conversion.infinitesimal (BaseContext.rational registry)).context.Value
    rw [(Conversion.infinitesimal_spec (BaseContext.rational registry)).1]
    exact BaseContext.Element.infinitesimal (BaseContext.rational registry)
  let mixed := match rebuilt.suffix with
    | .root converted .nil =>
      let next := conversion.context.adjoin converted
      let raised := next.generator
      let epsRaised := next.embed eps
      #[decide (next.context.compare (raised + epsRaised) raised = .gt),
        decide (next.context.compare (raised - epsRaised) 1 = .gt)]
    | _ => #[false, false]
  #[result.context.equal (root * root) (result.value (original.embed two)),
    decide (original.context.origin.length = 1),
    rebuildOrigin original.context.origin,
    (automatic.map (fun conversion => conversion.context.signature)) ==
      some result.context.signature,
    (automatic.map (fun conversion =>
      let raised := conversion.value original.generator
      conversion.context.equal (raised * raised)
        (conversion.value (original.embed two)))) == some true,
    (automatic.map (fun conversion =>
      conversion.context.compare (conversion.value original.generator) 1)) == some .gt,
    (original.context.write (suffix.embed two)).value ==
      (original.context.write (original.embed two)).value,
    decide (result.context.compare root 1 = .gt),
    decide (result.context.compare root (1 + 1) = .lt),
    decide (result.context.signature.base.infinitesimals = 1),
    (result.context.read (result.context.write root)).toOption.isSome,
    (original.context.read (result.context.write root)).toOption.isNone] ++ mixed

#guard rootSample == some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true]

/-- Change the first root definition and rebuild three later square roots.
An embedded noncanonical one and an inverse retain their original meaning. -/
private def sample : Option (Array Bool) :=
  let base := Context.base (BaseContext.rational registry)
  let two : base.Value := 1 + 1
  let three : base.Value := two + 1
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let factor := x * x - DensePoly.C two
  let raw₁ : RawDescriptor base.Value Signature :=
    { context := base.signature, head := DensePoly.scale three (factor * (x - DensePoly.C three)),
      lower := .finite 1, upper := .finite two, indices := [], signs := [] }
  (Descriptor.validate base.sign base.signature raw₁).bind fun d₁ =>
  let first := base.adjoin d₁
  let alpha := first.generator
  let below := alpha - first.embed three
  let inverse := below⁻¹
  let one := below * inverse
  let raw₂ : RawDescriptor first.context.Value Signature :=
    { context := first.context.signature, head := DensePoly.ofCoeffs #[-alpha, 0, 1],
      lower := .finite 1, upper := .finite (1 + 1), indices := [1], signs := [1] }
  (Descriptor.validate first.context.sign first.context.signature raw₂).bind fun d₂ =>
  let second := first.context.adjoin d₂
  let raw₃ : RawDescriptor second.context.Value Signature :=
    { context := second.context.signature, head := DensePoly.ofCoeffs #[-second.generator, 0, 1],
      lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
  (Descriptor.validate second.context.sign second.context.signature raw₃).bind fun d₃ =>
  let third := second.context.adjoin d₃
  let raw₄ : RawDescriptor third.context.Value Signature :=
    { context := third.context.signature, head := DensePoly.ofCoeffs #[-third.generator, 0, 1],
      lower := .finite 1, upper := .finite (1 + 1), indices := [1], signs := [1] }
  (Descriptor.validate third.context.sign third.context.signature raw₄).bind fun d₄ =>
  let fourth := third.context.adjoin d₄
  let oldOne := fourth.embed (third.embed (second.embed one))
  let oldInverse := fourth.embed (third.embed (second.embed inverse))
  let oldBelow := fourth.embed (third.embed (second.embed below))
  let oldTwo := fourth.embed (third.embed (second.embed (first.embed two)))
  let suffix : Suffix first.context := .root d₂ (.root d₃ (.root d₄ .nil))
  ((d₁.buildReencoding factor (.finite 1) (.finite two)).toOption).bind fun result =>
  result.bind fun encoding =>
  let initial := Conversion.refine base encoding
  (initial.extend? suffix).map fun conversion =>
  let root := conversion.value fourth.generator
  let movedOne := conversion.value oldOne
  let packet := conversion.context.write movedOne
  #[decide (fourth.context.signature.roots.length = 4),
    decide (fourth.context.origin.length = 4),
    (fourth.context.write (suffix.embed (first.embed two))).value ==
      (fourth.context.write oldTwo).value,
    decide (conversion.context.signature.roots.length = 4),
    decide (fourth.context.signature ≠ conversion.context.signature),
    conversion.context.equal (sixteenth root) (conversion.value oldTwo),
    conversion.context.equal (root * root) (conversion.value (fourth.embed third.generator)),
    decide (conversion.context.compare root 1 = .gt),
    decide (oldOne ≠ 1), conversion.context.equal movedOne 1,
    conversion.context.equal (conversion.value oldBelow * conversion.value oldInverse) 1,
    decide (conversion.value (sixteenth fourth.generator - oldTwo) = 0),
    (conversion.context.read packet).toOption.isSome,
    (fourth.context.read packet).toOption.isNone,
    (fourth.context.read (fourth.context.write oldOne)).toOption.isSome]

#check_failure Conversion.mk

end Hex.RealClosure.Tower.TransportTests

/-- Run the full four-level fixture explicitly, outside routine CI elaboration. -/
public def main : IO Unit := do
  match Hex.RealClosure.Tower.TransportTests.sample with
  | none => throw (IO.userError "four-level conversion failed")
  | some checks =>
    if checks.all id then
      IO.println s!"four-level transport: {checks.size} checks passed"
    else throw (IO.userError s!"four-level transport checks failed: {checks}")
