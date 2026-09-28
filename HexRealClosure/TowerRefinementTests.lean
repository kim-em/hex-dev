/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerRefinement
public import HexRealClosure.TowerCatalog
public import HexRealClosure.TowerOrder
public meta import HexRealClosure.TowerRefinement
public meta import HexRealClosure.TowerCatalog
public meta import HexRealClosure.TowerOrder

namespace Hex.RealClosure.Tower.RefinementTests
open SignDet

private def registry : BaseContext.Registry := fun _ => none

/-- Change a nonmonic reducible definition over an actual algebraic predecessor
while retaining the selected root, inverse, noncanonical one and polynomials. -/
private def sample : Option (Array Bool) :=
  let base := Context.base (BaseContext.rational registry)
  let two : base.Value := 1 + 1
  let raw₁ : RawDescriptor base.Value Signature :=
    { context := base.signature, head := DensePoly.ofCoeffs #[-two, 0, 1],
      lower := .finite 1, upper := .finite two, indices := [], signs := [] }
  (Descriptor.validate base.sign base.signature raw₁).bind fun d₁ =>
  let first := base.adjoin d₁
  let alpha := first.generator
  let three : first.context.Value := 1 + 1 + 1
  let x : DensePoly first.context.Value := DensePoly.ofCoeffs #[0, 1]
  let cofactor := DensePoly.ofCoeffs #[-alpha, 0, 1]
  let raw₂ : RawDescriptor first.context.Value Signature :=
    { context := first.context.signature,
      head := DensePoly.scale three (cofactor * (x - DensePoly.C three)),
      lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
  (Descriptor.validate first.context.sign first.context.signature raw₂).bind fun source =>
  let old := first.context.adjoin source
  let beta := old.generator
  let below := beta - old.embed three
  let inverse := below⁻¹
  let semanticOne := below * inverse
  let zero := beta * beta - old.embed alpha
  ((source.buildReencoding cofactor (.finite 1) (.finite (1 + 1))).toOption).bind fun result =>
  result.bind fun encoding =>
  let refinement := first.context.refine encoding
  let next := refinement.extension.context
  let newBeta := refinement.transport beta
  let newBelow := refinement.transport below
  let newInverse := refinement.transport inverse
  let p : DensePoly old.context.Value :=
    DensePoly.ofCoeffs #[beta * below, -(beta + below), semanticOne]
  let converted := refinement.mapPoly p
  let oldPacket := old.context.write semanticOne
  let newPacket := next.write (refinement.transport semanticOne)
  let raw₃ : RawDescriptor old.context.Value Signature :=
    { context := old.context.signature, head := DensePoly.ofCoeffs #[-beta, 0, 1],
      lower := .finite 1, upper := .finite (1 + 1), indices := [1], signs := [1] }
  (Descriptor.validate old.context.sign old.context.signature raw₃).bind fun later =>
  (refinement.mapDescriptor? later).map fun convertedLater =>
  let oldThird := old.context.adjoin later
  let third := next.adjoin convertedLater
  let laterInverse := (oldThird.generator - oldThird.embed beta)⁻¹
  let movedInverse := refinement.mapValue later convertedLater laterInverse
  let stale := { refinement.mapRaw later with context := old.context.signature }
  #[
    decide (old.context.signature ≠ next.signature),
    next.equal (newBeta * newBeta) (refinement.extension.embed alpha),
    next.equal (newBelow * newInverse) 1,
    decide (semanticOne ≠ 1), next.equal (refinement.transport semanticOne) 1,
    decide (zero = 0), decide (refinement.transport zero = 0),
    decide (converted.natDegree = p.natDegree),
    next.equal (converted.eval newBeta) 0,
    decide (old.context.compare beta (old.embed three) = .lt),
    decide (next.compare newBeta (refinement.extension.embed three) = .lt),
    (old.context.read oldPacket).toOption.isSome,
    (next.read oldPacket).toOption.isNone,
    (next.read newPacket).toOption.isSome,
    next.equal newBeta refinement.extension.generator,
    decide (convertedLater.raw.context = next.signature),
    (Descriptor.validate next.sign next.signature stale).isNone,
    third.context.equal (third.generator * third.generator) (third.embed newBeta),
    third.context.equal
      ((third.generator - third.embed newBeta) * movedInverse) 1]

/--
info: some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
-/
#guard_msgs in
#eval sample

#check_failure Refinement.mk

end Hex.RealClosure.Tower.RefinementTests
