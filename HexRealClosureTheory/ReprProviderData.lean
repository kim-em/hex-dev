/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.BaseContext
public import HexOrderedFnTheory.LiouvilleTests
public import HexRealClosure.TowerRepr
public import HexRealClosure.TowerEnlarge

public section

namespace Hex.RealClosure.Tower.ReprProviderData

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat

def key (version : Nat) : BaseContext.ConstantKey := ⟨"liouville", version⟩

def registry : BaseContext.Registry := fun k =>
  if k.name = "liouville" then some OrderedFn.LiouvilleTests.provider else none

private theorem present (version : Nat) : (registry (key version)).isSome = true := by
  simp [registry, key]

private abbrev rational := BaseContext.RealContext.rational registry

private theorem source_correct (version : Nat) :
    OrderedFn.Oracle.ApproximationCorrect (Rat.castHom ℝ) (liouvilleNumber 2)
      (rational.source (key version) (present version)) := by
  change OrderedFn.Oracle.ApproximationCorrect (Rat.castHom ℝ) (liouvilleNumber 2)
    OrderedFn.LiouvilleTests.source
  exact OrderedFn.LiouvilleTests.source_correct

private theorem valid (version : Nat) :
    OrderedFn.Real.Valid (rational.source (key version) (present version)) :=
  ⟨Rat.castHom ℝ, liouvilleNumber 2, source_correct version,
    OrderedFn.LiouvilleTests.source_width, OrderedFn.LiouvilleTests.transcendence⟩

/-- The existing test provider registered with its proved approximation laws. -/
private def registered (version : Nat) :=
  rational.register HexRationalFnTheory.ratField_eq (key version) (present version) (valid version)

def entry (version : Nat) : BaseContext.RealPrefix registry := .pack (registered version)

def baseCatalog (version : Nat) : BaseContext.Catalog registry :=
  ((BaseContext.Catalog.empty registry).insert (entry version)).getD
    (BaseContext.Catalog.empty registry)

/-- Only the validated real prefix is installed; algebraic suffixes are read afresh. -/
def catalog (version : Nat) : Catalog registry := .ofBase (baseCatalog version)

def emptyCatalog : Catalog registry := .ofBase (BaseContext.Catalog.empty registry)

private abbrev native := BaseContext.Context.real (registered 1)
private def initial : Context registry := .base native.infinitesimal
private def coefficient : initial.Value :=
  (⟨RationalFn.X⟩ : BaseContext.Element native).embed
private def epsilon : initial.Value := BaseContext.Element.infinitesimal native

structure Samples where
  element : PackedElement registry
  polynomial : PackedPolynomial registry
  root : PackedRoot registry
  roots : PackedRootSet registry

/-- Select a root over a registered real and an infinitesimal, then rebuild
that algebraic suffix over a second infinitesimal before printing its values. -/
def samples : Except String Samples := do
  let x : initial.Poly := DensePoly.ofList [0, 1]
  let subject := coefficient + epsilon
  let polynomial := x * x - DensePoly.C subject
  let some descriptor := SignDet.Descriptor.validate initial.sign initial.signature
      { context := initial.signature, head := polynomial,
        lower := .negInf, upper := .posInf, indices := [1], signs := [1] }
    | throw "registered-provider selected root failed"
  let extension := initial.adjoin descriptor
  let roots := initial.roots polynomial
  match roots with
  | .all => throw "registered-provider polynomial lost its finite roots"
  | .finite entries =>
    unless entries.length == 2 do throw "registered-provider polynomial lost a root"
  let some conversion := extension.context.enlarge?
    | throw "registered-provider algebraic enlargement failed"
  let generator := conversion.value extension.generator
  let inherited := conversion.value (extension.embed coefficient)
  let defining := conversion.value (extension.embed subject)
  unless conversion.context.sign (generator * generator - defining) == 0 do
    throw "registered-provider enlargement changed the selected equation"
  unless conversion.context.sign generator == 1 do
    throw "registered-provider enlargement changed the selected positive root"
  let signature := conversion.context.signature
  unless signature.base.constants == [key 1] && signature.base.infinitesimals == 2 &&
      signature.roots.length == 1 do
    throw "registered-provider enlargement changed its source bindings"
  let y : conversion.context.Poly := DensePoly.ofList [0, 1]
  let retained := y - DensePoly.C generator
  let some selected := SignDet.Descriptor.validate conversion.context.sign signature
      { context := signature, head := retained,
        lower := .negInf, upper := .posInf, indices := [1], signs := [1] }
    | throw "registered-provider root over the rebuilt predecessor failed"
  let child := conversion.context.adjoin selected
  let refreshedRoots := conversion.context.roots retained
  match refreshedRoots with
  | .all => throw "registered-provider linear polynomial lost its finite root"
  | .finite entries =>
    unless entries.length == 1 do throw "registered-provider linear polynomial changed its root count"
  return {
    element := ⟨conversion.context, generator + inherited⟩
    polynomial := ⟨conversion.context, DensePoly.ofList [-generator, inherited, 1]⟩
    root := ⟨conversion.context, .selected selected child rfl⟩
    roots := ⟨conversion.context, refreshedRoots⟩ }

end Hex.RealClosure.Tower.ReprProviderData

/-- info: 'Hex.RealClosure.Tower.ReprProviderData.entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.ReprProviderData.entry
