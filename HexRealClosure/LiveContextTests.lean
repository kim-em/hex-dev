/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.LiveContext
public import HexRealClosure.TowerOrder
public meta import HexRealClosure.LiveContext

public section

namespace Hex.RealClosure.Tower.LiveTests

private def registry : BaseContext.Registry := fun _ => none
private abbrev rational := BaseContext.rational registry
private abbrev first := rational.infinitesimal
private abbrev second := first.infinitesimal

private def require (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

def run : IO Unit := do
  let base := Context.base rational
  let two : base.Value := 1 + 1
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let some descriptor := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := x * x - DensePoly.C two,
        lower := .finite 1, upper := .finite two, indices := [], signs := [] }
    | throw (IO.userError "rational selected root failed")
  let extension := base.adjoin descriptor
  let alpha := extension.generator
  let epsilon : (Context.base first).Value := BaseContext.Element.infinitesimal rational
  let delta : (Context.base second).Value := BaseContext.Element.infinitesimal first
  let owners := [extension.context, Context.base first, Context.base second]
  let some shared := Shared.gather? (.pack second) owners
    | throw (IO.userError "compatible live-context assembly failed")
  require (shared.input.context.signature.roots.length == 1)
    "registration duplicated the selected root"
  let a := shared.value 0 alpha
  let e := shared.value 1 epsilon
  let d := shared.value 2 delta
  require (shared.input.context.equal (a * a) (1 + 1)) "shared root equation failed"
  require (shared.input.context.sign a == 1 && shared.input.context.sign e == 1 &&
    shared.input.context.sign d == 1) "shared positive values changed signs"
  require (shared.input.context.compare d e == .lt &&
    shared.input.context.compare e a == .lt) "staged inclusions lost strict order"
  let old : DensePoly extension.context.Value := DensePoly.ofCoeffs #[-alpha, 1]
  require (shared.input.context.equal ((shared.polynomial 0 old).eval a) 0)
    "live polynomial coefficients were not transported together"
  require ((Inclusion.base? (.pack second) (.pack first)).isNone)
    "decreasing infinitesimal depth was accepted"
  require (extension.context.equal (alpha * alpha) (1 + 1))
    "original root context no longer works"
  let some enlarged := shared.enlarge?
    | throw (IO.userError "shared-context enlargement failed")
  let next := enlarged.shared
  require (next.input.context.signature.roots.length == 1)
    "enlargement duplicated an algebraic dependency"
  let some sameTarget := next.add? next.input.context
    | throw (IO.userError "enlarged shared-target registration failed")
  require (sameTarget.input.context.signature.roots.length == 1)
    "registration duplicated the enlarged shared target"
  let a' := next.value 0 alpha
  let e' := next.value 1 epsilon
  let d' := next.value 2 delta
  let t := enlarged.parameter
  require (next.input.context.equal (a' * a') (1 + 1))
    "enlargement changed the original root equation"
  require (next.input.context.sign t == 1 &&
    next.input.context.compare t d' == .lt &&
    next.input.context.compare d' e' == .lt &&
    next.input.context.compare e' a' == .lt)
    "shared enlargement lost the infinitesimal order"
  require (next.input.context.equal (enlarged.previous.value a) a' &&
    next.input.context.equal (enlarged.previous.value e) e' &&
    next.input.context.equal (enlarged.previous.value d) d')
    "original-owner maps disagree with the shared-context inclusion"
  require (next.input.context.equal ((next.polynomial 0 old).eval a') 0)
    "enlargement did not transport the live polynomial"
  require (shared.input.context.equal (a * a) (1 + 1))
    "previous shared context no longer works"
  require (match next.input.context.read (shared.input.context.write a) with
    | .error _ => true | .ok _ => false)
    "enlargement accepted a stale serialized value"
  require (match next.input.context.readPoly (shared.input.context.writePoly
    (shared.polynomial 0 old)) with | .error _ => true | .ok _ => false)
    "enlargement accepted a stale serialized polynomial"
  let y : DensePoly extension.context.Value := DensePoly.ofCoeffs #[0, 1]
  let some dependent := SignDet.Descriptor.validate extension.context.sign
      extension.context.signature
      { context := extension.context.signature, head := y * y - DensePoly.C alpha,
        lower := .finite 0, upper := .finite (1 + 1), indices := [], signs := [] }
    | throw (IO.userError "dependent live-root descriptor failed")
  let child := extension.context.adjoin dependent
  let some registered := next.add? child.context
    | throw (IO.userError "dependent root registration after enlargement failed")
  require (registered.input.context.signature.roots.length == 2)
    "parent/child registration duplicated their common root"
  let retained := registered.value ⟨0, by simp [owners]⟩ alpha
  let b := registered.value ⟨3, by simp [owners]⟩ child.generator
  require (registered.input.context.equal (b * b) retained)
    "registered root did not retain its transported coefficient dependency"
  require (registered.input.context.sign b == 1)
    "registration selected a different dependent root"
  let some reversed := Shared.gather? (.pack rational) [child.context, extension.context]
    | throw (IO.userError "child/parent registration failed")
  require (reversed.input.context.signature.roots.length == 2)
    "child/parent registration did not reuse the cached predecessor"
  let some repeated := reversed.add? child.context
    | throw (IO.userError "repeated owner registration failed")
  require (repeated.input.context.signature.roots.length == 2)
    "repeated owner registration adjoined its roots again"
  let some siblingDescriptor := SignDet.Descriptor.validate extension.context.sign
      extension.context.signature
      { context := extension.context.signature, head := y * y - DensePoly.C (alpha + 1),
        lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
    | throw (IO.userError "sibling live-root descriptor failed")
  let sibling := extension.context.adjoin siblingDescriptor
  let some branches := Shared.gather? (.pack rational) [child.context, sibling.context]
    | throw (IO.userError "sibling registration failed")
  require (branches.input.context.signature.roots.length == 3)
    "sibling registration duplicated their common ancestor"
  let alpha' := branches.value 0 (child.embed alpha)
  let siblingRoot := branches.value 1 sibling.generator
  require (branches.input.context.equal (siblingRoot * siblingRoot) (alpha' + 1))
    "sibling root lost its common coefficient dependency"
  require ((shared.add? (Context.base second.infinitesimal)).isNone)
    "registration accepted an original base deeper than the declared target"
  let some sameOriginalTarget := shared.add? shared.input.context
    | throw (IO.userError "shared-target registration failed")
  require (sameOriginalTarget.input.context.signature.roots.length == 1)
    "registration duplicated the shared target"
  let some enlargedOwner := extension.context.enlarge?
    | throw (IO.userError "original owner enlargement failed")
  let some mixedOwners := Shared.gather? (.pack first)
      [extension.context, enlargedOwner.context]
    | throw (IO.userError "original/enlarged owner registration failed")
  require (mixedOwners.input.context.signature.roots.length == 1)
    "registration duplicated an owner and its exact enlarged target"
  let z : DensePoly next.input.context.Value := DensePoly.ofCoeffs #[0, 1]
  let some newDescriptor := SignDet.Descriptor.validate next.input.context.sign
      next.input.context.signature
      { context := next.input.context.signature, head := z * z - DensePoly.C a',
        lower := .finite 0, upper := .finite (1 + 1), indices := [], signs := [] }
    | throw (IO.userError "root over enlarged shared target failed")
  let newChild := next.input.context.adjoin newDescriptor
  let some derived := next.add? newChild.context
    | throw (IO.userError "registration of derived shared-target context failed")
  require (derived.input.context.signature.roots.length == 2)
    "derived shared-target registration duplicated an ancestor"

end Hex.RealClosure.Tower.LiveTests

#eval Hex.RealClosure.Tower.LiveTests.run
