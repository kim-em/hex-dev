/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootCollection
public import HexRealClosure.TowerCatalog

public section

namespace Hex.RealClosure.Tower.Collection.Tests

private def registry : BaseContext.Registry := fun _ => none

private def require (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

private def selected (parent : Context registry) (p : DensePoly parent.Value)
    (lower upper : parent.Value) : Option (Root parent) :=
  match SignDet.Descriptor.validate parent.sign parent.signature
      { context := parent.signature, head := p, lower := .finite lower,
        upper := .finite upper, indices := [], signs := [] } with
  | none => none
  | some descriptor => some (Root.ofSelection parent (.selected descriptor))

private def run : IO Unit := do
  let base := Context.base (BaseContext.rational registry)
  let two : base.Value := 1 + 1
  let three : base.Value := two + 1
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let some alpha := selected base (x * x - DensePoly.C two) 1 two
    | throw (IO.userError "first collection descriptor rejected")
  let some beta := selected base (DensePoly.scale three (x * x - DensePoly.C three)) 1 two
    | throw (IO.userError "nonmonic collection descriptor rejected")
  let some collection := base.collect? [alpha, .point 0, beta]
    | throw (IO.userError "collection failed")
  let [first, zero, last] := collection.entries
    | throw (IO.userError "collection changed input length")
  let shared := collection.input.context
  let a := first.value
  let b := last.value
  require (shared.sign (a * a - collection.input.value two) == 0)
    "first root equation changed after later nonlinear transport"
  require (shared.sign (b * b - collection.input.value three) == 0)
    "nonmonic last root equation changed"
  require (shared.sign zero.value == 0) "coefficient point changed"
  require (shared.sign a == 1 && shared.sign b == 1 && shared.sign (b - a) == 1)
    "shared root ordering changed"
  let sum := a + b
  let ten : shared.Value := NatCast.natCast 10
  require (shared.sign (sum * sum * sum * sum - ten * sum * sum + 1) == 0)
    "mixed-field arithmetic failed"
  require (shared.sign (sum * sum⁻¹ - 1) == 0) "shared-context inversion failed"
  for entry in collection.entries do
    let old := entry.source.context
    let value := entry.source.value
    require (shared.sign (entry.apply (value * value) - entry.value * entry.value) == 0)
      "whole old-context multiplication changed"
    require (shared.sign (entry.apply ((value - 1)⁻¹) * (entry.value - 1) - 1) == 0)
      "old-context inverse did not survive transport"
    require (old.sign value == shared.sign entry.value) "old context became invalid"
  require (alpha.context.sign (alpha.value * alpha.value - alpha.embed two) == 0)
    "original root handle became invalid"
  require (match shared.read (beta.context.write beta.value) with
    | .error _ => true
    | .ok _ => false) "old root evidence entered the shared context without conversion"
  let .ok restored := alpha.context.read (alpha.context.write alpha.value)
    | throw (IO.userError "old context reader stopped accepting its value")
  require (alpha.context.sign (restored - alpha.value) == 0) "old context reader changed its value"
  IO.println "common root contexts, nonlinear transport and mixed arithmetic checks passed"

#eval run

end Hex.RealClosure.Tower.Collection.Tests
