/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerEnlarge
public import HexRealClosure.TowerCatalog

public section

namespace Hex.RealClosure.Tower.EnlargeOrder.Tests

private def registry : BaseContext.Registry := fun _ => none

private def require (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

private def check (context : Context registry) (positive : List context.Value) : IO Unit := by
  cases context.origin with
  | pack base suffix target_eq => exact do
    let some rebuilt := (Conversion.infinitesimal base).rebuild? suffix
      | throw (IO.userError "ordered enlargement rebuild failed")
    let conversion := rebuilt.result.cast target_eq
    let parameter := _root_.cast
      (congrArg Context.Value (rebuilt.result.cast_spec target_eq).1.symm)
      (rebuilt.parameter base)
    require (conversion.context.sign parameter == 1) "new native parameter is not positive"
    for a in positive do
      require (context.sign a == 1) "old test input is not positive"
      require (conversion.context.sign (parameter - conversion.value a) == -1)
        "new native parameter is not below the old positive value"
      require (conversion.context.sign (conversion.value a) == 1)
        "ordered enlargement changed the old sign"
    require (conversion.context.signature.base.infinitesimals ==
      context.signature.base.infinitesimals + 1) "enlargement lost its staged infinitesimal"
    require (conversion.context.signature.roots.length == context.signature.roots.length)
      "enlargement lost a root level"

private def run : IO Unit := do
  let base := Context.base (BaseContext.rational registry)
  check base [1]
  let two : base.Value := 1 + 1
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let some descriptor := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := x * x - DensePoly.C two,
        lower := .finite 1, upper := .finite two, indices := [], signs := [] }
    | throw (IO.userError "ordered enlargement first descriptor failed")
  let first := base.adjoin descriptor
  let alpha := first.generator
  check first.context [alpha, alpha - 1, alpha⁻¹]
  let y : DensePoly first.context.Value := DensePoly.ofCoeffs #[0, 1]
  let some next := SignDet.Descriptor.validate first.context.sign first.context.signature
      { context := first.context.signature, head := y * y - DensePoly.C alpha,
        lower := .finite 1, upper := .finite alpha, indices := [], signs := [] }
    | throw (IO.userError "ordered enlargement nested descriptor failed")
  let second := first.context.adjoin next
  let beta := second.generator
  check second.context [beta, beta - 1, beta⁻¹,
    second.embed alpha - beta, (second.embed alpha - beta)⁻¹]
  require (first.context.sign (alpha - 1) == 1) "old root context became invalid"
  IO.println "native new parameter is positive and below old nested-root values"

#eval run

end Hex.RealClosure.Tower.EnlargeOrder.Tests
