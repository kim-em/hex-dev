/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerInclusion
public meta import HexRealClosure.TowerInclusion

public section

namespace Hex.RealClosure.Tower.BaseReconciliationTests

private def registry : BaseContext.Registry := fun _ => none
private abbrev rational := BaseContext.rational registry
private abbrev first := rational.infinitesimal
private abbrev second := first.infinitesimal
private abbrev third := second.infinitesimal

private def require (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

def run : IO Unit := do
  let some map := BaseReconciliation.make? (.pack first) (.pack third)
    | throw (IO.userError "nominal reconciliation rejected a staged inclusion")
  let epsilon : (Context.ofBase (.pack first)).Value := BaseContext.Element.infinitesimal rational
  let expected : (Context.ofBase (.pack third)).Value := epsilon.embed.embed
  require (map.value epsilon == expected) "nominal reconciliation changed the original variable"
  let conversion := Conversion.reconcileBase map
  let fixed : Inclusion (Context.ofBase (.pack first)) (Context.ofBase (.pack third)) :=
    ⟨conversion, (Conversion.reconcileBase_spec map).1⟩
  require (fixed.value epsilon == expected) "fixed-owner reconciliation changed the cached map"
  let some inclusion := Inclusion.reconcileBase? (.pack first) (.pack third)
    | throw (IO.userError "tower reconciliation rejected a staged inclusion")
  let expression := (epsilon + (1 + 1)) / (epsilon - 1)
  require (inclusion.value expression == (expected + (1 + 1)) / (expected - 1))
    "tower reconciliation changed fraction arithmetic"
  let polynomial : (Context.ofBase (.pack first)).Poly := DensePoly.ofCoeffs #[expression, epsilon, 1]
  let mapped := inclusion.polynomial polynomial
  require (mapped.coeff 0 == inclusion.value expression && mapped.coeff 1 == expected && mapped.coeff 2 == 1)
    "tower reconciliation changed polynomial coefficient ownership"
  require (inclusion.value (0⁻¹) == 0 &&
    inclusion.value (expression⁻¹) == (inclusion.value expression)⁻¹)
    "tower reconciliation changed totalized inversion"
  require ((Inclusion.reconcileBase? (.pack third) (.pack first)).isNone)
    "tower reconciliation accepted decreasing infinitesimal depth"

end Hex.RealClosure.Tower.BaseReconciliationTests

#eval Hex.RealClosure.Tower.BaseReconciliationTests.run
