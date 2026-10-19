/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseInclusion
public meta import HexRealClosure.BaseInclusion

public section

namespace Hex.RealClosure.Tower.BaseInclusionTests

private def registry : BaseContext.Registry := fun _ => none
private abbrev rational := BaseContext.rational registry
private abbrev first := rational.infinitesimal
private abbrev second := first.infinitesimal
private abbrev third := second.infinitesimal

private def require (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

def run : IO Unit := do
  let some inclusion := BaseInclusion.make? (.pack first) (.pack third)
    | throw (IO.userError "staged inclusion rejected compatible predecessors")
  let epsilon : (Context.ofBase (.pack first)).Value := BaseContext.Element.infinitesimal rational
  let delta : (Context.ofBase (.pack second)).Value := BaseContext.Element.infinitesimal first
  let eta : (Context.ofBase (.pack third)).Value := BaseContext.Element.infinitesimal second
  let expected : (Context.ofBase (.pack third)).Value := epsilon.embed.embed
  require (inclusion.value epsilon == expected)
    "base inclusion moved an old formal variable into the newest slot"
  let some middle := BaseInclusion.make? (.pack second) (.pack third)
    | throw (IO.userError "intermediate predecessor inclusion failed")
  require (middle.value delta == (show (Context.ofBase (.pack third)).Value from delta.embed)) "intermediate variable transport changed"
  let target := Context.ofBase (.pack third)
  require (target.sign (eta - middle.value delta) == -1 &&
    target.sign (middle.value delta - inclusion.value epsilon) == -1)
    "staged inclusion lost the strict infinitesimal order"
  let expression := (epsilon + (1 + 1)) / (epsilon - 1)
  require (inclusion.value expression == (expected + (1 + 1)) / (expected - 1))
    "base inclusion changed rational-function arithmetic"
  require (inclusion.value (0⁻¹) == 0 &&
    inclusion.value (expression⁻¹) == (inclusion.value expression)⁻¹)
    "base inclusion changed totalized inversion"
  require ((BaseInclusion.make? (.pack second) (.pack first)).isNone)
    "base inclusion accepted decreasing infinitesimal depth"

end Hex.RealClosure.Tower.BaseInclusionTests

#eval Hex.RealClosure.Tower.BaseInclusionTests.run
