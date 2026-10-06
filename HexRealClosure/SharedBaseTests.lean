/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SharedBase
public import HexRealClosure.TowerOrder
public meta import HexRealClosure.SharedBase

public section
namespace Hex.RealClosure.Tower.SharedBaseTests
private def registry : BaseContext.Registry := fun _ => none
private abbrev rational := BaseContext.rational registry
private abbrev first := rational.infinitesimal
private abbrev third := first.infinitesimal.infinitesimal

private def require (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

def run : IO Unit := do
  let catalog := BaseContext.Catalog.empty registry
  let sources : List (BaseContext.PackedContext registry) := [.pack first, .pack third, .pack rational]
  let some selected := SharedBase.choose? catalog sources
    | throw (IO.userError "automatic staged base selection failed")
  require (selected.target.signature.constants.isEmpty && selected.target.depth == 3)
    "automatic base selection changed the real prefix or infinitesimal depth"
  let inclusion := selected.inclusion (.pack first) (List.mem_cons_self)
  let epsilon : (Context.ofBase (.pack first)).Value := BaseContext.Element.infinitesimal rational
  require ((Context.ofBase selected.target).sign (inclusion.value epsilon) == 1)
    "selected inclusion lost the original infinitesimal sign"
  let old := Context.ofBase (.pack first)
  let latest := Context.ofBase (.pack third)
  let eta : latest.Value := BaseContext.Element.infinitesimal first.infinitesimal
  let request : Live.Request registry :=
    [⟨old, { values := [epsilon], polynomials := [DensePoly.ofCoeffs #[epsilon, 1]] }⟩,
      ⟨latest, { values := [eta] }⟩]
  let some result := request.gatherFrom? catalog
    | throw (IO.userError "automatic live request gathering failed")
  let target := result.2.shared.input.context
  require (result.1.depth == 3 && result.2.frames.length == 2)
    "automatic gathering changed the selected depth or owner order"
  let some originalFrame := result.2.frames[0]? | throw (IO.userError "first frame missing")
  let some latestFrame := result.2.frames[1]? | throw (IO.userError "last frame missing")
  let some a := originalFrame.values[0]? | throw (IO.userError "old infinitesimal missing")
  let some b := latestFrame.values[0]? | throw (IO.userError "new infinitesimal missing")
  require (target.sign a == 1 && target.sign b == 1 && target.sign (b-a) == -1)
    "automatic gathering changed the original infinitesimal variables or order"
  let some polynomial := originalFrame.polynomials[0]? | throw (IO.userError "live polynomial missing")
  require (target.equal (polynomial.eval 0) a && target.equal (polynomial.eval 1) (a+1))
    "automatic gathering changed the requested polynomial coefficients"
  let base := Context.base rational
  let x : base.Poly := DensePoly.ofCoeffs #[0, 1]
  let some descriptor := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := x*x - DensePoly.C (1+1),
        lower := .finite 1, upper := .finite (1+1), indices := [], signs := [] }
    | throw (IO.userError "rational selected root construction failed")
  let root := Root.ofSelection base (.selected descriptor)
  let some roots := (Live.rootRequest root).gatherFrom? catalog
    | throw (IO.userError "automatic selected-root gathering failed")
  require (roots.2.frames.length == 2 && roots.2.shared.input.context.signature.roots.length == 1)
    "automatic root gathering changed its descriptor or generator dependency"
  let some generatorFrame := roots.2.frames[1]? | throw (IO.userError "root generator frame missing")
  let some generator := generatorFrame.values[0]? | throw (IO.userError "root generator missing")
  let rootTarget := roots.2.shared.input.context
  require (rootTarget.sign generator == 1 && rootTarget.equal (generator*generator) (1+1))
    "automatic root gathering changed the selected root or defining equation"

end Hex.RealClosure.Tower.SharedBaseTests
#eval Hex.RealClosure.Tower.SharedBaseTests.run
