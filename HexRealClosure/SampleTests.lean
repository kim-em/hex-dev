/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Sample

namespace Hex.RealClosure.Tower.Sample.Tests

private def registry : BaseContext.Registry := fun _ => none
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def run : IO Unit := do
  let base := Context.base (BaseContext.rational registry)
  let x : base.Poly := DensePoly.ofCoeffs #[0, 1]
  let quadratic := x * x - DensePoly.C (1 + 1)
  let qs := [quadratic, 0]
  let family := partition base qs
  require (family.sections.length == 2 && family.sectors.length == 3) "wrong quadratic cell counts"
  require (family.sections.map (fun s => s.signs qs) == [[0, 0], [0, 0]]) "wrong section signs"
  require (family.sectors.map (fun s => s.signs qs) == [[1, 0], [-1, 0], [1, 0]]) "wrong sector signs"
  for s in family.sections ++ family.sectors do
    require (s.cell.contains s.value) "sample is outside its own cell"
  require (family.sector? 3).isNone "invalid sector index accepted"
  let wholeQs := [DensePoly.C (1 + 1 : base.Value), 0]
  let whole := partition base wholeQs
  require (whole.sections.isEmpty && whole.sectors.length == 1) "root-free family has boundaries"
  require (whole.sectors.map (fun s => s.signs wholeQs) == [[1, 0]]) "wrong whole-line signs"
  let staged := (BaseContext.rational registry).infinitesimal
  let inf := Context.base staged
  let epsilon : inf.Value := BaseContext.Element.infinitesimal (BaseContext.rational registry)
  let y : inf.Poly := DensePoly.ofCoeffs #[0, 1]
  let close := (y - DensePoly.C epsilon) * (y - DensePoly.C (epsilon + epsilon))
  let closeFamily := partition inf [close]
  require (closeFamily.sections.length == 2 && closeFamily.sectors.length == 3)
    "infinitesimal root family has wrong cell counts"
  require (closeFamily.sectors.map (fun s => s.signs [close]) == [[1], [-1], [1]])
    "wrong infinitesimal sector signs"
  for s in closeFamily.sections ++ closeFamily.sectors do
    require (s.cell.contains s.value) "infinitesimal sample is outside its cell"
  IO.println "native section and sector samples passed"

#eval run

end Hex.RealClosure.Tower.Sample.Tests
