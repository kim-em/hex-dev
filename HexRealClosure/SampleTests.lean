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
  let linear := x - DensePoly.C (1 : base.Value)
  let duplicates := [linear, x * x - DensePoly.C (1 : base.Value), linear * linear]
  let duplicateFamily := partition base duplicates
  require (duplicateFamily.sections.length == 2 && duplicateFamily.sectors.length == 3)
    "equal or repeated roots were retained as separate boundaries"
  require (duplicateFamily.sections.map (fun s => s.signs duplicates) == [[-1, 0, 1], [0, 0, 0]])
    "wrong repeated-root section signs"
  require (duplicateFamily.sectors.map (fun s => s.signs duplicates) ==
    [[-1, 1, 1], [-1, -1, 1], [1, 1, 1]]) "wrong duplicate-family sector signs"
  let cubicQs := [x * (x * x - DensePoly.C (1 : base.Value))]
  let boundedFamily := partition base cubicQs
  let lower := boundedFamily.collection.input.value (-1)
  let middle := boundedFamily.collection.input.value 0
  let upper := boundedFamily.collection.input.value 1
  require (boundedFamily.sectorBetween? (.finite lower) (.finite upper)).isNone
    "non-adjacent boundaries accepted"
  require (boundedFamily.sectorBetween? (.finite upper) (.finite lower)).isNone
    "reversed sector boundaries accepted"
  let some boundedSample := boundedFamily.sectorBetween? (.finite middle) (.finite upper)
    | throw (IO.userError "adjacent sector boundaries rejected")
  require (boundedSample.cell.contains boundedSample.value && boundedSample.signs cubicQs == [-1])
    "wrong requested bounded-sector sample"
  require (boundedFamily.sectorBetween? .negInf (.finite lower)).isSome
    "left ray request rejected"
  require (boundedFamily.sectorBetween? (.finite upper) .posInf).isSome
    "right ray request rejected"
  let some descriptor := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := quadratic,
        lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
    | throw (IO.userError "sample section descriptor failed")
  let selected := Tower.Sample.section base descriptor
  require (selected.cell.contains selected.value && selected.signs [quadratic, x] == [0, 1])
    "selected section lost membership or its input coefficients"
  let wholeQs := [DensePoly.C (1 + 1 : base.Value), 0]
  let whole := partition base wholeQs
  require (whole.sections.isEmpty && whole.sectors.length == 1) "root-free family has boundaries"
  require (whole.sectors.map (fun s => s.signs wholeQs) == [[1, 0]]) "wrong whole-line signs"
  require (whole.sectorBetween? .negInf .posInf).isSome "whole-line request rejected"
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
  let some closeDescriptor := SignDet.Descriptor.validate inf.sign inf.signature
      { context := inf.signature, head := y * y - DensePoly.C (1 + epsilon),
        lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
    | throw (IO.userError "infinitesimal selected parent failed")
  let parent := inf.adjoin closeDescriptor
  let z : parent.context.Poly := DensePoly.ofCoeffs #[0, 1]
  let gap := (z - DensePoly.C (1 : parent.context.Value)) * (z - DensePoly.C parent.generator)
  let parentFamily := partition parent.context [gap]
  require (parentFamily.sections.length == 2 && parentFamily.sectors.length == 3)
    "selected parent lost its infinitesimal gap"
  require (parentFamily.sectors.map (fun s => s.signs [gap]) == [[1], [-1], [1]])
    "wrong signs between a selected root and an infinitesimally close value"
  for s in parentFamily.sections ++ parentFamily.sectors do
    require (s.cell.contains s.value) "selected-parent sample is outside its cell"
  IO.println "native section and sector samples passed"

#eval run

end Hex.RealClosure.Tower.Sample.Tests
