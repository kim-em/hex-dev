/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Sample

namespace Hex.RealClosure.Tower.Sample.LocalTests

private def registry : BaseContext.Registry := fun _ => none
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def check {parent : Context registry} {ps : List parent.Poly}
    (f : Family parent ps) (sections sectors : List (List Int)) : IO Unit := do
  let actualSections := f.sections
  let actualSectors := f.sectors
  require (actualSections.map (fun s => s.signs ps) == sections) "local section signs differ"
  require (actualSectors.map (fun s => s.signs ps) == sectors) "local sector signs differ"
  for s in actualSections ++ actualSectors do
    require (s.cell.contains s.value) "local sample is outside its cell"
    require (s.input.context.signature.roots.length ≤ parent.signature.roots.length + 2)
      "local sector collected unrelated root contexts"
  require (f.sector? (f.boundaries.length + 1)).isNone "local invalid index accepted"

private def run : IO Unit := do
  let base := Context.base (BaseContext.rational registry)
  let x : base.Poly := DensePoly.ofCoeffs #[0, 1]
  let q := x * x - DensePoly.C (1 + 1)
  let duplicates := family base [q, q * q]
  require (duplicates.boundaries.length == 2) "irrational duplicate roots survived sorting"
  check duplicates [[0, 0], [0, 0]] [[1, 1], [-1, 1], [1, 1]]
  let some lower := duplicates.boundaries[0]?
    | throw (IO.userError "missing negative irrational boundary")
  let some upper := duplicates.boundaries[1]?
    | throw (IO.userError "missing positive irrational boundary")
  require (duplicates.sectorBetween? (.finite lower) (.finite upper)).isSome
    "local irrational bounded request rejected"
  require (duplicates.sectorBetween? (.finite upper) (.finite lower)).isNone
    "local reversed irrational request accepted"
  require (duplicates.sectorBetween? .negInf (.finite lower)).isSome "local left ray rejected"
  require (duplicates.sectorBetween? (.finite upper) .posInf).isSome "local right ray rejected"
  require (duplicates.sectorBetween? (.finite lower) (.finite (.point 0))).isNone
    "local non-boundary point accepted"
  let cubic := x * x * x - DensePoly.C (1 + 1 + 1) * x + DensePoly.C 1
  let three := family base [cubic]
  require (three.boundaries.length == 3) "irreducible cubic lost roots"
  check three [[0], [0], [0]] [[-1], [1], [-1], [1]]
  let quartic := q * (x * x - DensePoly.C (1 + 1 + 1))
  let mixed := family base [q, quartic]
  require (mixed.boundaries.length == 4) "mixed irrational family has duplicate or missing roots"
  check mixed [[1, 0], [0, 0], [0, 0], [1, 0]]
    [[1, 1], [1, -1], [-1, 1], [1, -1], [1, 1]]
  let some first := mixed.boundaries[0]?
    | throw (IO.userError "missing first mixed boundary")
  let some last := mixed.boundaries[3]?
    | throw (IO.userError "missing last mixed boundary")
  require (mixed.sectorBetween? (.finite first) (.finite last)).isNone
    "local non-adjacent irrational boundaries accepted"
  let whole := family base [DensePoly.C (1 + 1 : base.Value), 0]
  check whole [] [[1, 0]]
  require (whole.sectorBetween? .negInf .posInf).isSome "local whole line rejected"
  let staged := (BaseContext.rational registry).infinitesimal
  let inf := Context.base staged
  let epsilon : inf.Value := BaseContext.Element.infinitesimal (BaseContext.rational registry)
  let y : inf.Poly := DensePoly.ofCoeffs #[0, 1]
  let close := (y - DensePoly.C epsilon) * (y - DensePoly.C (epsilon + epsilon))
  let infinitesimal := family inf [close]
  check infinitesimal [[0], [0]] [[1], [-1], [1]]
  require (infinitesimal.sectorBetween? (.finite (.point epsilon))
    (.finite (.point (epsilon + epsilon)))).isSome "local infinitesimal gap request rejected"
  IO.println "local section and sector samples passed"

#eval run

end Hex.RealClosure.Tower.Sample.LocalTests
