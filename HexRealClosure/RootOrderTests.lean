/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootOrder

public section

open Hex

namespace Hex.RealClosure.Isolation

private def require (test : Bool) (label : String) : IO Unit :=
  unless test do throw (IO.userError label)

private def point (x : Rat) : Root (E := Rat) Sturm.orderSign (10378 : Nat) := .point x

private def selected (square : Rat) (lower upper : Rat) : IO (Root (E := Rat) Sturm.orderSign (10378 : Nat)) := do
  let head : DensePoly Rat := DensePoly.ofCoeffs #[-square, 0, 1]
  let .ok (some [descriptor]) := SignDet.Descriptor.buildRoots Sturm.orderSign
      (10378 : Nat) head (.finite lower) (.finite upper)
    | throw (IO.userError "positive square-root construction failed")
  return .selected descriptor

private def expectOrder (a b : Root (E := Rat) Sturm.orderSign (10378 : Nat))
    (order : Ordering) : IO Unit :=
  match a.compare b with
  | .ok actual => require (actual == order) "incorrect root comparison"
  | .error error => throw (IO.userError s!"comparison failed: {reprStr error}")

def run : IO Unit := do
  let root ← selected 2 1 2
  expectOrder (point (-1)) (point 0) .lt
  expectOrder (point 0) (point 0) .eq
  expectOrder (point 2) (point 0) .gt
  expectOrder root (point 1) .gt
  expectOrder root (point 2) .lt
  expectOrder (point 1) root .lt
  expectOrder (point 2) root .gt
  expectOrder root root .eq
  let negative ← selected 2 (-2) (-1)
  let larger ← selected 3 1 2
  expectOrder negative root .lt
  expectOrder root negative .gt
  expectOrder root larger .lt
  expectOrder larger root .gt

  let .ok result := Root.sort [point 2, root, point (-1), point 0]
    | throw (IO.userError "mixed root sorting failed")
  require (result.length == 4) "sorting lost a root"
  match result with
  | [.point a, .point b, .selected d, .point c] =>
    require (a == -1 && b == 0 && c == 2 &&
      d.raw.head == DensePoly.ofCoeffs #[-2, 0, 1] &&
      d.raw.lower == .finite 1 && d.raw.upper == .finite 2)
      "sorted result differs from [-1, 0, positive sqrt(2), 2]"
  | _ => throw (IO.userError "incorrect sorted root forms")

  for pair in result.zip result.tail do expectOrder pair.1 pair.2 .lt
  match Root.sort [point 0, point 0] with
  | .error .system => pure ()
  | _ => throw (IO.userError "duplicate roots accepted")
  match signOrder 2 with
  | .error .system => pure ()
  | _ => throw (IO.userError "invalid sign accepted")
  let bad : List (Root (E := Rat) (fun _ => 2) (10378 : Nat)) := [.point 1, .point 0]
  match Root.sort bad with
  | .error .system => pure ()
  | _ => throw (IO.userError "sort hid a comparison error")
  let polynomial : DensePoly Rat := DensePoly.ofCoeffs #[0, 2, 0, -1]
  let .ok (some completion) := complete? Sturm.orderSign (10378 : Nat) polynomial
    | throw (IO.userError "actual isolation failed")
  require (completion.roots.points == [0] && completion.roots.descriptors.length == 2)
    "isolation did not emit a point and two descriptors"
  let .ok ordered := completion.sort | throw (IO.userError "actual completion sort failed")
  match ordered with
  | [.selected left, .point middle, .selected right] =>
    require (middle == 0 && left.raw.head == DensePoly.ofCoeffs #[2, 0, -1] &&
      right.raw.head == DensePoly.ofCoeffs #[2, 0, -1])
      "wrong original isolation root values"
    match left.raw.upper, right.raw.lower with
    | .finite upper, .finite lower =>
      require (upper <= 0 && 0 <= lower) "incorrect negative/positive root selection"
    | _, _ => throw (IO.userError "unexpected finite-domain endpoints")
  | _ => throw (IO.userError "wrong actual completion order")
  IO.println "root ordering checks passed"

#eval run

end Hex.RealClosure.Isolation

def main : IO Unit := Hex.RealClosure.Isolation.run
