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

private def linear (root leading : Rat) : IO (Root (E := Rat) Sturm.orderSign (10378 : Nat)) := do
  let head := DensePoly.ofCoeffs #[-leading * root, leading]
  let .ok (some [descriptor]) := SignDet.Descriptor.buildRoots Sturm.orderSign
      (10378 : Nat) head .negInf .posInf
    | throw (IO.userError "linear selected-root construction failed")
  return .selected descriptor

private def intervalRoot (square lower upper : Rat) :
    IO (SignDet.Descriptor Rat Nat Sturm.orderSign 10378) := do
  let head := DensePoly.ofCoeffs #[-square, 0, 1]
  let some descriptor := SignDet.Descriptor.validate Sturm.orderSign (10378 : Nat)
      ⟨10378, head, .finite lower, .finite upper, [], []⟩
    | throw (IO.userError "interval-only selected-root construction failed")
  return descriptor

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

  -- Full words of one literal head use shared Thom order across intervals.
  match negative, root, larger with
  | .selected a, .selected b, .selected c =>
    require (a.fullOrder b == some .lt && b.fullOrder a == some .gt &&
      a.fullOrder a == some .eq) "same-head full words are not applicable"
    let .ok original := a.buildComparison b
      | throw (IO.userError "common-product comparison failed")
    require (a.fullOrder b == some original.order) "full and common-product orders disagree"
    require (b.fullOrder c == none) "different heads passed the full-word guard"
    let some restricted := SignDet.Descriptor.validate Sturm.orderSign (10378 : Nat)
      ⟨10378, b.raw.head, .finite 1, .finite 2, [2], [1]⟩
      | throw (IO.userError "partial selected-root construction failed")
    require (restricted.fullOrder a == none) "partial word passed the full-word guard"
    expectOrder (.selected restricted) negative .gt
    expectOrder negative (.selected restricted) .lt
    expectOrder (.selected restricted) root .eq
  | _, _, _ => throw (IO.userError "selected fixtures lost their descriptors")

  -- These partial words force comparison past the full-Thom shortcut. Their
  -- open intervals share zero, although their selected roots are distinct.
  let below ← intervalRoot 2 (-4) 0
  let above ← intervalRoot 2 0 4
  require (below.fullOrder above == none) "interval fixture unexpectedly has full words"
  require (Root.intervalOrder? below above == some .lt &&
    Root.intervalOrder? above below == some .gt) "adjacent open intervals not ordered"
  expectOrder (.selected below) (.selected above) .lt
  expectOrder (.selected above) (.selected below) .gt
  let .ok adjacentComparison := below.buildComparison above
    | throw (IO.userError "adjacent interval fallback failed")
  require (Root.intervalOrder? below above == some adjacentComparison.order)
    "adjacent interval and common-product orders disagree"
  let gapLeft ← intervalRoot 2 (-2) (-1)
  let gapRight ← intervalRoot 3 1 2
  require (Root.intervalOrder? gapLeft gapRight == some .lt) "strict interval gap rejected"
  expectOrder (.selected gapLeft) (.selected gapRight) .lt
  let .ok gapComparison := gapLeft.buildComparison gapRight
    | throw (IO.userError "strict-gap fallback failed")
  require (Root.intervalOrder? gapLeft gapRight == some gapComparison.order)
    "strict-gap and common-product orders disagree"
  let overlapping ← intervalRoot 3 0 4
  require (Root.intervalOrder? above overlapping == none &&
    Root.intervalOrder? above above == none) "overlapping intervals accepted"
  expectOrder (.selected above) (.selected overlapping) .lt
  expectOrder (.selected above) (.selected above) .eq
  require (!(endpointsLE (fun (_ : Rat) => 2) (.finite 0) (.finite 1)))
    "invalid endpoint sign accepted"
  require (!(endpointsLE Sturm.orderSign (.posInf : Endpoint Rat) (.finite 1)) &&
    !(endpointsLE Sturm.orderSign (.finite 0) (.negInf : Endpoint Rat)))
    "infinite endpoint accepted by finite shortcut"

  let left ← linear (-2) 1
  let middle ← linear 0 1
  let right ← linear 3 1
  match left, right with
  | .selected a, .selected b =>
    require (Root.intervalOrder? a b == none) "whole-line intervals passed shortcut"
  | _, _ => throw (IO.userError "linear fixtures lost their descriptors")
  expectOrder left middle .lt
  expectOrder middle left .gt
  expectOrder middle right .lt
  expectOrder right middle .gt
  expectOrder right right .eq
  -- Misclassifying X² - 2 as linear would put its negative root above zero.
  expectOrder negative middle .lt
  expectOrder middle negative .gt
  let scaled ← linear 3 2
  expectOrder right scaled .eq
  expectOrder scaled right .eq
  let negativeScale ← linear (-2) (-3)
  expectOrder negativeScale right .lt
  expectOrder right negativeScale .gt
  let .ok linears := Root.sort [right, middle, left]
    | throw (IO.userError "linear root sorting failed")
  require (linears.length == 3) "linear sorting lost a root"
  for pair in linears.zip linears.tail do expectOrder pair.1 pair.2 .lt
  match Root.sort [right, right] with
  | .error .system => pure ()
  | _ => throw (IO.userError "duplicate linear roots accepted")

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
