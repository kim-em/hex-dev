/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexNumberFieldTower
import LeanBench

/-!
Benchmark registrations for `HexNumberFieldTower`.

The fixed cases expose the Phase-4 components named by the library SPEC:

* arithmetic and recursive inversion in the dimension-four tower
  `Q(sqrt(2), sqrt(3))`;
* adjoining a fourth root of two to `Q(sqrt(2))`;
* rational, one-level Trager-retry, and recursive two-level factorization;
* splitting a quartic through two genuine extensions;
* flattening a two-level tower to a primitive-element presentation.

Every case stays within tower dimension four and input degree four. The driver
is Mathlib-free; external PARI comparison belongs to conformance, not timing.
-/

namespace Hex.NumberTowerBench

open Hex
open Hex.NumberTower

private def ratChecksum (q : Rat) : UInt64 :=
  mixHash (hash q.num) (hash (q.den : Int))

private def elemChecksum {T : NumberTower} (a : Elem T) : UInt64 :=
  (coeffs a).foldl
    (fun checksum q => mixHash checksum (ratChecksum q))
    (hash T.dim)

private def polyChecksum {T : NumberTower} (p : Poly T) : UInt64 :=
  p.toArray.foldl
    (fun checksum coefficient => mixHash checksum (elemChecksum coefficient))
    (hash p.toArray.size)

private def zpolyChecksum (p : ZPoly) : UInt64 :=
  hash p.toArray

private def extensionChecksum {T : NumberTower}
    (extension : Extension T) : UInt64 :=
  mixHash (hash extension.tower.dim) <|
    mixHash (elemChecksum extension.gen) (zpolyChecksum extension.root.p)

private def factorChecksum {T : NumberTower} {f : Poly T}
    (result : Hex.NumberTower.Factorization T f) : UInt64 :=
  result.factors.foldl
    (fun checksum entry =>
      mixHash checksum <| mixHash (polyChecksum entry.1) (hash entry.2))
    (elemChecksum result.scalar)

private def splitChecksum {T : NumberTower} {f : Poly T}
    (result : Splitting T f) : UInt64 :=
  let initial := mixHash (hash result.extension.tower.dim)
    (hash result.extension.tower.height)
  match result.roots with
  | .all => mixHash initial 1
  | .finite roots => roots.foldl
      (fun checksum entry =>
        mixHash checksum <| mixHash (elemChecksum entry.1) (hash entry.2))
      initial

/-! ## Shared fixed-embedding fixtures -/

private def sqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def sqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def sqrtTwoRep : RefinedIsolation sqrtTwoPoly :=
  ⟨⟨sqrtTwoSquare, by decide⟩, by decide⟩

private def sqrtTwo? : Option (Extension rat) :=
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly :=
      ⟨hirred, by decide⟩
    if hsimple : HasOnlySimpleRoots sqrtTwoPoly then
      some (ofQAdjoin (x := SimpleRoot.mk sqrtTwoRep)
        hsimple sqrtTwoRep rfl)
    else
      none
  else
    none

private def sqrtThreePoly : ZPoly := DensePoly.ofList [-3, 0, 1]

private def sqrtThreeSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 222 7, 0, 8⟩

private def sqrtThreeRep : RefinedIsolation sqrtThreePoly :=
  ⟨⟨sqrtThreeSquare, by decide⟩, by decide⟩

private def sqrtThree? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots sqrtThreePoly then
    some
      { p := sqrtThreePoly, prim := by rfl, pos_lc := by decide
        pos_degree := by decide, squarefree := hsimple
        x := SimpleRoot.mk sqrtThreeRep, rep := sqrtThreeRep, rep_mk := rfl }
  else
    none

private def fourthRootTwoPoly : ZPoly :=
  DensePoly.ofList [-2, 0, 0, 0, 1]

private def fourthRootTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 77936 16, 0, 17⟩

private def fourthRootTwoRep : RefinedIsolation fourthRootTwoPoly :=
  ⟨⟨fourthRootTwoSquare, by decide⟩, by decide⟩

private def fourthRootTwo? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots fourthRootTwoPoly then
    some
      { p := fourthRootTwoPoly, prim := by rfl, pos_lc := by decide
        pos_degree := by decide, squarefree := hsimple
        x := SimpleRoot.mk fourthRootTwoRep, rep := fourthRootTwoRep
        rep_mk := rfl }
  else
    none

private structure TwoLevel where
  base : Extension rat
  extension : Extension base.tower

private def twoLevel? : Option TwoLevel := do
  let base ← sqrtTwo?
  let root ← sqrtThree?
  let extension ← adjoin? base.tower root
  some ⟨base, extension⟩

private def rationalPoly (coefficients : List Rat) : Poly rat :=
  DensePoly.ofCoeffs (coefficients.toArray.map (ofRat rat))

initialize sqrtTwoRef : IO.Ref (Option (Extension rat)) ← IO.mkRef sqrtTwo?

initialize fourthRootRef : IO.Ref (Option AlgebraicRoot) ←
  IO.mkRef fourthRootTwo?

initialize twoLevelRef : IO.Ref (Option TwoLevel) ← IO.mkRef twoLevel?

/-! ## Arithmetic and adjoining -/

def runArithmetic : Unit → IO UInt64 := fun _ => do
  match ← twoLevelRef.get with
  | some tower =>
      let sqrtTwo := tower.extension.embed tower.base.gen
      let value := sqrtTwo + tower.extension.gen
      return elemChecksum (value * value + value⁻¹)
  | none => return 0

def runAdjoin : Unit → IO UInt64 := fun _ => do
  match ← sqrtTwoRef.get, ← fourthRootRef.get with
  | some base, some root =>
      return (adjoin? base.tower root).map extensionChecksum |>.getD 0
  | _, _ => return 0

/- Dimension-`D` multiplication and top-level extended-gcd inversion both use
schoolbook coordinate arithmetic bounded by `O(D^2)` before coefficient-size
growth. The fixed `D = 4` case records their combined recursive-tower cost. -/
setup_fixed_benchmark runArithmetic where {
  repeats := 5, maxSecondsPerCall := 2.0
}

/- Adjoining the fourth root factors a degree-four absolute presentation over
a dimension-two base, selects the quadratic relative factor using the fixed
embedding, and validates the new level. This fixed case attributes that whole
smart-constructor boundary. -/
setup_fixed_benchmark runAdjoin where {
  repeats := 3, maxSecondsPerCall := 10.0
}

/-! ## Trager factorization -/

private def repeatedInput : Poly rat :=
  rationalPoly [4, 0, -4, 0, 1]

initialize repeatedRef : IO.Ref (Option (Poly rat)) ←
  IO.mkRef (some repeatedInput)

def runFactorRat : Unit → IO UInt64 := fun _ => do
  match ← repeatedRef.get with
  | some input => return (factor? rat input).map factorChecksum |>.getD 0
  | none => return 0

def runFactorRetry : Unit → IO UInt64 := fun _ => do
  match ← sqrtTwoRef.get with
  | some base =>
      let T := base.tower
      let input : Poly T := DensePoly.ofCoeffs #[ofRat T (-3), 0, 1]
      return (factor? T input).map factorChecksum |>.getD 0
  | none => return 0

def runFactorRecursive : Unit → IO UInt64 := fun _ => do
  match ← twoLevelRef.get with
  | some tower =>
      let T := tower.extension.tower
      let input : Poly T := DensePoly.ofCoeffs #[ofRat T (-3), 0, 1]
      return (factor? T input).map factorChecksum |>.getD 0
  | none => return 0

/- Rational factorization separates Yun multiplicity for the degree-four
square `(X^2 - 2)^2` and then performs one integer factorization. The fixed
case is the base-case reference for the two Trager registrations below. -/
setup_fixed_benchmark runFactorRat where {
  repeats := 3, maxSecondsPerCall := 5.0
}

/- Over `Q(sqrt(2))`, the shift-zero norm of `X^2 - 3` is repeated, so the
bounded Trager search advances to a square-free one-level norm before gcd
recovery. This isolates retry cost at base dimension two and input degree two. -/
setup_fixed_benchmark runFactorRetry where {
  repeats := 3, maxSecondsPerCall := 10.0
}

/- Over `Q(sqrt(2), sqrt(3))`, `X^2 - 3` factors through the intermediate
field. The fixed dimension-four case measures recursive one-level norms and
lower-field factorization instead of an invalid absolute-norm shortcut. -/
setup_fixed_benchmark runFactorRecursive where {
  repeats := 3, maxSecondsPerCall := 10.0
}

/-! ## Splitting and flattening -/

private def quarticInput : Poly rat :=
  rationalPoly [6, 0, -5, 0, 1]

initialize quarticRef : IO.Ref (Option (Poly rat)) ←
  IO.mkRef (some quarticInput)

def runSplit : Unit → IO UInt64 := fun _ => do
  match ← quarticRef.get with
  | some input => return (split? rat input).map splitChecksum |>.getD 0
  | none => return 0

def runFlatten : Unit → IO UInt64 := fun _ => do
  match ← twoLevelRef.get with
  | some tower =>
      return (flatten? tower.extension.tower).map
        (fun result => zpolyChecksum result.root.p) |>.getD 0
  | none => return 0

/- Splitting `(X^2 - 2)(X^2 - 3)` factors and performs two genuine adjoining
steps before collecting four simple roots. Dimension and input degree are both
four, so this fixed case measures the complete degree-reducing outer loop. -/
setup_fixed_benchmark runSplit where {
  repeats := 2, maxSecondsPerCall := 20.0
}

/- Flattening the dimension-four two-level tower searches signed primitive
shifts, constructs a degree-four eliminant, performs exact linear recovery,
and verifies both coordinate maps. This is the SPEC's expected dominant
primitive-element path at the merge-facing size bound. -/
setup_fixed_benchmark runFlatten where {
  repeats := 2, maxSecondsPerCall := 20.0
}

end Hex.NumberTowerBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
