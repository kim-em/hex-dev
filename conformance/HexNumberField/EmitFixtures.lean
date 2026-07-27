/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexNumberField

/-!
Deterministic JSONL fixtures for the `HexNumberField` external oracle profile.

Every lazy-arithmetic case emits the original operand polynomials and the
polynomial retained by the checked Lean operation. The oracle independently
forms the appropriate PARI resultant or reciprocal and then asks python-flint
to primitive-normalize, square-free, and factor the resulting integer
polynomial. The exactification case additionally emits the original selected
root's dyadic box; the oracle factors the original enclosing polynomial and
selects the unique factor whose root meets that box.
-/

namespace Hex.NumberFieldEmit

open Hex
open Hex.Conformance.Emit

private def lib : String := "HexNumberField"

private def sqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def sqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def sqrtTwoRep : RefinedIsolation sqrtTwoPoly :=
  ⟨⟨sqrtTwoSquare, by decide⟩, by decide⟩

private def sqrtTwo? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots sqrtTwoPoly then
    some
      { p := sqrtTwoPoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsimple
        x := SimpleRoot.mk sqrtTwoRep
        rep := sqrtTwoRep
        rep_mk := rfl }
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
      { p := sqrtThreePoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsimple
        x := SimpleRoot.mk sqrtThreeRep
        rep := sqrtThreeRep
        rep_mk := rfl }
  else
    none

private def enclosingPoly : ZPoly :=
  sqrtTwoPoly * DensePoly.ofList [-3, 1]

private def enclosingSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 6074001000 32, 0, 32⟩

private def enclosingRep : RefinedIsolation enclosingPoly :=
  ⟨⟨enclosingSquare, by decide⟩, by decide⟩

private def enclosingRoot? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots enclosingPoly then
    some
      { p := enclosingPoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsimple
        x := SimpleRoot.mk enclosingRep
        rep := enclosingRep
        rep_mk := rfl }
  else
    none

private def emitBox (case : String) (square : DyadicSquare) : IO Unit := do
  let re := square.re.toRat
  let im := square.im.toRat
  emitMatrixFixture lib (case ++ "/box")
    [[re.num, Int.ofNat re.den], [im.num, Int.ofNat im.den],
      [square.prec]]

private def emitOperands (case : String) (left right : ZPoly) : IO Unit := do
  emitPolyFixture lib (case ++ "/left") left.toArray.toList
  emitPolyFixture lib (case ++ "/right") right.toArray.toList

private def emitBinary (case operation : String)
    (left right : AlgebraicRoot) : IO Unit := do
  emitOperands case left.p right.p
  let result : Option AlgebraicRoot := match operation with
    | "add" => left.add? right
    | "sub" => left.sub? right
    | "mul" => left.mul? right
    | _ => none
  match result with
  | some value =>
      emitResult lib case operation (polyValue value.p.toArray.toList)
  | none => throw <| IO.userError (case ++ ": checked operation failed")

private def emitUnary (case operation : String)
    (input : AlgebraicRoot) : IO Unit := do
  emitPolyFixture lib (case ++ "/input") input.p.toArray.toList
  let result : Option AlgebraicRoot := match operation with
    | "inv" => input.inv?
    | _ => none
  match result with
  | some value =>
      emitResult lib case operation (polyValue value.p.toArray.toList)
  | none => throw <| IO.userError (case ++ ": checked operation failed")

private def emitExact : IO Unit := do
  let case := "exact/enclosing-sqrt2"
  emitPolyFixture lib (case ++ "/input") enclosingPoly.toArray.toList
  emitBox case enclosingSquare
  match enclosingRoot? >>= AlgebraicRoot.exact? with
  | some value =>
      emitResult lib case "exact" (polyValue value.p.toArray.toList)
  | none => throw <| IO.userError (case ++ ": exactification failed")

end Hex.NumberFieldEmit

def main : IO Unit := do
  match Hex.NumberFieldEmit.sqrtTwo?, Hex.NumberFieldEmit.sqrtThree? with
  | some sqrtTwo, some sqrtThree =>
      Hex.NumberFieldEmit.emitBinary "lazy/add-sqrt2-sqrt2" "add"
        sqrtTwo sqrtTwo
      Hex.NumberFieldEmit.emitBinary "lazy/add-sqrt2-sqrt3" "add"
        sqrtTwo sqrtThree
      Hex.NumberFieldEmit.emitBinary "lazy/sub-sqrt2-sqrt3" "sub"
        sqrtTwo sqrtThree
      Hex.NumberFieldEmit.emitBinary "lazy/mul-sqrt2-sqrt2" "mul"
        sqrtTwo sqrtTwo
      Hex.NumberFieldEmit.emitBinary "lazy/mul-sqrt2-sqrt3" "mul"
        sqrtTwo sqrtThree
      Hex.NumberFieldEmit.emitUnary "lazy/inv-sqrt2" "inv" sqrtTwo
      Hex.NumberFieldEmit.emitExact
  | _, _ => throw <| IO.userError "number-field fixture construction failed"
