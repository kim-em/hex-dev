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
forms the appropriate PARI resultant and then asks python-flint
to primitive-normalize, square-free, and factor the resulting integer
polynomial. The exactification case additionally emits the original selected
root's dyadic box; the oracle factors the original enclosing polynomial and
selects the unique factor whose root meets that box.

Root cases emit the original integer polynomial together with the discs and
multiplicity buckets returned by the fixed-field or algebraic-coefficient API.
The oracle compares those discs to python-flint's certified Arb root balls.
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

/- The selected root is `2`, while the same squarefree enclosing polynomial
also contains zero. Product elimination therefore introduces an irrelevant
power of `X` that the public operation must remove. -/
private def twoWithZeroPoly : ZPoly := DensePoly.ofList [0, -2, 1]

private def twoWithZeroSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 2 0, 0, 8⟩

private def twoWithZeroRep : RefinedIsolation twoWithZeroPoly :=
  ⟨⟨twoWithZeroSquare, by decide⟩, by decide⟩

private def twoWithZero? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots twoWithZeroPoly then
    some
      { p := twoWithZeroPoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsimple
        x := SimpleRoot.mk twoWithZeroRep
        rep := twoWithZeroRep
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

private def rootObject (root : RootCount) : String :=
  let square := root.root.rep.1.square
  let re := square.re.toRat
  let im := square.im.toRat
  let kind := if root.multiplicity = 1 then "atom" else "cluster"
  "{\"kind\":\"" ++ kind ++ "\",\"k\":" ++ toString root.multiplicity ++
    ",\"re_num\":" ++ toString re.num ++
    ",\"re_den\":" ++ toString (re.den : Int) ++
    ",\"im_num\":" ++ toString im.num ++
    ",\"im_den\":" ++ toString (im.den : Int) ++
    ",\"prec\":" ++ toString square.prec ++ "}"

private def rootValue : RootSet → Option String
  | .all => none
  | .finite roots =>
      let objects := (roots.toList.map rootObject).mergeSort (· ≤ ·)
      some ("[" ++ String.intercalate "," objects ++ "]")

private def emitFixedRoots : IO Unit := do
  let case := "roots/fixed-rational-quadratic"
  emitPolyFixture lib (case ++ "/input") sqrtTwoPoly.toArray.toList
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly :=
      ⟨hirred, by decide⟩
    let root := SimpleRoot.mk sqrtTwoRep
    let constant : QAdjoin sqrtTwoPoly root :=
      QAdjoin.reduce sqrtTwoPoly root (DensePoly.C (-2))
    let input : DensePoly (QAdjoin sqrtTwoPoly root) :=
      DensePoly.ofCoeffs #[constant, 0, 1]
    match QAdjoin.roots? input sqrtTwoRep rfl >>= rootValue with
    | some value => emitResult lib case "roots" value
    | none => throw <| IO.userError (case ++ ": roots? failed")
  else
    throw <| IO.userError (case ++ ": irreducibility check failed")

private def emitAlgebraicRoots : IO Unit := do
  let case := "roots/algebraic-rational-repeated"
  let inputPoly : ZPoly := DensePoly.ofList [4, -4, 1]
  emitPolyFixture lib (case ++ "/input") inputPoly.toArray.toList
  let roots? : Option RootSet := do
    let four ← AlgebraicPoly.Common.rational? 4
    let minusFour ← AlgebraicPoly.Common.rational? (-4)
    let one ← AlgebraicPoly.Common.rational? 1
    AlgebraicPoly.roots? (AlgebraicPoly.ofArray #[four, minusFour, one])
  match roots? >>= rootValue with
  | some value => emitResult lib case "roots" value
  | none => throw <| IO.userError (case ++ ": roots? failed")

end Hex.NumberFieldEmit

def main : IO Unit := do
  match Hex.NumberFieldEmit.sqrtTwo?, Hex.NumberFieldEmit.sqrtThree?,
      Hex.NumberFieldEmit.twoWithZero? with
  | some sqrtTwo, some sqrtThree, some twoWithZero =>
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
      Hex.NumberFieldEmit.emitBinary
        "lazy/mul-sqrt2-two-with-zero-conjugate" "mul" sqrtTwo twoWithZero
      Hex.NumberFieldEmit.emitUnary "lazy/inv-sqrt2" "inv" sqrtTwo
      Hex.NumberFieldEmit.emitExact
      Hex.NumberFieldEmit.emitFixedRoots
      Hex.NumberFieldEmit.emitAlgebraicRoots
  | _, _, _ =>
      throw <| IO.userError "number-field fixture construction failed"
