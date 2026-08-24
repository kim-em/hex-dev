/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexPolyZGcd

/-!
Deterministic JSONL fixtures for the `HexPolyZGcd` SymPy oracle.

Integer pairs exercise the public gcd, cofactor, coprimality, and lcm
contracts.  Separate inputs cover the fast primitive square-free split and
the denominator-clearing rational gcd.  Every oracle answer is recomputed
from the emitted inputs; no route tag or expected value is carried as input.
-/

namespace Hex.PolyZGcdEmit

open Hex.Conformance.Emit
open Hex.DensePoly
open Hex.ZPoly

private def lib : String := "HexPolyZGcd"

private structure GcdCase where
  id : String
  left : List Int
  right : List Int

private def gcdCases : List GcdCase := [
  ⟨"gcd/zero-zero", [], []⟩,
  ⟨"gcd/zero-right", [], [6, -3]⟩,
  ⟨"gcd/unit", [1], [4, 6, 8]⟩,
  ⟨"gcd/right-unit", [4, 6, 8], [1]⟩,
  ⟨"gcd/constants", [6], [4]⟩,
  ⟨"gcd/two-and-two-x", [2], [0, 2]⟩,
  ⟨"gcd/six-and-four-x", [6], [0, 4]⟩,
  ⟨"gcd/self", [2, -3, 0, 1], [2, -3, 0, 1]⟩,
  ⟨"gcd/pure-x-power", [0, 0, 6, 6], [0, 0, 18, 9]⟩,
  ⟨"gcd/content-two-four", [0, 2], [0, 4]⟩,
  ⟨"gcd/content-twelve-eighteen", [0, 12], [0, 18]⟩,
  ⟨"gcd/constant-polynomial", [6], [0, 4]⟩,
  ⟨"gcd/nonmonic", [1, 3, 2], [2, 5, 2]⟩,
  ⟨"gcd/coprime-linear", [0, 1], [30030, 1]⟩,
  ⟨"gcd/coprime-quadratic-cubic", [1, 0, 1], [2, 0, 0, 1]⟩,
  ⟨"gcd/coprime-dense-degree-eight",
    [1, -2, 3, -4, 5, -6, 7, -8, 1],
    [2, 3, 5, 7, 11, 13, 17, 19, 1]⟩,
  ⟨"gcd/unlucky-two", [0, 1], [2, 1]⟩,
  ⟨"gcd/cyclotomic-shape", [-1, 0, 0, 0, 1], [-1, 0, 1]⟩,
  ⟨"gcd/subresultant-swell",
    [-5, 2, 8, -3, -3, 0, 1, 0, 1],
    [21, -9, -4, 0, 5, 0, 3]⟩,
  ⟨"gcd/large-coeff-small-gcd",
    [1000000007, 1000000008, 1], [2000000014, 2000000015, 1]⟩]

private def pairValue (a b : ZPoly) : String :=
  divModValue a.toArray.toList b.toArray.toList

private def emitGcd (c : GcdCase) : IO Unit := do
  emitPolyFixture lib (c.id ++ "/left") c.left
  emitPolyFixture lib (c.id ++ "/right") c.right
  let f : ZPoly := DensePoly.ofList c.left
  let h : ZPoly := DensePoly.ofList c.right
  let cert := gcdCert f h
  emitResult lib c.id "gcd" (polyValue cert.gcd.toArray.toList)
  emitResult lib c.id "cofactors" (pairValue cert.cofL cert.cofR)
  emitResult lib c.id "is_coprime" (toString (isCoprime f h))
  emitResult lib c.id "lcm" (polyValue (lcm f h).toArray.toList)

private structure SqfCase where
  id : String
  input : List Int

private def sqfCases : List SqfCase := [
  ⟨"sqf/zero", []⟩,
  ⟨"sqf/squarefree", [1, 0, 1]⟩,
  ⟨"sqf/repeated-linear", [2, 5, 4, 1]⟩,
  ⟨"sqf/content-and-sign", [-12, -30, -24, -6]⟩]

private def sqfValue (primitive core repeated : ZPoly) : String :=
  "[" ++ polyValue primitive.toArray.toList ++ "," ++
    polyValue core.toArray.toList ++ "," ++
    polyValue repeated.toArray.toList ++ "]"

private def emitSqf (c : SqfCase) : IO Unit := do
  emitPolyFixture lib (c.id ++ "/input") c.input
  let d := sqfDecomp (DensePoly.ofList c.input)
  emitResult lib c.id "sqf"
    (sqfValue d.primitive d.squareFreeCore d.repeatedPart)

private structure RatCase where
  id : String
  left : List Rat
  right : List Rat

private def ratCases : List RatCase := [
  ⟨"rat/integer-coeffs", [1, 2], [2, 4]⟩,
  ⟨"rat/zero-zero", [], []⟩,
  ⟨"rat/subresultant-swell",
    [-5, 2, 8, -3, -3, 0, 1, 0, 1],
    [21, -9, -4, 0, 5, 0, 3]⟩,
  ⟨"rat/large-denominators",
    [Rat.divInt 1 (1000003 * 1000033),
      Rat.divInt (1000003 + 1000033) (1000003 * 1000033), 1],
    [Rat.divInt 1 (1000003 * 1000037),
      Rat.divInt (1000003 + 1000037) (1000003 * 1000037), 1]⟩]

private def ratTerms (coeffs : List Rat) : List (Nat × Int × Int) :=
  (List.range coeffs.length).filterMap fun exponent =>
    let q := coeffs.getD exponent 0
    if q = 0 then none else some (exponent, q.num, Int.ofNat q.den)

private def emitRat (c : RatCase) : IO Unit := do
  emitSparsePolyFixture lib (c.id ++ "/left") "rat" none (ratTerms c.left)
  emitSparsePolyFixture lib (c.id ++ "/right") "rat" none (ratTerms c.right)
  let result := ratGcd (DensePoly.ofList c.left) (DensePoly.ofList c.right)
  emitResult lib c.id "rat_gcd" (polyRatValue result.toArray.toList)

end Hex.PolyZGcdEmit

def main : IO Unit := do
  for c in Hex.PolyZGcdEmit.gcdCases do Hex.PolyZGcdEmit.emitGcd c
  for c in Hex.PolyZGcdEmit.sqfCases do Hex.PolyZGcdEmit.emitSqf c
  for c in Hex.PolyZGcdEmit.ratCases do Hex.PolyZGcdEmit.emitRat c
