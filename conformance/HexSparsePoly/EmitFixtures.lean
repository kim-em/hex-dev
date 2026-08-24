/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexSparsePolyFixtures

/-!
JSONL emit driver for the `hex-sparse-poly` SymPy oracle.

The stream covers arithmetic, powering, evaluation, the derivative, and
the three substitutions on disjoint and overlapping supports, binomials
and trinomials at degrees `10^3` to `10^6` (including `x^1000000 − 1`
squared and its derivative), the `Φ_p(x^{p^{k-1}})` shapes, and inputs
over `Int`, `Rat`, and `ZMod64 p` — including a high-exponent `ZMod64`
evaluation no dense route could run.
-/

namespace Hex.SparsePolyEmit

open Hex
open Hex.Conformance.Emit
open Hex.SparsePoly
open Hex.SparsePolyFixtures

private def lib : String := "HexSparsePoly"

private def emitInt (case : String) (s : PZ) : IO Unit :=
  emitSparsePolyFixture lib case "int" none (wireInt s)

private def emitIntResult (case op : String) (s : PZ) : IO Unit :=
  emitResult lib case op (sparsePolyValue (wireInt s))

private def emitRat (case : String) (s : PQ) : IO Unit :=
  emitSparsePolyFixture lib case "rat" none (wireRat s)

private def emitRatResult (case op : String) (s : PQ) : IO Unit :=
  emitResult lib case op (sparsePolyValue (wireRat s))

private def emitMod (case : String) (s : P7) : IO Unit :=
  emitSparsePolyFixture lib case "zmod" (some 7) (wireMod s)

private def emitModResult (case op : String) (s : P7) : IO Unit :=
  emitResult lib case op (sparsePolyValue (wireMod s))

private structure BinaryCase where
  id : String
  left : PZ
  right : PZ

private def binaryCases : List BinaryCase := [
  ⟨"typical", pDisjoint, qDisjoint⟩,
  ⟨"edge", 0, binom3⟩,
  ⟨"adversarial", pOverlap, qOverlap⟩,
  ⟨"deg6", binom6, tri6⟩]

private def emitBinary (op : String) (f : PZ → PZ → PZ) : IO Unit := do
  for c in binaryCases do
    let case := op ++ "/" ++ c.id
    emitInt (case ++ "/left") c.left
    emitInt (case ++ "/right") c.right
    emitIntResult case op (f c.left c.right)

private def emitUnary (op : String) (f : PZ → PZ)
    (cases : List (String × PZ)) : IO Unit := do
  for (id, s) in cases do
    let case := op ++ "/" ++ id
    emitInt case s
    emitIntResult case op (f s)

private def emitAll : IO Unit := do
  emitBinary "add" (· + ·)
  emitBinary "sub" (· - ·)
  emitBinary "mul" (· * ·)

  emitUnary "neg" (- ·)
    [("typical", pDisjoint), ("edge", 0), ("deg6", tri6)]

  emitUnary "pow/2" (· ^ 2)
    [("typical", pOverlap), ("edge", 0), ("deg6", binom6)]
  emitUnary "pow/3" (· ^ 3)
    [("typical", qDisjoint), ("edge", C 1), ("deg4", tri4)]

  emitUnary "derivative" (·.derivative)
    [("typical", pDisjoint), ("edge", C 7), ("deg6", binom6),
     ("deg6sq", binom6 ^ 2)]

  emitUnary "substPow/3" (·.substPow 3)
    [("typical", pOverlap), ("edge", 0), ("phi3", phi3)]
  emitUnary "substPow/9" (·.substPow 9)
    [("phi3", phi3)]
  emitUnary "substPow/5" (·.substPow 5)
    [("phi5", phi5)]
  emitUnary "substPow/0" (·.substPow 0)
    [("cancel", #sp[(0, 3), (2, -3)]), ("sum", tri4)]

  emitUnary "substScale/2" (·.substScale 2)
    [("typical", pDisjoint), ("edge", 0), ("deg3", binom3)]
  emitUnary "substScale/-1" (·.substScale (-1))
    [("typical", pOverlap), ("deg4", tri4)]

  for (id, s, t) in [
      ("typical", #sp[(0, 2), (1, -1), (2, 1)], (#sp[(0, 1), (1, 1)] : PZ)),
      ("edge", (0 : PZ), pDisjoint),
      ("adversarial", #sp[(1, 1), (2, -1)], #sp[(0, 1), (1, 1)])] do
    let case := "compose/" ++ id
    emitInt (case ++ "/left") s
    emitInt (case ++ "/right") t
    emitIntResult case "compose" (s.compose t)

  for (id, s, x) in [
      ("typical", pDisjoint, (3 : Int)),
      ("edge", (0 : PZ), 17),
      ("deg3", binom3, 1),
      ("adversarial", pOverlap, -2)] do
    let case := "eval/" ++ id
    emitInt case s
    emitResult lib case ("eval/" ++ toString x)
      (sparsePolyValue [(0, s.eval x, 1)])

  -- Rational coefficients.
  emitRat "rat/add/typical/left" pRat
  emitRat "rat/add/typical/right" qRat
  emitRatResult "rat/add/typical" "add" (pRat + qRat)
  emitRat "rat/mul/typical/left" pRat
  emitRat "rat/mul/typical/right" qRat
  emitRatResult "rat/mul/typical" "mul" (pRat * qRat)
  emitRat "rat/derivative/typical" qRat
  emitRatResult "rat/derivative/typical" "derivative" qRat.derivative

  -- `ZMod64 7`: arithmetic, the vanishing derivative, and the
  -- high-exponent evaluation a dense route could not run.
  emitMod "mod/mul/typical/left" pMod7
  emitMod "mod/mul/typical/right" pMod7Big
  emitModResult "mod/mul/typical" "mul" (pMod7 * pMod7Big)
  emitMod "mod/derivative/typical" pMod7
  emitModResult "mod/derivative/typical" "derivative" pMod7.derivative
  emitMod "mod/eval/big" pMod7Big
  emitResult lib "mod/eval/big" "eval/2"
    (sparsePolyValue [(0, (ZMod64.toNat (pMod7Big.eval (ZMod64.ofNat 7 2)) : Int), 1)])
  emitMod "mod/substPow/7" pMod7
  emitModResult "mod/substPow/7" "substPow/7" (pMod7.substPow 7)

end Hex.SparsePolyEmit

def main : IO Unit :=
  Hex.SparsePolyEmit.emitAll
