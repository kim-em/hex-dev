/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField.QAdjoin
public meta import HexNumberField.QAdjoin

public section

/-!
Canonical fixed-presentation conversion and exactification of lazy roots.

Exactification factors the enclosing squarefree polynomial, rechecks each
factor's executable normalization certificates, isolates its roots, and keeps
the unique factor isolation whose disc meets the input representative. The
selected factor is finally passed through `AlgebraicNumber.ofNormalized?`, so
the stored representative follows the library's deterministic canonical
isolation strategy.
-/
namespace Hex

namespace AlgebraicNumber

/-- The canonical algebraic number as the fixed-field generator in its own
minimal-polynomial presentation. -/
@[expose]
def toQAdjoin (a : AlgebraicNumber) : QAdjoin a.p a.x :=
  QAdjoin.reduce a.p a.x (DensePoly.ofList ([0, 1] : List Rat))

/-- Forget minimality while retaining every checked root certificate. -/
@[expose]
def toRoot (a : AlgebraicNumber) : AlgebraicRoot where
  p := a.p
  prim := a.prim
  pos_lc := a.pos_lc
  pos_degree := a.pos_degree
  squarefree := a.squarefree
  x := a.x
  rep := a.rep
  rep_mk := a.rep_mk

end AlgebraicNumber

namespace AlgebraicRoot

/-- Try one normalized factor of an enclosing polynomial. Every proof stored
in the resulting canonical number comes from a freshly executed Boolean or
decidable check on this factor. -/
def exactFactor? (a : AlgebraicRoot) (q : ZPoly) : Option AlgebraicNumber :=
  if hprim : ZPoly.content q = 1 then
    if hpos : 0 < q.leadingCoeff then
      if hdegree : 0 < q.degree?.getD 0 then
        if hirred : ZPoly.isIrreducible q = true then
          if hsquarefree : HasOnlySimpleRoots q then do
            let isolations ← isolate q hsquarefree (separationDepth q : Int)
            let refined ← isolations.mapM DyadicRootIsolation.toRefined?
            let matching ← refined.toList.find? fun r =>
              r.1.square.discsMeet a.rep.1.square
            AlgebraicNumber.ofNormalized? q hprim hpos hdegree
              ⟨hirred, hdegree⟩ hsquarefree matching
          else
            none
        else
          none
      else
        none
    else
      none
  else
    none

/-- Factor a lazy root's enclosing polynomial and select the normalized
irreducible factor containing its chosen root. -/
@[expose]
def exact? (a : AlgebraicRoot) : Option AlgebraicNumber :=
  (ZPoly.factorize a.p).factors.foldl
    (fun found entry =>
      match found with
      | some b => some b
      | none => exactFactor? a entry.1)
    none

/-- Canonicalize a lazy root. Failure is a checked implementation branch whose
unreachability is proved by the Mathlib companion. -/
@[expose]
def exact (a : AlgebraicRoot) : AlgebraicNumber :=
  a.exact?.getD (Hex.panicWith 0 "AlgebraicRoot.exact: certification failed")

/-! Compiled canonicalization regressions. -/

private def sqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def sqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def sqrtTwoRep : RefinedIsolation sqrtTwoPoly :=
  ⟨⟨sqrtTwoSquare, by decide⟩, by decide⟩

private def sqrtTwoRoot (hsquarefree : HasOnlySimpleRoots sqrtTwoPoly) : AlgebraicRoot where
  p := sqrtTwoPoly
  prim := by rfl
  pos_lc := by decide
  pos_degree := by decide
  squarefree := hsquarefree
  x := SimpleRoot.mk sqrtTwoRep
  rep := sqrtTwoRep
  rep_mk := rfl

#guard
    if hsquarefree : HasOnlySimpleRoots sqrtTwoPoly then
      (sqrtTwoRoot hsquarefree).exact?.isSome
    else
      false

private def enclosingPoly : ZPoly :=
  sqrtTwoPoly * DensePoly.ofList [-3, 1]

private def enclosingSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 6074001000 32, 0, 32⟩

private def enclosingRep : RefinedIsolation enclosingPoly :=
  ⟨⟨enclosingSquare, by decide⟩, by decide⟩

private def reducibleRoot (hsquarefree : HasOnlySimpleRoots enclosingPoly) :
    AlgebraicRoot where
  p := enclosingPoly
  prim := by rfl
  pos_lc := by decide
  pos_degree := by decide
  squarefree := hsquarefree
  x := SimpleRoot.mk enclosingRep
  rep := enclosingRep
  rep_mk := rfl

-- Exactification discards the irrelevant linear factor and returns `X² - 2`.
#guard
    if hsquarefree : HasOnlySimpleRoots enclosingPoly then
      match (reducibleRoot hsquarefree).exact? with
      | some b => b.p = sqrtTwoPoly
      | none => false
    else
      false

#guard
    let q := AlgebraicNumber.zero.toQAdjoin
    q.coeffs = 0 && AlgebraicNumber.zero.toRoot.isZero

end AlgebraicRoot
end Hex
