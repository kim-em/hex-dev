/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyMathlib.LiteralData
public meta import HexPolyMathlib.LiteralData
public meta import HexMatrixMathlib.Literal

public meta section

namespace HexPolyMathlib.Literal

open Lean Meta HexMatrixMathlib.Literal

/-- The evaluated coefficients and the proof identifying the user's expression. -/
structure Recognized where
  coefficients : List _root_.Rat
  proof : Expr

/-- Finish an adapter step with equality of structural rational lists. -/
def finish (raw : Expr) (xs : List _root_.Rat) (proof : Expr) : MetaM Recognized := do
  let h ← decideProof (← mkEq raw (toExpr xs))
  let h ← mkCongrArg (mkConst ``polynomialOfList) h
  return ⟨xs, ← mkEqTrans proof h⟩

/-- Combine two identified literals through a proved list operation. -/
def binary (a b : Recognized) (op theoremName listOp : Name)
    (xs : List _root_.Rat) : MetaM Recognized := do
  let ty ← inferType (← mkAppM ``polynomialOfList #[toExpr a.coefficients])
  let f ← mkAppOptM op #[some ty, some ty, some ty, none]
  let h ← mkCongr (← mkCongrArg f a.proof) b.proof
  let ht ← mkAppM theoremName #[toExpr a.coefficients, toExpr b.coefficients]
  let raw ← mkAppM listOp #[toExpr a.coefficients, toExpr b.coefficients]
  finish raw xs (← mkEqTrans h (← mkEqSymm ht))

/-- Ascending coefficients of a subtraction, used only in adapter identities. -/
def subLists (xs ys : List _root_.Rat) : List _root_.Rat :=
  addLists xs (scaleList (-1) ys)

/-- Recognize the rational polynomial fragment with bounded unfolding and
closed powers. Each recursive step supplies its algebraic identification. -/
partial def parse (e : Expr) (fuel : Nat := 64) : MetaM Recognized := do
  if fuel == 0 then throwError "polynomial literal exceeds the unfolding budget of 64"
  if e.hasFVar || e.hasMVar then throwError "polynomial must be closed{indentExpr e}"
  let next := fuel - 1
  let args := e.getAppArgs
  if e.getAppFn.isConstOf ``Polynomial.X then
    return ⟨[0, 1], ← mkEqSymm (mkConst ``polynomialOfList_X)⟩
  if e.isAppOfArity ``DFunLike.coe 6 && args[4]!.getAppFn.isConstOf ``Polynomial.C then
    let q ← evalEntry args[5]!
    let a : _root_.Rat := q.num / q.den
    let h ← decideProof (← mkEq args[5]! (toExpr a))
    let h ← mkCongrArg e.appFn! h
    let ht ← mkAppM ``polynomialOfList_C #[toExpr a]
    return ⟨[a], ← mkEqTrans h (← mkEqSymm ht)⟩
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let a ← parse args[4]! next
    let b ← parse args[5]! next
    return ← binary a b ``HAdd.hAdd ``polynomialOfList_add ``addLists
      (addLists a.coefficients b.coefficients)
  if e.isAppOfArity ``HSub.hSub 6 then
    let a ← parse args[4]! next
    let b ← parse args[5]! next
    let ty ← inferType e
    let f ← mkAppOptM ``HSub.hSub #[some ty, some ty, some ty, none]
    let h ← mkCongr (← mkCongrArg f a.proof) b.proof
    let ht ← mkAppM ``polynomialOfList_sub #[toExpr a.coefficients, toExpr b.coefficients]
    let raw ← mkAppM ``addLists #[toExpr a.coefficients,
      ← mkAppM ``scaleList #[toExpr (-1 : _root_.Rat), toExpr b.coefficients]]
    return ← finish raw (subLists a.coefficients b.coefficients) (← mkEqTrans h (← mkEqSymm ht))
  if e.isAppOfArity ``HMul.hMul 6 then
    let a ← parse args[4]! next
    let b ← parse args[5]! next
    if a.coefficients.length + b.coefficients.length > 1025 then
      throwError "polynomial literal exceeds the coefficient budget of 1024"
    return ← binary a b ``HMul.hMul ``polynomialOfList_mul ``mulLists
      (mulLists a.coefficients b.coefficients)
  if e.isAppOfArity ``Neg.neg 3 then
    let a ← parse args[2]! next
    let h ← mkCongrArg e.appFn! a.proof
    let ht ← mkAppM ``polynomialOfList_neg #[toExpr a.coefficients]
    let raw ← mkAppM ``scaleList #[toExpr (-1 : _root_.Rat), toExpr a.coefficients]
    return ← finish raw (scaleList (-1) a.coefficients) (← mkEqTrans h (← mkEqSymm ht))
  if e.isAppOfArity ``HPow.hPow 6 then
    let some n ← (Meta.evalNat args[5]!).run |
      throwError "polynomial exponent must be a closed natural number{indentExpr args[5]!}"
    if n > 256 then throwError "polynomial exponent exceeds the budget of 256"
    let a ← parse args[4]! next
    if n * (a.coefficients.length - 1) + 1 > 1024 then
      throwError "polynomial literal exceeds the coefficient budget of 1024"
    let h ← mkCongr (← mkCongrArg e.appFn!.appFn! a.proof) (← mkEqRefl args[5]!)
    let ht ← mkAppM ``polynomialOfList_pow #[toExpr a.coefficients, mkNatLit n]
    let raw ← mkAppM ``powList #[toExpr a.coefficients, mkNatLit n]
    return ← finish raw (powList a.coefficients n) (← mkEqTrans h (← mkEqSymm ht))
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let some n ← (Meta.evalNat args[1]!).run | throwError "unsupported polynomial numeral"
    if n == 0 then return ⟨[0], mkConst ``polynomialOfList_zero⟩
    if n == 1 then return ⟨[1], mkConst ``polynomialOfList_one⟩
    return ⟨[n], ← mkEqSymm (← mkAppM ``polynomialOfList_nat #[mkNatLit n])⟩
  if let some e' ← unfoldDefinition? e then return ← parse e' next
  throwError "unsupported rational polynomial expression{indentExpr e}"

/-- Identify an expression with ascending coefficients. The consumer includes
this proof in its one auxiliary theorem; there is no adapter kernel precheck. -/
def recognize (p : Expr) : MetaM Recognized := do
  let expected ← mkAppOptM ``Polynomial #[some (mkConst ``_root_.Rat), none]
  unless ← isDefEq (← inferType p) expected do
    throwError "polynomial literal requires the rational coefficient codec"
  parse p

end HexPolyMathlib.Literal
