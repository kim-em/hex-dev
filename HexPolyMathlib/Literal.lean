/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyMathlib.ScaledLiteral
public meta import HexPolyMathlib.ScaledLiteral
public meta import HexMatrixMathlib.Literal

public meta section

namespace HexPolyMathlib.Literal

open Lean Meta HexMatrixMathlib.Literal

/-- The evaluated coefficients and the proof identifying the user's expression. -/
structure Recognized where
  coefficients : List _root_.Rat
  proof : Expr

/-- Integer cross products identify a compiled coefficient list with a block. -/
def blockProof (xs : List _root_.Rat) (block : Expr) : MetaM Expr := do
  let d ← mkAppM ``Hex.Matrix.Lists.Scaled.denom #[block]
  let nums ← mkAppM ``Hex.Matrix.Lists.Scaled.nums #[block]
  let hd ← decideProof (← mkAppM ``LT.lt #[mkNatLit 0, d])
  let hc ← decideProof (← mkEq
    (← mkAppM ``Hex.Matrix.Lists.scaleRow #[d, toExpr xs, nums]) (mkConst ``Bool.true))
  mkAppM ``polynomialOfList_eq_block #[toExpr xs, block, hd, hc]

/-- Encode coefficients in compiled code; only cross products enter the proof. -/
def encode (a : Recognized) : MetaM (Expr × Expr) := do
  let block := Hex.Matrix.Lists.Scaled.encode a.coefficients
  let e ← mkAppM ``Hex.Matrix.Lists.Scaled.mk #[toExpr block.denom, toExpr block.nums]
  return (e, ← mkEqTrans a.proof (← blockProof a.coefficients e))

/-- Finish an adapter step without reducing rational coefficient arithmetic. -/
def finish (raw : Expr) (xs : List _root_.Rat) (proof : Expr) : MetaM Recognized := do
  return ⟨xs, ← mkEqTrans proof (← mkEqSymm (← blockProof xs raw))⟩

/-- Combine two identified literals through integer coefficient operations. -/
def binary (a b : Recognized) (op theoremName listOp : Name)
    (xs : List _root_.Rat) : MetaM Recognized := do
  let (ea, ha) ← encode a
  let (eb, hb) ← encode b
  let ty ← inferType (← mkAppM ``blockPolynomial #[ea])
  let f ← mkAppOptM op #[some ty, some ty, some ty, none]
  let h ← mkCongr (← mkCongrArg f ha) hb
  let mut args := #[ea, eb]
  if theoremName == ``blockPolynomial_add || theoremName == ``blockPolynomial_sub then
    for e in #[ea, eb] do
      let d ← mkAppM ``Hex.Matrix.Lists.Scaled.denom #[e]
      args := args.push (← decideProof (← mkAppM ``LT.lt #[mkNatLit 0, d]))
  let ht ← mkAppM theoremName args
  let raw ← mkAppM listOp #[ea, eb]
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
    return ← binary a b ``HAdd.hAdd ``blockPolynomial_add ``Hex.Matrix.Lists.Scaled.add
      (addLists a.coefficients b.coefficients)
  if e.isAppOfArity ``HSub.hSub 6 then
    let a ← parse args[4]! next
    let b ← parse args[5]! next
    return ← binary a b ``HSub.hSub ``blockPolynomial_sub ``Hex.Matrix.Lists.Scaled.sub
      (subLists a.coefficients b.coefficients)
  if e.isAppOfArity ``HMul.hMul 6 then
    let a ← parse args[4]! next
    let b ← parse args[5]! next
    if a.coefficients.length + b.coefficients.length > 1025 then
      throwError "polynomial literal exceeds the coefficient budget of 1024"
    return ← binary a b ``HMul.hMul ``blockPolynomial_mul ``Hex.Matrix.Lists.Scaled.mul
      (mulLists a.coefficients b.coefficients)
  if e.isAppOfArity ``Neg.neg 3 then
    let a ← parse args[2]! next
    let (ea, ha) ← encode a
    let h ← mkCongrArg e.appFn! ha
    let ht ← mkAppM ``blockPolynomial_neg #[ea]
    let raw ← mkAppM ``Hex.Matrix.Lists.Scaled.neg #[ea]
    return ← finish raw (scaleList (-1) a.coefficients) (← mkEqTrans h (← mkEqSymm ht))
  if e.isAppOfArity ``HPow.hPow 6 then
    let some n ← (Meta.evalNat args[5]!).run |
      throwError "polynomial exponent must be a closed natural number{indentExpr args[5]!}"
    if n > 256 then throwError "polynomial exponent exceeds the budget of 256"
    let a ← parse args[4]! next
    if n * (a.coefficients.length - 1) + 1 > 1024 then
      throwError "polynomial literal exceeds the coefficient budget of 1024"
    let (ea, ha) ← encode a
    let h ← mkCongr (← mkCongrArg e.appFn!.appFn! ha) (← mkEqRefl args[5]!)
    let ht ← mkAppM ``blockPolynomial_pow #[ea, mkNatLit n]
    let raw ← mkAppM ``Hex.Matrix.Lists.Scaled.pow #[ea, mkNatLit n]
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
