/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexKronecker
import Hex.Conformance.Emit
import Lean.Data.Json

namespace Hex.Kronecker.Emit

open Lean
open Hex.MvPoly.Kernel

def exprJson : Expr → Json
  | .int z => toJson #[toJson "int", toJson z]
  | .atom i => toJson #[toJson "atom", toJson i]
  | .add a b => toJson #[toJson "add", exprJson a, exprJson b]
  | .sub a b => toJson #[toJson "sub", exprJson a, exprJson b]
  | .neg a => toJson #[toJson "neg", exprJson a]
  | .mul a b => toJson #[toJson "mul", exprJson a, exprJson b]
  | .pow a n => toJson #[toJson "pow", exprJson a, toJson n]

def sizeJson : Except SizeError SizeBound → Json
  | .error e => Json.mkObj [("error", toJson (reprStr e))]
  | .ok s => Json.mkObj [
      ("degrees", toJson s.degrees), ("strides", toJson s.strides), ("digits", toJson s.digits),
      ("coefficientBound", toJson s.coefficientBound), ("digitBits", toJson s.digitBits),
      ("outerSlotBits", toJson s.outerSlotBits?), ("packedBits", toJson s.packedBits),
      ("innerBits", toJson s.innerBits), ("limitingStage", toJson (reprStr s.limitingStage))]

def emit (name kind : String) (budget : Budget) (k : Nat) (fields : List (String × Json))
    (size : Except SizeError SizeBound) (result : Bool) : IO Unit :=
  Hex.Conformance.Emit.emitLine (Json.mkObj ([
    ("lib", toJson "HexKronecker"), ("kind", toJson "kronecker"),
    ("case", toJson name), ("op", toJson kind), ("k", toJson k),
    ("budget", toJson [budget.maxDenseDigits,budget.maxPackedBits]),
    ("size", sizeJson size), ("result", toJson result)] ++ fields)).compress

def tree (name : String) (k : Nat) (l r : Expr) (budget : Budget := ⟨65536,4096⟩) : IO Unit :=
  emit name "expr" budget k [("lhs",exprJson l),("rhs",exprJson r)]
    (sizeExprEq budget k l r) (checkExprEq budget k l r)

def treeMod (name : String) (k p : Nat) (l r : Expr) (q : PolyList Int)
    (budget : Budget := ⟨65536,4096⟩) : IO Unit :=
  emit name "exprMod" budget k [("lhs",exprJson l),("rhs",exprJson r),("p",toJson p),("q",toJson q)]
    (sizeExprEqMod budget k p l r q) (checkExprEqMod budget k p l r q)

def terms (name : String) (k : Nat) (l r : PolyList Int) : IO Unit :=
  let budget : Budget := ⟨65536,4096⟩
  emit name "terms" budget k [("lhs",toJson l),("rhs",toJson r)]
    (sizeTermsEq budget k l r) (checkTermsEq budget k l r)

def termsMod (name : String) (k p : Nat) (l r q : PolyList Int) : IO Unit :=
  let budget : Budget := ⟨65536,4096⟩
  emit name "termsMod" budget k [("lhs",toJson l),("rhs",toJson r),("p",toJson p),("q",toJson q)]
    (sizeTermsEqMod budget k p l r q) (checkTermsEqMod budget k p l r q)

def matrix (name : String) (k n r m : Nat) (a b c : TermMatrix)
    (budget : Budget := ⟨65536,4096⟩) : IO Unit := do
  for mode in [MulMode.plain, .signedPacked] do
    emit (name ++ "/" ++ reprStr mode) "mul" budget k [
      ("mode",toJson (reprStr mode)), ("n",toJson n),("r",toJson r),("m",toJson m),
      ("a",toJson a),("b",toJson b),("c",toJson c)]
      (sizeMulTerms budget mode k n r m a b c) (checkMulTerms budget mode k n r m a b c)

def matrixMod (name : String) (k n r m p : Nat) (a b c q : TermMatrix) : IO Unit := do
  let budget : Budget := ⟨65536,4096⟩
  for mode in [MulMode.plain, .signedPacked] do
    emit (name ++ "/" ++ reprStr mode) "mulMod" budget k [
      ("mode",toJson (reprStr mode)), ("n",toJson n),("r",toJson r),("m",toJson m),("p",toJson p),
      ("a",toJson a),("b",toJson b),("c",toJson c),("q",toJson q)]
      (sizeMulTermsMod budget mode k n r m p a b c q) (checkMulTermsMod budget mode k n r m p a b c q)

def x : Expr := .atom 0
def y : Expr := .atom 1
def constant (z : Int) : PolyList Int := [([],z)]

def emitAll : IO Unit := do
  tree "zero" 0 (.int 0) (.int 0)
  tree "negative" 0 (.neg (.int 3)) (.int (-3))
  tree "pow-zero" 0 (.pow (.int 0) 0) (.int 1)
  tree "pow-one" 1 (.pow x 1) x
  tree "cancel" 2 (.sub (.add x y) y) x
  tree "cube" 2 (.pow (.add x y) 3)
    (.add (.add (.pow x 3) (.mul (.int 3) (.mul (.pow x 2) y)))
      (.add (.mul (.int 3) (.mul x (.pow y 2))) (.pow y 3)))
  tree "false-target" 1 (.pow x 7) x
  tree "invalid-index" 1 y y
  tree "dense-decline" 2 (.pow (.add x y) 8) (.pow (.add x y) 8) ⟨64,4096⟩
  tree "constant-large-exponent" 0 (.pow (.int 1) 16777217) (.int 1) ⟨1,16⟩
  tree "coefficient-exact-refinement" 0 (.pow (.int 2) 9) (.pow (.int 2) 9) ⟨1,16⟩
  tree "cancelled-large-subtree" 0 (.mul (.pow (.int 2) 1000000000) (.int 0)) (.int 0) ⟨1,16⟩
  tree "digit-boundary" 1 (.pow x 15) (.pow x 15) ⟨16,4096⟩
  tree "digit-boundary-decline" 1 (.pow x 16) (.pow x 16) ⟨16,4096⟩
  tree "bit-boundary" 0 (.pow (.int 2) 9) (.pow (.int 2) 9) ⟨1,11⟩
  tree "bit-boundary-decline" 0 (.pow (.int 2) 9) (.pow (.int 2) 9) ⟨1,10⟩
  let l := Expr.pow (.add x (.int 1)) 7
  let r := Expr.add (.pow x 7) (.int 1)
  let q : PolyList Int := [([6],1),([5],3),([4],5),([3],5),([2],3),([1],1)]
  treeMod "frobenius" 1 7 l r q
  treeMod "corrupt-quotient" 1 7 l r [([6],2),([5],3),([4],5),([3],5),([2],3),([1],1)]
  treeMod "function-not-formal" 1 7 (.pow x 7) x q
  treeMod "bad-modulus" 1 0 l r q
  treeMod "bad-residue" 0 7 (.int 7) (.int 0) [([],1)]
  treeMod "bad-quotient-shape" 1 7 l r [([],1)]
  treeMod "bad-quotient-order" 1 7 l r q.reverse
  terms "terms-cancel" 1 [([1],1),([1],-1)] []
  terms "terms-negative" 1 [([2],-2),([0],3)] [([0],3),([2],-2)]
  terms "terms-false" 1 [([1],1)] [([2],1)]
  terms "terms-bad-shape" 1 [([],1)] [([],1)]
  termsMod "residue-terms" 1 7 [([1],6),([1],1)] [] [([1],1)]
  termsMod "residue-terms-corrupt" 1 7 [([1],6),([1],1)] [] [([1],2)]
  let a := [[constant 2,constant (-3)]]
  let b := [[constant (-4),constant 5],[constant 6,constant (-7)]]
  let c := [[constant (-26),constant 31]]
  matrix "rectangular" 0 1 2 2 a b c
  matrix "rectangular-corrupt" 0 1 2 2 a b [[constant 0,constant 31]]
  matrix "matrix-shape" 0 1 2 1 a b c
  matrix "empty-dot" 0 1 0 1 [[]] [] [[[]]]
  matrix "zero-rows" 1 0 0 2 [] [] []
  matrix "outer-decline" 0 1 2 2 a b c ⟨1,32⟩
  matrix "polynomial-product" 1 1 1 1 [[[([1],1),([0],1)]]] [[[([1],1),([0],-1)]]]
    [[[([2],1),([0],-1)]]]
  matrixMod "matrix-residue" 0 1 1 1 7 [[constant 3]] [[constant 5]] [[constant 1]] [[constant 2]]
  matrixMod "matrix-corrupt-quotient" 0 1 1 1 7 [[constant 3]] [[constant 5]] [[constant 1]] [[constant 3]]
  matrixMod "matrix-residue-bad" 0 1 1 1 7 [[constant (-1)]] [[constant 5]] [[constant 2]] [[constant (-1)]]

end Hex.Kronecker.Emit

def main : IO Unit := Hex.Kronecker.Emit.emitAll
