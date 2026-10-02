/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexKronecker

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

namespace Hex.Kronecker.Conformance

private def budget : Budget := ⟨65536, 4096⟩
private def x : Expr := .atom 0
private def y : Expr := .atom 1
private def cube : Expr := .pow (.add x y) 3
private def expanded : Expr := .add (.add (.pow x 3)
  (.mul (.int 3) (.mul (.pow x 2) y)))
  (.add (.mul (.int 3) (.mul x (.pow y 2))) (.pow y 3))

#guard checkExprEq budget 2 cube expanded
#guard !checkExprEq budget 1 cube expanded
#guard checkExprEq budget 0 (.pow (.int 0) 0) (.int 1)
#guard checkExprEq budget 0 (.pow (.int 1) 16777217) (.int 1)
#guard checkExprEq ⟨65536, 16⟩ 0 (.pow (.int 2) 9) (.pow (.int 2) 9)
#guard (sizeExprEq budget 0 (.pow (.int 1) 16777217) (.int 1)).toOption.map
  SizeBound.packedBits == some 2
#guard !checkExprEq ⟨65536, 16⟩ 0 (.mul (.pow (.int 2) 1000000000) (.int 0)) (.int 0)
#guard !checkExprEq ⟨2, 4096⟩ 2 cube expanded
#guard checkExprEq budget 0 (.neg (.int 3)) (.int (-3))
#guard checkExprEq budget 1 (.sub x x) (.int 0)
#guard !checkExprEq budget 1 (.pow x 7) x

private def quotient : Hex.MvPoly.Kernel.PolyList Int :=
  [([6], 1), ([5], 3), ([4], 5), ([3], 5), ([2], 3), ([1], 1)]
private def frobenius : Expr := .pow (.add x (.int 1)) 7
private def frobeniusRhs : Expr := .add (.pow x 7) (.int 1)

#guard !checkExprEq budget 1 frobenius frobeniusRhs
#guard checkExprEqMod budget 1 7 frobenius frobeniusRhs quotient
#guard !checkExprEqMod budget 1 7 frobenius frobeniusRhs []
#guard !checkExprEqMod budget 1 7 (.pow x 7) x quotient
#guard !checkExprEqMod budget 1 0 frobenius frobeniusRhs quotient
#guard !checkExprEqMod budget 0 7 (.int 7) (.int 0) [([], 1)]

#guard checkTermsEq budget 1 [([1], 1), ([1], -1)] []
#guard !checkTermsEq budget 1 [([], 1)] [([], 1)]
#guard checkTermsEqMod budget 1 7 [([1], 6), ([1], 1)] [] [([1], 1)]

private def constant (z : Int) : Hex.MvPoly.Kernel.PolyList Int := [([], z)]
private def a : TermMatrix := [[constant 2, constant (-3)]]
private def b : TermMatrix := [[constant (-4), constant 5], [constant 6, constant (-7)]]
private def c : TermMatrix := [[constant (-26), constant 31]]

#guard checkMulTerms budget .plain 0 1 2 2 a b c
#guard checkMulTerms budget .signedPacked 0 1 2 2 a b c
#guard !checkMulTerms budget .plain 0 1 2 1 a b c
#guard !checkMulTerms budget .signedPacked 0 1 2 2 a b [[constant 0, constant 31]]
#guard checkMulTerms budget .plain 0 1 0 1 [[]] [] [[[]]]
#guard checkMulTerms budget .signedPacked 0 1 0 1 [[]] [] [[[]]]
#guard checkMulTermsMod budget .plain 0 1 1 1 7 [[constant 3]] [[constant 5]]
  [[constant 1]] [[constant 2]]
#guard checkMulTermsMod budget .signedPacked 0 1 1 1 7 [[constant 3]] [[constant 5]]
  [[constant 1]] [[constant 2]]

-- Kernel replay, independently of the executable guards above.
example : checkExprEq budget 2 cube expanded = true := rfl
example : checkExprEqMod budget 1 7 frobenius frobeniusRhs quotient = true := rfl
example : checkMulTerms budget .signedPacked 0 1 2 2 a b c = true := rfl

end Hex.Kronecker.Conformance
