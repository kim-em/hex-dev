/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BasePermutation
public meta import HexRealClosure.BasePermutation

public section

namespace Hex.RealClosure.BaseContext.BaseTower

private def a : ConstantKey := ⟨"a", 1⟩
private def b : ConstantKey := ⟨"b", 1⟩
private def c : ConstantKey := ⟨"c", 1⟩

private def check : IO Unit := do
  for target in [[a, b, c], [a, c, b], [b, a, c], [b, c, a], [c, a, b], [c, b, a]] do
    unless (Permutation.make? [a, b, c] target).isSome do
      throw (IO.userError "three-provider permutation rejected")
  let some larger := Permutation.make? [a, b] [c, b, a]
    | throw (IO.userError "enlargement with reversed source keys rejected")
  let x : BaseTower 2 := RationalFn.C RationalFn.X
  let y : BaseTower 2 := RationalFn.X
  let three : BaseTower 2 := RationalFn.C (RationalFn.C (3 : Rat))
  let outer : BaseTower 3 := RationalFn.X
  let middle : BaseTower 3 := RationalFn.C RationalFn.X
  let inner : BaseTower 3 := RationalFn.C (RationalFn.C RationalFn.X)
  let targetThree : BaseTower 3 := RationalFn.C (RationalFn.C (RationalFn.C (3 : Rat)))
  unless larger.embedding.value (x / (y - three)) = outer / (middle - targetThree) do
    throw (IO.userError "enlarged fraction has incorrect variable positions")
  let some reordered := Permutation.make? [a, b, c] [c, a, b]
    | throw (IO.userError "three-provider cycle rejected")
  unless reordered.embedding.value ((inner * middle + outer) / (outer - inner)) =
      (middle * outer + inner) / (inner - middle) do
    throw (IO.userError "cyclic permutation changed fraction incorrectly")
  let some rational := Permutation.make? [] [c, b, a]
    | throw (IO.userError "rational inclusion rejected")
  unless rational.embedding.value (3 : Rat) = targetThree do
    throw (IO.userError "rational inclusion changed a coefficient")
  unless (Permutation.make? [a, b] [a, c]).isNone &&
      (Permutation.make? [a, b] [a]).isNone &&
      (Permutation.make? [a, a] [a, b]).isNone &&
      (Permutation.make? [a] [a, a]).isNone &&
      (exchange? 2 [1]).isNone do
    throw (IO.userError "invalid key or exchange position accepted")

#eval check

end Hex.RealClosure.BaseContext.BaseTower
