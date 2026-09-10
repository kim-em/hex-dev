/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.Unity
public section

/-! Principal complex radicals through the exact algebraic-coefficient root solver. -/
namespace Hex.AlgebraicNumber
namespace Radical

/-- The polynomial `X^n - a`, for the positive indices used by the root solver. -/
@[expose] def polynomial (a : AlgebraicNumber) (n : Nat) : AlgebraicPoly :=
  AlgebraicPoly.ofArray (Array.ofFn fun i : Fin (n + 1) =>
    if i.val = 0 then -a else if i.val = n then 1 else 0)

/-- The imaginary side containing the principal root for indices greater than one. -/
@[expose] def principalSide (a : AlgebraicNumber) : RootSide :=
  match a.side with
  | .real => if a.realCompare 0 == .lt then .upper else .real
  | side => side

/-- Retain the principal half circle and certify its maximal real coordinate. -/
@[expose] def fast? (a : AlgebraicNumber) (roots : Array RootCount) : Option AlgebraicRoot :=
  RootSelection.select? ((roots.toList.map RootCount.root).filter
    (fun r => decide (r.side = principalSide a)))

end Radical

/-- The principal complex nth root, matching `Complex.cpow` with exponent `1/n`.
In particular `nthRoot a 0 = 1`, and the principal odd root of a negative real
number need not be real. General inputs use the full polynomial root solver. -/
@[expose] def nthRoot (a : AlgebraicNumber) (n : Nat) : AlgebraicNumber :=
  if n = 0 then 1
  else if n = 1 then a
  else if a.isZero then 0
  else if a == 1 then 1
  else if a == -1 then rootOfUnity ((1 / 2 : Rat) / n)
  else if a == I then rootOfUnity ((1 / 4 : Rat) / n)
  else if a == -I then rootOfUnity ((-1 / 4 : Rat) / n)
  else
    let roots := (Radical.polynomial a n).roots.toArray
    match Radical.fast? a roots with
    | some root => root.exact
    | none => match Radical.select roots with
      | some result => result.value
      | none => Hex.panicWith 0 "AlgebraicNumber.nthRoot: root selection failed"

/-- The principal square root, with nonnegative real part and the positive
imaginary branch on the negative real axis. -/
@[expose] def sqrt (a : AlgebraicNumber) : AlgebraicNumber := a.nthRoot 2

@[simp] theorem nthRoot_zero (a : AlgebraicNumber) : a.nthRoot 0 = 1 := by simp [nthRoot]
@[simp] theorem nthRoot_one (a : AlgebraicNumber) : a.nthRoot 1 = a := by simp [nthRoot]

end Hex.AlgebraicNumber
