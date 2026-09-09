/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.Nearest
public section

/-! Principal complex radicals through the exact algebraic-coefficient root solver. -/
namespace Hex.AlgebraicNumber
namespace Radical

/-- Rank the sign of the imaginary coordinate without computing the coordinate. -/
@[expose] def rank (a : AlgebraicNumber) : Int :=
  match a.side with
  | .lower => -1
  | .real => 0
  | .upper => 1

/-- A root candidate with its doubled real part computed once. -/
structure Candidate where
  value : AlgebraicNumber
  twiceRe : AlgebraicNumber
  correct : twiceRe = value + value.conj

/-- Exactify a root and cache the real coordinate used in branch selection. -/
@[expose] def candidate (r : RootCount) : Candidate :=
  let a := r.root.exact
  ⟨a, a + a.conj, rfl⟩

/-- Prefer greater real part, then the upper imaginary side. -/
@[expose] def choose (a b : Candidate) : Candidate :=
  match realCompare a.twiceRe b.twiceRe with
  | .lt => b
  | .eq => if rank a.value < rank b.value then b else a
  | .gt => a

/-- Select one principal candidate, sharing cached coordinates throughout the fold. -/
@[expose] def select (roots : Array RootCount) : Option Candidate :=
  match roots.toList with
  | [] => none
  | r :: rs => some (rs.foldl (fun best root => choose best (candidate root)) (candidate r))

/-- The polynomial `X^n - a`, for the positive indices used by the root solver. -/
@[expose] def polynomial (a : AlgebraicNumber) (n : Nat) : AlgebraicPoly :=
  AlgebraicPoly.ofArray (Array.ofFn fun i : Fin (n + 1) =>
    if i.val = 0 then -a else if i.val = n then 1 else 0)

end Radical

/-- The principal complex nth root, matching `Complex.cpow` with exponent `1/n`.
In particular `nthRoot a 0 = 1`, and the principal odd root of a negative real
number need not be real. General inputs use the full polynomial root solver. -/
@[expose] def nthRoot (a : AlgebraicNumber) (n : Nat) : AlgebraicNumber :=
  if n = 0 then 1
  else if n = 1 then a
  else if a.isZero then 0
  else if a == 1 then 1
  else
    ((Radical.select (Radical.polynomial a n).roots.toArray).map (·.value)).getD
      (Hex.panicWith 0 "AlgebraicNumber.nthRoot: root selection failed")

/-- The principal square root, with nonnegative real part and the positive
imaginary branch on the negative real axis. -/
@[expose] def sqrt (a : AlgebraicNumber) : AlgebraicNumber := a.nthRoot 2

@[simp] theorem nthRoot_zero (a : AlgebraicNumber) : a.nthRoot 0 = 1 := by simp [nthRoot]
@[simp] theorem nthRoot_one (a : AlgebraicNumber) : a.nthRoot 1 = a := by simp [nthRoot]

end Hex.AlgebraicNumber
