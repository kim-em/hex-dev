/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolySmith.Diagonal

public section

/-! Consumer-facing data derived from polynomial Smith normal form. -/

namespace Hex.PolyMatrix

universe u

open Hex

/-- The monic invariant factors, computed on the transform-free path. -/
@[expose]
def invariantFactors {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) :
    Vector (DensePoly F) (snfRank A) :=
  diagonalVector (runSmith A false)

/-- Free rank and nonunit torsion factors of the presented module. -/
@[expose]
def moduleStructure {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) : Nat × Array (DensePoly F) :=
  let factors := invariantFactors A
  let torsion := factors.toList.filter fun p => p != polyOne
  (m - snfRank A, torsion.toArray)

/-- Monic generator of the zeroth Fitting ideal, or zero when the quotient
has a free summand. -/
@[expose]
def quotientOrder {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) : DensePoly F :=
  if snfRank A = m then
    (invariantFactors A).toList.foldl (fun acc p => acc * p) polyOne
  else polyZero

@[expose]
def diagonalSolvable {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (S : SmithData F n m) (b : Vector (DensePoly F) m) : Bool :=
  (List.finRange m).all fun j =>
    if h : j.val < S.rank then (b[j] % S.diag[j.val]'h).isZero else b[j].isZero

@[expose]
def diagonalSolution {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (S : SmithData F n m) (b : Vector (DensePoly F) m) :
    Vector (DensePoly F) n :=
  Vector.ofFn fun i =>
    if h : i.val < S.rank then
      if hm : i.val < m then Hex.exactDiv (b[i.val]'hm) (S.diag[i.val]'h) else polyZero
    else polyZero

/-- Solve `x * A = b` by transforming the right-hand side, solving the
diagonal system, and mapping the solution back with the left transform. -/
@[expose]
def solve {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) (b : Vector (DensePoly F) m) :
    Option (Vector (DensePoly F) n) :=
  let S := snfData A
  let transformed := b * S.right
  if diagonalSolvable S transformed then
    some (diagonalSolution S transformed * S.left)
  else none

end Hex.PolyMatrix
