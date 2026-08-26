/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly

@[expose] public section

/-!
Coordinate operations for multivariate Hensel lifting.

The factorization algorithms work after translating every variable except a
chosen main variable to put the evaluation point at the origin.  This module
also exposes the recursive univariate image, leading coefficient, and the box
truncation used by the stage loop.  None of these operations depends on gcd or
factorization infrastructure.
-/

namespace Hex.MvHensel

open Hex.MvPoly

variable {n : Nat}
  {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
  {cmp' : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp]

/-- Remove the distinguished position `i` from an index `j ≠ i`.

This is the index-level inverse of `i.succAbove`.  Keeping it explicit avoids
making the coordinate transform depend on Mathlib's equivalence API. -/
def remainingIndex (i j : Fin (n + 1)) (h : j ≠ i) : Fin n :=
  if hlt : j.val < i.val then
    ⟨j.val, by omega⟩
  else
    ⟨j.val - 1, by omega⟩

/-- Insert a remaining-variable index around the distinguished position.  This
is the Mathlib-free coordinate map denoted `Fin.succAbove i` in the SPEC. -/
def remainingVar (i : Fin (n + 1)) (j : Fin n) : Fin (n + 1) :=
  if j.val < i.val then
    ⟨j.val, by omega⟩
  else
    ⟨j.val + 1, by omega⟩

/-- Re-inserting a removed non-main index recovers the original index. -/
@[simp] theorem remainingVar_remainingIndex (i j : Fin (n + 1)) (h : j ≠ i) :
    remainingVar i (remainingIndex i j h) = j := by
  unfold remainingIndex
  split
  case isTrue hlt =>
    unfold remainingVar
    rw [if_pos hlt]
  case isFalse hnlt =>
    have hval : j.val ≠ i.val := by
      intro hv
      exact h (Fin.ext hv)
    have hinsert : ¬ (j.val - 1 < i.val) := by omega
    unfold remainingVar
    rw [if_neg hinsert]
    apply Fin.ext
    simp
    omega

/-- One descending synthetic-division pass over low-to-high coefficients.
The prefix below `k` is already final.  A right fold keeps the newly updated
higher coefficient at the head of its accumulator, so every remaining
coefficient is visited exactly once. -/
def shiftPass {R : Type} [Lean.Grind.Semiring R]
    (z : R) (coeffs : List R) (k : Nat) : List R :=
  let finalized := coeffs.take k
  let suffix := coeffs.drop k
  finalized ++ suffix.foldr
    (fun coefficient shifted =>
      match shifted with
      | [] => [coefficient]
      | next :: _ => (coefficient + z * next) :: shifted)
    []

/-- Translate one dense univariate polynomial by repeated synthetic division,
without materialising powers of the binomial `X + z`. -/
def shiftDense {R : Type} [Lean.Grind.Semiring R] [DecidableEq R]
    (z : R) (p : DensePoly R) : DensePoly R :=
  let coeffs := (List.range p.size).foldl (shiftPass z) p.toArray.toList
  DensePoly.ofList coeffs

/-- Arity-indexed Taylor translation.  The recursive view shifts every
coefficient in the remaining variables, then applies the dense synthetic
division loop in variable zero. -/
structure ShiftOpsAt (n : Nat) where
  run : (cmp : Mono n → Mono n → Ordering) → [IsMonomialOrder cmp] →
    (Fin n → Int) → MvPoly n Int cmp → MvPoly n Int cmp

def shiftOps : (n : Nat) → ShiftOpsAt n
  | 0 =>
      { run := fun _ _ _ p => p }
  | n + 1 =>
      let lower := shiftOps n
      { run := fun cmp _ a p =>
          let view := MvPoly.toUnivariate (0 : Fin (n + 1)) Mono.lex p
          let coeffs := view.toArray.toList.map fun coefficient =>
            lower.run Mono.lex (fun j => a j.succ) coefficient
          let translated :=
            if a 0 = 0 then DensePoly.ofList coeffs
            else shiftDense (C (a 0)) (DensePoly.ofList coeffs)
          MvPoly.ofUnivariate (cmp := cmp) (0 : Fin (n + 1)) Mono.lex translated }

/-- Translate every variable by the corresponding component of `a`. -/
def shiftAll [IsMonomialOrder cmp'] (a : Fin n → Int) (p : MvPoly n Int cmp') :
    MvPoly n Int cmp' :=
  (shiftOps n).run cmp' a p

/-- Translate every variable by the negative of the corresponding component. -/
def unshiftAll [IsMonomialOrder cmp'] (a : Fin n → Int) (p : MvPoly n Int cmp') :
    MvPoly n Int cmp' :=
  shiftAll (fun j => -a j) p

/-- Replacement polynomial for one variable in the affine coordinate shift.
The main variable is fixed; every other variable receives the matching entry
of the point with the main coordinate removed. -/
def shiftVar (i : Fin (n + 1)) (a : Fin n → Int)
    (j : Fin (n + 1)) : MvPoly (n + 1) Int cmp :=
  if h : j = i then X j
  else X j + C (a (remainingIndex i j h))

/-- Substitute `x_(i.succAbove j) ↦ x_(i.succAbove j) + a j`, fixing the
main variable `x_i`. -/
def shift (i : Fin (n + 1)) (a : Fin n → Int)
    (p : MvPoly (n + 1) Int cmp) : MvPoly (n + 1) Int cmp :=
  shiftAll (fun j => if h : j = i then 0 else a (remainingIndex i j h)) p

/-- Undo `shift i a`. -/
def unshift (i : Fin (n + 1)) (a : Fin n → Int)
    (p : MvPoly (n + 1) Int cmp) : MvPoly (n + 1) Int cmp :=
  shift i (fun j => -a j) p

/-- The univariate image at `a`, obtained by sparse Horner evaluation of every
coefficient in the recursive view in the non-main variables. -/
def imageAt (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (a : Fin n → Int) (p : MvPoly (n + 1) Int cmp) : DensePoly Int :=
  let q := MvPoly.toUnivariate i cmp' p
  DensePoly.ofCoeffs (q.toArray.map fun c => MvPoly.evalHorner a c)

/-- Leading coefficient in the chosen main variable, as a polynomial in the
remaining variables. -/
def lcIn (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (p : MvPoly (n + 1) Int cmp) : MvPoly n Int cmp' :=
  (MvPoly.toUnivariate i cmp' p).leadingCoeff

/-- Delete every term whose exponent in a non-main variable exceeds the
corresponding component of `d`. -/
def truncate (i : Fin (n + 1)) (d : Fin n → Nat)
    (p : MvPoly (n + 1) Int cmp) : MvPoly (n + 1) Int cmp :=
  p.restrictBy fun m =>
    decide (∀ j : Fin n, Mono.degreeOf (remainingVar i j) m ≤ d j)

/-! The coordinate laws used by the lift. -/

@[simp] theorem shift_unshift (i : Fin (n + 1)) (a : Fin n → Int)
    (p : MvPoly (n + 1) Int cmp) :
    unshift i a (shift i a p) = p := by
  sorry

@[simp] theorem unshift_shift (i : Fin (n + 1)) (a : Fin n → Int)
    (p : MvPoly (n + 1) Int cmp) :
    shift i a (unshift i a p) = p := by
  simpa [unshift] using shift_unshift i (fun j => -a j) p

theorem shift_add (i : Fin (n + 1)) (a : Fin n → Int)
    (p q : MvPoly (n + 1) Int cmp) :
    shift i a (p + q) = shift i a p + shift i a q := by
  sorry

theorem shift_mul (i : Fin (n + 1)) (a : Fin n → Int)
    (p q : MvPoly (n + 1) Int cmp) :
    shift i a (p * q) = shift i a p * shift i a q := by
  sorry

theorem degreeOf_shift (i j : Fin (n + 1)) (a : Fin n → Int)
    (p : MvPoly (n + 1) Int cmp) :
    MvPoly.degreeOf j (shift i a p) = MvPoly.degreeOf j p := by
  sorry

theorem lcIn_shift (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (a : Fin n → Int) (p : MvPoly (n + 1) Int cmp) :
    lcIn i cmp' (shift i a p) = shiftAll a (lcIn i cmp' p) := by
  sorry

theorem imageAt_shift (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (a : Fin n → Int) (p : MvPoly (n + 1) Int cmp) :
    imageAt i cmp' (fun _ => 0) (shift i a p) = imageAt i cmp' a p := by
  sorry

/-- Truncation has the expected coefficient projection. -/
theorem coeff_truncate (i : Fin (n + 1)) (d : Fin n → Nat)
    (m : Mono (n + 1)) (p : MvPoly (n + 1) Int cmp) :
    MvPoly.coeff m (truncate i d p) =
      if ∀ j : Fin n, Mono.degreeOf (remainingVar i j) m ≤ d j then
        MvPoly.coeff m p
      else 0 := by
  unfold truncate
  rw [MvPoly.coeff_restrictBy]
  simp only [decide_eq_true_eq]

end Hex.MvHensel
