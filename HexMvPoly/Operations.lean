/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.Basic

@[expose] public section

/-!
Canonical sparse arithmetic for `Hex.MvPoly`.

Addition folds the smaller operation stream into one tree, and multiplication
uses a Gustavson-style double traversal with a single output accumulator.
-/

namespace Hex.MvPoly

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- Polynomial addition, combining equal monomials and deleting cancellations. -/
def add [Lean.Grind.Semiring R] [DecidableEq R]
    (p q : MvPoly n R cmp) : MvPoly n R cmp :=
  q.foldTerms (fun acc m c => acc.addMonomial m c) p

instance [Lean.Grind.Semiring R] [DecidableEq R] :
    Add (MvPoly n R cmp) where
  add := add

theorem negCoeff_ne_zero [Lean.Grind.Ring R] (c : R) (hc : c ≠ 0) :
    -c ≠ 0 := by
  grind

/-- Coefficientwise negation. Since negation preserves nonzeroness, this
maps values in place without rebuilding the search tree. -/
def neg [Lean.Grind.Ring R] (p : MvPoly n R cmp) : MvPoly n R cmp :=
  p.mapCoeffs (fun c => -c) negCoeff_ne_zero

instance [Lean.Grind.Ring R] : Neg (MvPoly n R cmp) where
  neg := neg

/-- Polynomial subtraction. -/
def sub [Lean.Grind.Ring R] [DecidableEq R]
    (p q : MvPoly n R cmp) : MvPoly n R cmp :=
  add p (neg q)

instance [Lean.Grind.Ring R] [DecidableEq R] :
    Sub (MvPoly n R cmp) where
  sub := sub

/-- Polynomial multiplication. Every translated product term is accumulated
directly into one output map, so collisions and cancellations are normalized
as they arise. -/
def mul [Lean.Grind.Semiring R] [DecidableEq R]
    (p q : MvPoly n R cmp) : MvPoly n R cmp :=
  p.foldTerms
    (fun acc mp cp =>
      q.foldTerms
        (fun acc mq cq => acc.addMonomial (Mono.mul mp mq) (cp * cq))
        acc)
    0

instance [Lean.Grind.Semiring R] [DecidableEq R] :
    Mul (MvPoly n R cmp) where
  mul := mul

/-- Multiplicative identity. -/
def one [Lean.Grind.Semiring R] [DecidableEq R] : MvPoly n R cmp :=
  C 1

instance [Lean.Grind.Semiring R] [DecidableEq R] :
    One (MvPoly n R cmp) where
  one := one

/-- Exponentiation by repeated squaring. -/
def npowBySq [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) : Nat → MvPoly n R cmp
  | 0 => 1
  | k + 1 =>
      let q := npowBySq p ((k + 1) / 2)
      let q2 := q * q
      if (k + 1) % 2 = 0 then q2 else q2 * p
termination_by k => k
decreasing_by omega

instance [Lean.Grind.Semiring R] [DecidableEq R] :
    Pow (MvPoly n R cmp) Nat where
  pow := npowBySq

@[simp] theorem coeff_one [Lean.Grind.Semiring R] [DecidableEq R]
    (m : Mono n) :
    coeff m (1 : MvPoly n R cmp) =
      if m = Mono.zero then 1 else 0 := by
  change coeff m (C 1) = _
  exact coeff_C m 1

theorem coeff_add [Lean.Grind.Semiring R] [DecidableEq R]
    (m : Mono n) (p q : MvPoly n R cmp) :
    coeff m (p + q) = coeff m p + coeff m q := by
  sorry

theorem coeff_neg [Lean.Grind.Ring R] (m : Mono n) (p : MvPoly n R cmp) :
    coeff m (-p) = -coeff m p := by
  sorry

theorem coeff_sub [Lean.Grind.Ring R] [DecidableEq R]
    (m : Mono n) (p q : MvPoly n R cmp) :
    coeff m (p - q) = coeff m p - coeff m q := by
  sorry

theorem coeff_mul [Lean.Grind.Semiring R] [DecidableEq R]
    (m : Mono n) (p q : MvPoly n R cmp) :
    coeff m (p * q) =
      (Mono.splits m).foldl
        (fun acc ab => acc + coeff ab.1 p * coeff ab.2 q) 0 := by
  sorry

theorem coeff_pow_succ [Lean.Grind.Semiring R] [DecidableEq R]
    (m : Mono n) (p : MvPoly n R cmp) (k : Nat) :
    coeff m (p ^ (k + 1)) = coeff m (p ^ k * p) := by
  sorry

theorem npowBySq_eq_pow [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) (k : Nat) :
    npowBySq p k = p ^ k := by
  rfl

end Hex.MvPoly
