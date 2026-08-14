/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.Operations

@[expose] public section

/-!
The Mathlib-free multivariate polynomial ring instance.

`HexMvPoly.Operations` proves the ring laws as standalone lemmas so the
arithmetic does not impose an algebra hierarchy. Consumers that recurse into
polynomial coefficient rings need those laws packaged, so this file supplies
the numeral and scalar-multiplication operations and assembles the existing
lemmas into `Lean.Grind.CommRing`.

The consumer that forces this is `HexResultant`: its subresultant chain runs
over any coefficient type with `Div` and `ExactDivLaws`, but every one of its
correctness theorems takes `[Lean.Grind.CommRing S]`. Without the instance
below the chain computes over `MvPoly n R cmp` and none of its theorems apply.
`HexResultant.ExactDiv` builds the same tower for `DensePoly`.
-/

namespace Hex.MvPoly

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [BEq R] [LawfulBEq R]

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

/-- Natural number numerals, as constant polynomials. -/
instance instNatCast [Lean.Grind.CommRing R] [DecidableEq R] :
    NatCast (MvPoly n R cmp) :=
  ⟨fun k =>
    match k with
    | 0 => Zero.zero
    | 1 => One.one
    | k + 2 => C (Nat.cast (k + 2))⟩

instance instOfNat [Lean.Grind.CommRing R] [DecidableEq R] (k : Nat) :
    OfNat (MvPoly n R cmp) k :=
  ⟨match k with
    | 0 => Zero.zero
    | 1 => One.one
    | k + 2 => C (OfNat.ofNat (k + 2))⟩

instance instNSMul [Lean.Grind.CommRing R] [DecidableEq R] :
    SMul Nat (MvPoly n R cmp) :=
  ⟨fun k p => (Nat.cast k : MvPoly n R cmp) * p⟩

instance instIntCast [Lean.Grind.CommRing R] [DecidableEq R] :
    IntCast (MvPoly n R cmp) :=
  ⟨fun i =>
    match i with
    | .ofNat k => (Nat.cast k : MvPoly n R cmp)
    | .negSucc k => -(Nat.cast (k + 1) : MvPoly n R cmp)⟩

instance instZSMul [Lean.Grind.CommRing R] [DecidableEq R] :
    SMul Int (MvPoly n R cmp) :=
  ⟨fun i p =>
    match i with
    | .ofNat k => k • p
    | .negSucc k => -((k + 1) • p)⟩

/-- Numerals are constant polynomials. -/
@[simp]
theorem coeff_ofNat [Lean.Grind.CommRing R] [DecidableEq R] (k : Nat)
    (m : Mono n) :
    coeff m (OfNat.ofNat (α := MvPoly n R cmp) k) =
      if m = Mono.zero then OfNat.ofNat (α := R) k else 0 := by
  match k with
  | 0 =>
      change coeff m (0 : MvPoly n R cmp) = if m = Mono.zero then (0 : R) else 0
      rw [coeff_zero]
      by_cases hm : m = Mono.zero <;> simp only [hm, if_true, if_false]
  | 1 =>
      change coeff m (1 : MvPoly n R cmp) = if m = Mono.zero then (1 : R) else 0
      exact coeff_one m
  | k + 2 =>
      change coeff m (C (OfNat.ofNat (α := R) (k + 2))) = _
      exact coeff_C m _

/-- The canonical map from the natural numbers lands in the constants. -/
@[simp]
theorem coeff_natCast [Lean.Grind.CommRing R] [DecidableEq R] (k : Nat)
    (m : Mono n) :
    coeff m (Nat.cast k : MvPoly n R cmp) =
      if m = Mono.zero then (Nat.cast k : R) else 0 := by
  match k with
  | 0 =>
      change coeff m (0 : MvPoly n R cmp) = _
      rw [coeff_zero, Lean.Grind.Semiring.natCast_zero]
      by_cases hm : m = Mono.zero <;> simp only [hm, if_true, if_false]
  | 1 =>
      change coeff m (1 : MvPoly n R cmp) = _
      rw [coeff_one, Lean.Grind.Semiring.natCast_one]
  | k + 2 =>
      change coeff m (C ((Nat.cast (k + 2) : R))) = _
      exact coeff_C m _

/-- The zeroth power is one.

`npowBySq` is defined by well-founded recursion, so it is `@[irreducible]` and
`rfl` does not see through it; the equation lemma does. -/
theorem pow_zero [Lean.Grind.CommRing R] [DecidableEq R]
    (p : MvPoly n R cmp) : p ^ 0 = 1 := by
  change npowBySq p 0 = 1
  simp [npowBySq]

/-- Negating zero gives zero. -/
@[simp]
theorem neg_zero [Lean.Grind.CommRing R] [DecidableEq R] :
    -(0 : MvPoly n R cmp) = 0 := by
  apply ext
  intro m
  rw [coeff_neg, coeff_zero]
  grind

/-- Negation is an involution. -/
@[simp]
theorem neg_neg [Lean.Grind.CommRing R] [DecidableEq R]
    (p : MvPoly n R cmp) : -(-p) = p := by
  apply ext
  intro m
  rw [coeff_neg, coeff_neg]
  grind

/-- Negation is the left inverse of addition. -/
theorem neg_add_cancel [Lean.Grind.CommRing R] [DecidableEq R]
    (p : MvPoly n R cmp) : -p + p = 0 := by
  apply ext
  intro m
  rw [coeff_add, coeff_neg, coeff_zero]
  grind

/-- Subtraction is addition of the negation. -/
theorem sub_eq_add_neg [Lean.Grind.CommRing R] [DecidableEq R]
    (p q : MvPoly n R cmp) : p - q = p + -q := rfl

/-- Multiplying by a natural numeral is scalar multiplication. -/
theorem nsmul_eq_natCast_mul [Lean.Grind.CommRing R] [DecidableEq R]
    (k : Nat) (p : MvPoly n R cmp) :
    k • p = (Nat.cast k : MvPoly n R cmp) * p := rfl

/-- Successor numerals add one. -/
theorem ofNat_succ [Lean.Grind.CommRing R] [DecidableEq R] (k : Nat) :
    (OfNat.ofNat (α := MvPoly n R cmp) (k + 1)) =
      OfNat.ofNat (α := MvPoly n R cmp) k + 1 := by
  apply ext
  intro m
  rw [coeff_add, coeff_ofNat, coeff_ofNat, coeff_one]
  by_cases hm : m = Mono.zero
  · simpa only [hm, if_true] using (Lean.Grind.Semiring.ofNat_succ (α := R) k)
  · simp only [hm, if_false]
    grind

/-- Numerals agree with the canonical map from the natural numbers. -/
theorem ofNat_eq_natCast [Lean.Grind.CommRing R] [DecidableEq R] (k : Nat) :
    (OfNat.ofNat (α := MvPoly n R cmp) k) = (Nat.cast k : MvPoly n R cmp) := by
  apply ext
  intro m
  rw [coeff_ofNat, coeff_natCast]
  by_cases hm : m = Mono.zero
  · simpa only [hm, if_true] using (Lean.Grind.Semiring.ofNat_eq_natCast (α := R) k)
  · simp only [hm, if_false]

/-- Multivariate polynomials over a lightweight commutative ring form a
lightweight semiring. -/
instance instGrindSemiring [Lean.Grind.CommRing R] [DecidableEq R] :
    Lean.Grind.Semiring (MvPoly n R cmp) := by
  refine Lean.Grind.Semiring.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact add_zero
  · exact add_comm
  · exact add_assoc
  · exact mul_assoc
  · exact mul_one
  · exact one_mul
  · exact mul_add
  · exact add_mul
  · exact zero_mul
  · exact mul_zero
  · exact pow_zero
  · exact pow_succ
  · exact ofNat_succ
  · exact ofNat_eq_natCast
  · exact nsmul_eq_natCast_mul

/-- Multivariate polynomials over a lightweight commutative ring form a
lightweight ring. -/
instance instGrindRing [Lean.Grind.CommRing R] [DecidableEq R] :
    Lean.Grind.Ring (MvPoly n R cmp) := by
  refine Lean.Grind.Ring.mk ?_ ?_ ?_ ?_ ?_ ?_
  · exact neg_add_cancel
  · exact sub_eq_add_neg
  · intro i p
    cases i with
    | ofNat k =>
        cases k with
        | zero =>
            show (0 : Nat) • p = -((0 : Nat) • p)
            change (Nat.cast 0 : MvPoly n R cmp) * p =
              -((Nat.cast 0 : MvPoly n R cmp) * p)
            rw [show (Nat.cast 0 : MvPoly n R cmp) = 0 from rfl, zero_mul,
              neg_zero]
        | succ k => rfl
    | negSucc k =>
        show (k + 1 : Nat) • p = -(-((k + 1 : Nat) • p))
        rw [neg_neg]
  · intro k p
    rfl
  · intro k
    show (Nat.cast k : MvPoly n R cmp) = OfNat.ofNat k
    exact (ofNat_eq_natCast k).symm
  · intro i
    cases i with
    | ofNat k =>
        cases k with
        | zero =>
            show (Nat.cast 0 : MvPoly n R cmp) = -(Nat.cast 0 : MvPoly n R cmp)
            rw [show (Nat.cast 0 : MvPoly n R cmp) = 0 from rfl, neg_zero]
        | succ k => rfl
    | negSucc k =>
        show (Nat.cast (k + 1) : MvPoly n R cmp) =
          -(-(Nat.cast (k + 1) : MvPoly n R cmp))
        rw [neg_neg]

/-- Multivariate polynomial multiplication is commutative when coefficient
multiplication is. -/
instance instGrindCommRing [Lean.Grind.CommRing R] [DecidableEq R] :
    Lean.Grind.CommRing (MvPoly n R cmp) := by
  refine Lean.Grind.CommRing.mk ?_
  exact mul_comm

end Hex.MvPoly
