/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGF2.Field.Poly

public section

/-!
Root counting and the Frobenius endomorphism for the packed quotient
`GF2nPoly`.

A polynomial over the quotient has at most `degree` roots in it; that bound is
what the Frobenius fixed-point arguments need, and those in turn are what say
the fixed field of the `k`-fold Frobenius is the subfield of degree dividing
`k`. Everything here is proof-facing: `evalCoeffList` and `linearPow` have
simple recursion equations rather than the executable shapes, which stay in
`HexGF2.Field.Poly`.
-/

namespace Hex

namespace GF2nPoly

variable {f : GF2Poly} {hirr : GF2Poly.Irreducible f}

/-! # Quotient-coefficient polynomial evaluation -/

/--
Evaluate a low-to-high quotient-coefficient list at a quotient point.

The list `[c₀, c₁, ...]` denotes `c₀ + β * (c₁ + β * (...))`. This
proof-facing evaluator is separate from executable packed polynomial
evaluation; it is used by quotient-field root-count arguments.
-/
@[expose]
def evalCoeffList : List (GF2nPoly f hirr) → GF2nPoly f hirr → GF2nPoly f hirr
  | [], _ => 0
  | c :: cs, β => c + β * evalCoeffList cs β

/-- Evaluating the empty coefficient list yields `0`. -/
@[simp, grind =] theorem evalCoeffList_nil (β : GF2nPoly f hirr) :
    evalCoeffList ([] : List (GF2nPoly f hirr)) β = 0 :=
  rfl

/-- Horner recursion equation: evaluating `c :: cs` at `β` peels off the head
coefficient `c` and folds the tail through one more multiplication by `β`. -/
@[simp, grind =] theorem evalCoeffList_cons
    (c : GF2nPoly f hirr) (cs : List (GF2nPoly f hirr))
    (β : GF2nPoly f hirr) :
    evalCoeffList (c :: cs) β = c + β * evalCoeffList cs β :=
  rfl

namespace Internal

/--
Internal root-count helper: synthetic quotient coefficients for the divided
difference of `cs` at the base point `α`.

If `P` is represented by `cs`, this list represents the quotient
`(P(T) + P(α)) / (T + α)` in characteristic two. Its length is one less
than the input list, which is the measure used by root-count induction.
-/
@[expose]
def dividedDifferenceCoeffs :
    List (GF2nPoly f hirr) → GF2nPoly f hirr → List (GF2nPoly f hirr)
  | [], _ => []
  | [_], _ => []
  | _ :: c :: cs, α =>
      evalCoeffList (c :: cs) α :: dividedDifferenceCoeffs (c :: cs) α

/-- The divided-difference coefficient list of the zero polynomial is empty. -/
@[simp, grind =] theorem dividedDifferenceCoeffs_nil (α : GF2nPoly f hirr) :
    dividedDifferenceCoeffs ([] : List (GF2nPoly f hirr)) α = [] :=
  rfl

/-- A constant coefficient list has no divided-difference coefficients. -/
@[simp, grind =] theorem dividedDifferenceCoeffs_singleton
    (c : GF2nPoly f hirr) (α : GF2nPoly f hirr) :
    dividedDifferenceCoeffs ([c] : List (GF2nPoly f hirr)) α = [] :=
  rfl

/-- Divided differences peel the tail polynomial evaluated at the base point. -/
@[simp, grind =] theorem dividedDifferenceCoeffs_cons_cons
    (c d : GF2nPoly f hirr) (cs : List (GF2nPoly f hirr))
    (α : GF2nPoly f hirr) :
    dividedDifferenceCoeffs (c :: d :: cs) α =
      evalCoeffList (d :: cs) α :: dividedDifferenceCoeffs (d :: cs) α :=
  rfl

/-- The synthetic divided-difference coefficient list has one fewer entry. -/
@[simp, grind =] theorem dividedDifferenceCoeffs_length
    (cs : List (GF2nPoly f hirr)) (α : GF2nPoly f hirr) :
    (dividedDifferenceCoeffs cs α).length = cs.length - 1 := by
  induction cs with
  | nil =>
      rfl
  | cons c cs ih =>
      cases cs with
      | nil =>
          rfl
      | cons d ds =>
          simp [dividedDifferenceCoeffs, ih]

/-- Internal root-count helper: evaluate the divided difference of a
quotient-coefficient polynomial between the base point `α` and target point
`β`. -/
@[expose]
def dividedDifference
    (cs : List (GF2nPoly f hirr)) (α β : GF2nPoly f hirr) : GF2nPoly f hirr :=
  evalCoeffList (dividedDifferenceCoeffs cs α) β

/-- The divided difference of an empty coefficient list is zero. -/
@[simp, grind =] theorem dividedDifference_nil (α β : GF2nPoly f hirr) :
    dividedDifference ([] : List (GF2nPoly f hirr)) α β = 0 := by
  simp [dividedDifference, dividedDifferenceCoeffs]

/-- The divided difference of a nonconstant list satisfies the synthetic
recurrence used by the root-count induction. -/
@[simp, grind =] theorem dividedDifference_cons
    (c d : GF2nPoly f hirr) (cs : List (GF2nPoly f hirr))
    (α β : GF2nPoly f hirr) :
    dividedDifference (c :: d :: cs) α β =
      evalCoeffList (d :: cs) α + β * dividedDifference (d :: cs) α β := by
  simp [dividedDifference, dividedDifferenceCoeffs, evalCoeffList]

private theorem add_self_right (a b : GF2nPoly f hirr) :
    a + (b + a) = b := by
  calc
    a + (b + a) = a + (a + b) := by rw [add_comm b a]
    _ = (a + a) + b := by rw [add_assoc]
    _ = b := by rw [add_self, zero_add]

/--
The quotient-coefficient divided difference satisfies
`P(β) + P(α) = (β + α) * DD(P, α, β)`.

This is the characteristic-two orientation of the usual
`P(β) - P(α) = (β - α) * Q(β)` identity, and is the API consumed by
the root-count induction.
-/
theorem evalCoeffList_add_evalCoeffList_eq_add_mul_dividedDifference
    (cs : List (GF2nPoly f hirr)) (α β : GF2nPoly f hirr) :
    evalCoeffList cs β + evalCoeffList cs α =
      (β + α) * dividedDifference cs α β := by
  induction cs with
  | nil =>
      simp [dividedDifference]
  | cons c cs ih =>
      cases cs with
      | nil =>
          simp [dividedDifference, dividedDifferenceCoeffs]
      | cons d ds =>
          let Eβ := evalCoeffList (d :: ds) β
          let Eα := evalCoeffList (d :: ds) α
          let D := dividedDifference (d :: ds) α β
          have htail : Eβ + Eα = (β + α) * D := ih
          have hEβ : Eβ = Eα + (β + α) * D := by
            calc
              Eβ = Eα + (Eβ + Eα) := by
                exact (add_self_right (f := f) (hirr := hirr) Eα Eβ).symm
              _ = Eα + (β + α) * D := by rw [htail]
          calc
            evalCoeffList (c :: d :: ds) β + evalCoeffList (c :: d :: ds) α
                = (c + β * Eβ) + (c + α * Eα) := rfl
            _ = (c + c) + (β * Eβ + α * Eα) := by
                  exact add_pair_swap_quot c (β * Eβ) c (α * Eα)
            _ = β * Eβ + α * Eα := by rw [add_self, zero_add]
            _ = β * (Eα + (β + α) * D) + α * Eα := by rw [hEβ]
            _ = (β * Eα + β * ((β + α) * D)) + α * Eα := by
                  rw [left_distrib]
            _ = (β * Eα + α * Eα) + β * ((β + α) * D) := by
                  rw [add_assoc, add_comm (β * ((β + α) * D)) (α * Eα),
                    ← add_assoc]
            _ = (β + α) * Eα + β * ((β + α) * D) := by
                  rw [← right_distrib β α Eα]
            _ = (β + α) * Eα + (β * (β + α)) * D := by
                  rw [mul_assoc]
            _ = (β + α) * Eα + ((β + α) * β) * D := by
                  rw [mul_comm β (β + α)]
            _ = (β + α) * Eα + (β + α) * (β * D) := by
                  rw [mul_assoc]
            _ = (β + α) * (Eα + β * D) := by
                  rw [left_distrib]
            _ = (β + α) * dividedDifference (c :: d :: ds) α β := rfl

end Internal

/-- Iterated Frobenius preserves multiplication in the packed quotient. -/
@[grind =>] theorem frobeniusIter_mul (a b : GF2nPoly f hirr) (k : Nat) :
    frobeniusIter (a * b) k = frobeniusIter a k * frobeniusIter b k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [frobeniusIter_succ, ih, frobeniusIter_succ, frobeniusIter_succ]
      let x := frobeniusIter a k
      let y := frobeniusIter b k
      change (x * y) * (x * y) = (x * x) * (y * y)
      calc
        (x * y) * (x * y) = x * (y * (x * y)) := by rw [mul_assoc]
        _ = x * ((y * x) * y) := by rw [mul_assoc y x y]
        _ = x * ((x * y) * y) := by rw [mul_comm y x]
        _ = x * (x * (y * y)) := by rw [mul_assoc x y y]
        _ = (x * x) * (y * y) := by rw [← mul_assoc]

/-- Iterated Frobenius preserves addition in the packed quotient. -/
@[grind =>] theorem frobeniusIter_add_eq (a b : GF2nPoly f hirr) (k : Nat) :
    frobeniusIter (a + b) k = frobeniusIter a k + frobeniusIter b k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [frobeniusIter_succ, ih, frobeniusIter_succ, frobeniusIter_succ, add_sq]

/-- Zero is fixed by every iterated Frobenius. -/
@[simp, grind =] theorem frobeniusIter_zero_eq (k : Nat) :
    frobeniusIter (0 : GF2nPoly f hirr) k = 0 := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [frobeniusIter_succ, ih, zero_mul]

/-- Fixed packed quotient elements are closed under addition for a shared
Frobenius iterate. -/
@[grind =>] theorem frobeniusIter_fixed_add {a b : GF2nPoly f hirr} {k : Nat}
    (ha : frobeniusIter a k = a) (hb : frobeniusIter b k = b) :
    frobeniusIter (a + b) k = a + b := by
  rw [frobeniusIter_add_eq, ha, hb]

/-- Fixed packed quotient elements are closed under multiplication for a shared
Frobenius iterate. -/
@[grind =>] theorem frobeniusIter_fixed_mul {a b : GF2nPoly f hirr} {k : Nat}
    (ha : frobeniusIter a k = a) (hb : frobeniusIter b k = b) :
    frobeniusIter (a * b) k = a * b := by
  rw [frobeniusIter_mul, ha, hb]

/-- One is fixed by every iterated Frobenius. -/
@[simp, grind =] theorem frobeniusIter_one_eq (k : Nat) :
    frobeniusIter (1 : GF2nPoly f hirr) k = 1 := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [frobeniusIter_succ, ih, one_mul]

/-- Reducing the constant-one monomial gives the quotient one. -/
@[simp, grind =] theorem reducePoly_monomial_zero :
    reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial 0) = 1 := by
  rfl

/-- If the quotient class of `X` is fixed by a Frobenius iterate, then every
monomial quotient class is fixed by the same iterate. -/
theorem frobeniusIter_reducePoly_monomial_eq_self_of_X_fixed {k : Nat}
    (hX : frobeniusIter (X (f := f) (hirr := hirr)) k =
      X (f := f) (hirr := hirr)) :
    ∀ n : Nat,
      frobeniusIter
          (reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial n)) k =
        reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial n)
  | 0 => by
      rw [reducePoly_monomial_zero, frobeniusIter_one_eq]
  | n + 1 => by
      have ih := frobeniusIter_reducePoly_monomial_eq_self_of_X_fixed hX n
      have hprod :
          reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial (n + 1)) =
            X (f := f) (hirr := hirr) *
              reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial n) := by
        calc
          reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial (n + 1))
              = reducePoly (f := f) (hirr := hirr)
                  (GF2Poly.monomial 1 * GF2Poly.monomial n) := by
                    rw [GF2Poly.monomial_mul_monomial, Nat.add_comm]
          _ = reducePoly (f := f) (hirr := hirr)
                ((reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial 1)).val *
                  (reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial n)).val) := by
                    rw [reducePoly_mul_eq]
          _ = X (f := f) (hirr := hirr) *
                reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial n) := rfl
      rw [hprod]
      exact frobeniusIter_fixed_mul hX ih

/-- If the quotient class of `X` is fixed by a Frobenius iterate, then any
Boolean coefficient list starting at an arbitrary monomial degree is fixed. -/
theorem frobeniusIter_reducePoly_ofBoolListFrom_eq_self_of_X_fixed {k : Nat}
    (hX : frobeniusIter (X (f := f) (hirr := hirr)) k =
      X (f := f) (hirr := hirr)) :
    ∀ (start : Nat) (bs : List Bool),
      frobeniusIter
          (reducePoly (f := f) (hirr := hirr)
            (GF2Poly.Internal.ofBoolListFrom start bs)) k =
        reducePoly (f := f) (hirr := hirr)
          (GF2Poly.Internal.ofBoolListFrom start bs)
  | start, [] => by
      rw [GF2Poly.Internal.ofBoolListFrom, reducePoly_zero]
      exact frobeniusIter_zero_eq (f := f) (hirr := hirr) k
  | start, b :: bs => by
      have htail :=
        frobeniusIter_reducePoly_ofBoolListFrom_eq_self_of_X_fixed hX (start + 1) bs
      have hterm :
          frobeniusIter
              (reducePoly (f := f) (hirr := hirr)
                (if b then GF2Poly.monomial start else 0)) k =
            reducePoly (f := f) (hirr := hirr)
              (if b then GF2Poly.monomial start else 0) := by
        cases b
        · change frobeniusIter (reducePoly (f := f) (hirr := hirr) 0) k =
              reducePoly (f := f) (hirr := hirr) 0
          rw [reducePoly_zero]
          exact frobeniusIter_zero_eq (f := f) (hirr := hirr) k
        · exact frobeniusIter_reducePoly_monomial_eq_self_of_X_fixed
            (f := f) (hirr := hirr) hX start
      have hsum :
          reducePoly (f := f) (hirr := hirr)
              ((if b then GF2Poly.monomial start else 0) +
                GF2Poly.Internal.ofBoolListFrom (start + 1) bs) =
            reducePoly (f := f) (hirr := hirr)
                (if b then GF2Poly.monomial start else 0) +
              reducePoly (f := f) (hirr := hirr)
                (GF2Poly.Internal.ofBoolListFrom (start + 1) bs) := by
        rw [reducePoly_add_eq]
        rfl
      change
        frobeniusIter
            (reducePoly (f := f) (hirr := hirr)
              ((if b then GF2Poly.monomial start else 0) +
                GF2Poly.Internal.ofBoolListFrom (start + 1) bs)) k =
          reducePoly (f := f) (hirr := hirr)
            ((if b then GF2Poly.monomial start else 0) +
              GF2Poly.Internal.ofBoolListFrom (start + 1) bs)
      rw [hsum]
      exact frobeniusIter_fixed_add hterm htail

/-- If the quotient class of `X` is fixed by a Frobenius iterate, then every
Boolean coefficient expression generated from `X` is fixed. -/
theorem frobeniusIter_boolListExpression_eq_self_of_X_fixed {k : Nat}
    (hX : frobeniusIter (X (f := f) (hirr := hirr)) k =
      X (f := f) (hirr := hirr)) (bs : List Bool) :
    frobeniusIter (boolListExpression (f := f) (hirr := hirr) bs) k =
      boolListExpression (f := f) (hirr := hirr) bs := by
  unfold boolListExpression GF2Poly.Internal.ofBoolList
  exact frobeniusIter_reducePoly_ofBoolListFrom_eq_self_of_X_fixed
    (f := f) (hirr := hirr) hX 0 bs

/-- If the quotient class of `X` is fixed by a Frobenius iterate, then every
packed quotient-field element is fixed by the same iterate. -/
theorem frobeniusIter_eq_self_of_X_fixed {k : Nat}
    (hX : frobeniusIter (X (f := f) (hirr := hirr)) k =
      X (f := f) (hirr := hirr)) (a : GF2nPoly f hirr) :
    frobeniusIter a k = a := by
  rcases exists_boolListExpression (f := f) (hirr := hirr) a with
    ⟨bs, _hlen, hbs⟩
  rw [← hbs]
  exact frobeniusIter_boolListExpression_eq_self_of_X_fixed
    (f := f) (hirr := hirr) hX bs

/-- The inverse cancels on the left for nonzero quotient elements. -/
theorem inv_mul_cancel (a : GF2nPoly f hirr) (ha : a ≠ 0) :
    a⁻¹ * a = 1 := by
  rw [mul_comm]
  exact mul_inv_cancel a ha

/-- The product of two nonzero packed quotient elements is nonzero. -/
theorem mul_ne_zero_of_ne_zero {a b : GF2nPoly f hirr}
    (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro hab
  apply hb
  calc b
      = 1 * b := (one_mul b).symm
    _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel a ha]
    _ = a⁻¹ * (a * b) := mul_assoc _ _ _
    _ = a⁻¹ * 0 := by rw [hab]
    _ = 0 := mul_zero _

/-- Left multiplication by a nonzero packed quotient element is injective. -/
theorem mul_left_injective {a : GF2nPoly f hirr} (ha : a ≠ 0)
    {b₁ b₂ : GF2nPoly f hirr} (heq : a * b₁ = a * b₂) :
    b₁ = b₂ := by
  have h : a⁻¹ * (a * b₁) = a⁻¹ * (a * b₂) := congrArg (fun x => a⁻¹ * x) heq
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel a ha, one_mul, one_mul] at h
  exact h

/-- Two `Nodup` lists with the same membership predicate are permutations. -/
private theorem perm_of_nodup_mem_iff
    {α : Type} :
    ∀ {xs ys : List α}, xs.Nodup → ys.Nodup →
      (∀ a, a ∈ xs ↔ a ∈ ys) → List.Perm xs ys
  | [], ys, _, _, hmem => by
      cases ys with
      | nil => exact .nil
      | cons y _ =>
          have hy : y ∈ ([] : List α) := (hmem y).mpr List.mem_cons_self
          exact absurd hy List.not_mem_nil
  | x :: xs', ys, hxs, hys, hmem => by
      have hxs_inv := List.nodup_cons.mp hxs
      have hx_not_in_xs' : x ∉ xs' := hxs_inv.1
      have hxs' : xs'.Nodup := hxs_inv.2
      have hx_mem : x ∈ ys := (hmem x).mp List.mem_cons_self
      obtain ⟨ys₁, ys₂, hys_eq⟩ := List.append_of_mem hx_mem
      subst hys_eq
      have hys_perm : List.Perm (ys₁ ++ x :: ys₂) (x :: (ys₁ ++ ys₂)) :=
        List.perm_middle
      have h_inner_nodup : (x :: (ys₁ ++ ys₂)).Nodup := hys_perm.nodup hys
      have h_inner_inv := List.nodup_cons.mp h_inner_nodup
      have hx_not_inner : x ∉ ys₁ ++ ys₂ := h_inner_inv.1
      have h_concat_nodup : (ys₁ ++ ys₂).Nodup := h_inner_inv.2
      have hmem' : ∀ a, a ∈ xs' ↔ a ∈ ys₁ ++ ys₂ := by
        intro a
        constructor
        · intro ha
          have ha_in_xs : a ∈ x :: xs' := List.mem_cons.mpr (Or.inr ha)
          have ha_in_ys : a ∈ ys₁ ++ x :: ys₂ := (hmem a).mp ha_in_xs
          have ha_in_split : a ∈ x :: (ys₁ ++ ys₂) := hys_perm.mem_iff.mp ha_in_ys
          rcases List.mem_cons.mp ha_in_split with hax | h
          · exact absurd (hax ▸ ha) hx_not_in_xs'
          · exact h
        · intro ha
          have ha_in_split : a ∈ x :: (ys₁ ++ ys₂) := List.mem_cons.mpr (Or.inr ha)
          have ha_in_ys : a ∈ ys₁ ++ x :: ys₂ := hys_perm.mem_iff.mpr ha_in_split
          have ha_in_xs : a ∈ x :: xs' := (hmem a).mpr ha_in_ys
          rcases List.mem_cons.mp ha_in_xs with hax | h
          · exact absurd (hax ▸ ha) hx_not_inner
          · exact h
      have ih_perm := perm_of_nodup_mem_iff hxs' h_concat_nodup hmem'
      exact (ih_perm.cons x).trans hys_perm.symm

namespace Internal

/--
The highest coefficient in a low-to-high quotient coefficient list is nonzero.

This predicate gives the syntactic degree bound consumed by the root-count
theorem: a list satisfying it represents a polynomial of degree strictly below
the list length, with actual degree exactly `length - 1`.
-/
@[expose]
def coeffListTopNonzero : List (GF2nPoly f hirr) → Prop
  | cs => ∃ c, cs.getLast? = some c ∧ c ≠ 0

private theorem coeffListTopNonzero_tail_of_cons_cons
    {c d : GF2nPoly f hirr} {cs : List (GF2nPoly f hirr)}
    (h : coeffListTopNonzero (c :: d :: cs)) :
    coeffListTopNonzero (d :: cs) := by
  simpa [coeffListTopNonzero] using h

private theorem dividedDifferenceCoeffs_getLast?
    (c d : GF2nPoly f hirr) (cs : List (GF2nPoly f hirr))
    (α : GF2nPoly f hirr) :
    (dividedDifferenceCoeffs (c :: d :: cs) α).getLast? =
      (d :: cs).getLast? := by
  induction cs generalizing c d with
  | nil =>
      simp [dividedDifferenceCoeffs, evalCoeffList]
  | cons e es ih =>
      cases es with
      | nil =>
          simp [dividedDifferenceCoeffs, evalCoeffList]
      | cons g gs =>
          simpa [dividedDifferenceCoeffs] using ih e g

private theorem coeffListTopNonzero_dividedDifferenceCoeffs
    (c d : GF2nPoly f hirr) (cs : List (GF2nPoly f hirr))
    (α : GF2nPoly f hirr)
    (h : coeffListTopNonzero (d :: cs)) :
    coeffListTopNonzero (dividedDifferenceCoeffs (c :: d :: cs) α) := by
  rcases h with ⟨top, hlast, htop⟩
  refine ⟨top, ?_, htop⟩
  rw [dividedDifferenceCoeffs_getLast?]
  exact hlast

/-- Internal root-count helper: roots of a quotient-coefficient polynomial
inside the canonical quotient enumeration. -/
@[expose]
def rootsOfCoeffList (cs : List (GF2nPoly f hirr)) : List (GF2nPoly f hirr) :=
  (elements (f := f) (hirr := hirr)).filter
    (fun β => decide (evalCoeffList cs β = 0))

/-- Membership in the computed root list is exactly vanishing of the
coefficient-list polynomial at that quotient element. -/
@[simp, grind =] theorem mem_rootsOfCoeffList
    (cs : List (GF2nPoly f hirr)) (β : GF2nPoly f hirr) :
    β ∈ rootsOfCoeffList (f := f) (hirr := hirr) cs ↔
      evalCoeffList cs β = 0 := by
  simp [rootsOfCoeffList, mem_elements β]

/-- The quotient-coefficient root list has no duplicate roots. -/
theorem rootsOfCoeffList_nodup (cs : List (GF2nPoly f hirr)) :
    (rootsOfCoeffList (f := f) (hirr := hirr) cs).Nodup := by
  unfold rootsOfCoeffList
  exact (elements_nodup (f := f) (hirr := hirr)).filter _

private theorem length_filter_le (p : α → Bool) :
    ∀ xs : List α, (xs.filter p).length ≤ xs.length
  | [] => by simp
  | x :: xs => by
      by_cases hx : p x = true
      · rw [List.filter_cons_of_pos hx]
        simp only [List.length_cons]
        exact Nat.succ_le_succ (length_filter_le p xs)
      · rw [List.filter_cons_of_neg hx]
        exact Nat.le_trans (length_filter_le p xs) (Nat.le_succ xs.length)

private theorem length_le_of_nodup_subset
    {α : Type} [DecidableEq α] {xs ys : List α}
    (hxs : xs.Nodup) (hys : ys.Nodup)
    (hsub : ∀ a, a ∈ xs → a ∈ ys) :
    xs.length ≤ ys.length := by
  let zs := ys.filter (fun a => decide (a ∈ xs))
  have hzs_nodup : zs.Nodup := hys.filter _
  have hmem : ∀ a, a ∈ xs ↔ a ∈ zs := by
    intro a
    constructor
    · intro ha
      exact List.mem_filter.mpr ⟨hsub a ha, decide_eq_true ha⟩
    · intro ha
      exact of_decide_eq_true (List.mem_filter.mp ha).2
  have hperm : List.Perm xs zs :=
    perm_of_nodup_mem_iff hxs hzs_nodup hmem
  have hlen_eq : xs.length = zs.length := hperm.length_eq
  calc
    xs.length = zs.length := hlen_eq
    _ ≤ ys.length := length_filter_le (fun a => decide (a ∈ xs)) ys

private theorem add_ne_zero_of_ne {a b : GF2nPoly f hirr} (h : a ≠ b) :
    a + b ≠ 0 := by
  intro hab
  apply h
  calc
    a = a + 0 := (add_zero a).symm
    _ = a + (a + b) := by rw [hab]
    _ = (a + a) + b := by rw [add_assoc]
    _ = b := by rw [add_self, zero_add]

private theorem roots_without_base_subset_dividedDifference_roots
    (c d : GF2nPoly f hirr) (cs : List (GF2nPoly f hirr))
    {α β : GF2nPoly f hirr}
    (hα : α ∈ rootsOfCoeffList (f := f) (hirr := hirr) (c :: d :: cs))
    (hβ : β ∈ rootsOfCoeffList (f := f) (hirr := hirr) (c :: d :: cs))
    (hβα : β ≠ α) :
    β ∈ rootsOfCoeffList (f := f) (hirr := hirr)
      (dividedDifferenceCoeffs (c :: d :: cs) α) := by
  have hα_eval :
      evalCoeffList (c :: d :: cs) α = 0 :=
    (mem_rootsOfCoeffList (f := f) (hirr := hirr) (c :: d :: cs) α).mp hα
  have hβ_eval :
      evalCoeffList (c :: d :: cs) β = 0 :=
    (mem_rootsOfCoeffList (f := f) (hirr := hirr) (c :: d :: cs) β).mp hβ
  have hident :=
    evalCoeffList_add_evalCoeffList_eq_add_mul_dividedDifference
      (f := f) (hirr := hirr) (c :: d :: cs) α β
  rw [hβ_eval, hα_eval, zero_add] at hident
  have hadd_ne : β + α ≠ 0 :=
    add_ne_zero_of_ne (f := f) (hirr := hirr) hβα
  have hdd_zero : dividedDifference (c :: d :: cs) α β = 0 := by
    apply mul_left_injective hadd_ne
    rw [mul_zero]
    exact hident.symm
  exact (mem_rootsOfCoeffList
    (f := f) (hirr := hirr)
    (dividedDifferenceCoeffs (c :: d :: cs) α) β).mpr hdd_zero

/--
A nonzero quotient-coefficient polynomial has at most its degree many roots in
the duplicate-free packed quotient enumeration.

The coefficient list is low-to-high, and `coeffListTopNonzero cs` says the
highest listed coefficient is nonzero, so the degree bound is `cs.length - 1`.
-/
theorem rootsOfCoeffList_length_le_degree
    (cs : List (GF2nPoly f hirr))
    (htop : coeffListTopNonzero (f := f) (hirr := hirr) cs) :
    (rootsOfCoeffList (f := f) (hirr := hirr) cs).length ≤ cs.length - 1 := by
  have hmain :
      ∀ n, ∀ cs : List (GF2nPoly f hirr), cs.length = n →
        coeffListTopNonzero (f := f) (hirr := hirr) cs →
        (rootsOfCoeffList (f := f) (hirr := hirr) cs).length ≤ cs.length - 1 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro cs hlen htop
        cases cs with
        | nil =>
            rcases htop with ⟨top, hlast, _htop_ne⟩
            simp at hlast
        | cons c cs =>
            cases cs with
            | nil =>
                rcases htop with ⟨top, hlast, htop_ne⟩
                simp at hlast
                subst top
                unfold rootsOfCoeffList
                simp [evalCoeffList, htop_ne]
            | cons d ds =>
                let P := c :: d :: ds
                let rootsP := rootsOfCoeffList (f := f) (hirr := hirr) P
                by_cases hnil : rootsP = []
                · rw [show rootsOfCoeffList (f := f) (hirr := hirr) P = [] from hnil]
                  simp
                · cases hrootsP : rootsP with
                  | nil =>
                      exact False.elim (hnil hrootsP)
                  | cons α rest =>
                      have hα : α ∈ rootsOfCoeffList (f := f) (hirr := hirr) P := by
                        show α ∈ rootsP
                        rw [hrootsP]
                        exact List.mem_cons_self
                      let rootsWithoutα :=
                        rootsP.filter (fun β => decide (β ≠ α))
                      let ddCoeffs := dividedDifferenceCoeffs P α
                      let rootsDD :=
                        rootsOfCoeffList (f := f) (hirr := hirr) ddCoeffs
                      have hrootsP_nodup : rootsP.Nodup := by
                        dsimp [rootsP]
                        exact rootsOfCoeffList_nodup (f := f) (hirr := hirr) P
                      have hα_filter_len :
                          rootsWithoutα.length = rootsP.length - 1 := by
                        exact length_filter_ne_eq_pred_of_mem_nodup
                          (z := α) hα hrootsP_nodup
                      have hdd_top : coeffListTopNonzero
                          (f := f) (hirr := hirr) ddCoeffs := by
                        dsimp [ddCoeffs, P]
                        exact coeffListTopNonzero_dividedDifferenceCoeffs
                          (f := f) (hirr := hirr) c d ds α
                          (coeffListTopNonzero_tail_of_cons_cons
                            (f := f) (hirr := hirr) htop)
                      have hsub :
                          ∀ β, β ∈ rootsWithoutα → β ∈ rootsDD := by
                        intro β hβ
                        have hβ_rootsP : β ∈ rootsP :=
                          (List.mem_filter.mp hβ).1
                        have hβ_ne : β ≠ α :=
                          of_decide_eq_true (List.mem_filter.mp hβ).2
                        dsimp [rootsDD, ddCoeffs, P]
                        exact roots_without_base_subset_dividedDifference_roots
                          (f := f) (hirr := hirr) c d ds hα hβ_rootsP hβ_ne
                      have hwithout_le_dd :
                          rootsWithoutα.length ≤ rootsDD.length := by
                        apply length_le_of_nodup_subset
                        · exact hrootsP_nodup.filter _
                        · dsimp [rootsDD]
                          exact rootsOfCoeffList_nodup
                            (f := f) (hirr := hirr) ddCoeffs
                        · exact hsub
                      have hdd_len : ddCoeffs.length = P.length - 1 := by
                        dsimp [ddCoeffs, P]
                        exact dividedDifferenceCoeffs_length
                          (f := f) (hirr := hirr) (c :: d :: ds) α
                      have hP_len : P.length = n := by
                        dsimp [P]
                        exact hlen
                      have hP_len_two : 2 ≤ P.length := by
                        dsimp [P]
                        simp
                      have hdd_lt : ddCoeffs.length < n := by
                        omega
                      have hdd_bound :
                          rootsDD.length ≤ ddCoeffs.length - 1 := by
                        dsimp [rootsDD]
                        exact ih ddCoeffs.length hdd_lt ddCoeffs rfl hdd_top
                      have hrootsP_pos : 0 < rootsP.length := by
                        rw [hrootsP]
                        simp
                      have hwithout_bound :
                          rootsWithoutα.length ≤ P.length - 2 := by
                        calc
                          rootsWithoutα.length ≤ rootsDD.length := hwithout_le_dd
                          _ ≤ ddCoeffs.length - 1 := hdd_bound
                          _ = P.length - 2 := by omega
                      have hrootsP_eq :
                          rootsP.length = rootsWithoutα.length + 1 := by
                        omega
                      have hrootsP_bound : rootsP.length ≤ P.length - 1 := by
                        omega
                      exact hrootsP_bound
  exact hmain cs.length cs rfl htop

/--
Direct root-count bound for the canonical `elements` filter form used by
callers.
-/
theorem evalCoeffList_rootsIn_elements_length_le_degree
    (cs : List (GF2nPoly f hirr))
    (htop : coeffListTopNonzero (f := f) (hirr := hirr) cs) :
    ((elements (f := f) (hirr := hirr)).filter
      (fun β => decide (evalCoeffList cs β = 0))).length ≤ cs.length - 1 :=
  rootsOfCoeffList_length_le_degree (f := f) (hirr := hirr) cs htop

end Internal

/-- Multiplication by a nonzero packed quotient element permutes the nonzero
enumeration. The list of nonzero elements multiplied on the left by `a` is a
permutation of the original nonzero list. -/
theorem nonzeroElements_map_mul_left_perm
    {a : GF2nPoly f hirr} (ha : a ≠ 0) :
    List.Perm
      ((nonzeroElements (f := f) (hirr := hirr)).map (fun b => a * b))
      (nonzeroElements (f := f) (hirr := hirr)) := by
  let L : List (GF2nPoly f hirr) := nonzeroElements (f := f) (hirr := hirr)
  have hL_nodup : L.Nodup :=
    nonzeroElements_nodup (f := f) (hirr := hirr)
  have hmap_inj :
      ∀ b₁, b₁ ∈ L → ∀ b₂, b₂ ∈ L →
        (fun b => a * b) b₁ = (fun b => a * b) b₂ → b₁ = b₂ := by
    intro b₁ _ b₂ _ heq
    exact mul_left_injective ha heq
  have hmap_nodup : (L.map (fun b => a * b)).Nodup :=
    nodup_map_of_injective hL_nodup hmap_inj
  have hmem_iff : ∀ c, c ∈ L.map (fun b => a * b) ↔ c ∈ L := by
    intro c
    constructor
    · intro hc
      rcases List.mem_map.mp hc with ⟨b, hb_mem, hbc⟩
      have hb_ne : b ≠ 0 := (mem_nonzeroElements b).mp hb_mem
      have hab_ne : a * b ≠ 0 := mul_ne_zero_of_ne_zero ha hb_ne
      have hc_ne : c ≠ 0 := hbc ▸ hab_ne
      exact (mem_nonzeroElements c).mpr hc_ne
    · intro hc
      have hc_ne : c ≠ 0 := (mem_nonzeroElements c).mp hc
      refine List.mem_map.mpr ⟨a⁻¹ * c, ?_, ?_⟩
      · apply (mem_nonzeroElements _).mpr
        intro hac
        apply hc_ne
        calc c
            = 1 * c := (one_mul c).symm
          _ = (a * a⁻¹) * c := by rw [mul_inv_cancel a ha]
          _ = a * (a⁻¹ * c) := mul_assoc _ _ _
          _ = a * 0 := congrArg (a * ·) hac
          _ = 0 := mul_zero _
      · rw [← mul_assoc, mul_inv_cancel a ha, one_mul]
  exact perm_of_nodup_mem_iff hmap_nodup hL_nodup hmem_iff

namespace Internal

/-- Internal proof-facing linear natural powers in the packed quotient field.
This variant has simple recursion equations; executable exponentiation remains
the `Pow` instance above. -/
@[expose]
def linearPow (a : GF2nPoly f hirr) : Nat → GF2nPoly f hirr
  | 0 => 1
  | n + 1 => linearPow a n * a

/-- Base case of proof-facing linear exponentiation: the zeroth power is `1`. -/
@[simp, grind =] theorem linearPow_zero (a : GF2nPoly f hirr) :
    linearPow a 0 = 1 :=
  rfl

/-- Recursion equation for proof-facing linear exponentiation: each successor
power multiplies the previous power by one more factor of `a`. -/
@[simp, grind =] theorem linearPow_succ (a : GF2nPoly f hirr) (n : Nat) :
    linearPow a (n + 1) = linearPow a n * a :=
  rfl

/-- Linear quotient powers turn addition of exponents into multiplication. -/
theorem linearPow_add (a : GF2nPoly f hirr) (m n : Nat) :
    linearPow a (m + n) = linearPow a m * linearPow a n := by
  induction n with
  | zero =>
      rw [Nat.add_zero, linearPow_zero, mul_one]
  | succ n ih =>
      calc linearPow a (m + (n + 1))
          = linearPow a ((m + n) + 1) := by rw [Nat.add_succ]
        _ = linearPow a (m + n) * a := rfl
        _ = (linearPow a m * linearPow a n) * a := by rw [ih]
        _ = linearPow a m * (linearPow a n * a) := by rw [mul_assoc]
        _ = linearPow a m * linearPow a (n + 1) := rfl

/-- Doubling an exponent squares the base, in the linear reference form. -/
theorem linearPow_double (a : GF2nPoly f hirr) (n : Nat) :
    linearPow (a * a) n = linearPow a (2 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc linearPow (a * a) (n + 1)
          = linearPow (a * a) n * (a * a) := rfl
        _ = linearPow a (2 * n) * (a * a) := by rw [ih]
        _ = linearPow a (2 * n) * a * a := by rw [mul_assoc]
        _ = linearPow a (2 * n + 1) * a := rfl
        _ = linearPow a (2 * n + 1 + 1) := rfl
        _ = linearPow a (2 * (n + 1)) := by
              rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by omega]

/-- The odd-exponent companion of {name}`Hex.GF2nPoly.Internal.linearPow_double`. -/
theorem linearPow_double_add_one (a : GF2nPoly f hirr) (n : Nat) :
    a * linearPow (a * a) n = linearPow a (2 * n + 1) := by
  rw [linearPow_double]
  calc a * linearPow a (2 * n)
      = linearPow a (2 * n) * a := by rw [mul_comm]
    _ = linearPow a (2 * n + 1) := rfl

/-- The executable square-and-multiply accumulator computes `acc * base ^ k`.

This is the invariant that ties the fast `Pow` instance to the linear reference:
the loop halves the exponent and squares the base, so the accumulator carries
exactly the factors already consumed. -/
theorem pow_go_eq_acc_mul_linearPow (acc base : GF2nPoly f hirr) (k : Nat) :
    GF2nPoly.pow.go acc base k = acc * linearPow base k := by
  induction k using Nat.strongRecOn generalizing acc base with
  | ind k ih =>
      rw [GF2nPoly.pow.go.eq_def]
      by_cases hk : k = 0
      · subst hk
        simp [linearPow_zero, mul_one]
      · rw [dite_eq_right hk]
        have hlt : k / 2 < k :=
          Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide : 1 < 2)
        cases Nat.mod_two_eq_zero_or_one k with
        | inl hmod0 =>
            have hk_eq : k = 2 * (k / 2) := by
              have h := Nat.mod_add_div k 2
              omega
            have hnot : ¬k % 2 = 1 := by omega
            rw [ite_eq_right hnot, ih (k / 2) hlt acc (base * base), linearPow_double]
            congr 2
            omega
        | inr hmod1 =>
            have hk_eq : k = 2 * (k / 2) + 1 := by
              have h := Nat.mod_add_div k 2
              omega
            rw [ite_eq_left hmod1, ih (k / 2) hlt (acc * base) (base * base)]
            calc acc * base * linearPow (base * base) (k / 2)
                = acc * (base * linearPow (base * base) (k / 2)) := by rw [mul_assoc]
              _ = acc * linearPow base (2 * (k / 2) + 1) := by
                    rw [linearPow_double_add_one]
              _ = acc * linearPow base k := by rw [← hk_eq]

/-- The executable square-and-multiply power agrees with the linear reference. -/
theorem pow_eq_linearPow (a : GF2nPoly f hirr) (n : Nat) :
    a ^ n = linearPow a n := by
  show GF2nPoly.pow a n = linearPow a n
  rw [GF2nPoly.pow, pow_go_eq_acc_mul_linearPow, one_mul]

/-- Linear powers of a product factor in the commutative packed quotient. -/
theorem linearPow_mul (a b : GF2nPoly f hirr) (n : Nat) :
    linearPow (a * b) n = linearPow a n * linearPow b n := by
  induction n with
  | zero =>
      rw [linearPow_zero, linearPow_zero, linearPow_zero, one_mul]
  | succ n ih =>
      calc linearPow (a * b) (n + 1)
          = linearPow (a * b) n * (a * b) := rfl
        _ = (linearPow a n * linearPow b n) * (a * b) := by rw [ih]
        _ = linearPow a n * (linearPow b n * (a * b)) := by rw [mul_assoc]
        _ = linearPow a n * ((linearPow b n * a) * b) := by
              rw [mul_assoc (linearPow b n) a b]
        _ = linearPow a n * ((a * linearPow b n) * b) := by
              rw [mul_comm (linearPow b n) a]
        _ = linearPow a n * (a * (linearPow b n * b)) := by
              rw [mul_assoc a (linearPow b n) b]
        _ = (linearPow a n * a) * (linearPow b n * b) := by
              rw [← mul_assoc]
        _ = linearPow a (n + 1) * linearPow b (n + 1) := rfl

/-- Iterated Frobenius squaring agrees with linear powering by `2^k`. -/
theorem frobeniusIter_eq_linearPow_two_pow (a : GF2nPoly f hirr) (k : Nat) :
    frobeniusIter a k = linearPow a (2 ^ k) := by
  induction k with
  | zero =>
      change a = linearPow a 1
      rw [show (1 : Nat) = 0 + 1 from rfl, linearPow_succ, linearPow_zero, one_mul]
  | succ k ih =>
      calc frobeniusIter a (k + 1)
          = frobeniusIter a k * frobeniusIter a k := rfl
        _ = linearPow a (2 ^ k) * linearPow a (2 ^ k) := by rw [ih]
        _ = linearPow a (2 ^ k + 2 ^ k) := by
              rw [linearPow_add]
        _ = linearPow a (2 ^ (k + 1)) := by
              rw [Nat.pow_succ, show 2 ^ k + 2 ^ k = 2 ^ k * 2 by omega]

end Internal

/-- Coefficients for the characteristic-two polynomial `T^(2^k) + T`.

For `0 < k`, the list is low-to-high with nonzero coefficients exactly at
degrees `1` and `2^k`. The `k = 0` list intentionally evaluates to zero,
matching `T + T`; root-count callers use the positive-`k` theorem below. -/
@[expose]
def frobeniusFixedCoeffList (k : Nat) : List (GF2nPoly f hirr) :=
  if k = 0 then
    [0]
  else
    0 :: 1 :: (List.replicate (2 ^ k - 2) (0 : GF2nPoly f hirr) ++ [1])

private theorem evalCoeffList_replicate_zero_append_one
    (β : GF2nPoly f hirr) (n : Nat) :
    evalCoeffList (List.replicate n (0 : GF2nPoly f hirr) ++ [1]) β =
      Internal.linearPow β n := by
  induction n with
  | zero =>
      simp [evalCoeffList, Internal.linearPow_zero]
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, evalCoeffList_cons]
      rw [ih, zero_add, Internal.linearPow_succ, mul_comm]

private theorem evalCoeffList_frobeniusFixedCoeffList_of_pos
    (β : GF2nPoly f hirr) {k : Nat} (hk : 0 < k) :
    evalCoeffList (frobeniusFixedCoeffList (f := f) (hirr := hirr) k) β =
      frobeniusIter β k + β := by
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  have htwo : 2 ≤ 2 ^ k := by
    cases k with
    | zero => exact False.elim (Nat.lt_irrefl 0 hk)
    | succ k =>
        rw [Nat.pow_succ]
        have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide : 0 < 2)
        omega
  rw [frobeniusFixedCoeffList, ite_eq_right hk_ne]
  simp only [evalCoeffList_cons]
  rw [zero_add, evalCoeffList_replicate_zero_append_one,
    Internal.frobeniusIter_eq_linearPow_two_pow]
  have hpow_two : Internal.linearPow β 2 = β * β := by
    rw [show (2 : Nat) = 1 + 1 from rfl, Internal.linearPow_succ,
      Internal.linearPow_succ, Internal.linearPow_zero, one_mul]
  calc
    β * (1 + β * Internal.linearPow β (2 ^ k - 2))
        = β * 1 + β * (β * Internal.linearPow β (2 ^ k - 2)) := by
            rw [left_distrib]
    _ = β + β * (β * Internal.linearPow β (2 ^ k - 2)) := by rw [mul_one]
    _ = β + (β * β) * Internal.linearPow β (2 ^ k - 2) := by rw [mul_assoc]
    _ = β + Internal.linearPow β 2 * Internal.linearPow β (2 ^ k - 2) := by rw [hpow_two]
    _ = β + Internal.linearPow β (2 + (2 ^ k - 2)) := by
            have hadd :=
              (Internal.linearPow_add (f := f) (hirr := hirr) β 2 (2 ^ k - 2)).symm
            rw [hadd]
    _ = β + Internal.linearPow β (2 ^ k) := by
            have hidx : 2 + (2 ^ k - 2) = 2 ^ k := by omega
            rw [hidx]
    _ = Internal.linearPow β (2 ^ k) + β := by rw [add_comm]

private theorem getLast?_append_singleton {α : Type} (xs : List α) (x : α) :
    (xs ++ [x]).getLast? = some x := by
  induction xs with
  | nil =>
      simp
  | cons y ys ih =>
      cases ys with
      | nil => simp
      | cons z zs =>
          simpa using ih

private theorem coeffListTopNonzero_frobeniusFixedCoeffList_of_pos
    (hf_pos : 0 < f.degree) {k : Nat} (hk : 0 < k) :
    Internal.coeffListTopNonzero
      (f := f) (hirr := hirr)
      (frobeniusFixedCoeffList (f := f) (hirr := hirr) k) := by
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  refine ⟨1, ?_, one_ne_zero (f := f) (hirr := hirr) hf_pos⟩
  rw [frobeniusFixedCoeffList, ite_eq_right hk_ne]
  change
    (((0 : GF2nPoly f hirr) :: 1 ::
        List.replicate (2 ^ k - 2) (0 : GF2nPoly f hirr)) ++ [1]).getLast? =
      some 1
  exact getLast?_append_singleton
    ((0 : GF2nPoly f hirr) :: 1 ::
      List.replicate (2 ^ k - 2) (0 : GF2nPoly f hirr)) 1

private theorem add_eq_zero_iff_eq (a b : GF2nPoly f hirr) :
    a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc
      a = a + 0 := (add_zero a).symm
      _ = a + (a + b) := by rw [h]
      _ = (a + a) + b := by rw [add_assoc]
      _ = b := by rw [add_self, zero_add]
  · intro h
    rw [h, add_self]

/--
At most `2^k` packed quotient elements are fixed by the `k`-fold Frobenius
when `0 < k`.

This is the root-count specialization for `T^(2^k) + T`, stated directly
against the canonical duplicate-free `elements` enumeration so downstream
Rabin arguments can combine it with `elements_card`.
-/
theorem frobeniusIter_fixed_elements_length_le_two_pow
    (hf_pos : 0 < f.degree) {k : Nat} (hk : 0 < k) :
    ((elements (f := f) (hirr := hirr)).filter
      (fun β => decide (frobeniusIter β k = β))).length ≤ 2 ^ k := by
  let cs := frobeniusFixedCoeffList (f := f) (hirr := hirr) k
  have htop :
      Internal.coeffListTopNonzero (f := f) (hirr := hirr) cs :=
    coeffListTopNonzero_frobeniusFixedCoeffList_of_pos
      (f := f) (hirr := hirr) hf_pos hk
  have hroot :=
    Internal.evalCoeffList_rootsIn_elements_length_le_degree
      (f := f) (hirr := hirr) cs htop
  have hlen : cs.length - 1 = 2 ^ k := by
    have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
    have htwo : 2 ≤ 2 ^ k := by
      cases k with
      | zero => exact False.elim (Nat.lt_irrefl 0 hk)
      | succ k =>
          rw [Nat.pow_succ]
          have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide : 0 < 2)
          omega
    dsimp [cs]
    rw [frobeniusFixedCoeffList, ite_eq_right hk_ne]
    simp
    omega
  have hfilter :
      (elements (f := f) (hirr := hirr)).filter
          (fun β => decide (frobeniusIter β k = β)) =
        (elements (f := f) (hirr := hirr)).filter
          (fun β => decide (evalCoeffList cs β = 0)) := by
    apply List.filter_congr
    intro β _hβ
    have heval :
        evalCoeffList cs β = frobeniusIter β k + β := by
      dsimp [cs]
      exact evalCoeffList_frobeniusFixedCoeffList_of_pos
        (f := f) (hirr := hirr) β hk
    by_cases hfixed : frobeniusIter β k = β
    · have hzero : evalCoeffList cs β = 0 := by
        rw [heval, hfixed, add_self]
      rw [decide_eq_true hfixed, decide_eq_true hzero]
    · have hnot_zero : evalCoeffList cs β ≠ 0 := by
        intro hzero
        apply hfixed
        exact (add_eq_zero_iff_eq
          (f := f) (hirr := hirr) (frobeniusIter β k) β).mp
          (by rw [← heval]; exact hzero)
      rw [decide_eq_false hfixed, decide_eq_false hnot_zero]
  rw [hfilter]
  exact hlen ▸ hroot

/--
If every packed quotient element is fixed by a positive Frobenius iterate,
then the iterate is at least the modulus degree.

This is the downstream cardinality form of the fixed-root bound: otherwise
all `2^f.degree` quotient elements would be roots of `T^(2^k) + T`, whose
packed root-count bound is only `2^k`.
-/
theorem frobeniusIter_universal_fixed_degree_le
    (hf_pos : 0 < f.degree) {k : Nat} (hk : 0 < k)
    (hfixed : ∀ β : GF2nPoly f hirr, frobeniusIter β k = β) :
    f.degree ≤ k := by
  have hfilter_eq :
      (elements (f := f) (hirr := hirr)).filter
          (fun β => decide (frobeniusIter β k = β)) =
        elements (f := f) (hirr := hirr) := by
    apply (List.filter_eq_self).mpr
    intro β _hβ
    exact decide_eq_true (hfixed β)
  have hbound :=
    frobeniusIter_fixed_elements_length_le_two_pow
      (f := f) (hirr := hirr) hf_pos hk
  rw [hfilter_eq, elements_card] at hbound
  by_cases hle : f.degree ≤ k
  · exact hle
  · have hlt : k < f.degree := Nat.lt_of_not_ge hle
    have hpow_lt : 2 ^ k < 2 ^ f.degree :=
      Nat.pow_lt_pow_right (by decide : 1 < 2) hlt
    exact False.elim (Nat.not_lt_of_ge hbound hpow_lt)

/--
For a positive iterate below the packed quotient degree, not every quotient
element can be fixed by Frobenius.

This contrapositive is the form Rabin soundness uses after reducing an
exponent modulo the irreducible factor degree.
-/
theorem not_forall_frobeniusIter_eq_self_of_pos_lt_degree
    (hf_pos : 0 < f.degree) {r : Nat} (hr_pos : 0 < r)
    (hr_lt : r < f.degree) :
    ¬ ∀ β : GF2nPoly f hirr, frobeniusIter β r = β := by
  intro hfixed
  have hdeg_le :
      f.degree ≤ r :=
    frobeniusIter_universal_fixed_degree_le
      (f := f) (hirr := hirr) hf_pos hr_pos hfixed
  exact Nat.not_lt_of_ge hdeg_le hr_lt

/-- A positive iterate below the quotient degree has some non-fixed element. -/
theorem exists_frobeniusIter_ne_self_of_pos_lt_degree
    (hf_pos : 0 < f.degree) {r : Nat} (hr_pos : 0 < r)
    (hr_lt : r < f.degree) :
    ∃ β : GF2nPoly f hirr, frobeniusIter β r ≠ β := by
  classical
  by_cases h : ∃ β : GF2nPoly f hirr, frobeniusIter β r ≠ β
  · exact h
  · exact False.elim
      (not_forall_frobeniusIter_eq_self_of_pos_lt_degree
        (f := f) (hirr := hirr) hf_pos hr_pos hr_lt
        (fun β => by
          by_cases hβ : frobeniusIter β r = β
          · exact hβ
          · exact False.elim (h ⟨β, hβ⟩)))

/--
For a positive iterate below the quotient degree, the quotient class of `X`
cannot be fixed by Frobenius.

If `X` were fixed, the existing quotient-generation theorem would make every
element fixed, contradicting the fixed-point cardinality bound.
-/
theorem frobeniusIter_X_ne_self_of_pos_lt_degree
    (hf_pos : 0 < f.degree) {r : Nat} (hr_pos : 0 < r)
    (hr_lt : r < f.degree) :
    frobeniusIter (X (f := f) (hirr := hirr)) r ≠
      X (f := f) (hirr := hirr) := by
  intro hX
  exact not_forall_frobeniusIter_eq_self_of_pos_lt_degree
    (f := f) (hirr := hirr) hf_pos hr_pos hr_lt
    (frobeniusIter_eq_self_of_X_fixed (f := f) (hirr := hirr) hX)

namespace Internal

/-- Internal proof-facing product of a list of packed quotient elements
(right fold), used with the canonical nonzero quotient enumeration. -/
@[expose]
def listProd (xs : List (GF2nPoly f hirr)) : GF2nPoly f hirr :=
  xs.foldr (· * ·) 1

/-- The right-folded product of the empty quotient-element list is one. -/
@[simp, grind =] theorem listProd_nil :
    listProd ([] : List (GF2nPoly f hirr)) = 1 :=
  rfl

/-- The right-folded product of a cons multiplies the head by the tail
product. -/
@[simp, grind =] theorem listProd_cons (x : GF2nPoly f hirr)
    (xs : List (GF2nPoly f hirr)) :
    listProd (x :: xs) = x * listProd xs :=
  rfl

/-- The list product is invariant under `List.Perm`. -/
theorem listProd_perm {xs ys : List (GF2nPoly f hirr)}
    (h : List.Perm xs ys) :
    listProd xs = listProd ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih =>
      simp only [listProd_cons]
      rw [ih]
  | swap x y zs =>
      simp only [listProd_cons]
      rw [← mul_assoc, ← mul_assoc, mul_comm x y]
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Mapping a list by left-multiplication factors out as a linear power of the
multiplier times the original list product. -/
theorem listProd_map_mul_left (a : GF2nPoly f hirr)
    (xs : List (GF2nPoly f hirr)) :
    listProd (xs.map (fun b => a * b)) = linearPow a xs.length * listProd xs := by
  induction xs with
  | nil =>
      simp only [List.map_nil, List.length_nil, listProd_nil, linearPow_zero, one_mul]
  | cons x xs ih =>
      calc listProd ((x :: xs).map (fun b => a * b))
          = (a * x) * listProd (xs.map (fun b => a * b)) := by
              simp only [List.map_cons, listProd_cons]
        _ = (a * x) * (linearPow a xs.length * listProd xs) := by rw [ih]
        _ = a * (x * (linearPow a xs.length * listProd xs)) := by rw [mul_assoc]
        _ = a * ((x * linearPow a xs.length) * listProd xs) := by
              rw [mul_assoc x (linearPow a xs.length) (listProd xs)]
        _ = a * ((linearPow a xs.length * x) * listProd xs) := by
              rw [mul_comm x (linearPow a xs.length)]
        _ = a * (linearPow a xs.length * (x * listProd xs)) := by
              rw [mul_assoc (linearPow a xs.length) x (listProd xs)]
        _ = (a * linearPow a xs.length) * (x * listProd xs) := by
              rw [← mul_assoc]
        _ = linearPow a (xs.length + 1) * (x * listProd xs) := by
              rw [linearPow_succ, mul_comm (linearPow a xs.length) a]
        _ = linearPow a (x :: xs).length * listProd (x :: xs) := by
              simp only [listProd_cons, List.length_cons]

/-- The product of a list of nonzero packed quotient elements is nonzero. -/
theorem listProd_ne_zero (hf_pos : 0 < f.degree)
    {xs : List (GF2nPoly f hirr)}
    (hxs : ∀ x ∈ xs, x ≠ 0) :
    listProd xs ≠ 0 := by
  induction xs with
  | nil =>
      simp only [listProd_nil]
      exact one_ne_zero (f := f) (hirr := hirr) hf_pos
  | cons x xs ih =>
      simp only [listProd_cons]
      apply mul_ne_zero_of_ne_zero
      · exact hxs x List.mem_cons_self
      · exact ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy))

/-- Finite-field exponent theorem for the packed quotient: every nonzero
quotient element raised to the number of nonzero representatives is `1`. -/
theorem linearPow_pred_card_eq_one_of_ne_zero
    (hf_pos : 0 < f.degree) {a : GF2nPoly f hirr} (ha : a ≠ 0) :
    linearPow a (2 ^ f.degree - 1) = 1 := by
  let L : List (GF2nPoly f hirr) := nonzeroElements (f := f) (hirr := hirr)
  let P : GF2nPoly f hirr := listProd L
  have hL_card : L.length = 2 ^ f.degree - 1 :=
    nonzeroElements_card (f := f) (hirr := hirr)
  have hP_ne : P ≠ 0 :=
    listProd_ne_zero (f := f) (hirr := hirr) hf_pos
      (fun x hx => (mem_nonzeroElements x).mp hx)
  have hperm := nonzeroElements_map_mul_left_perm
    (f := f) (hirr := hirr) ha
  have hprod_eq : listProd (L.map (fun b => a * b)) = P :=
    listProd_perm hperm
  have hfactor : listProd (L.map (fun b => a * b)) = linearPow a L.length * P :=
    listProd_map_mul_left a L
  have hkey : linearPow a L.length * P = P := hfactor.symm.trans hprod_eq
  have hcancel : linearPow a L.length * P * P⁻¹ = P * P⁻¹ :=
    congrArg (fun x => x * P⁻¹) hkey
  rw [mul_assoc, mul_inv_cancel P hP_ne, mul_one] at hcancel
  rw [hL_card] at hcancel
  exact hcancel

end Internal

/-- Every packed quotient element is fixed by the degree-cardinality
Frobenius iterate. -/
theorem frobeniusIter_degree_eq_self
    (hf_pos : 0 < f.degree) (a : GF2nPoly f hirr) :
    frobeniusIter a f.degree = a := by
  rw [Internal.frobeniusIter_eq_linearPow_two_pow]
  have hpos : 0 < 2 ^ f.degree := Nat.pow_pos (by decide : 0 < 2)
  have hsplit : 2 ^ f.degree = (2 ^ f.degree - 1) + 1 := by omega
  by_cases ha : a = 0
  · rw [ha, hsplit, Internal.linearPow_succ, mul_zero]
  · rw [hsplit, Internal.linearPow_succ,
      Internal.linearPow_pred_card_eq_one_of_ne_zero (f := f) (hirr := hirr) hf_pos ha,
      one_mul]

/-- Adding any multiple of the modulus degree to a Frobenius iterate does not
change the result. -/
theorem frobeniusIter_add_mul_degree_eq
    (hf_pos : 0 < f.degree) (a : GF2nPoly f hirr) (m q : Nat) :
    frobeniusIter a (m + f.degree * q) = frobeniusIter a m := by
  induction q with
  | zero =>
      rw [Nat.mul_zero, Nat.add_zero]
  | succ q ih =>
      have hidx : m + f.degree * (q + 1) = (m + f.degree * q) + f.degree := by
        rw [Nat.mul_succ]
        omega
      calc
        frobeniusIter a (m + f.degree * (q + 1))
            = frobeniusIter a ((m + f.degree * q) + f.degree) := by rw [hidx]
        _ = frobeniusIter (frobeniusIter a (m + f.degree * q)) f.degree := by
              rw [frobeniusIter_add]
        _ = frobeniusIter (frobeniusIter a m) f.degree := by rw [ih]
        _ = frobeniusIter a m :=
              frobeniusIter_degree_eq_self (f := f) (hirr := hirr) hf_pos
                (frobeniusIter a m)

/-- If a quotient element is fixed by the `n`-fold Frobenius, it is also fixed
by the remainder of `n` modulo the modulus degree. -/
theorem frobeniusIter_mod_degree_eq_of_fixed
    (hf_pos : 0 < f.degree) {a : GF2nPoly f hirr} {n : Nat}
    (hfixed : frobeniusIter a n = a) :
    frobeniusIter a (n % f.degree) = a := by
  have hdecomp : n % f.degree + f.degree * (n / f.degree) = n :=
    Nat.mod_add_div n f.degree
  have hperiod :
      frobeniusIter a (n % f.degree + f.degree * (n / f.degree)) =
        frobeniusIter a (n % f.degree) :=
    frobeniusIter_add_mul_degree_eq (f := f) (hirr := hirr) hf_pos a
      (n % f.degree) (n / f.degree)
  rw [hdecomp] at hperiod
  rw [← hperiod]
  exact hfixed

end GF2nPoly

end Hex
