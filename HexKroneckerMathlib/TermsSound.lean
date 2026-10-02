/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.Bounds
public import Mathlib.Algebra.CharP.Defs

public section

namespace Hex.Kronecker

open Hex.MvPoly.Kernel

theorem termShape_iff (k : Nat) (ts : PolyList Int) :
    termShape k ts = true ↔ ∀ t ∈ ts, t.1.length = k := by
  induction ts with
  | nil => simp [termShape]
  | cons t ts ih => cases t; simp [termShape, ih]

theorem canonical_termShape {k : Nat} {ts : PolyList Int} (h : isCanonical k ts = true) :
    termShape k ts = true := (termShape_iff k ts).mpr (isCanonical_iff.mp h).1

theorem checkTermsEq_polynomial {budget : Budget} {k : Nat} {lhs rhs : PolyList Int}
    (h : checkTermsEq budget k lhs rhs = true) : termsPolynomial k lhs = termsPolynomial k rhs := by
  by_cases hw : (termShape k lhs && termShape k rhs) = true
  swap
  · simp [checkTermsEq, sizeTermsEq, hw] at h
  have hl := (Bool.and_eq_true_iff.mp hw).1
  have hr := (Bool.and_eq_true_iff.mp hw).2
  let cap := 2^budget.maxPackedBits
  let l := termBounds cap k lhs
  let r := termBounds cap k rhs
  let s := makeSize budget (l.add cap r) [l,r]
  simp only [checkTermsEq, sizeTermsEq, hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  change (s.accepts budget && (packTerms (2^s.digitBits) s.strides lhs ==
    packTerms (2^s.digitBits) s.strides rhs)) = true at h
  have he := eq_of_beq (Bool.and_eq_true_iff.mp h).2
  have hs : s.strides.length = k := by
    simp [s, makeSize, Bounds.add, l, r, termBounds_length cap k lhs hl, termBounds_length cap k rhs hr]
  apply bounded_pair budget [l,r] (terms_bounded cap k lhs hl) (terms_bounded cap k rhs hr)
    (by simp [l]) (by simp [r]) (Bool.and_eq_true_iff.mp h).1
  rw [packTerms_eq_eval₂ _ _ hs lhs hl, packTerms_eq_eval₂ _ _ hs rhs hr] at he
  exact he

/-- Evaluate the established term-list identity in any commutative ring. -/
theorem checkTermsEq_sound {budget : Budget} {k : Nat} {lhs rhs : PolyList Int}
    (h : checkTermsEq budget k lhs rhs = true) :
    ∀ {R : Type u} [CommRing R] (v : Fin k → R),
      denoteTerms R v lhs = denoteTerms R v rhs := by
  intro R _ v
  unfold denoteTerms
  rw [checkTermsEq_polynomial h]

/-- Map an integer quotient identity into a ring of the stated characteristic. -/
theorem quotient_sound {k p : Nat} {l r q : MvPolynomial (Fin k) Int}
    (h : l-r = MvPolynomial.C (p : Int)*q) :
    ∀ {R : Type u} [CommRing R] [CharP R p] (v : Fin k → R),
      MvPolynomial.eval₂Hom (Int.castRingHom R) v l =
      MvPolynomial.eval₂Hom (Int.castRingHom R) v r := by
  intro R _ _ v
  have he := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) v) h
  simpa only [map_sub, map_mul, MvPolynomial.eval₂Hom_C, map_natCast,
    CharP.cast_eq_zero, zero_mul, sub_eq_zero] using he

end Hex.Kronecker
