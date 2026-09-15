/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.TermsSound

public section

namespace Hex.Kronecker

open Hex.MvPoly.Kernel

theorem checkTermsEqMod_polynomial {budget : Budget} {k p : Nat} {lhs rhs q : PolyList Int}
    (h : checkTermsEqMod budget k p lhs rhs q = true) :
    termsPolynomial k lhs - termsPolynomial k rhs = MvPolynomial.C (p : Int)*termsPolynomial k q := by
  by_cases hp : (p == 0) = true
  · simp [checkTermsEqMod, sizeTermsEqMod, hp] at h
  by_cases hw : (termShape k lhs && termShape k rhs) = true
  swap
  · simp [checkTermsEqMod, sizeTermsEqMod, hp, hw] at h
  by_cases hv : (termResidues p lhs && termResidues p rhs) = true
  swap
  · simp [checkTermsEqMod, sizeTermsEqMod, hp, hw, hv] at h
  by_cases hq : isCanonical k q = true
  swap
  · simp [checkTermsEqMod, sizeTermsEqMod, hp, hw, hv, hq] at h
  have hl := (Bool.and_eq_true_iff.mp hw).1
  have hr := (Bool.and_eq_true_iff.mp hw).2
  have hqs := canonical_termShape hq
  let cap := 2^budget.maxPackedBits
  let l := termBounds cap k lhs
  let r := termBounds cap k rhs
  let qb := termBounds cap k q
  let d := l.add cap r
  let t := (Bounds.mk (zeroDegrees k) (min p cap)).mul cap qb
  let obs := [l,r,qb,t,d]
  let s := makeSize budget (d.add cap t) obs
  simp only [checkTermsEqMod, sizeTermsEqMod, hp, hw, hv, hq,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  change (s.accepts budget && (packTerms (2^s.digitBits) s.strides lhs -
    packTerms (2^s.digitBits) s.strides rhs == (p:Int)*packTerms (2^s.digitBits) s.strides q)) = true at h
  have hd := (terms_bounded cap k lhs hl).sub (terms_bounded cap k rhs hr)
  have ht := (Bounded.int cap k (p : Int)).mul (terms_bounded cap k q hqs)
  have ht' : Bounded cap t (MvPolynomial.C (p:Int)*termsPolynomial k q) := by
    simpa only [Int.natAbs_natCast] using ht
  have hs : s.strides.length = k := by
    simp [s, makeSize, Bounds.add, show d.degrees.length = k from hd.length, ht'.length]
  apply bounded_pair budget obs hd ht' (by simp [obs,d,l,r]) (by simp [obs])
    (Bool.and_eq_true_iff.mp h).1
  have he := eq_of_beq (Bool.and_eq_true_iff.mp h).2
  rw [packTerms_eq_eval₂ _ _ hs lhs hl, packTerms_eq_eval₂ _ _ hs rhs hr,
    packTerms_eq_eval₂ _ _ hs q hqs] at he
  simpa only [map_sub, map_mul, MvPolynomial.eval₂Hom_C, RingHom.id_apply] using he

theorem checkTermsEqMod_sound {budget : Budget} {k p : Nat} {lhs rhs q : PolyList Int}
    (h : checkTermsEqMod budget k p lhs rhs q = true) :
    ∀ {R : Type u} [CommRing R] [CharP R p] (v : Fin k → R),
      denoteTerms R v lhs = denoteTerms R v rhs :=
  quotient_sound (checkTermsEqMod_polynomial h)

theorem checkExprEqMod_polynomial {budget : Budget} {k p : Nat} {lhs rhs : Expr} {q : PolyList Int}
    (h : checkExprEqMod budget k p lhs rhs q = true) :
    ∃ (hl : lhs.WellFormed k) (hr : rhs.WellFormed k),
      lhs.toMvPolynomial hl - rhs.toMvPolynomial hr = MvPolynomial.C (p : Int)*termsPolynomial k q := by
  by_cases hp : (p == 0) = true
  · simp [checkExprEqMod, sizeExprEqMod, hp] at h
  by_cases hw : (lhs.wellFormed k && rhs.wellFormed k) = true
  swap
  · simp [checkExprEqMod, sizeExprEqMod, hp, hw] at h
  by_cases hv : (lhs.residues p && rhs.residues p) = true
  swap
  · simp [checkExprEqMod, sizeExprEqMod, hp, hw, hv] at h
  by_cases hq : isCanonical k q = true
  swap
  · simp [checkExprEqMod, sizeExprEqMod, hp, hw, hv, hq] at h
  have hl := (Bool.and_eq_true_iff.mp hw).1
  have hr := (Bool.and_eq_true_iff.mp hw).2
  have hqs := canonical_termShape hq
  refine ⟨hl,hr,?_⟩
  let cap := 2^budget.maxPackedBits
  let l := lhs.analyze cap k []
  let r := rhs.analyze cap k l.2
  let qb := termBounds cap k q
  let d := l.1.add cap r.1
  let t := (Bounds.mk (zeroDegrees k) (min p cap)).mul cap qb
  let obs := d::t::qb::r.2
  let s := makeSize budget (d.add cap t) obs
  simp only [checkExprEqMod, sizeExprEqMod, hp, hw, hv, hq,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  change (s.accepts budget && (evalKron (2^s.digitBits) s.strides lhs -
    evalKron (2^s.digitBits) s.strides rhs == (p:Int)*packTerms (2^s.digitBits) s.strides q)) = true at h
  have hd := (lhs.bounded cap k hl []).sub (rhs.bounded cap k hr l.2)
  have ht := (Bounded.int cap k (p : Int)).mul (terms_bounded cap k q hqs)
  have ht' : Bounded cap t (MvPolynomial.C (p:Int)*termsPolynomial k q) := by
    simpa only [Int.natAbs_natCast] using ht
  have hs : s.strides.length = k := by
    simp [s, makeSize, Bounds.add, show d.degrees.length = k from hd.length, ht'.length]
  apply bounded_pair budget obs hd ht' (by simp [obs,d,l,r]) (by simp [obs])
    (Bool.and_eq_true_iff.mp h).1
  have he := eq_of_beq (Bool.and_eq_true_iff.mp h).2
  rw [evalKron_eq_eval₂ _ _ lhs hl, evalKron_eq_eval₂ _ _ rhs hr,
    packTerms_eq_eval₂ _ _ hs q hqs] at he
  simpa only [map_sub, map_mul, MvPolynomial.eval₂Hom_C, RingHom.id_apply] using he

theorem checkExprEqMod_sound {budget : Budget} {k p : Nat} {lhs rhs : Expr} {q : PolyList Int}
    (h : checkExprEqMod budget k p lhs rhs q = true) :
    ∀ {R : Type u} [CommRing R] [CharP R p] (v : Nat → R), lhs.denote v = rhs.denote v := by
  intro R _ _ v
  obtain ⟨hl,hr,he⟩ := checkExprEqMod_polynomial h
  rw [← lhs.denoteFin_eq hl v, ← rhs.denoteFin_eq hr v,
    denote_eq_eval₂ lhs hl, denote_eq_eval₂ rhs hr]
  exact quotient_sound he _

end Hex.Kronecker
