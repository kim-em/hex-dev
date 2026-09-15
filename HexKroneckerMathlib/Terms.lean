/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.Preflight

public section

namespace Hex.Kronecker

open Hex.MvPoly.Kernel
open scoped HexMvPolyMathlib

/-- The existing kernel-list denotation, transported through the Hex equivalence. -/
@[expose] noncomputable def termsPolynomial (k : Nat) (ts : PolyList Int) :
    MvPolynomial (Fin k) Int := HexMvPolyMathlib.Kernel.denote (cmp := Hex.Mono.grevlex) ts

@[simp] theorem termsPolynomial_nil (k : Nat) : termsPolynomial k [] = 0 := by
  simp [termsPolynomial, HexMvPolyMathlib.Kernel.denote, denote]

theorem termsPolynomial_cons (k : Nat) (e : List Nat) (c : Int) (ts : PolyList Int) :
    termsPolynomial k ((e,c)::ts) =
      MvPolynomial.monomial (HexMvPolyMathlib.monoEquiv (mono k e)) c + termsPolynomial k ts := by
  simp [termsPolynomial, HexMvPolyMathlib.Kernel.denote, denote,
    HexMvPolyMathlib.equiv_apply]

theorem ofFn_mono {k : Nat} (es : List Nat) (he : es.length = k) :
    (List.ofFn fun i => HexMvPolyMathlib.monoEquiv (mono k es) i) = es := by
  apply List.ext_getElem
  · simp [he]
  · intro i h₁ h₂
    simp only [List.getElem_ofFn, HexMvPolyMathlib.monoEquiv_apply, get_mono]
    simp [List.getD, h₂]

theorem packTerms_eq_eval₂ {k : Nat} (base : Nat) (ss : List Nat) (hs : ss.length = k)
    (ts : PolyList Int) (ht : termShape k ts = true) :
    packTerms base ss ts = MvPolynomial.eval₂Hom (RingHom.id Int)
      (fun i : Fin k => (base : Int) ^ ss.getD i.val 0) (termsPolynomial k ts) := by
  induction ts with
  | nil => simp [packTerms]
  | cons t ts ih =>
      obtain ⟨e,c⟩ := t
      have h := Bool.and_eq_true_iff.mp ht
      have he : e.length = k := eq_of_beq h.1
      rw [packTerms, termsPolynomial_cons, map_add, ← ih h.2]
      congr 1
      rw [MvPolynomial.eval₂Hom_monomial]
      simp only [RingHom.id_apply, power_eq]
      congr 1
      rw [Finsupp.prod_pow]
      simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]
      rw [← code_ofFn ss hs, ofFn_mono e he]
      rfl

/-- Structural coefficient bound of a supplied term stream. -/
@[expose] def termHeight : PolyList Int → Nat
  | [] => 0
  | (_,c)::ts => c.natAbs + termHeight ts

theorem termBounds_height (cap k : Nat) (ts : PolyList Int) :
    (termBounds cap k ts).height = min (termHeight ts) cap := by
  induction ts with
  | nil => simp [termBounds, Bounds.zero, termHeight]
  | cons t ts ih =>
      obtain ⟨e,c⟩ := t
      simp only [termBounds, Bounds.add, Saturating.add_eq, ih, termHeight]
      exact Saturating.min_add _ _ _

theorem terms_norm₁_le (k : Nat) (ts : PolyList Int) :
    norm₁ (termsPolynomial k ts) ≤ termHeight ts := by
  induction ts with
  | nil => simp [termHeight]
  | cons t ts ih =>
      obtain ⟨e,c⟩ := t
      rw [termsPolynomial_cons]
      exact (norm₁_add _ _).trans (Nat.add_le_add (le_of_eq (norm₁_monomial _ c)) ih)

theorem termBounds_length (cap k : Nat) (ts : PolyList Int) (ht : termShape k ts = true) :
    (termBounds cap k ts).degrees.length = k := by
  induction ts with
  | nil => simp [termBounds, Bounds.zero]
  | cons t ts ih =>
      obtain ⟨e,c⟩ := t
      have h := Bool.and_eq_true_iff.mp ht
      simp only [termBounds, Bounds.add, length_maxDegrees, eq_of_beq h.1, ih h.2, Nat.max_self]

theorem terms_degreeOf_le (cap k : Nat) (ts : PolyList Int)
    (ht : termShape k ts = true) (i : Fin k) :
    (termsPolynomial k ts).degreeOf i ≤ (termBounds cap k ts).degrees.getD i.val 0 := by
  induction ts with
  | nil => simp [termBounds, Bounds.zero]
  | cons t ts ih =>
      obtain ⟨e,c⟩ := t
      have h := Bool.and_eq_true_iff.mp ht
      rw [termsPolynomial_cons]
      apply (MvPolynomial.degreeOf_add_le _ _ _).trans
      simp only [termBounds, Bounds.add, getD_maxDegrees]
      apply max_le_max _ (ih h.2)
      by_cases hc : c = 0
      · simp [hc]
      · rw [MvPolynomial.degreeOf_monomial_eq _ _ hc]
        simp only [HexMvPolyMathlib.monoEquiv_apply, get_mono, le_refl]

theorem terms_inBox (cap k : Nat) (ts : PolyList Int) (ht : termShape k ts = true) :
    InBox (termBounds cap k ts).degrees (termsPolynomial k ts) := by
  intro e he
  apply box_ofFn _ (termBounds_length cap k ts ht)
  intro i
  exact (MvPolynomial.le_degreeOf_of_mem_support i he).trans (terms_degreeOf_le cap k ts ht i)

end Hex.Kronecker
