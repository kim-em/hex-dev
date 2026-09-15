/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.Preflight

public section

namespace Hex.Kronecker

theorem checkExprEq_valid {budget : Budget} {k : Nat} {lhs rhs : Expr}
    (h : checkExprEq budget k lhs rhs = true) : lhs.WellFormed k ∧ rhs.WellFormed k := by
  by_cases hw : (lhs.wellFormed k && rhs.wellFormed k) = true
  · exact Bool.and_eq_true_iff.mp hw
  · simp [checkExprEq, sizeExprEq, hw] at h

theorem checkExprEq_polynomial {budget : Budget} {k : Nat} {lhs rhs : Expr}
    (h : checkExprEq budget k lhs rhs = true) (hl : lhs.WellFormed k) (hr : rhs.WellFormed k) :
    lhs.toMvPolynomial hl = rhs.toMvPolynomial hr := by
  let cap := 2 ^ budget.maxPackedBits
  let l := lhs.analyze cap k []
  let r := rhs.analyze cap k l.2
  let common := l.1.add cap r.1
  let s := makeSize budget common r.2
  have hw : (lhs.wellFormed k && rhs.wellFormed k) = true := Bool.and_eq_true_iff.mpr ⟨hl, hr⟩
  simp only [checkExprEq, sizeExprEq, hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  change (s.accepts budget &&
    (evalKron (2 ^ s.digitBits) s.strides lhs == evalKron (2 ^ s.digitBits) s.strides rhs)) = true at h
  have hacc := (Bool.and_eq_true_iff.mp h).1
  have heval := eq_of_beq (Bool.and_eq_true_iff.mp h).2
  have hlmem : l.1 ∈ r.2 := rhs.analyze_acc cap k l.2 (lhs.analyze_root cap k [])
  have hrmem : r.1 ∈ r.2 := rhs.analyze_root cap k l.2
  have hlb : l.1 = ⟨lhs.degrees k, lhs.cappedHeight cap⟩ := lhs.analyze_bound cap k []
  have hrb : r.1 = ⟨rhs.degrees k, rhs.cappedHeight cap⟩ := rhs.analyze_bound cap k l.2
  have hlcap := height_of_accept budget common r.2 hacc l.1 hlmem
  have hrcap := height_of_accept budget common r.2 hacc r.1 hrmem
  have hleq := height_eq_of_accept budget common r.2 hacc lhs k (hlb ▸ hlmem)
  have hreq := height_eq_of_accept budget common r.2 hacc rhs k (hrb ▸ hrmem)
  have hlen : common.degrees.length = k := by simp [common, Bounds.add, hlb, hrb]
  have hlbox : InBox common.degrees (lhs.toMvPolynomial hl) :=
    (lhs.inBox hl).mono hlen (fun i => by
      simp only [common, Bounds.add, hlb, hrb, getD_maxDegrees]
      exact Nat.le_max_left _ _)
  have hrbox : InBox common.degrees (rhs.toMvPolynomial hr) :=
    (rhs.inBox hr).mono hlen (fun i => by
      simp only [common, Bounds.add, hlb, hrb, getD_maxDegrees]
      exact Nat.le_max_right _ _)
  have hlH : norm₁ (lhs.toMvPolynomial hl) ≤ common.height := by
    apply (lhs.norm₁_le hl).trans
    rw [hleq]
    change lhs.cappedHeight cap ≤ Saturating.add cap l.1.height r.1.height
    rw [← show l.1.height = lhs.cappedHeight cap from congrArg Bounds.height hlb]
    exact Saturating.le_add_left cap _ _ (Nat.le_of_lt hlcap)
  have hrH : norm₁ (rhs.toMvPolynomial hr) ≤ common.height := by
    apply (rhs.norm₁_le hr).trans
    rw [hreq]
    change rhs.cappedHeight cap ≤ Saturating.add cap l.1.height r.1.height
    rw [← show r.1.height = rhs.cappedHeight cap from congrArg Bounds.height hrb]
    exact Saturating.le_add_right cap _ _ (Nat.le_of_lt hrcap)
  apply balanced_injective common.degrees hlen _ _ hlbox hrbox common.height
    (common.height.log2 + 2) hlH hrH (width_bound common.height)
  rw [evalKron_eq_eval₂ _ _ lhs hl, evalKron_eq_eval₂ _ _ rhs hr] at heval
  simpa only [s, makeSize, Nat.cast_pow, Nat.cast_ofNat] using heval

/-- A successful integer polynomial check establishes the identity in every
commutative ring, with no characteristic or injectivity hypothesis. -/
theorem checkExprEq_sound {budget : Budget} {k : Nat} {lhs rhs : Expr}
    (h : checkExprEq budget k lhs rhs = true) :
    ∀ {R : Type u} [CommRing R] (v : Nat → R), lhs.denote v = rhs.denote v := by
  intro R _ v
  obtain ⟨hl, hr⟩ := checkExprEq_valid h
  have hp := checkExprEq_polynomial h hl hr
  rw [← lhs.denoteFin_eq hl v, ← rhs.denoteFin_eq hr v,
    denote_eq_eval₂ lhs hl, denote_eq_eval₂ rhs hr, hp]

end Hex.Kronecker
