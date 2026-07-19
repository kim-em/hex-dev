/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Completeness.PelletTail
public import Mathlib.Analysis.Complex.Polynomial.Basic

public section

/-!
# Exact Pellet converse

This module connects the inverse-root elementary-symmetric tail to polynomial
coefficients and turns a wide one-root isolation margin into exact first-term
Pellet dominance.
-/

open Finset Polynomial

namespace HexRootsMathlib

noncomputable section

private theorem esymm_cons_succ (a : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  rw [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add,
    Multiset.sum_add, Multiset.map_map]
  simp only [Function.comp_apply, Multiset.prod_cons]
  rw [Multiset.sum_map_mul_left]
  rfl

/-- The normalized product with inverse-root parameters. -/
@[expose] noncomputable def remotePoly (s : Multiset ℂ) : ℂ[X] :=
  (s.map fun a => 1 - C a * X).prod

/-- Coefficients of the normalized remote-root product are the elementary
symmetric functions of its parameters, with alternating sign. -/
theorem coeff_remotePoly (s : Multiset ℂ) (k : ℕ) :
    (remotePoly s).coeff k = (-1 : ℂ) ^ k * s.esymm k := by
  induction s using Multiset.induction_on generalizing k with
  | empty =>
      cases k with
      | zero => simp [remotePoly, Multiset.esymm]
      | succ k =>
          simp [remotePoly, Multiset.esymm]
          rw [coeff_one]
          simp
  | @cons a s ih =>
      have hpoly : remotePoly (a ::ₘ s) =
          remotePoly s - C a * (X * remotePoly s) := by
        simp only [remotePoly, Multiset.map_cons, Multiset.prod_cons]
        ring
      cases k with
      | zero =>
          rw [hpoly, coeff_sub, coeff_C_mul, coeff_X_mul_zero, ih]
          simp [Multiset.esymm]
      | succ k =>
          rw [hpoly, coeff_sub, coeff_C_mul, coeff_X_mul, ih, ih,
            esymm_cons_succ, pow_succ]
          ring

/-- The item-25 bound is exactly a coefficient-tail bound for the normalized
remote-root product. -/
theorem remotePoly_tail_le {s : Multiset ℂ} {d ρ : ℝ} (hd : 0 < d)
    (hρ : 0 ≤ ρ) (hs : ∀ z ∈ s, d ≤ ‖z‖) :
    (∑ k ∈ (Finset.range (s.card + 1)).erase 0,
        ‖(remotePoly (s.map Inv.inv)).coeff k‖ * ρ ^ k) ≤
      (1 + ρ / d) ^ s.card - 1 := by
  calc
    (∑ k ∈ (Finset.range (s.card + 1)).erase 0,
        ‖(remotePoly (s.map Inv.inv)).coeff k‖ * ρ ^ k) =
        ∑ k ∈ (Finset.range (s.card + 1)).erase 0,
          ‖(s.map Inv.inv).esymm k‖ * ρ ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [coeff_remotePoly, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
        one_mul]
    _ ≤ (1 + ρ / d) ^ s.card - 1 := remote_tail_le hd hρ hs

/-- The normalized remote-root product has constant coefficient one. -/
@[simp] theorem coeff_remotePoly_zero (s : Multiset ℂ) :
    (remotePoly s).coeff 0 = 1 := by
  rw [coeff_remotePoly]
  simp [Multiset.esymm]

/-- The normalized product has degree at most the number of parameters,
including when a zero parameter makes a nominal linear factor constant. -/
theorem natDegree_remotePoly_le (s : Multiset ℂ) :
    (remotePoly s).natDegree ≤ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp [remotePoly]
  | @cons a s ih =>
      rw [show remotePoly (a ::ₘ s) = (1 - C a * X) * remotePoly s by
        simp [remotePoly]]
      have hfactor : (1 - C a * X : ℂ[X]).natDegree ≤ 1 := by
        calc
          (1 - C a * X : ℂ[X]).natDegree ≤
              max (1 : ℂ[X]).natDegree (C a * X).natDegree :=
            natDegree_sub_le (1 : ℂ[X]) (C a * X)
          _ ≤ 1 := by
            have hmul : (C a * X : ℂ[X]).natDegree ≤ 1 :=
              natDegree_mul_le.trans <| by simp
            simpa using hmul
      exact natDegree_mul_le.trans <| by
        simpa [add_comm] using add_le_add hfactor ih

/-- Normalizing each nonzero linear root factor by its constant term produces
the inverse-root polynomial `remotePoly`. -/
theorem normalize_root_product (s : Multiset ℂ)
    (hs : ∀ z ∈ s, z ≠ 0) :
    C ((s.map Neg.neg).prod) * remotePoly (s.map Inv.inv) =
      (s.map fun z => X - C z).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [remotePoly]
  | @cons z s ih =>
      have hz : z ≠ 0 := hs z (Multiset.mem_cons_self z s)
      have hs' : ∀ w ∈ s, w ≠ 0 := by
        intro w hw
        exact hs w (Multiset.mem_cons_of_mem hw)
      have hfactor : C (-z) * (1 - C z⁻¹ * X) = X - C z := by
        calc
          C (-z) * (1 - C z⁻¹ * X) =
              C (-z) - C ((-z) * z⁻¹) * X := by rw [map_mul]; ring
          _ = C (-z) - C (-1) * X := by rw [neg_mul, mul_inv_cancel₀ hz]
          _ = X - C z := by simp; ring
      simp only [Multiset.map_cons, Multiset.prod_cons, remotePoly, map_mul]
      calc
        C (-z) * C ((s.map Neg.neg).prod) *
              ((1 - C z⁻¹ * X) * remotePoly (s.map Inv.inv)) =
            (C (-z) * (1 - C z⁻¹ * X)) *
              (C ((s.map Neg.neg).prod) * remotePoly (s.map Inv.inv)) := by
                ring
        _ = (X - C z) * (s.map fun w => X - C w).prod := by
          rw [hfactor, ih hs']

/-- A nonzero complex polynomial with nonzero constant term is its constant
term times the normalized inverse-root product. This is the polynomial bridge
from item 25's multiset estimate. -/
theorem C_coeff_zero_mul_remotePoly (p : ℂ[X]) (hp : p ≠ 0)
    (h0 : p.coeff 0 ≠ 0) :
    C (p.coeff 0) * remotePoly (p.roots.map Inv.inv) = p := by
  have hroots : ∀ z ∈ p.roots, z ≠ 0 := by
    intro z hz hz0
    subst z
    apply h0
    simpa [Polynomial.IsRoot, coeff_zero_eq_eval_zero] using (mem_roots hp).mp hz
  have hnorm := normalize_root_product p.roots hroots
  have hsplit := IsAlgClosed.splits p
  calc
    C (p.coeff 0) * remotePoly (p.roots.map Inv.inv) =
        C (p.leadingCoeff * (p.roots.map Neg.neg).prod) *
          remotePoly (p.roots.map Inv.inv) := by
      rw [hsplit.coeff_zero_eq_leadingCoeff_mul_prod_roots,
        Multiset.prod_map_neg, ← hsplit.natDegree_eq_card_roots]
      ring_nf
    _ = C p.leadingCoeff *
        (C ((p.roots.map Neg.neg).prod) *
          remotePoly (p.roots.map Inv.inv)) := by
      rw [map_mul]
      ring
    _ = C p.leadingCoeff * (p.roots.map fun z => X - C z).prod := by
      rw [hnorm]
    _ = p := hsplit.eq_prod_roots.symm

/-- The weighted coefficient mass through degree `< n`. -/
private noncomputable def coeffMass (p : ℂ[X]) (n : ℕ) (ρ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, ‖p.coeff k‖ * ρ ^ k

/-- Multiplication by one linear factor increases weighted coefficient mass
by at most the weighted mass of that factor. -/
private theorem coeffMass_X_sub_C_mul_le {g : ℂ[X]} {a : ℂ} {n : ℕ}
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hdeg : g.natDegree < n) :
    coeffMass ((X - C a) * g) (n + 1) ρ ≤
      (ρ + ‖a‖) * coeffMass g n ρ := by
  have hgn : g.coeff n = 0 := coeff_eq_zero_of_natDegree_lt hdeg
  have hmass_succ : coeffMass g (n + 1) ρ = coeffMass g n ρ := by
    unfold coeffMass
    rw [Finset.sum_range_succ, hgn, norm_zero, zero_mul, add_zero]
  rw [coeffMass, Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  calc
    (∑ i ∈ Finset.range n,
          ‖((X - C a) * g).coeff (i + 1)‖ * ρ ^ (i + 1)) +
        ‖((X - C a) * g).coeff 0‖ ≤
      (∑ i ∈ Finset.range n,
          (‖g.coeff i‖ + ‖a‖ * ‖g.coeff (i + 1)‖) * ρ ^ (i + 1)) +
        ‖a‖ * ‖g.coeff 0‖ := by
      gcongr with i hi
      · rw [coeff_X_sub_C_mul]
        calc
          ‖g.coeff i - a * g.coeff (i + 1)‖ ≤
              ‖g.coeff i‖ + ‖a * g.coeff (i + 1)‖ := norm_sub_le _ _
          _ = ‖g.coeff i‖ + ‖a‖ * ‖g.coeff (i + 1)‖ := by rw [norm_mul]
      · simp [mul_coeff_zero]
    _ = ρ * coeffMass g n ρ + ‖a‖ * coeffMass g (n + 1) ρ := by
      have hfirst :
          (∑ i ∈ Finset.range n, ‖g.coeff i‖ * ρ ^ (i + 1)) =
            ρ * coeffMass g n ρ := by
        unfold coeffMass
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [pow_succ]
        ring
      have hsecond :
          ‖a‖ * ‖g.coeff 0‖ +
              ∑ i ∈ Finset.range n,
                ‖a‖ * ‖g.coeff (i + 1)‖ * ρ ^ (i + 1) =
            ‖a‖ * coeffMass g (n + 1) ρ := by
        unfold coeffMass
        rw [Finset.sum_range_succ']
        simp only [pow_zero, mul_one]
        rw [mul_add]
        have hshift :
            (∑ i ∈ Finset.range n,
                ‖a‖ * ‖g.coeff (i + 1)‖ * ρ ^ (i + 1)) =
              ‖a‖ * ∑ i ∈ Finset.range n,
                ‖g.coeff (i + 1)‖ * ρ ^ (i + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        rw [hshift]
        ring
      have hsplit :
          (∑ i ∈ Finset.range n,
              (‖g.coeff i‖ + ‖a‖ * ‖g.coeff (i + 1)‖) * ρ ^ (i + 1)) =
            (∑ i ∈ Finset.range n, ‖g.coeff i‖ * ρ ^ (i + 1)) +
              ∑ i ∈ Finset.range n,
                ‖a‖ * ‖g.coeff (i + 1)‖ * ρ ^ (i + 1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hsplit]
      calc
        (∑ i ∈ Finset.range n, ‖g.coeff i‖ * ρ ^ (i + 1)) +
              (∑ i ∈ Finset.range n,
                ‖a‖ * ‖g.coeff (i + 1)‖ * ρ ^ (i + 1)) +
            ‖a‖ * ‖g.coeff 0‖ =
          (∑ i ∈ Finset.range n, ‖g.coeff i‖ * ρ ^ (i + 1)) +
            (‖a‖ * ‖g.coeff 0‖ +
              ∑ i ∈ Finset.range n,
                ‖a‖ * ‖g.coeff (i + 1)‖ * ρ ^ (i + 1)) := by ring
        _ = ρ * coeffMass g n ρ + ‖a‖ * coeffMass g (n + 1) ρ := by
          rw [hfirst, hsecond]
    _ = (ρ + ‖a‖) * coeffMass g n ρ := by
      rw [hmass_succ]
      ring

/-- Item 25 bounds the entire weighted mass of the normalized remote
polynomial after restoring its constant coefficient. -/
private theorem coeffMass_remotePoly_le {s : Multiset ℂ} {d ρ : ℝ}
    (hd : 0 < d) (hρ : 0 ≤ ρ) (hs : ∀ z ∈ s, d ≤ ‖z‖) :
    coeffMass (remotePoly (s.map Inv.inv)) (s.card + 1) ρ ≤
      (1 + ρ / d) ^ s.card := by
  have htail := remotePoly_tail_le hd hρ hs
  have hzero : 0 ∈ Finset.range (s.card + 1) := by simp
  unfold coeffMass
  rw [← Finset.sum_erase_add _ _ hzero, coeff_remotePoly_zero,
    norm_one, pow_zero, mul_one]
  linarith

/-- The first remote coefficient is bounded by the same positive-degree
tail. This also covers the degree-one case, where the remote multiset is
empty and the coefficient vanishes. -/
private theorem coeff_one_remotePoly_le {s : Multiset ℂ} {d ρ : ℝ}
    (hd : 0 < d) (hρ : 0 ≤ ρ) (hs : ∀ z ∈ s, d ≤ ‖z‖) :
    ‖(remotePoly (s.map Inv.inv)).coeff 1‖ * ρ ≤
      (1 + ρ / d) ^ s.card - 1 := by
  by_cases hs0 : s = 0
  · subst s
    simp [remotePoly, coeff_one]
  · have hcard : 0 < s.card := Multiset.card_pos.mpr hs0
    have hone : 1 ∈ (Finset.range (s.card + 1)).erase 0 := by simp [hcard]
    simpa only [pow_one] using (Finset.single_le_sum
      (fun i _ => mul_nonneg (norm_nonneg _) (pow_nonneg hρ _)) hone).trans
        (remotePoly_tail_le hd hρ hs)

/-- A linear factor whose root is near zero satisfies exact first-term
Pellet dominance when the remaining normalized coefficient mass has enough
margin. The coefficient-mass argument deliberately keeps the degree-one
case in the same statement. -/
private theorem pellet_one_normalized {g : ℂ[X]} {a : ℂ} {n : ℕ}
    {ρ E : ℝ} (hn : 0 < n) (hρ : 0 ≤ ρ) (hdeg : g.natDegree < n)
    (hg0 : g.coeff 0 = 1)
    (hmass : coeffMass g n ρ ≤ 1 + E)
    (hone : ‖g.coeff 1‖ * ρ ≤ E)
    (hmargin : ‖a‖ + (ρ + 3 * ‖a‖) * E < ρ) :
    (∑ i ∈ (Finset.range (n + 1)).erase 1,
        ‖((X - C a) * g).coeff i‖ * ρ ^ i) <
      ‖((X - C a) * g).coeff 1‖ * ρ ^ 1 := by
  let h := (X - C a) * g
  have hE : 0 ≤ E :=
    (mul_nonneg (norm_nonneg (g.coeff 1)) hρ).trans hone
  have hfactor : 0 ≤ ρ + ‖a‖ := add_nonneg hρ (norm_nonneg a)
  have htotal : coeffMass h (n + 1) ρ ≤ (ρ + ‖a‖) * (1 + E) :=
    (coeffMass_X_sub_C_mul_le hρ hdeg).trans
      (mul_le_mul_of_nonneg_left hmass hfactor)
  have hcoeff : h.coeff 1 = 1 - a * g.coeff 1 := by
    dsimp [h]
    rw [coeff_X_sub_C_mul, hg0]
  have hreverse :
      1 - ‖a‖ * ‖g.coeff 1‖ ≤ ‖h.coeff 1‖ := by
    rw [hcoeff]
    simpa only [norm_one, norm_mul] using
      (norm_sub_norm_le (1 : ℂ) (a * g.coeff 1))
  have hscaled :
      ‖a‖ * (‖g.coeff 1‖ * ρ) ≤ ‖a‖ * E :=
    mul_le_mul_of_nonneg_left hone (norm_nonneg a)
  have hmain : ρ - ‖a‖ * E ≤ ‖h.coeff 1‖ * ρ := by
    calc
      ρ - ‖a‖ * E ≤ ρ - ‖a‖ * (‖g.coeff 1‖ * ρ) :=
        sub_le_sub_left hscaled ρ
      _ = (1 - ‖a‖ * ‖g.coeff 1‖) * ρ := by ring
      _ ≤ ‖h.coeff 1‖ * ρ := mul_le_mul_of_nonneg_right hreverse hρ
  have hwide :
      (ρ + ‖a‖) * (1 + E) < 2 * (ρ - ‖a‖ * E) := by
    nlinarith [norm_nonneg a]
  have htotal_lt : coeffMass h (n + 1) ρ < 2 * (‖h.coeff 1‖ * ρ) :=
    htotal.trans_lt <| hwide.trans_le <| mul_le_mul_of_nonneg_left hmain (by norm_num)
  have hone_mem : 1 ∈ Finset.range (n + 1) := by simp [hn]
  have hdecomp :
      (∑ i ∈ (Finset.range (n + 1)).erase 1,
          ‖h.coeff i‖ * ρ ^ i) + ‖h.coeff 1‖ * ρ =
        coeffMass h (n + 1) ρ := by
    unfold coeffMass
    simpa only [pow_one] using
      (Finset.sum_erase_add (Finset.range (n + 1))
        (fun i => ‖h.coeff i‖ * ρ ^ i) hone_mem)
  have hresult :
      (∑ i ∈ (Finset.range (n + 1)).erase 1,
          ‖h.coeff i‖ * ρ ^ i) < ‖h.coeff 1‖ * ρ := by
    linarith
  simpa only [h, pow_one] using hresult

/-- The degree side condition paired with `pellet_one_of_roots`. Keeping it
next to the dominance theorem makes the two hypotheses of `pellet` directly
available from the same root-multiset decomposition. -/
theorem natDegree_eq_of_roots {q : ℂ[X]} {a : ℂ} {s : Multiset ℂ}
    (hroots : q.roots = a ::ₘ s) : q.natDegree = s.card + 1 := by
  rw [(IsAlgClosed.splits q).natDegree_eq_card_roots, hroots]
  simp

/-- **Exact first-term Pellet converse.** Suppose the complete root multiset
of `q` consists of one designated near root `a` and the remote multiset `s`.
If every remote root is at least `d` from zero and the displayed wide-margin
inequality holds, then the first coefficient of `q` strictly dominates the
complete coefficient tail at radius `ρ`.

The exponent `s.card` counts remote roots with multiplicity. The statement
also covers `s = 0`, so linear polynomials require no separate API. -/
theorem pellet_one_of_roots {q : ℂ[X]} {a : ℂ} {s : Multiset ℂ} {d ρ : ℝ}
    (hq : q ≠ 0) (hroots : q.roots = a ::ₘ s) (hd : 0 < d) (hρ : 0 ≤ ρ)
    (hremote : ∀ z ∈ s, d ≤ ‖z‖)
    (hmargin :
      ‖a‖ + (ρ + 3 * ‖a‖) * ((1 + ρ / d) ^ s.card - 1) < ρ) :
    (∑ i ∈ (Finset.range (s.card + 2)).erase 1,
        ‖q.coeff i‖ * ρ ^ i) < ‖q.coeff 1‖ * ρ ^ 1 := by
  let g := remotePoly (s.map Inv.inv)
  let h := (X - C a) * g
  let K := q.leadingCoeff * (s.map Neg.neg).prod
  have hs0 : ∀ z ∈ s, z ≠ 0 := by
    intro z hz hz0
    subst z
    simpa using (hd.trans_le (hremote 0 hz)).ne'
  have hnorm := normalize_root_product s hs0
  have hfactor : q = C K * h := by
    calc
      q = C q.leadingCoeff * (q.roots.map fun z => X - C z).prod :=
        (IsAlgClosed.splits q).eq_prod_roots
      _ = C q.leadingCoeff *
          ((X - C a) * (s.map fun z => X - C z).prod) := by
        rw [hroots]
        simp
      _ = C (q.leadingCoeff * (s.map Neg.neg).prod) *
          ((X - C a) * remotePoly (s.map Inv.inv)) := by
        rw [← hnorm, map_mul]
        ring
      _ = C K * h := rfl
  have hK : K ≠ 0 := by
    apply mul_ne_zero (leadingCoeff_ne_zero.mpr hq)
    apply Multiset.prod_ne_zero
    intro hz
    obtain ⟨w, hw, hzero⟩ := Multiset.mem_map.mp hz
    have : -w ≠ 0 := by simpa using hs0 w hw
    exact this hzero
  have hgdeg : g.natDegree < s.card + 1 := by
    dsimp [g]
    have := natDegree_remotePoly_le (s.map Inv.inv)
    simpa using Nat.lt_succ_of_le this
  have hgdom :
      (∑ i ∈ (Finset.range (s.card + 2)).erase 1,
          ‖h.coeff i‖ * ρ ^ i) < ‖h.coeff 1‖ * ρ ^ 1 := by
    apply pellet_one_normalized (n := s.card + 1) (E :=
      (1 + ρ / d) ^ s.card - 1) (by omega) hρ hgdeg
    · exact coeff_remotePoly_zero _
    · dsimp [g]
      calc
        coeffMass (remotePoly (s.map Inv.inv)) (s.card + 1) ρ ≤
            (1 + ρ / d) ^ s.card := coeffMass_remotePoly_le hd hρ hremote
        _ = 1 + ((1 + ρ / d) ^ s.card - 1) := by ring
    · dsimp [g]
      exact coeff_one_remotePoly_le hd hρ hremote
    · exact hmargin
  rw [hfactor]
  simp only [coeff_C_mul, norm_mul]
  calc
    (∑ i ∈ (Finset.range (s.card + 2)).erase 1,
        (‖K‖ * ‖h.coeff i‖) * ρ ^ i) =
      ‖K‖ * ∑ i ∈ (Finset.range (s.card + 2)).erase 1,
        ‖h.coeff i‖ * ρ ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ < ‖K‖ * (‖h.coeff 1‖ * ρ ^ 1) :=
      mul_lt_mul_of_pos_left hgdom (norm_pos_iff.mpr hK)
    _ = (‖K‖ * ‖h.coeff 1‖) * ρ ^ 1 := by ring

/-- Translation form of `pellet_one_of_roots`. Here `z` is the designated
root of `p`, `s` is the multiset of every other root (with multiplicity), and
the conclusion is stated directly for the Taylor polynomial about an
arbitrary centre `c`. -/
theorem pellet_one_comp_dominates {p : ℂ[X]} {c z : ℂ} {s : Multiset ℂ}
    {d ρ : ℝ} (hp : p ≠ 0) (hroots : p.roots = z ::ₘ s) (hd : 0 < d)
    (hρ : 0 ≤ ρ) (hremote : ∀ w ∈ s, d ≤ ‖w - c‖)
    (hmargin :
      ‖z - c‖ + (ρ + 3 * ‖z - c‖) *
          ((1 + ρ / d) ^ s.card - 1) < ρ) :
    (∑ i ∈ (Finset.range (s.card + 2)).erase 1,
        ‖(p.comp (X + C c)).coeff i‖ * ρ ^ i) <
      ‖(p.comp (X + C c)).coeff 1‖ * ρ ^ 1 := by
  let q := p.comp (X + C c)
  have hq : q ≠ 0 := (comp_X_add_C_ne_zero_iff (p := p) (t := c)).mpr hp
  have hqroots : q.roots = (z - c) ::ₘ s.map fun w => w - c := by
    have htranslate : q.roots = p.roots.map fun w => w - c := by
      dsimp [q]
      convert roots_comp_C_mul_X_add_C p 1 c isUnit_one using 1 <;> simp
    rw [htranslate, hroots]
    simp
  have hremote' : ∀ w ∈ s.map (fun w => w - c), d ≤ ‖w‖ := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hw
    exact hremote u hu
  have hmargin' :
      ‖z - c‖ + (ρ + 3 * ‖z - c‖) *
          ((1 + ρ / d) ^ (s.map fun w => w - c).card - 1) < ρ := by
    simpa using hmargin
  simpa only [q, Multiset.card_map] using
    pellet_one_of_roots hq hqroots hd hρ hremote' hmargin'

end

end HexRootsMathlib
