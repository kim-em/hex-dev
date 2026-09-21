/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRootsMathlib.TarskiGcd

public section

namespace HexRealRootsMathlib.Tarski

open Hex HexPolyMathlib.Interpret Polynomial

variable {K : Type u} [Field K]

private theorem scale_mod (c : K) (p q : Polynomial K) :
    (C c * p) % q = C c * (p % q) := by
  simp only [Polynomial.mod_def, ← Polynomial.smul_eq_C_mul, Polynomial.smul_modByMonic]

private theorem mod_scale (c : K) (hc : c ≠ 0) (p q : Polynomial K) :
    p % (C c * q) = p % q := by
  simp only [Polynomial.mod_def, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, mul_inv_rev,
    Polynomial.C_mul]
  congr 1
  calc
    C c * q * (C q.leadingCoeff⁻¹ * C c⁻¹) =
        (C c * C c⁻¹) * (q * C q.leadingCoeff⁻¹) := by ring
    _ = q * C q.leadingCoeff⁻¹ := by rw [← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]

/-- Rescaling the dividend and rescaling the divisor by a nonzero scalar
rescales the remainder by the dividend's scalar. -/
theorem remainder_scale (a b : K) (hb : b ≠ 0) (p q : Polynomial K) :
    (C a * p) % (C b * q) = C a * (p % q) := by
  rw [mod_scale b hb, scale_mod]

private theorem remainder_eq {p q r a : Polynomial K} {l s : K}
    (hs : s ≠ 0) (hq : q ≠ 0) (hr : r = 0 ∨ r.natDegree < q.natDegree)
    (h : C l * p = a * q + C s * r) :
    r = C (l / s) * (p % q) := by
  have hsmall : r % q = r := by
    rcases hr with rfl | hr
    · simp
    · exact (Polynomial.mod_eq_self_iff hq).mpr (Polynomial.degree_lt_degree hr)
  have he := congrArg (fun t => t % q) h
  have hmultiple : (a * q) % q = 0 := EuclideanDomain.mod_eq_zero.mpr (dvd_mul_left _ _)
  rw [scale_mod, Polynomial.add_mod, hmultiple, zero_add, scale_mod, hsmall] at he
  calc
    r = C s⁻¹ * (C s * r) := by rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hs, C_1, one_mul]
    _ = C s⁻¹ * (C l * (p % q)) := by rw [← he]
    _ = C (l / s) * (p % q) := by rw [← mul_assoc, ← C_mul, div_eq_mul_inv, mul_comm s⁻¹]

private theorem compare_entries [LinearOrder K] [IsStrictOrderedRing K]
    (P Q : Nat → Polynomial K) (n m : Nat)
    (hp : ∀ i, P i = 0 ↔ n ≤ i) (hq : ∀ i, Q i = 0 ↔ m ≤ i)
    (h0 : ∃ a : K, 0 < a ∧ Q 0 = C a * P 0)
    (h1 : ∃ a : K, 0 < a ∧ Q 1 = C a * P 1)
    (hP : ∀ i, i + 1 < n → ∃ a : K, 0 < a ∧ P (i + 2) = C a * -(P i % P (i + 1)))
    (hQ : ∀ i, i + 1 < m → ∃ a : K, 0 < a ∧ Q (i + 2) = C a * -(Q i % Q (i + 1))) :
    n = m ∧ ∀ i, ∃ a : K, 0 < a ∧ Q i = C a * P i := by
  have he : ∀ i, ∃ a : K, 0 < a ∧ Q i = C a * P i := by
    intro i
    induction i using Nat.twoStepInduction with
    | zero => exact h0
    | one => exact h1
    | more i hi hi1 =>
      obtain ⟨a, ha, hi⟩ := hi
      obtain ⟨b, hb, hi1⟩ := hi1
      by_cases hpi : i + 1 < n
      · have hqi : i + 1 < m := by
          by_contra hqi
          have he := (hq (i + 1)).mpr (by omega)
          rw [hi1, mul_eq_zero] at he
          rcases he with he | he
          · exact (C_ne_zero.mpr (ne_of_gt hb)) he
          · have := (hp _).mp he
            omega
        obtain ⟨c, hc, hpc⟩ := hP i hpi
        obtain ⟨d, hd, hqd⟩ := hQ i hqi
        refine ⟨d * a / c, div_pos (mul_pos hd ha) hc, ?_⟩
        rw [hqd, hi, hi1, remainder_scale a b (ne_of_gt hb), hpc, ← mul_neg]
        have hs : (d * a / c) * c = d * a := div_mul_cancel₀ _ (ne_of_gt hc)
        simp only [← mul_assoc, ← C_mul, hs]
      · refine ⟨1, zero_lt_one, ?_⟩
        have hp1 := (hp _).mpr (by omega : n ≤ i + 1)
        have hq1 : Q (i + 1) = 0 := by rw [hi1, hp1, mul_zero]
        have hm := (hq _).mp hq1
        rw [(hq _).mpr (by omega : m ≤ i + 2), (hp _).mpr (by omega : n ≤ i + 2), mul_zero]
  refine ⟨?_, he⟩
  obtain ⟨a, _, ha⟩ := he n
  have hmn : m ≤ n := (hq n).mp (by rw [ha, (hp n).mpr le_rfl, mul_zero])
  obtain ⟨b, hb, he⟩ := he m
  have hnm : n ≤ m := by
    have hz := (hq m).mpr le_rfl
    rw [he, mul_eq_zero] at hz
    exact (hp m).mp (hz.resolve_left (C_ne_zero.mpr (ne_of_gt hb)))
  omega

section Replay

variable {D : Type v} [Zero D] [DecidableEq D] [Add D] [Sub D] [Mul D] [NatCast D]
variable [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K]
variable (f : D → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hn : ∀ n : Nat, f (n : D) = (n : K))
variable (sign : D → Int) (hpos : ∀ a, sign a = 1 ↔ 0 < f a)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The zero-padded view of an accepted chain is zero precisely beyond its
stored entries. This uses zero reflection, not injectivity of interpretation. -/
theorem check_entry_zero (p g : DensePoly D) (cert : SignedRemainderChain D)
    (h : SignedRemainderChain.check sign p g cert = true) (i : Nat) :
    interpret f hz (cert.chain.getD i 0) = 0 ↔ cert.chain.size ≤ i := by
  by_cases hi : i < cert.chain.size
  · have hnz := check_nonzero f hz sign p g cert h (cert.chain.getD i 0) (by
      rw [← Array.getElem_eq_getD (h := hi) 0]
      exact Array.getElem_mem _)
    simp only [hnz, Nat.not_le.mpr hi]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    simp only [Option.getD_none, interpret_zero, le_of_not_gt hi]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Successive interpreted entries have strictly smaller degree, with the
implicit zero after the last entry handled separately. -/
theorem check_descent (p g : DensePoly D) (cert : SignedRemainderChain D)
    (h : SignedRemainderChain.check sign p g cert = true) (i : Nat) :
    interpret f hz (cert.chain.getD (i + 1) 0) = 0 ∨
      (interpret f hz (cert.chain.getD (i + 1) 0)).natDegree <
        (interpret f hz (cert.chain.getD i 0)).natDegree := by
  by_cases hi : i + 1 < cert.chain.size
  · have hnz := check_nonzero f hz sign p g cert h (cert.chain.getD (i + 1) 0) (by
      rw [← Array.getElem_eq_getD (h := hi) 0]
      exact Array.getElem_mem _)
    have hsize : 0 < (cert.chain.getD (i + 1) 0).size := by
      apply Nat.pos_of_ne_zero
      intro he
      exact hnz (by rw [(DensePoly.size_eq_zero_iff _).mp he, interpret_zero])
    simp only [SignedRemainderChain.check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
    have hd := Array.all_eq_true_iff_forall_mem.mp h.2.2.2.2.2.2.1 i
      (Array.mem_range.mpr (by omega))
    simp only [decide_eq_true_eq] at hd
    right
    simp only [natDegree_interpret, DensePoly.natDegree_eq_size_sub_one]
    omega
  · left
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    exact interpret_zero f hz

include ha hs hm hn hpos in
/-- An accepted initial reduction determines the second entry up to its
recorded positive scalar, including the singleton/zero-remainder case. -/
theorem check_initial_rem (p g : DensePoly D) (cert : SignedRemainderChain D)
    (h : SignedRemainderChain.check sign p g cert = true) :
    ∃ c : K, 0 < c ∧ interpret f hz (cert.chain.getD 1 0) =
      C c * ((interpret f hz g * (interpret f hz p).derivative) % interpret f hz p) := by
  obtain ⟨hl, hr, he⟩ := check_initial f hz ha hs hm hn sign hpos p g cert h
  have hp := check_nonzero f hz sign p g cert h (cert.chain.getD 0 0) (by
    rw [← Array.getElem_eq_getD (h := (check_bound f hz sign p g cert h).1) 0]
    exact Array.getElem_mem _)
  rw [check_head sign p g cert h] at hp
  have hd := check_descent f hz sign p g cert h 0
  rw [check_head sign p g cert h] at hd
  exact ⟨_, div_pos hl hr, remainder_eq (ne_of_gt hr) hp hd he⟩

include ha hs hm hpos in
/-- Each checked step determines the following entry up to a positive scalar.
The terminal identity supplies the same equation with zero as the next entry;
no constant-tail or coprimality hypothesis is needed. -/
theorem check_next_rem (p g : DensePoly D) (cert : SignedRemainderChain D)
    (h : SignedRemainderChain.check sign p g cert = true) (i : Nat) (hi : i + 1 < cert.chain.size) :
    ∃ c : K, 0 < c ∧ interpret f hz (cert.chain.getD (i + 2) 0) =
      C c * -(interpret f hz (cert.chain.getD i 0) %
        interpret f hz (cert.chain.getD (i + 1) 0)) := by
  have hcur := check_nonzero f hz sign p g cert h (cert.chain.getD (i + 1) 0) (by
    rw [← Array.getElem_eq_getD (h := hi) 0]
    exact Array.getElem_mem _)
  have hsingle : cert.chain.size ≠ 1 := by omega
  obtain ⟨hsize, u, q, ht⟩ := check_tail sign p g cert h hsingle
  by_cases hstep : i < cert.steps.size
  · obtain ⟨hl, hr, he⟩ := check_step f hz ha hs hm sign hpos p g cert h hsingle i hstep
    have hd := check_descent f hz sign p g cert h (i + 1)
    have hd' : -interpret f hz (cert.chain.getD (i + 2) 0) = 0 ∨
        (-interpret f hz (cert.chain.getD (i + 2) 0)).natDegree <
          (interpret f hz (cert.chain.getD (i + 1) 0)).natDegree := by
      simpa only [neg_eq_zero, Polynomial.natDegree_neg, Nat.add_assoc] using hd
    rw [sub_eq_add_neg, ← mul_neg] at he
    have hr' := remainder_eq (ne_of_gt hr) hcur hd' he
    refine ⟨_, div_pos hl hr, ?_⟩
    simpa only [neg_neg, neg_mul_eq_mul_neg] using congrArg Neg.neg hr'
  · have hi' : i = cert.chain.size - 2 := by omega
    have hi'' : i + 1 = cert.chain.size - 1 := by omega
    have hznext : interpret f hz (cert.chain.getD (i + 2) 0) = 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      exact interpret_zero f hz
    obtain ⟨hu, he⟩ := check_terminal f hz ha hs hm sign hpos p g cert h hsingle u q ht
    have he' : C (f u) * interpret f hz (cert.chain.getD i 0) =
        interpret f hz q * interpret f hz (cert.chain.getD (i + 1) 0) + C (1 : K) * 0 := by
      rw [hi'', hi', mul_zero, add_zero]
      exact he
    have hr' := remainder_eq (one_ne_zero : (1 : K) ≠ 0) hcur (Or.inl rfl) he'
    refine ⟨f u, hu, ?_⟩
    rw [hznext]
    simpa only [div_one, neg_zero, neg_mul_eq_mul_neg] using congrArg Neg.neg hr'

include ha hs hm hn hpos in
/-- Accepted chains for positively scaled inputs have the same length and
correspond entry by entry by positive scalars. Both coefficient interpretations
may be noninjective; no producer provenance or root theorem is assumed. -/
theorem check_compare {E : Type w} [Zero E] [DecidableEq E] [Add E] [Sub E] [Mul E] [NatCast E]
    (j : E → K) (jz : ∀ a, j a = 0 ↔ a = 0)
    (ja : ∀ a b, j (a + b) = j a + j b) (js : ∀ a b, j (a - b) = j a - j b)
    (jm : ∀ a b, j (a * b) = j a * j b) (jn : ∀ n : Nat, j (n : E) = (n : K))
    (sign' : E → Int) (jpos : ∀ a, sign' a = 1 ↔ 0 < j a)
    (p g : DensePoly D) (cert : SignedRemainderChain D) (h : SignedRemainderChain.check sign p g cert = true)
    (p' g' : DensePoly E) (cert' : SignedRemainderChain E) (h' : SignedRemainderChain.check sign' p' g' cert' = true)
    (a b : K) (ha' : 0 < a) (hb' : 0 < b)
    (hp : interpret j jz p' = C a * interpret f hz p)
    (hg : interpret j jz g' = C b * interpret f hz g) :
    cert.chain.size = cert'.chain.size ∧ ∀ i, ∃ c : K, 0 < c ∧
      interpret j jz (cert'.chain.getD i 0) = C c * interpret f hz (cert.chain.getD i 0) := by
  apply compare_entries (fun i => interpret f hz (cert.chain.getD i 0))
    (fun i => interpret j jz (cert'.chain.getD i 0)) cert.chain.size cert'.chain.size
    (check_entry_zero f hz sign p g cert h) (check_entry_zero j jz sign' p' g' cert' h')
  · exact ⟨a, ha', by rw [check_head sign p g cert h, check_head sign' p' g' cert' h', hp]⟩
  · obtain ⟨c, hc, he⟩ := check_initial_rem f hz ha hs hm hn sign hpos p g cert h
    obtain ⟨d, hd, he'⟩ := check_initial_rem j jz ja js jm jn sign' jpos p' g' cert' h'
    refine ⟨d * (b * a) / c, div_pos (mul_pos hd (mul_pos hb' ha')) hc, ?_⟩
    rw [he', hg, hp, Polynomial.derivative_C_mul]
    have hprod : (C b * interpret f hz g) * (C a * (interpret f hz p).derivative) =
        C (b * a) * (interpret f hz g * (interpret f hz p).derivative) := by
      rw [C_mul]
      ring
    rw [hprod, remainder_scale (b * a) a (ne_of_gt ha'), he]
    have hc' : d * b * a / c * c = d * b * a := div_mul_cancel₀ _ (ne_of_gt hc)
    simp only [← mul_assoc, ← C_mul, hc']
  · exact check_next_rem f hz ha hs hm sign hpos p g cert h
  · exact check_next_rem j jz ja js jm sign' jpos p' g' cert' h'

end Replay

end HexRealRootsMathlib.Tarski
