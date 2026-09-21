/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRootsMathlib.TarskiInterpret
public import Mathlib.FieldTheory.Perfect

public section

namespace HexRealRootsMathlib.Tarski

open Hex DensePoly HexPolyMathlib.Interpret

private theorem dvd_step {K : Type u} [Field K] {a b c q : Polynomial K} {l r : K}
    (hl : l ≠ 0) (hr : r ≠ 0) (heq : Polynomial.C l * a = q * b - Polynomial.C r * c)
    (d : Polynomial K) : (d ∣ a ∧ d ∣ b) ↔ (d ∣ b ∧ d ∣ c) := by
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨hb, (Polynomial.dvd_C_mul hr).mp ?_⟩
    have h := dvd_sub (dvd_mul_of_dvd_right hb q) (dvd_mul_of_dvd_right ha (Polynomial.C l))
    rw [heq, sub_sub_cancel] at h
    exact h
  · rintro ⟨hb, hc⟩
    refine ⟨(Polynomial.dvd_C_mul hl).mp ?_, hb⟩
    rw [heq]
    exact dvd_sub (dvd_mul_of_dvd_right hb q) (dvd_mul_of_dvd_right hc (Polynomial.C r))

private theorem dvd_initial {K : Type u} [Field K] {a b c q : Polynomial K} {l r : K}
    (hl : l ≠ 0) (hr : r ≠ 0) (heq : Polynomial.C l * b = q * a + Polynomial.C r * c)
    (d : Polynomial K) : (d ∣ a ∧ d ∣ b) ↔ (d ∣ a ∧ d ∣ c) := by
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨ha, (Polynomial.dvd_C_mul hr).mp ?_⟩
    have h := dvd_sub (dvd_mul_of_dvd_right hb (Polynomial.C l)) (dvd_mul_of_dvd_right ha q)
    rw [heq, add_sub_cancel_left] at h
    exact h
  · rintro ⟨ha, hc⟩
    refine ⟨ha, (Polynomial.dvd_C_mul hl).mp ?_⟩
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_right ha q) (dvd_mul_of_dvd_right hc (Polynomial.C r))

variable {D : Type u} {K : Type v} [Zero D] [DecidableEq D]
variable [Add D] [Sub D] [Mul D] [NatCast D]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K]
variable (f : D → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hn : ∀ n : Nat, f (n : D) = (n : K))
variable (sign : D → Int) (hpos : ∀ a, sign a = 1 ↔ 0 < f a)

/-- Accepted replay retains the exact input head. -/
theorem check_head (p g : DensePoly D) (cert : SignedRemainderChain D)
    (h : SignedRemainderChain.check sign p g cert = true) : cert.chain.getD 0 0 = p := by
  simp only [SignedRemainderChain.check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨_, _, _, hhead, _⟩ := h
  rw [Array.getD_eq_getD_getElem?, hhead]
  rfl

/-- A nonsingleton accepted chain has all steps and a terminal identity. -/
theorem check_tail (p g : DensePoly D) (cert : SignedRemainderChain D)
    (h : SignedRemainderChain.check sign p g cert = true) (hn : cert.chain.size ≠ 1) :
    cert.steps.size + 2 = cert.chain.size ∧ ∃ u q, cert.terminal = some (u, q) := by
  simp only [SignedRemainderChain.check, hn, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hlength, _, ht⟩ := h
  refine ⟨hlength, ?_⟩
  cases heq : cert.terminal with
  | none => rw [heq] at ht; contradiction
  | some pair => exact ⟨pair.1, pair.2, rfl⟩

include ha hs hm hn hpos in
/-- The last entry of an accepted replay has exactly the common divisors of
`P` and `F*P'` in the semantic field, including singleton chains. -/
theorem check_dvd_last (p g : DensePoly D) (cert : SignedRemainderChain D)
    (h : SignedRemainderChain.check sign p g cert = true) (d : Polynomial K) :
    (d ∣ interpret f hz p ∧ d ∣ interpret f hz g * (interpret f hz p).derivative) ↔
      d ∣ interpret f hz (cert.chain.getD (cert.chain.size - 1) 0) := by
  obtain ⟨hl, hr, hi⟩ := check_initial f hz ha hs hm hn sign hpos p g cert h
  have hfirst := dvd_initial (ne_of_gt hl) (ne_of_gt hr) hi d
  have hhead := check_head sign p g cert h
  by_cases hsingle : cert.chain.size = 1
  · have hsecond : cert.chain.getD 1 0 = 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    simpa only [hsingle, Nat.sub_self, hhead, hsecond, interpret_zero, dvd_zero, and_true] using hfirst
  · obtain ⟨hsize, u, q, ht⟩ := check_tail sign p g cert h hsingle
    obtain ⟨hu, hterminal⟩ := check_terminal f hz ha hs hm sign hpos p g cert h hsingle u q ht
    have htail : ∀ (k i : Nat) (_ : i + k + 2 = cert.chain.size),
        (d ∣ interpret f hz (cert.chain.getD i 0) ∧
          d ∣ interpret f hz (cert.chain.getD (i + 1) 0)) ↔
        d ∣ interpret f hz (cert.chain.getD (cert.chain.size - 1) 0) := by
      intro k
      induction k with
      | zero =>
        intro i hi
        have hi' : i = cert.chain.size - 2 := by omega
        have hi'' : i + 1 = cert.chain.size - 1 := by omega
        rw [hi'', hi']
        constructor
        · exact And.right
        · intro hd
          refine ⟨(Polynomial.dvd_C_mul (ne_of_gt hu)).mp ?_, hd⟩
          rw [hterminal]
          exact dvd_mul_of_dvd_right hd _
      | succ k ih =>
        intro i hi
        obtain ⟨hl, hr, hs⟩ := check_step f hz ha hs hm sign hpos p g cert h hsingle i (by omega)
        have hstep := dvd_step (ne_of_gt hl) (ne_of_gt hr) hs d
        have hnext := ih (i + 1) (by omega)
        exact hstep.trans (by simpa only [Nat.add_assoc] using hnext)
    have ht0 := htail (cert.chain.size - 2) 0 (by omega)
    simp only [Nat.zero_add, hhead] at ht0
    exact hfirst.trans ht0

include ha hs hm hn hpos in
/-- The terminal polynomial in an accepted query replay is associated to the
semantic gcd, whether that gcd is constant or nonconstant. -/
theorem check_gcd (p g : DensePoly D) (cert : SignedRemainderChain D)
    (h : SignedRemainderChain.check sign p g cert = true) :
    Associated (interpret f hz (cert.chain.getD (cert.chain.size - 1) 0))
      (EuclideanDomain.gcd (interpret f hz p)
        (interpret f hz g * (interpret f hz p).derivative)) := by
  apply associated_of_dvd_dvd
  · have hd := (check_dvd_last f hz ha hs hm hn sign hpos p g cert h _).mpr (dvd_refl _)
    exact EuclideanDomain.dvd_gcd hd.1 hd.2
  · exact (check_dvd_last f hz ha hs hm hn sign hpos p g cert h _).mp
      ⟨EuclideanDomain.gcd_dvd_left _ _, EuclideanDomain.gcd_dvd_right _ _⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The replay's literal constant-tail guard means a nonzero constant after
interpretation, without requiring a canonical representative of one. -/
theorem lastIsConstant_iff (p g : DensePoly D) (cert : SignedRemainderChain D)
    (h : SignedRemainderChain.check sign p g cert = true) :
    SignedRemainderChain.lastIsConstant cert = true ↔
      IsUnit (interpret f hz (cert.chain.getD (cert.chain.size - 1) 0)) := by
  have hb := (check_bound f hz sign p g cert h).1
  have hmem : cert.chain.getD (cert.chain.size - 1) 0 ∈ cert.chain := by
    rw [← Array.getElem_eq_getD (h := by omega) 0]
    exact Array.getElem_mem _
  have hnz := check_nonzero f hz sign p g cert h _ hmem
  have hsiz : 0 < (cert.chain.getD (cert.chain.size - 1) 0).size := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply hnz
    rw [(size_eq_zero_iff _).mp hzero, interpret_zero]
  rw [SignedRemainderChain.lastIsConstant, beq_iff_eq, Polynomial.isUnit_iff_degree_eq_zero,
    Polynomial.degree_eq_natDegree hnz]
  simp only [Nat.cast_eq_zero, natDegree_interpret, natDegree_eq_size_sub_one]
  omega

include ha hs hm hn hpos in
/-- For the derivative replay, the exact constant-tail guard is equivalent to
squarefreeness over the semantic ordered field. -/
theorem check_squarefree [One D] (h1 : f (1 : D) = 1)
    (p : DensePoly D) (cert : SignedRemainderChain D)
    (h : SignedRemainderChain.check sign p 1 cert = true) :
    SignedRemainderChain.lastIsConstant cert = true ↔ Squarefree (interpret f hz p) := by
  rw [lastIsConstant_iff f hz sign p 1 cert h,
    (check_gcd f hz ha hs hm hn sign hpos p 1 cert h).isUnit_iff,
    interpret_one f hz h1, one_mul, EuclideanDomain.gcd_isUnit_iff,
    ← Polynomial.separable_def, PerfectField.separable_iff_squarefree]

include ha hs hm hn hpos in
/-- Query production succeeds exactly when the endpoint guards and semantic
squarefreeness hold. There is no exhaustion case hidden in the `Option`. -/
theorem query_isSome [One D] [Neg D] (h1 : f (1 : D) = 1)
    {E : Type w} (endpointSigns : EndpointSigns D E)
    (normalize : DensePoly D → D × DensePoly D)
    (hchains : ∀ p g : DensePoly D, p ≠ 0 →
      SignedRemainderChain.check sign p g (SignedRemainderChain.build sign normalize p g) = true)
    (p g : DensePoly D) (a b : Endpoint E) :
    (TarskiCertificate.query sign endpointSigns normalize p g a b).isSome = true ↔
      TarskiCertificate.checkEndpoints endpointSigns p a b = true ∧ Squarefree (interpret f hz p) := by
  by_cases hg : TarskiCertificate.checkEndpoints endpointSigns p a b = true
  · have hp : p ≠ 0 := by
      have hg' := hg
      simp only [TarskiCertificate.checkEndpoints, Bool.and_eq_true] at hg'
      intro hp
      have hp' := hg'.1.1.1
      rw [hp] at hp'
      contradiction
    have hsf := check_squarefree f hz ha hs hm hn sign hpos h1 p
      (SignedRemainderChain.build sign normalize p 1) (hchains p 1 hp)
    simp only [TarskiCertificate.query, TarskiCertificate.certify, hg, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Option.isSome_map, true_and]
    cases ht : SignedRemainderChain.lastIsConstant (SignedRemainderChain.build sign normalize p 1) <;>
      simp_all only [Bool.not_false, Bool.not_true, ↓reduceIte, Option.isSome_none,
        Option.isSome_some, Bool.false_eq_true, true_iff, false_iff]
  · have hg' : TarskiCertificate.checkEndpoints endpointSigns p a b = false := Bool.eq_false_iff.mpr hg
    simp only [TarskiCertificate.query, TarskiCertificate.certify, hg', Bool.not_false, ↓reduceIte,
      Option.map_none, Option.isSome_none, Bool.false_eq_true, false_and]

end HexRealRootsMathlib.Tarski


