/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFast.Cyclic

public section
set_option backward.proofsInPublic true

/-!
# Polynomial-remainder semantics of cyclic products

This module identifies the coefficient folds from `HexPolyFast.Cyclic` with
monic division by `x^n - 1` and `x^n + 1`.  The explicit nontriviality
hypothesis is necessary: in the zero ring both displayed moduli normalize to
the zero polynomial.
-/

namespace Hex.DensePoly

universe u

attribute [local instance 1000] Lean.Grind.Semiring.ofNat

variable {R : Type u} [DecidableEq R] [Lean.Grind.CommRing R]

/-- The monic polynomial `x^n - 1` used for cyclic convolution. -/
def cyclicModulus (n : Nat) : DensePoly R :=
  monomial n 1 - 1

/-- The monic polynomial `x^n + 1` used for negacyclic convolution. -/
def negacyclicModulus (n : Nat) : DensePoly R :=
  monomial n 1 + 1

theorem size_cyclicModulus (n : Nat) (hn : 0 < n) (hone : (1 : R) ≠ 0) :
    (cyclicModulus (R := R) n).size = n + 1 := by
  have hn0 : n ≠ 0 := by omega
  apply Nat.le_antisymm
  · unfold cyclicModulus
    refine Nat.le_trans (size_sub_le_max _ _) ?_
    rw [size_monomial_of_ne_zero hone, size_one hone]
    omega
  · apply Nat.le_of_not_gt
    intro hlt
    have hz := coeff_eq_zero_of_size_le (cyclicModulus (R := R) n)
      (i := n) (by omega)
    rw [cyclicModulus, coeff_sub_ring, coeff_monomial] at hz
    change (if n = n then 1 else 0) - (C (1 : R)).coeff n = 0 at hz
    rw [coeff_C] at hz
    simp [hn0] at hz
    change (1 : R) - 0 = 0 at hz
    have hz' : (1 : R) = 0 := Lean.Grind.AddCommGroup.sub_eq_zero_iff.mp hz
    exact hone hz'

theorem size_negacyclicModulus (n : Nat) (hn : 0 < n) (hone : (1 : R) ≠ 0) :
    (negacyclicModulus (R := R) n).size = n + 1 := by
  have hn0 : n ≠ 0 := by omega
  apply Nat.le_antisymm
  · unfold negacyclicModulus
    refine Nat.le_trans (size_add_le_max _ _) ?_
    rw [size_monomial_of_ne_zero hone, size_one hone]
    omega
  · apply Nat.le_of_not_gt
    intro hlt
    have hz := coeff_eq_zero_of_size_le (negacyclicModulus (R := R) n)
      (i := n) (by omega)
    rw [negacyclicModulus, coeff_add _ _ _ (by
      change (0 : R) + 0 = 0
      grind), coeff_monomial] at hz
    change (if n = n then 1 else 0) + (C (1 : R)).coeff n = 0 at hz
    rw [coeff_C] at hz
    simp [hn0] at hz
    change (1 : R) + 0 = 0 at hz
    rw [Lean.Grind.Semiring.add_zero] at hz
    have hz' : (1 : R) = 0 := hz
    exact hone hz'

theorem cyclicModulus_monic (n : Nat) (hn : 0 < n) (hone : (1 : R) ≠ 0) :
    (cyclicModulus (R := R) n).Monic := by
  have hn0 : n ≠ 0 := by omega
  rw [monic_iff_leadingCoeff_eq_one,
    leadingCoeff_eq_coeff_last _ (by rw [size_cyclicModulus n hn hone]; omega),
    size_cyclicModulus n hn hone]
  have hidx : n + 1 - 1 = n := by omega
  rw [hidx, cyclicModulus, coeff_sub_ring, coeff_monomial]
  change (if n = n then 1 else 0) - (C (1 : R)).coeff n = 1
  rw [coeff_C]
  simp [hn0]
  change (1 : R) - 0 = 1
  rw [Lean.Grind.Ring.sub_eq_add_neg, Lean.Grind.AddCommGroup.neg_zero,
    Lean.Grind.Semiring.add_zero]

theorem negacyclicModulus_monic (n : Nat) (hn : 0 < n) (hone : (1 : R) ≠ 0) :
    (negacyclicModulus (R := R) n).Monic := by
  have hn0 : n ≠ 0 := by omega
  rw [monic_iff_leadingCoeff_eq_one,
    leadingCoeff_eq_coeff_last _ (by rw [size_negacyclicModulus n hn hone]; omega),
    size_negacyclicModulus n hn hone]
  have hidx : n + 1 - 1 = n := by omega
  rw [hidx, negacyclicModulus, coeff_add _ _ _ (by
    change (0 : R) + 0 = 0
    grind), coeff_monomial]
  change (if n = n then 1 else 0) + (C (1 : R)).coeff n = 1
  rw [coeff_C]
  simp [hn0]
  change (1 : R) + 0 = 1
  rw [Lean.Grind.Semiring.add_zero]

/-- A monomial and the monomial obtained by reducing its exponent modulo `n`
are congruent modulo `x^n - 1`. -/
theorem cyclicModulus_dvd_monomial_sub (n i : Nat) (hn : 0 < n) (c : R) :
    cyclicModulus (R := R) n ∣
      monomial i c - monomial (i % n) c := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
      by_cases hi : i < n
      · rw [Nat.mod_eq_of_lt hi]
        have hself : monomial i c - monomial i c = (0 : DensePoly R) := by
          apply ext_coeff
          intro k
          rw [coeff_sub_ring, coeff_zero]
          grind
        rw [hself]
        exact dvd_zero_poly (cyclicModulus (R := R) n)
      · have hni : n ≤ i := Nat.le_of_not_gt hi
        let j := i - n
        have hjlt : j < i := by dsimp [j]; omega
        have hmod : j % n = i % n := by
          dsimp [j]
          exact (Nat.mod_eq_sub_mod hni).symm
        have hstep : cyclicModulus (R := R) n ∣
            monomial i c - monomial j c := by
          refine ⟨monomial j c, ?_⟩
          rw [cyclicModulus, sub_mul_poly, monomial_mul_monomial]
          have hsum : n + j = i := by dsimp [j]; omega
          rw [hsum, Lean.Grind.Semiring.one_mul]
          have hone_mul : (1 : DensePoly R) * monomial j c = monomial j c := by
            rw [mul_comm_poly, mul_one_right_poly]
          rw [hone_mul]
        have htail : cyclicModulus (R := R) n ∣
            monomial j c - monomial (i % n) c := by
          simpa [hmod] using ih j hjlt
        have hsplit :
            monomial i c - monomial (i % n) c =
              (monomial i c - monomial j c) +
                (monomial j c - monomial (i % n) c) := by
          apply ext_coeff
          intro k
          rw [coeff_sub_ring, coeff_add _ _ _ (by
            change (0 : R) + 0 = 0
            grind),
            coeff_sub_ring, coeff_sub_ring]
          grind
        rw [hsplit]
        exact dvd_add_poly hstep htail

private theorem coeff_foldl_monomials (p : DensePoly R) (N k : Nat) :
    ((List.range N).foldl
        (fun q i => q + monomial i (p.coeff i)) 0).coeff k =
      if k < N then p.coeff k else 0 := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        coeff_add _ _ _ (by
          change (0 : R) + 0 = 0
          grind), ih, coeff_monomial]
      by_cases hk : k < N
      · have hkne : k ≠ N := by omega
        have hksucc : k < N + 1 := by omega
        simp [hk, hkne, hksucc]
        change p.coeff k + 0 = p.coeff k
        exact Lean.Grind.Semiring.add_zero _
      · by_cases hkeq : k = N
        · subst k
          simp [Lean.Grind.AddCommMonoid.zero_add]
        · have hksucc : ¬ k < N + 1 := by omega
          simp [hk, hkeq, hksucc]
          change (0 : R) + 0 = 0
          exact Lean.Grind.Semiring.add_zero 0

theorem foldl_monomials_eq (p : DensePoly R) :
    (List.range p.size).foldl
        (fun q i => q + monomial i (p.coeff i)) 0 = p := by
  apply ext_coeff
  intro k
  rw [coeff_foldl_monomials]
  by_cases hk : k < p.size
  · rw [ite_eq_left hk]
  · rw [ite_eq_right hk, coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hk)]
    rfl

private theorem cyclicModulus_dvd_fold_sub (n N : Nat) (hn : 0 < n)
    (p : DensePoly R) :
    cyclicModulus (R := R) n ∣
      (List.range N).foldl
          (fun q i => q + monomial i (p.coeff i)) 0 -
        (List.range N).foldl
          (fun q i => q + monomial (i % n) (p.coeff i)) 0 := by
  induction N with
  | zero =>
      have hzero : (0 : DensePoly R) - 0 = 0 := by
        apply ext_coeff
        intro k
        rw [coeff_sub_ring, coeff_zero]
        grind
      simp only [List.range_zero, List.foldl_nil]
      rw [hzero]
      exact dvd_zero_poly _
  | succ N ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hsplit :
          ((List.range N).foldl
                (fun q i => q + monomial i (p.coeff i)) 0 +
              monomial N (p.coeff N)) -
            ((List.range N).foldl
                (fun q i => q + monomial (i % n) (p.coeff i)) 0 +
              monomial (N % n) (p.coeff N)) =
          ((List.range N).foldl
                (fun q i => q + monomial i (p.coeff i)) 0 -
              (List.range N).foldl
                (fun q i => q + monomial (i % n) (p.coeff i)) 0) +
            (monomial N (p.coeff N) - monomial (N % n) (p.coeff N)) := by
        apply ext_coeff
        intro k
        rw [coeff_sub_ring, coeff_add _ _ _ (by
              change (0 : R) + 0 = 0
              grind),
            coeff_add _ _ _ (by
              change (0 : R) + 0 = 0
              grind),
            coeff_add _ _ _ (by
              change (0 : R) + 0 = 0
              grind), coeff_sub_ring, coeff_sub_ring]
        grind
      rw [hsplit]
      exact dvd_add_poly ih
        (cyclicModulus_dvd_monomial_sub n N hn (p.coeff N))

theorem cyclicModulus_dvd_sub_fold (n : Nat) (hn : 0 < n) (p : DensePoly R) :
    cyclicModulus (R := R) n ∣
      p - ofCoeffs (cyclicCoeffs n p) := by
  have h := cyclicModulus_dvd_fold_sub n p.size hn p
  rw [foldl_monomials_eq p] at h
  rw [ofCoeffs_cyclicCoeffs n hn p]
  exact h

/-- The cyclic coefficient fold is exactly the canonical monic remainder
modulo `x^n - 1`. -/
theorem ofCoeffs_cyclicCoeffs_eq_modByMonic (n : Nat) (hn : 0 < n)
    (hone : (1 : R) ≠ 0) (p : DensePoly R) :
    (ofCoeffs (cyclicCoeffs n p) : DensePoly R) =
      modByMonic p (cyclicModulus (R := R) n)
        (cyclicModulus_monic n hn hone) := by
  let g := cyclicModulus (R := R) n
  let r : DensePoly R := ofCoeffs (cyclicCoeffs n p)
  have hgsize : g.size = n + 1 := by
    simpa [g] using size_cyclicModulus (R := R) n hn hone
  have hgdeg : g.degree?.getD 0 = n := by
    simp [degree?, hgsize]
  have hgpos : 0 < g.degree?.getD 0 := by omega
  have hrsize : r.size ≤ n := by
    dsimp [r]
    exact Nat.le_trans (size_ofCoeffs_le _)
      (by rw [size_cyclicCoeffs]; exact Nat.le_refl n)
  have hrdeg : r.degree?.getD 0 < g.degree?.getD 0 := by
    rw [hgdeg]
    by_cases hrzero : r.size = 0
    · simp [degree?, hrzero, hn]
    · have hrpos : 0 < r.size := Nat.pos_of_ne_zero hrzero
      rw [degree?_eq_some_of_pos_size r hrpos, Option.getD_some]
      omega
  have hdvd : g ∣ p - r := by
    simpa [g, r] using cyclicModulus_dvd_sub_fold n hn p
  rcases hdvd with ⟨q, hq⟩
  have hrec : q * g + r = p := by
    have hcancel : (p - r) + r = p := by
      apply ext_coeff
      intro k
      rw [coeff_add _ _ _ (by
            change (0 : R) + 0 = 0
            grind), coeff_sub_ring]
      grind
    rw [mul_comm_poly q g, ← hq]
    exact hcancel
  letI : Div R := ⟨fun a _ => a⟩
  have hgmonic : g.Monic := by
    simpa [g] using cyclicModulus_monic (R := R) n hn hone
  have hcancel : ∀ a : R,
      a - (a / g.leadingCoeff) * g.leadingCoeff = (Zero.zero : R) := by
    intro a
    rw [hgmonic]
    change a - a * 1 = (0 : R)
    rw [Lean.Grind.Semiring.mul_one, Lean.Grind.AddCommGroup.sub_self]
  have hexact : ∀ a : R, (a * g.leadingCoeff) / g.leadingCoeff = a := by
    intro a
    rw [hgmonic]
    change a * 1 = a
    exact Lean.Grind.Semiring.mul_one a
  have htop : ∀ a : R, a ≠ (Zero.zero : R) →
      a * g.leadingCoeff ≠ (Zero.zero : R) := by
    intro a ha
    rw [hgmonic, Lean.Grind.Semiring.mul_one]
    exact ha
  have huniq : divMod p g = (q, r) :=
    divMod_eq_of_reconstruction p g q r hgpos hcancel hexact htop hrec hrdeg
  change r = modByMonic p g hgmonic
  by_cases hlt : p.degree?.getD 0 < g.degree?.getD 0
  · have hshort : divMod p g = (0, p) :=
      divMod_eq_zero_self_of_degree_lt p g hlt
    have hpairs : ((0 : DensePoly R), p) = (q, r) := hshort.symm.trans huniq
    have hpr : p = r := congrArg Prod.snd hpairs
    unfold modByMonic divModMonic
    rw [divModArray_eq_zero_self_of_degree_lt p g id hlt]
    exact hpr.symm
  · have hscale : ∀ a : R, a / g.leadingCoeff = a := by intro a; rfl
    have heq := divModMonic_eq_divMod_of_monic_of_scale p g hgmonic hlt hscale
    rw [modByMonic_eq_divModMonic, heq, huniq]

/-- Planned cyclic multiplication is polynomial remainder modulo `x^n - 1`. -/
theorem mulCyclic_eq_modByMonic (plan : MulPlan R) (n : Nat) (hn : 0 < n)
    (hone : (1 : R) ≠ 0) (a b : DensePoly R) :
    mulCyclic plan n hn a b =
      modByMonic (a * b) (cyclicModulus (R := R) n)
        (cyclicModulus_monic n hn hone) := by
  unfold mulCyclic
  rw [ofCoeffs_cyclicCoeffs_eq_modByMonic n hn hone, mulWith_eq]

private theorem monomial_neg (i : Nat) (c : R) :
    monomial i (0 - c) = (0 : DensePoly R) - monomial i c := by
  apply ext_coeff
  intro k
  rw [coeff_monomial, coeff_sub_ring, coeff_zero, coeff_monomial]
  by_cases hki : k = i
  · subst k
    simp
  · simp [hki]
    change (0 : R) = 0 - 0
    grind

private theorem monomial_neg_neg (i : Nat) (c : R) :
    monomial i c = (0 : DensePoly R) - monomial i (0 - c) := by
  apply ext_coeff
  intro k
  rw [coeff_monomial, coeff_sub_ring, coeff_zero, coeff_monomial]
  by_cases hki : k = i
  · subst k
    simp
    grind
  · simp [hki]
    change (0 : R) = 0 - 0
    grind

private theorem negacyclicResidue_step (n i : Nat) (hn : 0 < n)
    (hni : n ≤ i) (c : R) :
    negacyclicResidue (R := R) n i c =
      0 - negacyclicResidue n (i - n) c := by
  let j := i - n
  have hmod : j % n = i % n := by
    dsimp [j]
    exact (Nat.mod_eq_sub_mod hni).symm
  have hdiv : i / n = j / n + 1 := by
    dsimp [j]
    exact Nat.div_eq_sub_div hn hni
  rcases Nat.mod_two_eq_zero_or_one (j / n) with hpar | hpar
  · have hipar : (i / n) % 2 = 1 := by
      rw [hdiv, Nat.add_mod]
      simp [hpar]
    have hpar' : ((i - n) / n) % 2 = 0 := by simpa [j] using hpar
    have hmod' : (i - n) % n = i % n := by simpa [j] using hmod
    unfold negacyclicResidue
    rw [ite_eq_right (by omega), ite_eq_left hpar', hmod']
    exact monomial_neg (i % n) c
  · have hipar : (i / n) % 2 = 0 := by
      rw [hdiv, Nat.add_mod]
      simp [hpar]
    have hpar' : ((i - n) / n) % 2 = 1 := by simpa [j] using hpar
    have hmod' : (i - n) % n = i % n := by simpa [j] using hmod
    unfold negacyclicResidue
    rw [ite_eq_left hipar, ite_eq_right (by omega), hmod']
    exact monomial_neg_neg (i % n) c

/-- A monomial and its signed exponent reduction are congruent modulo
`x^n + 1`. -/
theorem negacyclicModulus_dvd_monomial_sub (n i : Nat) (hn : 0 < n) (c : R) :
    negacyclicModulus (R := R) n ∣
      monomial i c - negacyclicResidue n i c := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
      by_cases hi : i < n
      · have hdiv : i / n = 0 := Nat.div_eq_of_lt hi
        have hmod : i % n = i := Nat.mod_eq_of_lt hi
        unfold negacyclicResidue
        rw [hdiv, hmod]
        simp
        have hself : monomial i c - monomial i c = (0 : DensePoly R) := by
          apply ext_coeff
          intro k
          rw [coeff_sub_ring, coeff_zero]
          grind
        rw [hself]
        exact dvd_zero_poly _
      · have hni : n ≤ i := Nat.le_of_not_gt hi
        let j := i - n
        have hjlt : j < i := by dsimp [j]; omega
        have hstep : negacyclicModulus (R := R) n ∣
            monomial i c + monomial j c := by
          refine ⟨monomial j c, ?_⟩
          rw [negacyclicModulus, mul_add_left_poly, monomial_mul_monomial]
          have hsum : n + j = i := by dsimp [j]; omega
          rw [hsum, Lean.Grind.Semiring.one_mul]
          have hone_mul : (1 : DensePoly R) * monomial j c = monomial j c := by
            rw [mul_comm_poly, mul_one_right_poly]
          rw [hone_mul]
        have htail : negacyclicModulus (R := R) n ∣
            monomial j c - negacyclicResidue n j c := ih j hjlt
        have hres := negacyclicResidue_step (R := R) n i hn hni c
        have hsplit :
            monomial i c - negacyclicResidue n i c =
              (monomial i c + monomial j c) -
                (monomial j c - negacyclicResidue n j c) := by
          rw [hres]
          apply ext_coeff
          intro k
          rw [coeff_sub_ring (monomial i c) (0 - negacyclicResidue n (i - n) c) k,
            coeff_sub_ring 0 (negacyclicResidue n (i - n) c) k,
            coeff_zero,
            coeff_sub_ring (monomial i c + monomial j c)
              (monomial j c - negacyclicResidue n j c) k,
            coeff_add _ _ _ (by
              change (0 : R) + 0 = 0
              grind), coeff_sub_ring]
          grind
        rw [hsplit]
        exact dvd_sub_poly hstep htail

private theorem negacyclicModulus_dvd_fold_sub (n N : Nat) (hn : 0 < n)
    (p : DensePoly R) :
    negacyclicModulus (R := R) n ∣
      (List.range N).foldl
          (fun q i => q + monomial i (p.coeff i)) 0 -
        (List.range N).foldl
          (fun q i => q + negacyclicTerm n p i) 0 := by
  induction N with
  | zero =>
      have hzero : (0 : DensePoly R) - 0 = 0 := by
        apply ext_coeff
        intro k
        rw [coeff_sub_ring, coeff_zero]
        grind
      simp only [List.range_zero, List.foldl_nil]
      rw [hzero]
      exact dvd_zero_poly _
  | succ N ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hsplit :
          ((List.range N).foldl
                (fun q i => q + monomial i (p.coeff i)) 0 +
              monomial N (p.coeff N)) -
            ((List.range N).foldl
                (fun q i => q + negacyclicTerm n p i) 0 +
              negacyclicTerm n p N) =
          ((List.range N).foldl
                (fun q i => q + monomial i (p.coeff i)) 0 -
              (List.range N).foldl
                (fun q i => q + negacyclicTerm n p i) 0) +
            (monomial N (p.coeff N) - negacyclicTerm n p N) := by
        apply ext_coeff
        intro k
        rw [coeff_sub_ring, coeff_add _ _ _ (by
              change (0 : R) + 0 = 0
              grind),
            coeff_add _ _ _ (by
              change (0 : R) + 0 = 0
              grind),
            coeff_add _ _ _ (by
              change (0 : R) + 0 = 0
              grind), coeff_sub_ring, coeff_sub_ring]
        grind
      rw [hsplit]
      apply dvd_add_poly ih
      simpa [negacyclicTerm, negacyclicResidue] using
        negacyclicModulus_dvd_monomial_sub (R := R) n N hn (p.coeff N)

theorem negacyclicModulus_dvd_sub_fold (n : Nat) (hn : 0 < n)
    (p : DensePoly R) :
    negacyclicModulus (R := R) n ∣
      p - ofCoeffs (negacyclicCoeffs n p) := by
  have h := negacyclicModulus_dvd_fold_sub n p.size hn p
  rw [foldl_monomials_eq p] at h
  rw [ofCoeffs_negacyclicCoeffs n hn p]
  exact h

/-- The negacyclic coefficient fold is exactly the canonical monic remainder
modulo `x^n + 1`. -/
theorem ofCoeffs_negacyclicCoeffs_eq_modByMonic (n : Nat) (hn : 0 < n)
    (hone : (1 : R) ≠ 0) (p : DensePoly R) :
    (ofCoeffs (negacyclicCoeffs n p) : DensePoly R) =
      modByMonic p (negacyclicModulus (R := R) n)
        (negacyclicModulus_monic n hn hone) := by
  let g := negacyclicModulus (R := R) n
  let r : DensePoly R := ofCoeffs (negacyclicCoeffs n p)
  have hgsize : g.size = n + 1 := by
    simpa [g] using size_negacyclicModulus (R := R) n hn hone
  have hgdeg : g.degree?.getD 0 = n := by
    simp [degree?, hgsize]
  have hgpos : 0 < g.degree?.getD 0 := by omega
  have hrsize : r.size ≤ n := by
    dsimp [r]
    exact Nat.le_trans (size_ofCoeffs_le _)
      (by rw [size_negacyclicCoeffs]; exact Nat.le_refl n)
  have hrdeg : r.degree?.getD 0 < g.degree?.getD 0 := by
    rw [hgdeg]
    by_cases hrzero : r.size = 0
    · simp [degree?, hrzero, hn]
    · have hrpos : 0 < r.size := Nat.pos_of_ne_zero hrzero
      rw [degree?_eq_some_of_pos_size r hrpos, Option.getD_some]
      omega
  have hdvd : g ∣ p - r := by
    simpa [g, r] using negacyclicModulus_dvd_sub_fold n hn p
  rcases hdvd with ⟨q, hq⟩
  have hrec : q * g + r = p := by
    have hcancel : (p - r) + r = p := by
      apply ext_coeff
      intro k
      rw [coeff_add _ _ _ (by
            change (0 : R) + 0 = 0
            grind), coeff_sub_ring]
      grind
    rw [mul_comm_poly q g, ← hq]
    exact hcancel
  letI : Div R := ⟨fun a _ => a⟩
  have hgmonic : g.Monic := by
    simpa [g] using negacyclicModulus_monic (R := R) n hn hone
  have hcancel : ∀ a : R,
      a - (a / g.leadingCoeff) * g.leadingCoeff = (Zero.zero : R) := by
    intro a
    rw [hgmonic]
    change a - a * 1 = (0 : R)
    rw [Lean.Grind.Semiring.mul_one, Lean.Grind.AddCommGroup.sub_self]
  have hexact : ∀ a : R, (a * g.leadingCoeff) / g.leadingCoeff = a := by
    intro a
    rw [hgmonic]
    change a * 1 = a
    exact Lean.Grind.Semiring.mul_one a
  have htop : ∀ a : R, a ≠ (Zero.zero : R) →
      a * g.leadingCoeff ≠ (Zero.zero : R) := by
    intro a ha
    rw [hgmonic, Lean.Grind.Semiring.mul_one]
    exact ha
  have huniq : divMod p g = (q, r) :=
    divMod_eq_of_reconstruction p g q r hgpos hcancel hexact htop hrec hrdeg
  change r = modByMonic p g hgmonic
  by_cases hlt : p.degree?.getD 0 < g.degree?.getD 0
  · have hshort : divMod p g = (0, p) :=
      divMod_eq_zero_self_of_degree_lt p g hlt
    have hpairs : ((0 : DensePoly R), p) = (q, r) := hshort.symm.trans huniq
    have hpr : p = r := congrArg Prod.snd hpairs
    unfold modByMonic divModMonic
    rw [divModArray_eq_zero_self_of_degree_lt p g id hlt]
    exact hpr.symm
  · have hscale : ∀ a : R, a / g.leadingCoeff = a := by intro a; rfl
    have heq := divModMonic_eq_divMod_of_monic_of_scale p g hgmonic hlt hscale
    rw [modByMonic_eq_divModMonic, heq, huniq]

/-- Planned negacyclic multiplication is polynomial remainder modulo
`x^n + 1`. -/
theorem mulNegacyclic_eq_modByMonic (plan : MulPlan R) (n : Nat) (hn : 0 < n)
    (hone : (1 : R) ≠ 0) (a b : DensePoly R) :
    mulNegacyclic plan n hn a b =
      modByMonic (a * b) (negacyclicModulus (R := R) n)
        (negacyclicModulus_monic n hn hone) := by
  unfold mulNegacyclic
  rw [ofCoeffs_negacyclicCoeffs_eq_modByMonic n hn hone, mulWith_eq]

end Hex.DensePoly
