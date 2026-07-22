/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus
public import HexBerlekampZassenhausMathlib.Lattice
public import HexBerlekampZassenhausMathlib.WordCld
public import HexHenselMathlib.Correctness
public import HexPolyZMathlib.Mignotte
public import HexPolyZMathlib.RobinsonForm
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.BigOperators.Ring.Multiset
public import Mathlib.Data.Nat.Choose.Bounds

public section
set_option backward.proofsInPublic true

/-!
BHKS CLD-column coefficient bounds (van Hoeij `W ⊆ L'` analytics, #8519).

Resurrected from the pre-#8411 `CLDColumnBound.lean` (6bf20977^): the exact
integer CLD column `phi g = f * g' / g` with its Landau-Mignotte coefficient
bound, the aggregate-residue congruence for a recovered true-factor support,
the period-aware carry bound `two_mul_natAbs_sum_psiCut_period_le`, and the
short-vector producer `supportShortVectorData_of_recoveredLift` feeding
`cutProjectionHypotheses_of_shortVectors`.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

namespace BHKS


/-- The exact integer-polynomial CLD column `Phi(g) = f * g' / g`. -/
def phi (f g : Polynomial ℤ) : Polynomial ℤ :=
  (f * g.derivative).divByMonic g

/--
If `f = g * h` and `g` is monic, the quotient definition of `Phi(g)` is the
integer polynomial `h * g'`.
-/
theorem phi_eq_factor_mul_derivative
    (f g h : Polynomial ℤ) (hg_monic : g.Monic) (hfac : f = g * h) :
    phi f g = h * g.derivative := by
  rw [phi, hfac]
  calc
    ((g * h) * g.derivative).divByMonic g =
        (g * (h * g.derivative)).divByMonic g := by
      ring_nf
    _ = h * g.derivative :=
      Polynomial.mul_divByMonic_cancel_left (h * g.derivative) hg_monic

/--
Coefficient bound for the BHKS `Phi` column from the valid replacement
analytic estimate `M(Phi) <= n * ||f||_2`.

The hypotheses `hphi_degree` and `hphi_mahler` are the precise downstream
analytic obligations: the theorem does not use, imply, or reintroduce the false
unconditional derivative Mahler bound.
-/
theorem abs_phi_coeff_le
    (f g h : Polynomial ℤ) (_hg_monic : g.Monic) (_hfac : f = g * h)
    (j : Nat)
    (hphi_degree : (phi f g).natDegree ≤ f.natDegree - 1)
    (hphi_mahler :
      ((phi f g).map (Int.castRingHom ℂ)).mahlerMeasure ≤
        (f.natDegree : ℝ) * HexPolyZMathlib.l2norm f) :
    (Int.natAbs ((phi f g).coeff j) : ℝ) ≤
      (Nat.choose (f.natDegree - 1) j : ℝ) *
        (f.natDegree : ℝ) * HexPolyZMathlib.l2norm f := by
  have hcoeff :=
    Polynomial.norm_coeff_le_choose_mul_mahlerMeasure
      (n := j) (p := (phi f g).map (Int.castRingHom ℂ))
  have hchoose :
      (Nat.choose ((phi f g).map (Int.castRingHom ℂ)).natDegree j : ℝ) ≤
        (Nat.choose (f.natDegree - 1) j : ℝ) := by
    rw [HexPolyZMathlib.natDegree_map_intCast]
    exact_mod_cast Nat.choose_le_choose j hphi_degree
  calc
    (Int.natAbs ((phi f g).coeff j) : ℝ) =
        ‖((phi f g).map (Int.castRingHom ℂ)).coeff j‖ := by
      exact (HexPolyZMathlib.norm_coeff_map_intCast (f := phi f g) (n := j)).symm
    _ ≤ Nat.choose ((phi f g).map (Int.castRingHom ℂ)).natDegree j *
        ((phi f g).map (Int.castRingHom ℂ)).mahlerMeasure := hcoeff
    _ ≤ (Nat.choose (f.natDegree - 1) j : ℝ) *
        ((f.natDegree : ℝ) * HexPolyZMathlib.l2norm f) := by
      exact mul_le_mul hchoose hphi_mahler
        (Polynomial.mahlerMeasure_nonneg _)
        (Nat.cast_nonneg _)
    _ =
        (Nat.choose (f.natDegree - 1) j : ℝ) *
          (f.natDegree : ℝ) * HexPolyZMathlib.l2norm f := by
      ring

/--
Partial-fractions decomposition of `Phi.map ℂ`: under the monic factorisation
`f = g * h`, `Phi.map ℂ` equals the multiset sum over the complex roots of
`g.map ℂ` of `h.map ℂ` times the corresponding root-deletion derivative summand.

This is the analytic frame used to discharge the Mahler hypothesis without
invoking the false unconditional derivative Mahler inequality.
-/
private theorem phi_map_eq_sum_h_mul_rootDeletionDerivativeSummand
    (f g h : Polynomial ℤ) (hg_monic : g.Monic) (hfac : f = g * h) :
    (phi f g).map (Int.castRingHom ℂ) =
      ((g.map (Int.castRingHom ℂ)).roots.map fun α =>
        (h.map (Int.castRingHom ℂ)) *
          Polynomial.rootDeletionDerivativeSummand
            (g.map (Int.castRingHom ℂ)) α).sum := by
  rw [phi_eq_factor_mul_derivative f g h hg_monic hfac]
  rw [Polynomial.map_mul, ← Polynomial.derivative_map]
  rw [Polynomial.derivative_eq_sum_rootDeletionDerivativeSummand]
  exact (Multiset.sum_map_mul_left
    (s := (g.map (Int.castRingHom ℂ)).roots)
    (a := h.map (Int.castRingHom ℂ))
    (f := fun α => Polynomial.rootDeletionDerivativeSummand
      (g.map (Int.castRingHom ℂ)) α)).symm

/--
Mahler-measure bound for one `h * rootDeletionDerivativeSummand g α` summand,
when `f = g * h` and `g` is monic: each summand has Mahler measure
at most `M(f.map ℂ)`.
-/
private theorem mahlerMeasure_h_mul_rootDeletionDerivativeSummand_le
    (f g h : Polynomial ℤ) (hfac : f = g * h) (α : ℂ) :
    ((h.map (Int.castRingHom ℂ)) *
        Polynomial.rootDeletionDerivativeSummand
          (g.map (Int.castRingHom ℂ)) α).mahlerMeasure ≤
      (f.map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [Polynomial.mahlerMeasure_mul]
  have hsummand := Polynomial.mahlerMeasure_rootDeletionDerivativeSummand_le
    (g.map (Int.castRingHom ℂ)) α
  have hh_nonneg : 0 ≤ (h.map (Int.castRingHom ℂ)).mahlerMeasure :=
    Polynomial.mahlerMeasure_nonneg _
  have hcalc :
      (h.map (Int.castRingHom ℂ)).mahlerMeasure *
          (Polynomial.rootDeletionDerivativeSummand
            (g.map (Int.castRingHom ℂ)) α).mahlerMeasure ≤
        (h.map (Int.castRingHom ℂ)).mahlerMeasure *
          (g.map (Int.castRingHom ℂ)).mahlerMeasure :=
    mul_le_mul_of_nonneg_left hsummand hh_nonneg
  apply hcalc.trans_eq
  rw [mul_comm]
  rw [← Polynomial.mahlerMeasure_mul]
  congr 1
  rw [hfac, Polynomial.map_mul]

/--
Degree bound for one `h * rootDeletionDerivativeSummand g α` summand at a
root `α` of `g.map ℂ`. Under the monic factorisation `f = g * h`, each such
summand has degree at most `f.natDegree - 1`.
-/
private theorem natDegree_h_mul_rootDeletionDerivativeSummand_le
    (f g h : Polynomial ℤ) (hg_monic : g.Monic) (hfac : f = g * h) (α : ℂ)
    (hα : α ∈ (g.map (Int.castRingHom ℂ)).roots) :
    ((h.map (Int.castRingHom ℂ)) *
        Polynomial.rootDeletionDerivativeSummand
          (g.map (Int.castRingHom ℂ)) α).natDegree ≤
      f.natDegree - 1 := by
  classical
  -- α ∈ roots forces roots ≠ 0, hence (g.map ℂ).natDegree ≥ 1 and g ≠ 1.
  have hroots_nonempty : (0 : ℕ) < Multiset.card (g.map (Int.castRingHom ℂ)).roots := by
    rcases Multiset.exists_mem_of_ne_zero (s := (g.map (Int.castRingHom ℂ)).roots)
      (by intro hz; rw [hz] at hα; exact (Multiset.notMem_zero _) hα) with ⟨_, _⟩
    exact Multiset.card_pos.mpr
      (by intro hz; rw [hz] at hα; exact (Multiset.notMem_zero _) hα)
  have hcardroots :
      Multiset.card (g.map (Int.castRingHom ℂ)).roots ≤
        (g.map (Int.castRingHom ℂ)).natDegree :=
    Polynomial.card_roots' _
  have hgnat : (g.map (Int.castRingHom ℂ)).natDegree = g.natDegree :=
    HexPolyZMathlib.natDegree_map_intCast g
  have hgd_pos : 0 < g.natDegree := by
    rw [hgnat] at hcardroots
    omega
  by_cases hh : h = 0
  · simp [hh]
  have hgh : (g * h).natDegree = g.natDegree + h.natDegree := hg_monic.natDegree_mul' hh
  have hf_deg : f.natDegree = g.natDegree + h.natDegree := by rw [hfac, hgh]
  have hh_map_deg : (h.map (Int.castRingHom ℂ)).natDegree ≤ h.natDegree :=
    Polynomial.natDegree_map_le
  -- Bound the summand degree.
  -- rootDeletionDerivativeSummand p α = C lc(p) * prod over (roots.erase α) of (X - C β),
  -- which has natDegree ≤ card (roots.erase α).
  have hcarderase :
      Multiset.card ((g.map (Int.castRingHom ℂ)).roots.erase α) =
        Multiset.card (g.map (Int.castRingHom ℂ)).roots - 1 :=
    Multiset.card_erase_of_mem hα
  have hsummand_deg :
      (Polynomial.rootDeletionDerivativeSummand
        (g.map (Int.castRingHom ℂ)) α).natDegree ≤ g.natDegree - 1 := by
    rw [Polynomial.rootDeletionDerivativeSummand]
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
    rw [hgnat] at hcardroots
    omega
  have hmul_deg :
      ((h.map (Int.castRingHom ℂ)) *
        Polynomial.rootDeletionDerivativeSummand
          (g.map (Int.castRingHom ℂ)) α).natDegree ≤
      (h.map (Int.castRingHom ℂ)).natDegree +
        (Polynomial.rootDeletionDerivativeSummand
          (g.map (Int.castRingHom ℂ)) α).natDegree :=
    Polynomial.natDegree_mul_le
  omega

/--
Degree bound for the BHKS `Phi` column under a monic factorisation
`f = g * h`: `Phi.natDegree ≤ f.natDegree - 1`.
-/
private theorem phi_natDegree_le_of_monic_factor
    (f g h : Polynomial ℤ) (hg_monic : g.Monic) (hfac : f = g * h) :
    (phi f g).natDegree ≤ f.natDegree - 1 := by
  rw [phi_eq_factor_mul_derivative f g h hg_monic hfac]
  by_cases hg_one : g = 1
  · simp [hg_one]
  by_cases hh : h = 0
  · simp [hh]
  have hgd_pos : 0 < g.natDegree := by
    rcases Nat.eq_zero_or_pos g.natDegree with hzero | hpos
    · exact absurd (hg_monic.natDegree_eq_zero.mp hzero) hg_one
    · exact hpos
  have hgh : (g * h).natDegree = g.natDegree + h.natDegree := hg_monic.natDegree_mul' hh
  have hf_deg : f.natDegree = g.natDegree + h.natDegree := by rw [hfac, hgh]
  have h1 : (h * g.derivative).natDegree ≤ h.natDegree + g.derivative.natDegree :=
    Polynomial.natDegree_mul_le
  have h2 : g.derivative.natDegree ≤ g.natDegree - 1 := Polynomial.natDegree_derivative_le _
  omega

/--
**BHKS Lemma 5.1** (unconditional form): the coefficient bound for the BHKS
`Phi` column under a monic factorisation `f = g * h`. This discharges the
analytic hypotheses of `BHKS.abs_phi_coeff_le`.

The proof avoids the false unconditional derivative Mahler estimate by
decomposing `Phi.map ℂ` via the product-rule sum
`Polynomial.derivative_eq_sum_rootDeletionDerivativeSummand` (one summand per
complex root of `g.map ℂ`). Each summand has Mahler measure at most
`M(f.map ℂ)` by Mahler multiplicativity (using `g.Monic`), and there are at
most `g.natDegree ≤ f.natDegree` summands.
-/
theorem abs_phi_coeff_le_of_monic_factor
    (f g h : Polynomial ℤ) (hg_monic : g.Monic) (hfac : f = g * h)
    (j : Nat) :
    (Int.natAbs ((phi f g).coeff j) : ℝ) ≤
      (Nat.choose (f.natDegree - 1) j : ℝ) *
        (f.natDegree : ℝ) * HexPolyZMathlib.l2norm f := by
  classical
  -- Handle the degenerate `h = 0` case (equivalently `f = 0`).
  by_cases hh : h = 0
  · have hf0 : f = 0 := by rw [hfac, hh, mul_zero]
    have hphi0 : phi f g = 0 := by
      unfold phi
      rw [hf0]
      simp
    rw [hphi0]
    simp
    -- Goal: 0 ≤ choose * natDegree * l2norm
    have : (0 : ℝ) ≤ HexPolyZMathlib.l2norm f := Real.sqrt_nonneg _
    positivity
  -- From here on `h ≠ 0`.
  -- Step 0: lift to ℂ.
  rw [(HexPolyZMathlib.norm_coeff_map_intCast (f := phi f g) (n := j)).symm]
  -- Step 1: substitute the partial-fractions decomposition.
  rw [phi_map_eq_sum_h_mul_rootDeletionDerivativeSummand f g h hg_monic hfac]
  -- Step 2: push `coeff j` through the multiset sum via the linear map `lcoeff`.
  rw [show (((g.map (Int.castRingHom ℂ)).roots.map fun α =>
            (h.map (Int.castRingHom ℂ)) *
              Polynomial.rootDeletionDerivativeSummand
                (g.map (Int.castRingHom ℂ)) α).sum).coeff j =
          (((g.map (Int.castRingHom ℂ)).roots.map fun α =>
            ((h.map (Int.castRingHom ℂ)) *
              Polynomial.rootDeletionDerivativeSummand
                (g.map (Int.castRingHom ℂ)) α).coeff j)).sum from ?_]
  pick_goal 2
  · rw [← Polynomial.lcoeff_apply (R := ℂ) j,
      map_multiset_sum (Polynomial.lcoeff ℂ j)]
    simp [Multiset.map_map, Polynomial.lcoeff_apply]
  -- Step 3: norm of multiset sum ≤ multiset sum of norms.
  refine (norm_multiset_sum_le _).trans ?_
  -- Now the goal is over `(roots.map (fun α => ‖...‖))` after `map_map` simplification.
  rw [Multiset.map_map]
  -- Step 4: bound each per-summand coefficient norm.
  set B : ℝ := (Nat.choose (f.natDegree - 1) j : ℝ) * HexPolyZMathlib.l2norm f with hB_def
  have hB_nonneg : 0 ≤ B := by
    refine mul_nonneg ?_ (Real.sqrt_nonneg _)
    exact Nat.cast_nonneg _
  have hsummand_bound : ∀ α ∈ (g.map (Int.castRingHom ℂ)).roots,
      ((fun x : ℂ[X] => ‖x.coeff j‖) ∘ fun α =>
          (h.map (Int.castRingHom ℂ)) *
            Polynomial.rootDeletionDerivativeSummand
              (g.map (Int.castRingHom ℂ)) α) α ≤ B := by
    intro α hα
    simp only [Function.comp_apply]
    have hcoeff_le := Polynomial.norm_coeff_le_choose_mul_mahlerMeasure
      (n := j)
      (p := (h.map (Int.castRingHom ℂ)) *
        Polynomial.rootDeletionDerivativeSummand
          (g.map (Int.castRingHom ℂ)) α)
    have hM_le := mahlerMeasure_h_mul_rootDeletionDerivativeSummand_le
      f g h hfac α
    have hdeg_le := natDegree_h_mul_rootDeletionDerivativeSummand_le
      f g h hg_monic hfac α hα
    have hM_nonneg :
        0 ≤ ((h.map (Int.castRingHom ℂ)) *
              Polynomial.rootDeletionDerivativeSummand
                (g.map (Int.castRingHom ℂ)) α).mahlerMeasure :=
      Polynomial.mahlerMeasure_nonneg _
    have hchoose_le :
        (Nat.choose
            ((h.map (Int.castRingHom ℂ)) *
              Polynomial.rootDeletionDerivativeSummand
                (g.map (Int.castRingHom ℂ)) α).natDegree j : ℝ) ≤
          (Nat.choose (f.natDegree - 1) j : ℝ) := by
      exact_mod_cast Nat.choose_le_choose j hdeg_le
    have hchoose_nonneg : (0 : ℝ) ≤ Nat.choose (f.natDegree - 1) j :=
      Nat.cast_nonneg _
    have hmf_le_l2 :
        (f.map (Int.castRingHom ℂ)).mahlerMeasure ≤ HexPolyZMathlib.l2norm f :=
      HexPolyZMathlib.mahlerMeasure_le_l2norm f
    calc ‖((h.map (Int.castRingHom ℂ)) *
              Polynomial.rootDeletionDerivativeSummand
                (g.map (Int.castRingHom ℂ)) α).coeff j‖
        ≤ (Nat.choose
            ((h.map (Int.castRingHom ℂ)) *
              Polynomial.rootDeletionDerivativeSummand
                (g.map (Int.castRingHom ℂ)) α).natDegree j : ℝ) *
            ((h.map (Int.castRingHom ℂ)) *
              Polynomial.rootDeletionDerivativeSummand
                (g.map (Int.castRingHom ℂ)) α).mahlerMeasure := hcoeff_le
      _ ≤ (Nat.choose (f.natDegree - 1) j : ℝ) *
            (f.map (Int.castRingHom ℂ)).mahlerMeasure := by
          exact mul_le_mul hchoose_le hM_le hM_nonneg hchoose_nonneg
      _ ≤ B := by
          rw [hB_def]; gcongr
  -- Step 5: multiset sum ≤ card • B.
  have hsum_le_card_nsmul := Multiset.sum_le_card_nsmul
    ((g.map (Int.castRingHom ℂ)).roots.map
      ((fun x : ℂ[X] => ‖x.coeff j‖) ∘ fun α =>
        (h.map (Int.castRingHom ℂ)) *
          Polynomial.rootDeletionDerivativeSummand
            (g.map (Int.castRingHom ℂ)) α))
    B (by
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨α, hα, rfl⟩ := hx
      exact hsummand_bound α hα)
  refine hsum_le_card_nsmul.trans ?_
  -- Step 6: card • B ≤ f.natDegree * (choose * l2norm).
  rw [Multiset.card_map]
  -- nsmul rewrite: (n : ℕ) • (r : ℝ) = (n : ℝ) * r
  rw [nsmul_eq_mul]
  -- Goal: (card roots : ℝ) * B ≤ choose * f.natDegree * l2norm
  have hcardroots : Multiset.card (g.map (Int.castRingHom ℂ)).roots ≤ g.natDegree := by
    have h1 : Multiset.card (g.map (Int.castRingHom ℂ)).roots ≤
        (g.map (Int.castRingHom ℂ)).natDegree :=
      Polynomial.card_roots' _
    have h2 : (g.map (Int.castRingHom ℂ)).natDegree = g.natDegree :=
      HexPolyZMathlib.natDegree_map_intCast g
    rw [h2] at h1
    exact h1
  have hgh : (g * h).natDegree = g.natDegree + h.natDegree :=
    hg_monic.natDegree_mul' hh
  have hf_deg : f.natDegree = g.natDegree + h.natDegree := by rw [hfac, hgh]
  have hcardroots_f : Multiset.card (g.map (Int.castRingHom ℂ)).roots ≤ f.natDegree := by
    omega
  have hcardroots_real :
      ((Multiset.card (g.map (Int.castRingHom ℂ)).roots : ℕ) : ℝ) ≤ (f.natDegree : ℝ) :=
    Nat.cast_le.mpr hcardroots_f
  calc ((Multiset.card (g.map (Int.castRingHom ℂ)).roots : ℕ) : ℝ) * B
      ≤ (f.natDegree : ℝ) * B :=
        mul_le_mul_of_nonneg_right hcardroots_real hB_nonneg
    _ = (Nat.choose (f.natDegree - 1) j : ℝ) *
          (f.natDegree : ℝ) * HexPolyZMathlib.l2norm f := by
        rw [hB_def]; ring

end BHKS

/-- CLD quotient congruence (BHKS logarithmic-derivative bridge).

When a monic positive-degree lifted factor `g` divides `input` modulo `p ^ k`
(witnessed by `input ≡ g * h`), multiplying the executable CLD quotient
`cldQuotientMod input g p k` back by `g` recovers the logarithmic-derivative
numerator `input * g'` modulo `p ^ k`:

`g * cldQuotientMod input g p k ≡ input * g'  (mod p ^ k)`.

This is the semantic link from the executable quotient to the exact integer CLD
column `BHKS.phi g = input * g' / g`: composed with
`BHKS.phi_eq_factor_mul_derivative`, it identifies `g * cldQuotientMod input g p k`
with `g * BHKS.phi g` modulo `p ^ k`. The divisibility hypothesis is on `input`
itself, not on the BHKS auxiliary polynomial, which need not be divisible by `g`
modulo `p ^ k`.

The proof transports the executable monic division to `Polynomial (ZMod (p ^ k))`,
where the reconstruction identity and the remainder degree bound pin the mapped
remainder down by uniqueness of division by a monic polynomial; divisibility of
the mapped numerator by `g` then forces that remainder to vanish. -/
theorem cldQuotientMod_congr_mul_derivative
    (input g h : Hex.ZPoly) (p k : Nat)
    (hk : 1 < p ^ k)
    (hg_monic : Hex.DensePoly.Monic g)
    (hg_deg : 0 < g.degree?.getD 0)
    (hdvd : Hex.ZPoly.congr input (g * h) (p ^ k)) :
    Hex.ZPoly.congr
      (g * Hex.cldQuotientMod input g p k)
      (input * Hex.DensePoly.derivative g) (p ^ k) := by
  have hpk_pos : 0 < p ^ k := by omega
  haveI : Fact (1 < p ^ k) := ⟨hk⟩
  -- Executable quotient / remainder of the monic division underlying `cldQuotientMod`.
  set num : Hex.ZPoly :=
    Hex.ZPoly.reduceModPow (input * Hex.DensePoly.derivative g) p k with hnum
  set q : Hex.ZPoly := (Hex.DensePoly.divMod num g).1 with hq
  set r : Hex.ZPoly := (Hex.DensePoly.divMod num g).2 with hr
  have hcld : Hex.cldQuotientMod input g p k = Hex.ZPoly.reduceModPow q p k :=
    (HexBerlekampZassenhausMathlib.cldQuotientMod_eq_spec input g p k).trans rfl
  have hrecon : q * g + r = num :=
    Hex.ZPoly.divMod_reconstruction_of_monic num g hg_monic
  have hcancel :
      ∀ a : Int, a - (a / g.leadingCoeff) * g.leadingCoeff = 0 := by
    intro a; rw [hg_monic]; omega
  have hrdeg : r.degree?.getD 0 < g.degree?.getD 0 :=
    Hex.DensePoly.divMod_remainder_degree_lt_of_pos_degree_core num g hg_deg hcancel
  -- Move the goal to Mathlib polynomials reduced modulo `p ^ k`.
  refine HexHenselMathlib.zpoly_congr_of_toPolynomial_map_eq _ _ (p ^ k) ?_
  intro φ
  -- Ring-hom transport for the composite `(toPolynomial ·).map φ`.
  have hmul : ∀ a b : Hex.ZPoly,
      (HexPolyMathlib.toPolynomial (a * b)).map φ =
        (HexPolyMathlib.toPolynomial a).map φ * (HexPolyMathlib.toPolynomial b).map φ := by
    intro a b; rw [HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul]
  have hred : ∀ x : Hex.ZPoly,
      (HexPolyMathlib.toPolynomial (Hex.ZPoly.reduceModPow x p k)).map φ =
        (HexPolyMathlib.toPolynomial x).map φ := fun x =>
    HexHenselMathlib.zpoly_congr_toPolynomial_map_eq _ x (p ^ k)
      (Hex.ZPoly.congr_reduceModPow x p k hpk_pos)
  -- The monic divisor maps to a monic Mathlib polynomial.
  have hMg_monic : ((HexPolyMathlib.toPolynomial g).map φ).Monic :=
    (HexHenselMathlib.toPolynomial_monic_of_dense_monic g hg_monic).map φ
  -- The mapped numerator equals the target `input * g'`, and `g` divides it.
  have hnum_eq :
      (HexPolyMathlib.toPolynomial num).map φ =
        (HexPolyMathlib.toPolynomial (input * Hex.DensePoly.derivative g)).map φ := by
    rw [hnum]; exact hred _
  have hMinput : (HexPolyMathlib.toPolynomial input).map φ =
      (HexPolyMathlib.toPolynomial g).map φ * (HexPolyMathlib.toPolynomial h).map φ := by
    have h1 : (HexPolyMathlib.toPolynomial input).map φ =
        (HexPolyMathlib.toPolynomial (g * h)).map φ :=
      HexHenselMathlib.zpoly_congr_toPolynomial_map_eq input (g * h) (p ^ k) hdvd
    rw [h1, hmul]
  have hdvd_num :
      (HexPolyMathlib.toPolynomial g).map φ ∣ (HexPolyMathlib.toPolynomial num).map φ := by
    rw [hnum_eq, hmul, hMinput]
    exact ⟨(HexPolyMathlib.toPolynomial h).map φ *
      (HexPolyMathlib.toPolynomial (Hex.DensePoly.derivative g)).map φ, by ring⟩
  -- The mapped reconstruction identity.
  have hrecon_map :
      (HexPolyMathlib.toPolynomial q).map φ * (HexPolyMathlib.toPolynomial g).map φ +
          (HexPolyMathlib.toPolynomial r).map φ =
        (HexPolyMathlib.toPolynomial num).map φ := by
    have hcg := congrArg (fun s : Hex.ZPoly => (HexPolyMathlib.toPolynomial s).map φ) hrecon
    simpa [HexPolyMathlib.toPolynomial_add, HexPolyMathlib.toPolynomial_mul,
      Polynomial.map_add, Polynomial.map_mul] using hcg
  -- The mapped remainder has degree below the mapped divisor.
  have hdeg_Mg : ((HexPolyMathlib.toPolynomial g).map φ).degree =
      (g.degree?.getD 0 : WithBot ℕ) := by
    rw [(HexHenselMathlib.toPolynomial_monic_of_dense_monic g hg_monic).degree_map φ,
      Polynomial.degree_eq_natDegree
        (HexHenselMathlib.toPolynomial_monic_of_dense_monic g hg_monic).ne_zero,
      HexPolyMathlib.natDegree_toPolynomial]
  have hdeg_Mr :
      ((HexPolyMathlib.toPolynomial r).map φ).degree <
        ((HexPolyMathlib.toPolynomial g).map φ).degree := by
    rw [hdeg_Mg]
    calc ((HexPolyMathlib.toPolynomial r).map φ).degree
        ≤ (HexPolyMathlib.toPolynomial r).degree := Polynomial.degree_map_le
      _ ≤ (r.degree?.getD 0 : WithBot ℕ) := by
          rw [← HexPolyMathlib.natDegree_toPolynomial r]
          exact Polynomial.degree_le_natDegree
      _ < (g.degree?.getD 0 : WithBot ℕ) := by exact_mod_cast hrdeg
  -- Uniqueness of monic division forces the mapped remainder to vanish.
  have hsum : (HexPolyMathlib.toPolynomial r).map φ +
      (HexPolyMathlib.toPolynomial g).map φ * (HexPolyMathlib.toPolynomial q).map φ =
        (HexPolyMathlib.toPolynomial num).map φ := by
    rw [← hrecon_map]; ring
  have huniq := (Polynomial.div_modByMonic_unique
    ((HexPolyMathlib.toPolynomial q).map φ) ((HexPolyMathlib.toPolynomial r).map φ)
    hMg_monic ⟨hsum, hdeg_Mr⟩).2
  have hrem_zero : (HexPolyMathlib.toPolynomial r).map φ = 0 := by
    rw [← huniq, Polynomial.modByMonic_eq_zero_iff_dvd hMg_monic]; exact hdvd_num
  -- Assemble: mapped `g * cldQuotientMod = g * q = num = input * g'`.
  rw [hmul, hcld, hred q]
  have hfin : (HexPolyMathlib.toPolynomial g).map φ * (HexPolyMathlib.toPolynomial q).map φ =
      (HexPolyMathlib.toPolynomial num).map φ := by
    rw [← hrecon_map, hrem_zero]; ring
  rw [hfin]; exact hnum_eq

namespace BHKS

/--
Product logarithmic-derivative congruence over a list of factors.

If every factor `g` in `gs` satisfies the per-factor CLD congruence
`g * q g ≡ f * g'  (mod m)`, then the product of `gs` times the sum of the
`q`-images is congruent modulo `m` to `f` times the derivative of the product.
This is the executable list form of the logarithmic-derivative identity
`(∏ gᵢ) · Σ (f · gᵢ' / gᵢ) ≡ f · (∏ gᵢ)'`, proved by structural induction on the
list using the Leibniz product rule, with no leave-one-out indexing.
-/
theorem congr_polyProduct_mul_listSum_derivative
    (f : Hex.ZPoly) (q : Hex.ZPoly → Hex.ZPoly) (m : Nat) :
    ∀ gs : List Hex.ZPoly,
      (∀ g ∈ gs, Hex.ZPoly.congr (g * q g) (f * Hex.DensePoly.derivative g) m) →
      Hex.ZPoly.congr
        (Array.polyProduct gs.toArray * (gs.map q).sum)
        (f * Hex.DensePoly.derivative (Array.polyProduct gs.toArray)) m := by
  intro gs
  induction gs with
  | nil =>
      intro _
      have h1 : Array.polyProduct ([] : List Hex.ZPoly).toArray = 1 := by simp
      have hd : Hex.DensePoly.derivative (1 : Hex.ZPoly) = 0 :=
        Hex.DensePoly.derivative_C_semiring (1 : Int)
      rw [h1, hd, List.map_nil, List.sum_nil]
      have e1 : (1 : Hex.ZPoly) * 0 = 0 := by
        rw [Hex.DensePoly.mul_comm_poly, Hex.DensePoly.zero_mul]
      have e2 : f * (0 : Hex.ZPoly) = 0 := by
        rw [Hex.DensePoly.mul_comm_poly, Hex.DensePoly.zero_mul]
      rw [e1, e2]
      exact Hex.ZPoly.congr_refl 0 m
  | cons g rest ih =>
      intro hall
      have hg : Hex.ZPoly.congr (g * q g) (f * Hex.DensePoly.derivative g) m :=
        hall g (List.mem_cons_self ..)
      have hrest : ∀ g' ∈ rest,
          Hex.ZPoly.congr (g' * q g') (f * Hex.DensePoly.derivative g') m :=
        fun g' hg' => hall g' (List.mem_cons_of_mem g hg')
      have IHrest := ih hrest
      rw [Hex.ZPoly.polyProduct_cons_toArray, List.map_cons, List.sum_cons,
        Hex.DensePoly.derivative_mul, Hex.DensePoly.mul_add_right_poly,
        Hex.DensePoly.mul_add_right_poly]
      set Prest := Array.polyProduct rest.toArray with hPrest
      set Srest := (rest.map q).sum with hSrest
      set dPrest := Hex.DensePoly.derivative Prest with hdPrest
      refine Hex.ZPoly.congr_add _ _ _ _ m ?_ ?_
      · -- `(g * Prest) * q g ≡ f * (g' * Prest)`
        have lhs_eq : (g * Prest) * q g = (g * q g) * Prest := by
          rw [Hex.DensePoly.mul_assoc_poly, Hex.DensePoly.mul_comm_poly Prest (q g),
            ← Hex.DensePoly.mul_assoc_poly]
        have hcong :
            Hex.ZPoly.congr ((g * q g) * Prest)
              ((f * Hex.DensePoly.derivative g) * Prest) m :=
          Hex.ZPoly.congr_mul (g * q g) Prest (f * Hex.DensePoly.derivative g) Prest m
            hg (Hex.ZPoly.congr_refl Prest m)
        rw [lhs_eq,
          ← Hex.DensePoly.mul_assoc_poly f (Hex.DensePoly.derivative g) Prest]
        exact hcong
      · -- `(g * Prest) * Srest ≡ f * (g * Prest')`
        have lhs_eq : (g * Prest) * Srest = g * (Prest * Srest) :=
          Hex.DensePoly.mul_assoc_poly g Prest Srest
        have hcong :
            Hex.ZPoly.congr (g * (Prest * Srest)) (g * (f * dPrest)) m :=
          Hex.ZPoly.congr_mul g (Prest * Srest) g (f * dPrest) m
            (Hex.ZPoly.congr_refl g m) IHrest
        have rhs_eq : g * (f * dPrest) = f * (g * dPrest) := by
          rw [← Hex.DensePoly.mul_assoc_poly g f dPrest,
            Hex.DensePoly.mul_comm_poly g f, Hex.DensePoly.mul_assoc_poly f g dPrest]
        rw [lhs_eq, ← rhs_eq]
        exact hcong

/-- A coefficientwise congruence `a ≡ b (mod m)` transports to a
`Polynomial.C (m : ℤ)`-divisibility of the difference of the mapped Mathlib
polynomials. -/
private theorem C_dvd_toPolynomial_sub_of_congr
    (a b : Hex.ZPoly) (m : Nat) (h : Hex.ZPoly.congr a b m) :
    Polynomial.C (m : ℤ) ∣
      (HexPolyMathlib.toPolynomial a - HexPolyMathlib.toPolynomial b) := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro j
  rw [Polynomial.coeff_sub, HexPolyMathlib.coeff_toPolynomial,
    HexPolyMathlib.coeff_toPolynomial]
  exact Int.dvd_of_emod_eq_zero (h j)

/-- The converse of `C_dvd_toPolynomial_sub_of_congr`. -/
private theorem congr_of_C_dvd_toPolynomial_sub
    (a b : Hex.ZPoly) (m : Nat)
    (h : Polynomial.C (m : ℤ) ∣
      (HexPolyMathlib.toPolynomial a - HexPolyMathlib.toPolynomial b)) :
    Hex.ZPoly.congr a b m := by
  rw [Polynomial.C_dvd_iff_dvd_coeff] at h
  intro j
  have hj := h j
  rw [Polynomial.coeff_sub, HexPolyMathlib.coeff_toPolynomial,
    HexPolyMathlib.coeff_toPolynomial] at hj
  exact Int.emod_eq_zero_of_dvd hj

/-- A centred residue modulo `m` has magnitude at most `m / 2`: `2·|x mod^± m| ≤ m`. -/
theorem two_mul_natAbs_centeredModNat_le (z : Int) (m : Nat) (hm : 0 < m) :
    2 * (Hex.centeredModNat z m).natAbs ≤ m := by
  unfold Hex.centeredModNat
  rw [if_neg hm.ne']
  have h1 : 0 ≤ z % (m : Int) := Int.emod_nonneg z (by exact_mod_cast hm.ne')
  have h2 : z % (m : Int) < (m : Int) := Int.emod_lt_of_pos z (by exact_mod_cast hm)
  simp only [Int.ofNat_eq_natCast]
  by_cases hc : 2 * (z % (m : Int)).natAbs ≤ m
  · rw [if_pos hc]; exact hc
  · rw [if_neg hc, if_neg (by omega : ¬ z % (m : Int) < 0)]
    omega

/-- The high-bit cut residue `Psi^a_b` lands in the centred range modulo `p^b`. -/
theorem two_mul_natAbs_centeredResiduePow_le (p b : Nat) (z : Int) (hpb : 0 < p ^ b) :
    2 * (Hex.centeredResiduePow p b z).natAbs ≤ p ^ b := by
  unfold Hex.centeredResiduePow
  exact two_mul_natAbs_centeredModNat_le z (p ^ b) hpb

/--
**BHKS Lemma 5.7, period-aware aggregate form.**  Where
`two_mul_natAbs_sum_psiCut_le` bounds the *raw* high-bit cut-sum and needs
per-element ambient residues pinned to a small integer (forcing per-factor
smallness), this version bounds the cut-sum *modulo the period* `q = p^(a−b)` and
needs only the *aggregate* residue `centeredResiduePow p a (Σ w_i)` to be small.

This is the analytic core of the recombination case: for split irreducible
factors the per-local CLD residues are not individually small — only their
aggregate `Φ(factor)` is — and the lattice's period rows `diag(p^(a−l_j))` absorb
the large per-local parts.  The raw-sum bound is *false* here (no per-factor
hypothesis is available); the `∃ t` period reduction by an integer multiple of `q`
is exactly what makes the aggregate-only bound true.
-/
theorem two_mul_natAbs_sum_psiCut_period_le
    {ι : Type*} (T : Finset ι) (p a b : Nat) (hba : b ≤ a) (hp : 1 < p)
    (z : ι → Int) (y : Int) (B : Nat)
    (hagg : Hex.centeredResiduePow p a (∑ i ∈ T, Hex.centeredResiduePow p a (z i)) = y)
    (hy : y.natAbs ≤ B) (hsep : 2 * B < p ^ b) :
    ∃ t : Int,
      2 * (((∑ i ∈ T, Hex.psiCut p a b (z i)) - t * (p ^ (a - b) : Int))).natAbs
        ≤ T.card := by
  classical
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpb : 0 < p ^ b := pow_pos hp0 b
  have hm0 : (p ^ b : Nat) ≠ 0 := hpb.ne'
  set w : ι → Int := fun i => Hex.centeredResiduePow p a (z i) with hwdef
  set col : Int := ∑ i ∈ T, Hex.psiCut p a b (z i) with hcol
  set lo : ι → Int := fun i => Hex.centeredResiduePow p b (w i) with hlodef
  -- Per element: `p^b · Psi(z i) = w i - lo i`.
  have hkey : ∀ i ∈ T, ((p ^ b : Nat) : Int) * Hex.psiCut p a b (z i) = w i - lo i := by
    intro i hi
    have hdec := Hex.centeredResiduePow_add_pow_mul_psiCut p a b (z i) hm0
    simp only [hwdef, hlodef]
    linarith [hdec]
  -- Aggregate: `p^b · col = (Σ w) − (Σ lo)`.
  have hsumw : ((p ^ b : Nat) : Int) * col = (∑ i ∈ T, w i) - ∑ i ∈ T, lo i := by
    rw [hcol, Finset.mul_sum, Finset.sum_congr rfl hkey, Finset.sum_sub_distrib]
  -- Aggregate residue smallness gives the period divisibility `p^a ∣ (Σ w) − y`.
  have hdvd_a : ((p ^ a : Nat) : Int) ∣ (∑ i ∈ T, w i) - y := by
    have hcm : Hex.centeredModNat (∑ i ∈ T, w i) (p ^ a) = y := by
      simpa [Hex.centeredResiduePow] using hagg
    have h := Hex.self_sub_centeredModNat_dvd (∑ i ∈ T, w i) (p ^ a)
    rwa [hcm] at h
  obtain ⟨k, hk⟩ := hdvd_a
  -- `p^a = p^b · q` with `q = p^(a−b)` (in `ℤ`), using `b ≤ a`.
  have hab : b + (a - b) = a := by omega
  have hpa_split : ((p ^ a : Nat) : Int) = ((p ^ b : Nat) : Int) * ((p : Int) ^ (a - b)) := by
    push_cast
    rw [← pow_add, hab]
  -- Bound on the lower-residue sum: `2 · |Σ lo| ≤ |T| · p^b`.
  have hlo_le : 2 * |∑ i ∈ T, lo i| ≤ (T.card : Int) * (p ^ b : Nat) := by
    have htri : |∑ i ∈ T, lo i| ≤ ∑ i ∈ T, |lo i| := Finset.abs_sum_le_sum_abs _ _
    have hpt : ∑ i ∈ T, (2 * |lo i|) ≤ ∑ i ∈ T, ((p ^ b : Nat) : Int) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      have := two_mul_natAbs_centeredResiduePow_le p b (w i) hpb
      have hcast : 2 * |lo i| = ((2 * (Hex.centeredResiduePow p b (w i)).natAbs : Nat) : Int) := by
        simp only [hlodef, Nat.cast_mul, Nat.cast_ofNat, Int.abs_eq_natAbs]
      rw [hcast]; exact_mod_cast this
    calc 2 * |∑ i ∈ T, lo i| ≤ 2 * ∑ i ∈ T, |lo i| := by linarith
      _ = ∑ i ∈ T, (2 * |lo i|) := by rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ T, ((p ^ b : Nat) : Int) := hpt
      _ = (T.card : Int) * (p ^ b : Nat) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- The period-reduced value `d := col − k·q` satisfies `p^b · d = y − Σ lo`.
  refine ⟨k, ?_⟩
  set d : Int := col - k * ((p : Int) ^ (a - b)) with hddef
  have hpd : ((p ^ b : Nat) : Int) * d = y - ∑ i ∈ T, lo i := by
    have hk' : (∑ i ∈ T, w i) = y + ((p ^ a : Nat) : Int) * k := by linarith [hk]
    rw [hddef, mul_sub, hsumw, hk', hpa_split]
    ring
  -- Tail: identical to the raw lemma with `col` replaced by the reduced `d`.
  have hyZ : |y| ≤ (B : Int) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hy
  have habs : ((p ^ b : Nat) : Int) * |d| = |y - ∑ i ∈ T, lo i| := by
    rw [← hpd, abs_mul]; congr 1
    rw [Int.abs_eq_natAbs]; simp
  have hstep : 2 * (((p ^ b : Nat) : Int) * |d|) ≤ 2 * (B : Int) + (T.card : Int) * (p ^ b : Nat) := by
    rw [habs]
    calc 2 * |y - ∑ i ∈ T, lo i| ≤ 2 * (|y| + |∑ i ∈ T, lo i|) := by
            linarith [abs_sub y (∑ i ∈ T, lo i)]
      _ = 2 * |y| + 2 * |∑ i ∈ T, lo i| := by ring
      _ ≤ 2 * (B : Int) + (T.card : Int) * (p ^ b : Nat) := by linarith [hlo_le, hyZ]
  have hsepZ : 2 * (B : Int) < ((p ^ b : Nat) : Int) := by exact_mod_cast hsep
  have hpbZ : (0 : Int) < ((p ^ b : Nat) : Int) := by exact_mod_cast hpb
  have hdNat : 2 * |d| ≤ (T.card : Int) := by
    have hlt2 : ((p ^ b : Nat) : Int) * (2 * |d|) <
        ((p ^ b : Nat) : Int) * ((T.card : Int) + 1) := by
      nlinarith [hstep, hsepZ, hpbZ]
    have h2N : 2 * |d| < (T.card : Int) + 1 := lt_of_mul_lt_mul_left hlt2 (le_of_lt hpbZ)
    omega
  have hfin : (2 * d.natAbs : Int) ≤ (T.card : Int) := by
    rw [Int.abs_eq_natAbs] at hdNat; push_cast at hdNat ⊢; linarith
  exact_mod_cast hfin

/-- The executable Pascal-recursion `Hex.Nat.choose` agrees with Mathlib's
`Nat.choose`; needed because `Hex.bhksCoeffBound` elaborates `Nat.choose` to the
executable shadow inside `namespace Hex`. -/
theorem hex_choose_eq (n k : Nat) : Hex.Nat.choose n k = Nat.choose n k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih => cases k with
    | zero => simp
    | succ k => rw [Hex.Nat.choose_succ_succ, Nat.choose_succ_succ, ih, ih]

/-- **Monic cancellation modulo `m`.**  Over `Polynomial ℤ`, if `C m` divides a
product `g * z` and `g` is monic, then `C m` divides `z`.  The proof maps to
`Polynomial (ZMod m)`, where `g.map` is monic hence a non-zero-divisor. -/
theorem C_dvd_of_monic_mul {m : Nat} {Pg Z : Polynomial ℤ} (hPg : Pg.Monic)
    (h : Polynomial.C ((m : Nat) : ℤ) ∣ Pg * Z) :
    Polynomial.C ((m : Nat) : ℤ) ∣ Z := by
  classical
  have hmap : (Pg * Z).map (Int.castRingHom (ZMod m)) = 0 := by
    obtain ⟨W, hW⟩ := h
    rw [hW, Polynomial.map_mul, Polynomial.map_C]
    have hz : (Int.castRingHom (ZMod m)) ((m : Nat) : ℤ) = 0 := by simp
    rw [hz, Polynomial.C_0, zero_mul]
  rw [Polynomial.map_mul] at hmap
  have hZ0 : Z.map (Int.castRingHom (ZMod m)) = 0 :=
    (hPg.map (Int.castRingHom (ZMod m))).mul_right_eq_zero_iff.mp hmap
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro k
  have hck : (Z.map (Int.castRingHom (ZMod m))).coeff k = 0 := by rw [hZ0]; simp
  rw [Polynomial.coeff_map] at hck
  have hcast : ((Z.coeff k : ℤ) : ZMod m) = 0 := by simpa using hck
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcast

/-- **BHKS Lemma 5.1, executable bound form.**  For a monic divisor `g` of `f`
over `Polynomial ℤ`, every `Phi`-column coefficient is bounded by the executable
Mignotte column bound `Hex.bhksCoeffBound f j`. -/
theorem abs_phi_coeff_le_bhksCoeffBound (f g : Hex.ZPoly) (j : Nat)
    (hg_monic : (HexPolyMathlib.toPolynomial g).Monic)
    (hgf : HexPolyMathlib.toPolynomial g ∣ HexPolyMathlib.toPolynomial f) :
    ((phi (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)).coeff j).natAbs
      ≤ Hex.bhksCoeffBound f j := by
  classical
  obtain ⟨hpoly, hfac⟩ := hgf
  have hreal := abs_phi_coeff_le_of_monic_factor
    (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g) hpoly hg_monic hfac j
  have hnd : (HexPolyMathlib.toPolynomial f).natDegree = f.degree?.getD 0 :=
    HexPolyMathlib.natDegree_toPolynomial f
  have hZeq : HexPolyZMathlib.toPolynomial f = HexPolyMathlib.toPolynomial f := rfl
  have hl2 : HexPolyZMathlib.l2norm (HexPolyMathlib.toPolynomial f)
      ≤ (Hex.ZPoly.coeffL2NormBound f : ℝ) := by
    rw [← hZeq]; exact l2norm_toPolynomial_le_coeffL2NormBound f
  have hbb_nat : Hex.bhksCoeffBound f j
      = Nat.choose (f.degree?.getD 0 - 1) j * (f.degree?.getD 0)
          * Hex.ZPoly.coeffL2NormBound f := by
    simp only [Hex.bhksCoeffBound, hex_choose_eq]
  have hbb : (Hex.bhksCoeffBound f j : ℝ)
      = (Nat.choose (f.degree?.getD 0 - 1) j : ℝ) * (f.degree?.getD 0 : ℝ)
          * (Hex.ZPoly.coeffL2NormBound f : ℝ) := by
    rw [hbb_nat]; push_cast; ring
  have hkey :
      (((phi (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)).coeff j).natAbs : ℝ)
        ≤ (Hex.bhksCoeffBound f j : ℝ) := by
    refine hreal.trans ?_
    rw [hnd, hbb]
    have hnn : (0 : ℝ) ≤ (Nat.choose (f.degree?.getD 0 - 1) j : ℝ) * (f.degree?.getD 0 : ℝ) := by
      positivity
    exact mul_le_mul_of_nonneg_left hl2 hnn
  exact_mod_cast hkey

/-- **Generic CLD residue bridge.**  For a monic divisor `g` of `f` whose
precision `p^a` separates the Mignotte column bound, the centred ambient residue
of *any* polynomial `q` whose product `g * q` is congruent to the
logarithmic-derivative numerator `f * g'` modulo `p^a` is exactly the integer
`Phi`-column coefficient.  The per-factor bridge below is the special case
`q := cldQuotientMod f g p a`; the aggregate residue work instantiates it with
`q := supportCldSum`, which satisfies the same congruence against the whole
recovered factor without being a single `cldQuotientMod`. -/
theorem residue_eq_phi_coeff_of_congr
    (f g q : Hex.ZPoly) (p a j : Nat)
    (hg_monic : (HexPolyMathlib.toPolynomial g).Monic)
    (hgf : HexPolyMathlib.toPolynomial g ∣ HexPolyMathlib.toPolynomial f)
    (hsep : 2 * Hex.bhksCoeffBound f j < p ^ a)
    (hcongr : Hex.ZPoly.congr (g * q)
        (f * Hex.DensePoly.derivative g) (p ^ a)) :
    Hex.centeredResiduePow p a (q.coeff j)
      = (phi (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)).coeff j := by
  obtain ⟨hpoly, hHpoly⟩ := hgf
  have hphi : phi (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)
      = hpoly * (HexPolyMathlib.toPolynomial g).derivative :=
    phi_eq_factor_mul_derivative _ _ hpoly hg_monic hHpoly
  have hC := C_dvd_toPolynomial_sub_of_congr (g * q)
      (f * Hex.DensePoly.derivative g) (p ^ a) hcongr
  rw [HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_mul,
      HexPolyMathlib.toPolynomial_derivative] at hC
  have hfeq :
      (HexPolyMathlib.toPolynomial g * HexPolyMathlib.toPolynomial q
        - HexPolyMathlib.toPolynomial f * (HexPolyMathlib.toPolynomial g).derivative)
      = HexPolyMathlib.toPolynomial g *
          (HexPolyMathlib.toPolynomial q
            - phi (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)) := by
    rw [hphi, hHpoly]; ring
  rw [hfeq] at hC
  have hZ := C_dvd_of_monic_mul hg_monic hC
  rw [Polynomial.C_dvd_iff_dvd_coeff] at hZ
  have hj := hZ j
  rw [Polynomial.coeff_sub, HexPolyMathlib.coeff_toPolynomial] at hj
  have hcongr_emod :
      (phi (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)).coeff j
          % ((p ^ a : Nat) : Int)
        = q.coeff j % ((p ^ a : Nat) : Int) :=
    Int.modEq_iff_dvd.mpr hj
  exact Hex.centeredResiduePow_eq_of_natAbs_le p a _ _ (Hex.bhksCoeffBound f j)
    (abs_phi_coeff_le_bhksCoeffBound f g j hg_monic ⟨hpoly, hHpoly⟩) hsep hcongr_emod

/-- `centeredResiduePow p a` depends only on its argument modulo `p ^ a`. -/
theorem centeredResiduePow_emod_self (p a : Nat) (z : Int) :
    Hex.centeredResiduePow p a z % ((p ^ a : Nat) : Int)
      = z % ((p ^ a : Nat) : Int) := by
  unfold Hex.centeredResiduePow
  exact Int.modEq_iff_dvd.mpr (Hex.self_sub_centeredModNat_dvd z (p ^ a))

/-- `centeredResiduePow p a` is invariant under replacing its argument by a
congruent one modulo `p ^ a`. -/
theorem centeredResiduePow_emod_eq (p a : Nat) (x y : Int)
    (h : x % ((p ^ a : Nat) : Int) = y % ((p ^ a : Nat) : Int)) :
    Hex.centeredResiduePow p a x = Hex.centeredResiduePow p a y := by
  unfold Hex.centeredResiduePow
  rw [← Hex.centeredModNat_emod_self x, h, Hex.centeredModNat_emod_self y]

/-- The `j`-th coefficient of a list sum of `ZPoly`s is the integer list sum of
the per-summand `j`-th coefficients. -/
theorem coeff_listSum (l : List Hex.ZPoly) (j : Nat) :
    (l.sum).coeff j = (l.map (fun q => q.coeff j)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.sum_cons, Hex.DensePoly.coeff_add (R := Int) x xs.sum j (by rfl), ih,
      List.map_cons, List.sum_cons]

/-- A list sum is invariant modulo `m` under replacing each summand by a
congruent one. -/
theorem listSum_emod_eq {α : Type*} (l : List α) (F G : α → Int) (m : Int)
    (h : ∀ x ∈ l, F x % m = G x % m) :
    (l.map F).sum % m = (l.map G).sum % m := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact Int.ModEq.add (h x (List.mem_cons_self ..))
      (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- A finite sum over the support filter of `Finset.univ` equals the list sum
over the correspondingly filtered `finRange`. -/
theorem sum_filter_univ_eq_listSum {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (F : Fin n → Int) :
    ∑ i ∈ Finset.univ.filter P, F i
      = (((List.finRange n).filter (fun i => decide (P i))).map F).sum := by
  rw [← List.sum_toFinset F ((List.nodup_finRange n).filter _)]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext i
  simp

/-- Coefficientwise congruence modulo `m` is preserved by the formal
derivative. -/
theorem congr_derivative (a b : Hex.ZPoly) (m : Nat)
    (h : Hex.ZPoly.congr a b m) :
    Hex.ZPoly.congr (Hex.DensePoly.derivative a) (Hex.DensePoly.derivative b) m := by
  intro n
  rw [Hex.DensePoly.coeff_derivative a n (mul_zero _),
    Hex.DensePoly.coeff_derivative b n (mul_zero _)]
  have hd : (m : Int) ∣ (a.coeff (n + 1) - b.coeff (n + 1)) :=
    Int.dvd_of_emod_eq_zero (h (n + 1))
  have hfac : (((n + 1 : Nat) : Int) * a.coeff (n + 1)
        - ((n + 1 : Nat) : Int) * b.coeff (n + 1))
      = ((n + 1 : Nat) : Int) * (a.coeff (n + 1) - b.coeff (n + 1)) := by ring
  rw [hfac]
  exact Int.emod_eq_zero_of_dvd (hd.mul_left _)

/-- Aggregate CLD congruence for a recovered support, parametrised directly by
the per-selected-factor monic / positive-degree / modular-cofactor data instead
of a semantic package.  Mirrors `TrueFactorLiftSemantics.supportProduct_cldSum_congr`
but takes the per-factor hypotheses explicitly, so it applies to a
`RecoveredLift` which carries no semantic package. -/
theorem supportProduct_cldSum_congr_of_factors
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (f : Hex.ZPoly) (p a : Nat) (hk : 1 < p ^ a)
    (hfac : ∀ i : Fin L.factorCount, i ∈ S →
        ∃ h : Hex.ZPoly,
          Hex.DensePoly.Monic (L.liftedFactors.getD i.val 1) ∧
          0 < (L.liftedFactors.getD i.val 1).degree?.getD 0 ∧
          Hex.ZPoly.congr f ((L.liftedFactors.getD i.val 1) * h) (p ^ a)) :
    Hex.ZPoly.congr
      (supportProduct L S * supportCldSum L S f p a)
      (f * Hex.DensePoly.derivative (supportProduct L S)) (p ^ a) := by
  classical
  have hfilter_mem : ∀ i ∈ (List.finRange L.factorCount).filter
        (fun i => decide (i ∈ S)), i ∈ S := by
    intro i hi
    exact of_decide_eq_true (List.mem_filter.mp hi).2
  have hyps : ∀ g ∈ ((List.finRange L.factorCount).filter
        (fun i => decide (i ∈ S))).map (fun i => L.liftedFactors.getD i.val 1),
      Hex.ZPoly.congr (g * Hex.cldQuotientMod f g p a)
        (f * Hex.DensePoly.derivative g) (p ^ a) := by
    intro g hg
    rw [List.mem_map] at hg
    obtain ⟨i, hi_mem, rfl⟩ := hg
    obtain ⟨h, hmono, hdeg, hcongr⟩ := hfac i (hfilter_mem i hi_mem)
    exact cldQuotientMod_congr_mul_derivative f (L.liftedFactors.getD i.val 1)
      h p a hk hmono hdeg hcongr
  have key := congr_polyProduct_mul_listSum_derivative f
    (fun g => Hex.cldQuotientMod f g p a) (p ^ a)
    (((List.finRange L.factorCount).filter (fun i => decide (i ∈ S))).map
      (fun i => L.liftedFactors.getD i.val 1)) hyps
  rw [List.map_map] at key
  exact key

open Classical in

/-- **Aggregate CLD residue from a `RecoveredLift` (monic coordinate, issue
#7872).**  In the monic regime (`leadingCoeff f = 1`, so the `dilate` in
`recovered_eq` is the identity) the aggregate centred residue of the per-factor
CLD coefficients equals the integer `Phi`-column coefficient of the *whole*
recovered factor, and that coefficient is Mignotte-bounded.  This is exactly the
`hagg` / `hy` input shape consumed by `two_mul_natAbs_sum_psiCut_period_le`
(#7869), with `y = phi(...).coeff j` and `B = bhksCoeffBound f j`.

The per-selected-factor `hfac` (monic, positive degree, modular cofactor) is the
Hensel-factorisation datum `∏ gᵢ ≡ f (mod pᵃ)`; the recovered factor itself only
needs `factor ∣ f` over ℤ (from `factor_mul`), routed through the *whole-factor*
`phi (toPolynomial f) (toPolynomial factor)`, never per-`gᵢ` integer columns. -/
theorem recoveredLift_aggregate_residue
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (D : RecoveredLift L S)
    (hf_lc : Hex.DensePoly.leadingCoeff D.f = 1)
    (hfactor_monic : (HexPolyMathlib.toPolynomial D.factor).Monic)
    (hk : 1 < D.p ^ D.a)
    (hsep : ∀ j, 2 * Hex.bhksCoeffBound D.f j < D.p ^ D.a)
    (hfac : ∀ i : Fin L.factorCount, i ∈ S →
        ∃ h : Hex.ZPoly,
          Hex.DensePoly.Monic (L.liftedFactors.getD i.val 1) ∧
          0 < (L.liftedFactors.getD i.val 1).degree?.getD 0 ∧
          Hex.ZPoly.congr D.f ((L.liftedFactors.getD i.val 1) * h) (D.p ^ D.a))
    (j : Nat) :
    Hex.centeredResiduePow D.p D.a
        (∑ i ∈ Finset.univ.filter (fun i => i ∈ S),
          Hex.centeredResiduePow D.p D.a
            ((Hex.cldQuotientMod D.f (L.liftedFactors.getD i.val 1) D.p D.a).coeff j))
      = (phi (HexPolyMathlib.toPolynomial D.f)
          (HexPolyMathlib.toPolynomial D.factor)).coeff j
    ∧ ((phi (HexPolyMathlib.toPolynomial D.f)
          (HexPolyMathlib.toPolynomial D.factor)).coeff j).natAbs
        ≤ Hex.bhksCoeffBound D.f j := by
  classical
  -- Divisibility of the recovered factor over ℤ, from the factor/cofactor split.
  have hfac_dvd : HexPolyMathlib.toPolynomial D.factor ∣ HexPolyMathlib.toPolynomial D.f :=
    ⟨HexPolyMathlib.toPolynomial D.cofactor, by
      rw [← HexPolyMathlib.toPolynomial_mul, D.factor_mul]⟩
  -- (a) Aggregate CLD congruence against the support product.
  have hagg := supportProduct_cldSum_congr_of_factors (L := L) (S := S)
    D.f D.p D.a hk hfac
  -- supportProduct ≡ factor (mod p^a), from recovered_eq with the trivial dilate.
  have hcl : Hex.centeredLiftPoly (supportProduct L S) (D.p ^ D.a) = D.factor := by
    have h := D.recovered_eq
    rw [hf_lc, Hex.ZPoly.dilate_one] at h
    exact h
  have hsp_eq : Hex.ZPoly.congr (supportProduct L S) D.factor (D.p ^ D.a) := by
    intro i
    rw [← hcl, Hex.coeff_centeredLiftPoly]
    exact Int.emod_eq_zero_of_dvd (Hex.self_sub_centeredModNat_dvd _ _)
  have hsp_deriv : Hex.ZPoly.congr
      (Hex.DensePoly.derivative (supportProduct L S))
      (Hex.DensePoly.derivative D.factor) (D.p ^ D.a) :=
    congr_derivative _ _ _ hsp_eq
  -- Transport (a) to the recovered factor's CLD congruence.
  have hcong_factor : Hex.ZPoly.congr
      (D.factor * supportCldSum L S D.f D.p D.a)
      (D.f * Hex.DensePoly.derivative D.factor) (D.p ^ D.a) := by
    have step1 : Hex.ZPoly.congr
        (D.factor * supportCldSum L S D.f D.p D.a)
        (supportProduct L S * supportCldSum L S D.f D.p D.a) (D.p ^ D.a) :=
      Hex.ZPoly.congr_mul _ _ _ _ _
        (Hex.ZPoly.congr_symm _ _ _ hsp_eq) (Hex.ZPoly.congr_refl _ _)
    have step3 : Hex.ZPoly.congr
        (D.f * Hex.DensePoly.derivative (supportProduct L S))
        (D.f * Hex.DensePoly.derivative D.factor) (D.p ^ D.a) :=
      Hex.ZPoly.congr_mul _ _ _ _ _ (Hex.ZPoly.congr_refl _ _) hsp_deriv
    exact Hex.ZPoly.congr_trans _ _ _ _
      (Hex.ZPoly.congr_trans _ _ _ _ step1 hagg) step3
  -- (b) The aggregate residue of supportCldSum is the factor's Phi column.
  have hres : Hex.centeredResiduePow D.p D.a
      ((supportCldSum L S D.f D.p D.a).coeff j)
      = (phi (HexPolyMathlib.toPolynomial D.f)
          (HexPolyMathlib.toPolynomial D.factor)).coeff j :=
    residue_eq_phi_coeff_of_congr D.f D.factor (supportCldSum L S D.f D.p D.a)
      D.p D.a j hfactor_monic hfac_dvd (hsep j) hcong_factor
  refine ⟨?_, abs_phi_coeff_le_bhksCoeffBound D.f D.factor j hfactor_monic hfac_dvd⟩
  -- (c) Bridge the goal's per-factor residue sum to supportCldSum's coefficient.
  rw [← hres]
  refine centeredResiduePow_emod_eq D.p D.a _ _ ?_
  have hA : (∑ i ∈ Finset.univ.filter (fun i => i ∈ S),
        Hex.centeredResiduePow D.p D.a
          ((Hex.cldQuotientMod D.f (L.liftedFactors.getD i.val 1) D.p D.a).coeff j))
      = (((List.finRange L.factorCount).filter (fun i => decide (i ∈ S))).map
          (fun i => Hex.centeredResiduePow D.p D.a
            ((Hex.cldQuotientMod D.f (L.liftedFactors.getD i.val 1) D.p D.a).coeff j))).sum :=
    sum_filter_univ_eq_listSum (fun i => i ∈ S) _
  have hB : (supportCldSum L S D.f D.p D.a).coeff j
      = (((List.finRange L.factorCount).filter (fun i => decide (i ∈ S))).map
          (fun i => (Hex.cldQuotientMod D.f (L.liftedFactors.getD i.val 1)
            D.p D.a).coeff j)).sum := by
    show (((List.finRange L.factorCount).filter (fun i => decide (i ∈ S))).map
          (fun i => Hex.cldQuotientMod D.f (L.liftedFactors.getD i.val 1)
            D.p D.a)).sum.coeff j = _
    rw [coeff_listSum, List.map_map]
    rfl
  rw [hA, hB]
  exact listSum_emod_eq _ _ _ _
    (fun i _ => centeredResiduePow_emod_self D.p D.a _)

/-! ### Period-adjusted true-factor short vector from a `RecoveredLift` (issue #7876)

The per-factor tight column (`tightColumnBound_of_lift`) bounds the *zero-period*
tail `∑_{i∈S} psiCut(zᵢ)` and routes through per-factor integer divisibility,
which a `RecoveredLift` cannot supply (the period trap of #7866/#7867).  The
sound route uses the BHKS lattice's own period rows `diag(p^(a−ℓⱼ))`: the
*period-adjusted* tail `∑_{i∈S} psiCut(zᵢ) − tⱼ·p^(a−ℓⱼ)` is still bounded by
`factorCount/2` (`two_mul_natAbs_sum_psiCut_period_le`) from only the aggregate
residue (`recoveredLift_aggregate_residue`), and the adjusted vector is still a
genuine BHKS lattice vector (the period rows are basis rows), projecting to the
same support indicator.  This produces a `SupportShortVectorData`, fed to the
fast-disjunct consumer through `cutProjectionHypotheses_of_shortVectors`. -/

/-- The executable cut-threshold array reads back the per-coordinate threshold. -/
theorem bhksCutThresholds_getD_of_lt (f : Hex.ZPoly) (p j : Nat)
    (h : j < f.degree?.getD 0) :
    (Hex.bhksCutThresholds f p).getD j 0 = Hex.bhksCoeffCutThreshold p f j := by
  unfold Hex.bhksCutThresholds
  rw [Array.getD_eq_getD_getElem?]
  have hsize :
      (((List.range (f.degree?.getD 0)).map
        (fun j => Hex.bhksCoeffCutThreshold p f j)).toArray).size = f.degree?.getD 0 := by
    simp
  rw [Array.getElem?_eq_getElem (by simpa [hsize] using h)]
  simp [List.getElem_toArray, List.getElem_map, List.getElem_range]

/-- Selection coefficients for the period-adjusted true-factor short vector: the
support indicator on the first block, and `−t j` on the diagonal-period rows. -/
def periodAdjustedRowCoeffs (L : Hex.BhksLatticeBasis) (S : LiftedFactorSupport L)
    (t : Fin L.coeffWidth → ℤ) : Vector ℤ (L.factorCount + L.coeffWidth) :=
  Vector.ofFn fun x =>
    if hx : x.val < L.factorCount then indicatorVector S ⟨x.val, hx⟩
    else - t ⟨x.val - L.factorCount, by omega⟩

theorem periodAdjustedRowCoeffs_castAdd (L : Hex.BhksLatticeBasis)
    (S : LiftedFactorSupport L) (t : Fin L.coeffWidth → ℤ) (i : Fin L.factorCount) :
    (periodAdjustedRowCoeffs L S t)[Fin.castAdd L.coeffWidth i] = indicatorVector S i := by
  unfold periodAdjustedRowCoeffs
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  rw [
    dif_pos (show (Fin.castAdd L.coeffWidth i).val < L.factorCount from i.isLt)]
  congr 1

theorem periodAdjustedRowCoeffs_natAdd (L : Hex.BhksLatticeBasis)
    (S : LiftedFactorSupport L) (t : Fin L.coeffWidth → ℤ) (j : Fin L.coeffWidth) :
    (periodAdjustedRowCoeffs L S t)[Fin.natAdd L.factorCount j] = - t j := by
  unfold periodAdjustedRowCoeffs
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  rw [
    dif_neg (by simp only [Fin.val_natAdd]; omega)]
  congr 2
  apply Fin.ext
  simp only [Fin.val_natAdd]
  omega

/-- The period-adjusted true-factor short vector: the support indicator on the
first block, with the CLD tail reduced by the diagonal-period rows. -/
def periodAdjustedVector (L : Hex.BhksLatticeBasis) (S : LiftedFactorSupport L)
    (t : Fin L.coeffWidth → ℤ) : Vector ℤ (L.factorCount + L.coeffWidth) :=
  Hex.Matrix.vecMul (periodAdjustedRowCoeffs L S t) L.basis

theorem periodAdjustedVector_memLattice (L : Hex.BhksLatticeBasis)
    (S : LiftedFactorSupport L) (t : Fin L.coeffWidth → ℤ) :
    Hex.Matrix.memLattice L.basis (periodAdjustedVector L S t) :=
  ⟨periodAdjustedRowCoeffs L S t, rfl⟩

/-- Under block form, the first `factorCount` coordinates of the period-adjusted
vector are exactly the support indicator (the period rows do not touch the first
block). -/
theorem periodAdjustedVector_project_of_blockForm
    {L : Hex.BhksLatticeBasis} (S : LiftedFactorSupport L)
    (hL : BhksBlockForm L) (t : Fin L.coeffWidth → ℤ) (i : Fin L.factorCount) :
    (periodAdjustedVector L S t)[
        (⟨i.val, Nat.lt_add_right L.coeffWidth i.isLt⟩ :
          Fin (L.factorCount + L.coeffWidth))] =
      indicatorVector S i := by
  unfold periodAdjustedVector
  rw [vecMul_getElem_eq_sum, Fin.sum_univ_add]
  have hentry : ∀ x : Fin (L.factorCount + L.coeffWidth),
      L.basis[x][(⟨i.val, Nat.lt_add_right L.coeffWidth i.isLt⟩ :
          Fin (L.factorCount + L.coeffWidth))]
        = Hex.bhksLatticeEntry L.factorCount L.coeffWidth L.p L.precision
            L.cutThresholds L.cldRows x
            ⟨i.val, Nat.lt_add_right L.coeffWidth i.isLt⟩ := by
    intro x
    rw [hL, Hex.Matrix.getElem_ofFn]
  have hsnd : (∑ j : Fin L.coeffWidth,
      L.basis[Fin.natAdd L.factorCount j][(⟨i.val,
          Nat.lt_add_right L.coeffWidth i.isLt⟩ :
          Fin (L.factorCount + L.coeffWidth))] *
        (periodAdjustedRowCoeffs L S t)[Fin.natAdd L.factorCount j]) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hentry]
    unfold Hex.bhksLatticeEntry
    rw [dif_neg (by simp only [Fin.val_natAdd]; omega),
      dif_pos (show (⟨i.val, Nat.lt_add_right L.coeffWidth i.isLt⟩ :
          Fin (L.factorCount + L.coeffWidth)).val < L.factorCount from i.isLt),
      zero_mul]
  rw [hsnd, add_zero]
  have hfst : ∀ i' : Fin L.factorCount,
      L.basis[Fin.castAdd L.coeffWidth i'][(⟨i.val,
          Nat.lt_add_right L.coeffWidth i.isLt⟩ :
          Fin (L.factorCount + L.coeffWidth))] *
        (periodAdjustedRowCoeffs L S t)[Fin.castAdd L.coeffWidth i']
        = (if i' = i then (1 : ℤ) else 0) * indicatorVector S i' := by
    intro i'
    rw [hentry, periodAdjustedRowCoeffs_castAdd]
    unfold Hex.bhksLatticeEntry
    rw [dif_pos (show (Fin.castAdd L.coeffWidth i').val < L.factorCount from i'.isLt),
      dif_pos (show (⟨i.val, Nat.lt_add_right L.coeffWidth i.isLt⟩ :
          Fin (L.factorCount + L.coeffWidth)).val < L.factorCount from i.isLt)]
    by_cases h : i' = i
    · subst h; simp
    · rw [if_neg h,
        if_neg (by simp only [Fin.val_castAdd]; exact fun hv => h (Fin.ext hv))]
  rw [Finset.sum_congr rfl (fun i' _ => hfst i'), Finset.sum_eq_single i]
  · rw [if_pos rfl, one_mul]
  · intro i' _ hne
    rw [if_neg hne, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Under block form, the trailing `coeffWidth` coordinates of the period-adjusted
vector are the support CLD-column sum reduced by the diagonal-period correction. -/
theorem periodAdjustedVector_coeff_of_blockForm
    {L : Hex.BhksLatticeBasis} (S : LiftedFactorSupport L)
    (hL : BhksBlockForm L) (t : Fin L.coeffWidth → ℤ) (j : Fin L.coeffWidth) :
    (periodAdjustedVector L S t)[
        (⟨L.factorCount + j.val, Nat.add_lt_add_left j.isLt L.factorCount⟩ :
          Fin (L.factorCount + L.coeffWidth))] =
      (∑ i : Fin L.factorCount,
        indicatorVector S i * (L.cldRows.getD i.val #[]).getD j.val 0)
      - (Int.ofNat (L.p ^ (L.precision - L.cutThresholds.getD j.val 0))) * t j := by
  unfold periodAdjustedVector
  rw [vecMul_getElem_eq_sum, Fin.sum_univ_add]
  have hentry : ∀ x : Fin (L.factorCount + L.coeffWidth),
      L.basis[x][(⟨L.factorCount + j.val,
          Nat.add_lt_add_left j.isLt L.factorCount⟩ :
          Fin (L.factorCount + L.coeffWidth))]
        = Hex.bhksLatticeEntry L.factorCount L.coeffWidth L.p L.precision
            L.cutThresholds L.cldRows x
            ⟨L.factorCount + j.val, Nat.add_lt_add_left j.isLt L.factorCount⟩ := by
    intro x
    rw [hL, Hex.Matrix.getElem_ofFn]
  -- First block: the indicator-weighted CLD column sum.
  have hfst : (∑ i' : Fin L.factorCount,
      L.basis[Fin.castAdd L.coeffWidth i'][(⟨L.factorCount + j.val,
          Nat.add_lt_add_left j.isLt L.factorCount⟩ :
          Fin (L.factorCount + L.coeffWidth))] *
        (periodAdjustedRowCoeffs L S t)[Fin.castAdd L.coeffWidth i'])
      = ∑ i : Fin L.factorCount,
        indicatorVector S i * (L.cldRows.getD i.val #[]).getD j.val 0 := by
    refine Finset.sum_congr rfl ?_
    intro i' _
    rw [hentry, periodAdjustedRowCoeffs_castAdd]
    have hcld : Hex.bhksLatticeEntry L.factorCount L.coeffWidth L.p L.precision
        L.cutThresholds L.cldRows (Fin.castAdd L.coeffWidth i')
        ⟨L.factorCount + j.val, Nat.add_lt_add_left j.isLt L.factorCount⟩
        = (L.cldRows.getD i'.val #[]).getD j.val 0 := by
      unfold Hex.bhksLatticeEntry
      rw [dif_pos (show (Fin.castAdd L.coeffWidth i').val < L.factorCount from i'.isLt),
        dif_neg (by
          show ¬ (⟨L.factorCount + j.val,
            Nat.add_lt_add_left j.isLt L.factorCount⟩ :
            Fin (L.factorCount + L.coeffWidth)).val < L.factorCount
          simp only []; omega)]
      simp [Fin.val_castAdd]
    rw [hcld, mul_comm]
  -- Tail block: only the diagonal row `j` survives, contributing the period term.
  have hsnd : (∑ j' : Fin L.coeffWidth,
      L.basis[Fin.natAdd L.factorCount j'][(⟨L.factorCount + j.val,
          Nat.add_lt_add_left j.isLt L.factorCount⟩ :
          Fin (L.factorCount + L.coeffWidth))] *
        (periodAdjustedRowCoeffs L S t)[Fin.natAdd L.factorCount j'])
      = - (Int.ofNat (L.p ^ (L.precision - L.cutThresholds.getD j.val 0)) * t j) := by
    rw [Finset.sum_eq_single j]
    · rw [hentry, periodAdjustedRowCoeffs_natAdd]
      have hdiag : Hex.bhksLatticeEntry L.factorCount L.coeffWidth L.p L.precision
          L.cutThresholds L.cldRows (Fin.natAdd L.factorCount j)
          ⟨L.factorCount + j.val, Nat.add_lt_add_left j.isLt L.factorCount⟩
          = Int.ofNat (L.p ^ (L.precision - L.cutThresholds.getD j.val 0)) := by
        unfold Hex.bhksLatticeEntry
        rw [dif_neg (by simp only [Fin.val_natAdd]; omega),
          dif_neg (by
            show ¬ (⟨L.factorCount + j.val,
              Nat.add_lt_add_left j.isLt L.factorCount⟩ :
              Fin (L.factorCount + L.coeffWidth)).val < L.factorCount
            simp only []; omega)]
        simp only [Fin.val_natAdd, Nat.add_sub_cancel_left, ↓reduceIte]
      rw [hdiag]; ring
    · intro j' _ hne
      rw [hentry]
      have hoff : Hex.bhksLatticeEntry L.factorCount L.coeffWidth L.p L.precision
          L.cutThresholds L.cldRows (Fin.natAdd L.factorCount j')
          ⟨L.factorCount + j.val, Nat.add_lt_add_left j.isLt L.factorCount⟩ = 0 := by
        unfold Hex.bhksLatticeEntry
        rw [dif_neg (by simp only [Fin.val_natAdd]; omega),
          dif_neg (by
            show ¬ (⟨L.factorCount + j.val,
              Nat.add_lt_add_left j.isLt L.factorCount⟩ :
              Fin (L.factorCount + L.coeffWidth)).val < L.factorCount
            simp only []; omega)]
        simp only [Fin.val_natAdd, Nat.add_sub_cancel_left]
        rw [if_neg (by
          intro hcontra
          exact hne (Fin.ext hcontra.symm))]
      rw [hoff, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [hfst, hsnd]
  ring

private theorem intSq_le_of_natAbs_le' (z : ℤ) (B : Nat) (h : z.natAbs ≤ B) :
    ((z : ℝ) ^ 2) ≤ (B : ℝ) ^ 2 := by
  have hR : (z.natAbs : ℝ) ≤ (B : ℝ) := by exact_mod_cast h
  have hsq : ((z.natAbs : ℝ) ^ 2) ≤ (B : ℝ) ^ 2 := by
    have hdiff : 0 ≤ (B : ℝ) - (z.natAbs : ℝ) := sub_nonneg.mpr hR
    have hsum : 0 ≤ (B : ℝ) + (z.natAbs : ℝ) := by positivity
    nlinarith [mul_nonneg hdiff hsum]
  rcases Int.natAbs_eq z with hz | hz
  · rw [hz]; exact hsq
  · rw [hz]; simpa using hsq

/-- Generic tight cut-radius norm bound for any support vector whose first block
is the indicator and whose tail columns satisfy `2·|colⱼ| ≤ factorCount`. -/
theorem four_mul_sq_norm_le_of_colBound
    {L : Hex.BhksLatticeBasis} (S : LiftedFactorSupport L)
    (v : Vector ℤ (L.factorCount + L.coeffWidth))
    (hfirst : ∀ i : Fin L.factorCount,
      (v[(⟨i.val, Nat.lt_add_right L.coeffWidth i.isLt⟩ :
        Fin (L.factorCount + L.coeffWidth))] : ℤ) = indicatorVector S i)
    (hcol : ∀ j : Fin L.coeffWidth,
      2 * (v[Fin.natAdd L.factorCount j] : ℤ).natAbs ≤ L.factorCount) :
    4 * (∑ i : Fin (L.factorCount + L.coeffWidth), (((v[i] : ℤ) : ℝ) ^ 2))
      ≤ (Hex.bhksCutRadiusSq4 L : ℝ) := by
  rw [Fin.sum_univ_add, mul_add]
  have hcast : ∀ i : Fin L.factorCount,
      (v[Fin.castAdd L.coeffWidth i] : ℤ) = indicatorVector S i := fun i => hfirst i
  have hfirst' : (∑ i : Fin L.factorCount,
      (((v[Fin.castAdd L.coeffWidth i] : ℤ) : ℝ) ^ 2)) ≤ (L.factorCount : ℝ) := by
    have heq : (∑ i : Fin L.factorCount,
        (((v[Fin.castAdd L.coeffWidth i] : ℤ) : ℝ) ^ 2))
        = ∑ i : Fin L.factorCount, (((indicatorVector S i : ℤ) : ℝ) ^ 2) :=
      Finset.sum_congr rfl (fun i _ => by rw [hcast i])
    rw [heq]
    exact indicatorVector_sq_sum_le_factorCount S
  have hfirst4 : 4 * (∑ i : Fin L.factorCount,
      (((v[Fin.castAdd L.coeffWidth i] : ℤ) : ℝ) ^ 2))
      ≤ 4 * (L.factorCount : ℝ) := by linarith
  have htail : 4 * (∑ j : Fin L.coeffWidth,
        (((v[Fin.natAdd L.factorCount j] : ℤ) : ℝ) ^ 2))
      ≤ (L.coeffWidth * L.factorCount * L.factorCount : ℝ) := by
    rw [Finset.mul_sum]
    calc
      (∑ j : Fin L.coeffWidth,
          4 * (((v[Fin.natAdd L.factorCount j] : ℤ) : ℝ) ^ 2))
          ≤ ∑ _j : Fin L.coeffWidth, ((L.factorCount : ℝ) ^ 2) := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            set z : ℤ := (v[Fin.natAdd L.factorCount j] : ℤ) with hz
            have hnat : (2 * z).natAbs ≤ L.factorCount := by
              rw [Int.natAbs_mul]; simpa [hz] using hcol j
            have hsq := intSq_le_of_natAbs_le' (2 * z) L.factorCount hnat
            have hexpand : (((2 * z : ℤ)) : ℝ) ^ 2 = 4 * ((z : ℤ) : ℝ) ^ 2 := by
              push_cast; ring
            rw [hexpand] at hsq
            exact hsq
      _ = (L.coeffWidth * L.factorCount * L.factorCount : ℝ) := by
            simp [pow_two, mul_assoc]
  refine (add_le_add hfirst4 htail).trans (le_of_eq ?_)
  unfold Hex.bhksCutRadiusSq4
  push_cast
  ring

/-- **Period-adjusted true-factor short vector from a `RecoveredLift` (issue
#7876).**  In the monic regime, the aggregate residue bridge
(`recoveredLift_aggregate_residue`) and the period-aware carry lemma
(`two_mul_natAbs_sum_psiCut_period_le`) bound each tail column of the
period-adjusted vector by `factorCount/2`.  Together with the structural project
and lattice-membership facts, this yields a `SupportShortVectorData` for the
recovered support — the genuine aggregate-tail lattice path the period trap
(#7866/#7867) forces, feeding the fast-disjunct consumer through
`cutProjectionHypotheses_of_shortVectors`. -/
def supportShortVectorData_of_recoveredLift
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (D : RecoveredLift L S)
    (hf_lc : Hex.DensePoly.leadingCoeff D.f = 1)
    (hfactor_monic : (HexPolyMathlib.toPolynomial D.factor).Monic)
    (hp : 2 ≤ D.p)
    (hk : 1 < D.p ^ D.a)
    (hsep : ∀ j, 2 * Hex.bhksCoeffBound D.f j < D.p ^ D.a)
    (hthr : ∀ j, Hex.bhksCoeffCutThreshold D.p D.f j ≤ D.a)
    (hfac : ∀ i : Fin L.factorCount, i ∈ S →
        ∃ h : Hex.ZPoly,
          Hex.DensePoly.Monic (L.liftedFactors.getD i.val 1) ∧
          0 < (L.liftedFactors.getD i.val 1).degree?.getD 0 ∧
          Hex.ZPoly.congr D.f ((L.liftedFactors.getD i.val 1) * h) (D.p ^ D.a)) :
    SupportShortVectorData L S := by
  classical
  -- Per-column cut-modulus separation `2·B < p^ℓⱼ`.
  have hsep_b : ∀ j : Fin L.coeffWidth,
      2 * Hex.bhksCoeffBound D.f j.val < D.p ^ Hex.bhksCoeffCutThreshold D.p D.f j.val := by
    intro j
    have hcut := Hex.le_pow_ceilLogP hp (2 * Hex.bhksCoeffBound D.f j.val + 1)
    have hcut2 : 2 * Hex.bhksCoeffBound D.f j.val + 1
        ≤ D.p ^ Hex.bhksCoeffCutThreshold D.p D.f j.val := hcut
    omega
  -- Per-column period existential from the aggregate residue and carry lemma.
  have hperiod : ∀ j : Fin L.coeffWidth, ∃ tj : ℤ,
      2 * (((∑ i ∈ Finset.univ.filter (fun i => i ∈ S),
          Hex.psiCut D.p D.a (Hex.bhksCoeffCutThreshold D.p D.f j.val)
            ((Hex.cldQuotientMod D.f (L.liftedFactors.getD i.val 1) D.p D.a).coeff j.val))
        - tj * (D.p ^ (D.a - Hex.bhksCoeffCutThreshold D.p D.f j.val) : Int))).natAbs
        ≤ (Finset.univ.filter (fun i => i ∈ S)).card := by
    intro j
    obtain ⟨hres, hbnd⟩ :=
      recoveredLift_aggregate_residue D hf_lc hfactor_monic hk hsep hfac j.val
    exact two_mul_natAbs_sum_psiCut_period_le
      (Finset.univ.filter (fun i => i ∈ S)) D.p D.a
      (Hex.bhksCoeffCutThreshold D.p D.f j.val) (hthr j.val) (by omega)
      (fun i => (Hex.cldQuotientMod D.f (L.liftedFactors.getD i.val 1) D.p D.a).coeff j.val)
      ((phi (HexPolyMathlib.toPolynomial D.f)
        (HexPolyMathlib.toPolynomial D.factor)).coeff j.val)
      (Hex.bhksCoeffBound D.f j.val) hres hbnd (hsep_b j)
  set t : Fin L.coeffWidth → ℤ := fun j => Classical.choose (hperiod j) with ht_def
  have ht : ∀ j : Fin L.coeffWidth,
      2 * (((∑ i ∈ Finset.univ.filter (fun i => i ∈ S),
          Hex.psiCut D.p D.a (Hex.bhksCoeffCutThreshold D.p D.f j.val)
            ((Hex.cldQuotientMod D.f (L.liftedFactors.getD i.val 1) D.p D.a).coeff j.val))
        - t j * (D.p ^ (D.a - Hex.bhksCoeffCutThreshold D.p D.f j.val) : Int))).natAbs
        ≤ (Finset.univ.filter (fun i => i ∈ S)).card :=
    fun j => Classical.choose_spec (hperiod j)
  have hcard : (Finset.univ.filter (fun i => i ∈ S)).card ≤ L.factorCount := by
    calc (Finset.univ.filter (fun i => i ∈ S)).card
          ≤ (Finset.univ : Finset (Fin L.factorCount)).card := Finset.card_filter_le _ _
      _ = L.factorCount := by simp
  -- Each tail coordinate of the period-adjusted vector is the period-reduced cut.
  have hcoord_eq : ∀ j : Fin L.coeffWidth,
      ((periodAdjustedVector L S t)[Fin.natAdd L.factorCount j] : ℤ)
        = (∑ i ∈ Finset.univ.filter (fun i => i ∈ S),
            Hex.psiCut D.p D.a (Hex.bhksCoeffCutThreshold D.p D.f j.val)
              ((Hex.cldQuotientMod D.f (L.liftedFactors.getD i.val 1) D.p D.a).coeff j.val))
          - t j * (D.p ^ (D.a - Hex.bhksCoeffCutThreshold D.p D.f j.val) : Int) := by
    intro j
    have hjlt : j.val < D.f.degree?.getD 0 := j.isLt.trans_eq D.coeffWidth_eq
    have hcoord := periodAdjustedVector_coeff_of_blockForm S D.blockForm t j
    rw [show ((periodAdjustedVector L S t)[Fin.natAdd L.factorCount j] : ℤ)
        = (periodAdjustedVector L S t)[(⟨L.factorCount + j.val,
            Nat.add_lt_add_left j.isLt L.factorCount⟩ :
            Fin (L.factorCount + L.coeffWidth))] from rfl, hcoord]
    have hLp : L.p = D.p := D.p_eq
    have hLprec : L.precision = D.a := D.precision_eq
    have hLthr : L.cutThresholds.getD j.val 0 = Hex.bhksCoeffCutThreshold D.p D.f j.val := by
      rw [D.cutThresholds_eq, bhksCutThresholds_getD_of_lt D.f D.p j.val hjlt]
    simp only [hLp, hLprec, hLthr]
    congr 1
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hi : i ∈ S
      · rw [indicatorVector_apply_mem S hi, one_mul, if_pos hi]
        have hLcld : (L.cldRows.getD i.val #[]).getD j.val 0
            = (Hex.cldCoeffs D.f D.p D.a (L.liftedFactors.getD i.val 1)).getD j.val 0 := by
          congr 1
          rw [D.cldRows_eq, D.liftedFactors_eq]
          have hsz : i.val < D.liftedFactors.size := i.isLt.trans_eq D.factorCount_eq
          simp [Array.getD, hsz]
        rw [hLcld,
          Hex.cldCoeffs_getD_of_lt D.f D.p D.a (L.liftedFactors.getD i.val 1) j.val hjlt]
      · rw [indicatorVector_apply_not_mem S hi, zero_mul, if_neg hi]
    · rw [Int.ofNat_eq_natCast, Nat.cast_pow]
      ring
  refine
    { vector := periodAdjustedVector L S t
      memLattice := periodAdjustedVector_memLattice L S t
      project_eq := fun i => periodAdjustedVector_project_of_blockForm S D.blockForm t i
      four_mul_sq_norm_le := ?_ }
  refine four_mul_sq_norm_le_of_colBound S (periodAdjustedVector L S t)
    (fun i => periodAdjustedVector_project_of_blockForm S D.blockForm t i)
    (fun j => ?_)
  rw [hcoord_eq j]
  exact le_trans (ht j) hcard

end BHKS

end

end HexBerlekampZassenhausMathlib
