import HexPolyZMathlib.Mignotte
import HexPolyZMathlib.RobinsonForm
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Data.Nat.Choose.Bounds

/-!
BHKS CLD-column coefficient bounds.

This file isolates the exact integer-polynomial `Phi` column used in BHKS
Lemma 5.1.  The main coefficient theorem is deliberately conditional on a
Mahler-measure bound for `Phi`; this is the replacement analytic obligation for
the invalid unconditional derivative estimate.
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

end

end HexBerlekampZassenhausMathlib
