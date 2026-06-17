import HexBerlekampZassenhaus
import HexBerlekampZassenhausMathlib.BadVectorAuxiliary
import HexBerlekampZassenhausMathlib.Resultant
import HexHenselMathlib.Correctness
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
  have hcld : Hex.cldQuotientMod input g p k = Hex.ZPoly.reduceModPow q p k := rfl
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
Semantic `TrueFactorLift` packages supply exactly the hypotheses needed to
interpret a selected executable CLD quotient as a logarithmic-derivative column
modulo the Hensel precision.
-/
theorem TrueFactorLiftSemantics.selected_cldQuotientMod_congr_mul_derivative
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (D : TrueFactorLift L S) (H : TrueFactorLiftSemantics D)
    (hk : 1 < D.p ^ D.a)
    (i : Fin L.factorCount) (hi : i ∈ S) :
    Hex.ZPoly.congr
      ((D.liftedFactors.getD i.val 1) *
        Hex.cldQuotientMod D.f (D.liftedFactors.getD i.val 1) D.p D.a)
      (D.f * Hex.DensePoly.derivative (D.liftedFactors.getD i.val 1))
      (D.p ^ D.a) :=
  cldQuotientMod_congr_mul_derivative D.f (D.liftedFactors.getD i.val 1)
    (H.selectedCofactor i hi) D.p D.a hk
    (H.selected_monic i hi)
    (H.selected_pos_degree i hi)
    (H.selected_congr i hi)

end BHKS

/--
ZPoly → `Polynomial ℤ` bridge for the CLD-syzygy resultant valuation.

Given the executable coefficientwise congruence
`g * q ≡ input * q'  (mod p ^ k)` — exactly the shape produced by
`cldQuotientMod_congr_mul_derivative`, with `g = cldQuotientMod input q p k`
the CLD-column quotient of the selected monic factor `q` — the transported
polynomials satisfy the syzygy `(toPolynomial g) * (toPolynomial q)
- (toPolynomial input) * (toPolynomial q)' = C (p ^ k) * z`. Feeding it to
`cld_syzygy_pow_dvd_resultant` yields `p ^ (k * d)` dividing the integer
resultant of `toPolynomial input` and `toPolynomial g`, with no hypothesis that
`q` divides `g` modulo `p ^ k`.

The conclusion is about `resultant input g` where `g` is the CLD-column
quotient. Identifying `g` with the BHKS bad-vector auxiliary polynomial
`auxiliaryPolynomialWithCorrections` — a *combination*
`Σᵢ vec i • cldCoeffs i` of the per-factor CLD columns, not a single
`cldQuotientMod` — is a separate modular-reduction step the downstream
bad-vector wiring (#6949) must supply; this lemma only transports the
per-factor syzygy of one selected factor.
-/
theorem cld_syzygy_pow_dvd_resultant_of_congr
    (input g q : Hex.ZPoly) {p k d : Nat}
    (hq_monic : (HexPolyMathlib.toPolynomial q).Monic)
    (hq_deg : (HexPolyMathlib.toPolynomial q).natDegree = d)
    (hcongr : Hex.ZPoly.congr (g * q) (input * Hex.DensePoly.derivative q) (p ^ k))
    (hf_deg : 2 * d ≤ (HexPolyMathlib.toPolynomial input).natDegree)
    (hg_deg : 2 * d ≤ (HexPolyMathlib.toPolynomial g).natDegree + 1) :
    ((p ^ (k * d) : Nat) : ℤ) ∣
      Polynomial.resultant (HexPolyMathlib.toPolynomial input)
        (HexPolyMathlib.toPolynomial g) := by
  -- The transported difference is `C (p ^ k)`-divisible, coefficient by coefficient.
  have hdvd : Polynomial.C ((p ^ k : Nat) : ℤ) ∣
      (HexPolyMathlib.toPolynomial (g * q)
        - HexPolyMathlib.toPolynomial (input * Hex.DensePoly.derivative q)) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro j
    rw [Polynomial.coeff_sub, HexPolyMathlib.coeff_toPolynomial,
      HexPolyMathlib.coeff_toPolynomial]
    exact Int.dvd_of_emod_eq_zero (hcongr j)
  obtain ⟨z, hz⟩ := hdvd
  -- Repackage as the `Polynomial ℤ` CLD syzygy and apply the resultant valuation.
  have hsyz : HexPolyMathlib.toPolynomial g * HexPolyMathlib.toPolynomial q
      - HexPolyMathlib.toPolynomial input
          * Polynomial.derivative (HexPolyMathlib.toPolynomial q)
      = Polynomial.C ((p ^ k : Nat) : ℤ) * z := by
    rw [← HexPolyMathlib.toPolynomial_mul, ← HexPolyMathlib.toPolynomial_derivative,
      ← HexPolyMathlib.toPolynomial_mul]
    exact hz
  exact cld_syzygy_pow_dvd_resultant (HexPolyMathlib.toPolynomial input)
    (HexPolyMathlib.toPolynomial g) (HexPolyMathlib.toPolynomial q) z
    hq_monic hq_deg hsyz hf_deg hg_deg

namespace BHKS

/--
Coefficient-level CLD bridge for the corrected BHKS auxiliary polynomial.

The first component is the high/low cut decomposition of the scaled auxiliary
coefficient.  The second component records the semantic content of every
`cldQuotientMod` term appearing in that decomposition: after multiplication by
the corresponding lifted factor, the executable quotient is congruent to the
logarithmic-derivative numerator modulo `p ^ k`.

This is the form needed by the later Sylvester-column argument.  It keeps the
per-coordinate cut weight and the diagonal correction term explicit, and it
does not assert the false statement that a lifted factor divides the auxiliary
polynomial itself modulo `p ^ k`.
-/
theorem auxCutBridge
    (input : Hex.ZPoly) (liftData : Hex.LiftData)
    (vec corrections : Array Int) (j : Nat)
    (hj : j < input.degree?.getD 0)
    (hb : liftData.p ^ Hex.bhksCoeffCutThreshold liftData.p input j ≠ 0)
    (hk : 1 < liftData.p ^ liftData.k)
    (hfac :
      ∀ i, i ∈ List.range liftData.liftedFactors.size →
        ∃ h : Hex.ZPoly,
          Hex.DensePoly.Monic (liftData.liftedFactors.getD i 0) ∧
          0 < (liftData.liftedFactors.getD i 0).degree?.getD 0 ∧
          Hex.ZPoly.congr input ((liftData.liftedFactors.getD i 0) * h)
            (liftData.p ^ liftData.k)) :
    ((liftData.p ^ Hex.bhksCoeffCutThreshold liftData.p input j : Nat) : Int) *
        (auxiliaryPolynomialWithCorrections input liftData vec corrections).coeff j =
      (List.range liftData.liftedFactors.size).foldl
        (fun acc i =>
          acc + vec.getD i 0 *
            (Hex.centeredResiduePow liftData.p liftData.k
                ((Hex.cldQuotientMod input (liftData.liftedFactors.getD i 0)
                    liftData.p liftData.k).coeff j) -
              Hex.centeredResiduePow liftData.p
                  (Hex.bhksCoeffCutThreshold liftData.p input j)
                  (Hex.centeredResiduePow liftData.p liftData.k
                    ((Hex.cldQuotientMod input (liftData.liftedFactors.getD i 0)
                        liftData.p liftData.k).coeff j)))) 0 -
        corrections.getD j 0 *
            Int.ofNat (liftData.p ^
              (liftData.k - Hex.bhksCoeffCutThreshold liftData.p input j)) *
            ((liftData.p ^ Hex.bhksCoeffCutThreshold liftData.p input j : Nat) : Int) ∧
      ∀ i, i ∈ List.range liftData.liftedFactors.size →
        Hex.ZPoly.congr
          ((liftData.liftedFactors.getD i 0) *
            Hex.cldQuotientMod input (liftData.liftedFactors.getD i 0)
              liftData.p liftData.k)
          (input * Hex.DensePoly.derivative (liftData.liftedFactors.getD i 0))
          (liftData.p ^ liftData.k) := by
  constructor
  · exact coeff_auxiliaryPolynomialWithCorrections_high_decomp
      input liftData vec corrections j hj hb
  · intro i hi
    rcases hfac i hi with ⟨h, hg_monic, hg_deg, hdvd⟩
    exact cldQuotientMod_congr_mul_derivative input
      (liftData.liftedFactors.getD i 0) h liftData.p liftData.k
      hk hg_monic hg_deg hdvd

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

/-- **Product-side CLD aggregation.**  If every factor `q` in a list satisfies
the per-factor logarithmic-derivative congruence `q * cld q ≡ f * q'  (mod m)` —
the shape produced by `cldQuotientMod_congr_mul_derivative` with
`cld q = cldQuotientMod f q p k` — then the ordered product `∏ qs` satisfies the
aggregated congruence `(∏ qs) * Σ (cld qs) ≡ f * (∏ qs)'  (mod m)`.

This is the polynomial-level core of the BHKS product CLD column identity: the
logarithmic derivative of a product is the sum of the per-factor logarithmic
derivatives.  The proof maps to `Polynomial ℤ`, where `Polynomial.C (m : ℤ) ∣ ·`
is an ideal and `Polynomial.derivative_mul` supplies the Leibniz rule. -/
theorem polyProduct_cld_aggregation
    (f : Hex.ZPoly) (m : Nat) (cld : Hex.ZPoly → Hex.ZPoly) :
    ∀ qs : List Hex.ZPoly,
      (∀ q ∈ qs, Hex.ZPoly.congr (q * cld q)
        (f * Hex.DensePoly.derivative q) m) →
      Hex.ZPoly.congr
        (Array.polyProduct qs.toArray * (qs.map cld).foldr (· + ·) 0)
        (f * Hex.DensePoly.derivative (Array.polyProduct qs.toArray)) m := by
  intro qs
  induction qs with
  | nil =>
    intro _
    apply congr_of_C_dvd_toPolynomial_sub
    have hp : Array.polyProduct ([] : List Hex.ZPoly).toArray = 1 := rfl
    rw [hp]
    simp only [List.map_nil, List.foldr_nil, HexPolyMathlib.toPolynomial_mul,
      HexPolyMathlib.toPolynomial_derivative, HexPolyMathlib.toPolynomial_one,
      HexPolyMathlib.toPolynomial_zero, Polynomial.derivative_one, mul_zero,
      sub_zero]
    exact dvd_zero _
  | cons q rest ih =>
    intro hper
    have hq : Hex.ZPoly.congr (q * cld q) (f * Hex.DensePoly.derivative q) m :=
      hper q (by simp)
    have hrest : ∀ q' ∈ rest, Hex.ZPoly.congr (q' * cld q')
        (f * Hex.DensePoly.derivative q') m :=
      fun q' hq' => hper q' (List.mem_cons_of_mem q hq')
    have IHc := ih hrest
    have Dq := C_dvd_toPolynomial_sub_of_congr _ _ m hq
    have Dr := C_dvd_toPolynomial_sub_of_congr _ _ m IHc
    rw [Hex.ZPoly.polyProduct_cons_toArray]
    simp only [List.map_cons, List.foldr_cons]
    apply congr_of_C_dvd_toPolynomial_sub
    have key :
        HexPolyMathlib.toPolynomial
            (q * Array.polyProduct rest.toArray *
              (cld q + (rest.map cld).foldr (· + ·) 0))
          - HexPolyMathlib.toPolynomial
              (f * Hex.DensePoly.derivative (q * Array.polyProduct rest.toArray))
          = HexPolyMathlib.toPolynomial (Array.polyProduct rest.toArray) *
              (HexPolyMathlib.toPolynomial (q * cld q)
                - HexPolyMathlib.toPolynomial (f * Hex.DensePoly.derivative q))
            + HexPolyMathlib.toPolynomial q *
              (HexPolyMathlib.toPolynomial
                  (Array.polyProduct rest.toArray * (rest.map cld).foldr (· + ·) 0)
                - HexPolyMathlib.toPolynomial
                    (f * Hex.DensePoly.derivative (Array.polyProduct rest.toArray))) := by
      simp only [HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_add,
        HexPolyMathlib.toPolynomial_derivative, Polynomial.derivative_mul]
      ring
    rw [key]
    exact dvd_add (Dq.mul_left _) (Dr.mul_left _)

open Classical in
/-- Product-side CLD aggregation specialised to the selected support of a
`TrueFactorLift`.  The selected support product satisfies the aggregated
logarithmic-derivative congruence against the sum of the per-selected-factor CLD
quotients, with all per-factor hypotheses discharged from the semantic package.

This is the interface form consumed by the tight `psiCut` / `TightColumnBound`
column estimate: it identifies the executable column sum
`Σᵢ cldQuotientMod f gᵢ` (before centring) with `f · (∏ gᵢ)' / (∏ gᵢ)` modulo
the Hensel precision. -/
theorem TrueFactorLiftSemantics.supportProduct_cld_aggregation
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (D : TrueFactorLift L S) (H : TrueFactorLiftSemantics D)
    (hk : 1 < D.p ^ D.a) :
    Hex.ZPoly.congr
      (supportProduct L S *
        ((((List.finRange L.factorCount).filter fun i => decide (i ∈ S)).map
            fun i => L.liftedFactors.getD i.val 1).map
          (fun q => Hex.cldQuotientMod D.f q D.p D.a)).foldr (· + ·) 0)
      (D.f * Hex.DensePoly.derivative (supportProduct L S))
      (D.p ^ D.a) := by
  have hsp : supportProduct L S =
      Array.polyProduct
        (((List.finRange L.factorCount).filter fun i => decide (i ∈ S)).map
          fun i => L.liftedFactors.getD i.val 1).toArray := rfl
  rw [hsp]
  apply polyProduct_cld_aggregation D.f (D.p ^ D.a)
    (fun q => Hex.cldQuotientMod D.f q D.p D.a)
  intro q hq
  rw [List.mem_map] at hq
  obtain ⟨i, hi_mem, rfl⟩ := hq
  rw [List.mem_filter] at hi_mem
  have hiS : i ∈ S := by simpa using hi_mem.2
  rw [D.liftedFactors_eq]
  exact TrueFactorLiftSemantics.selected_cldQuotientMod_congr_mul_derivative D H hk i hiS

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
**BHKS Lemma 5.7 high-bit estimate (carry core).**  The sum over a finite index
set of the high-bit cuts `Psi^a_b(z i)` is bounded in magnitude by half the
cardinality: `2·|Σ Psi^a_b(z i)| ≤ |T|`.

The hypotheses pin the per-element ambient centred residue to an exact integer
`w i` (`hw`), whose support sum is a small integer `y` with `|y| ≤ B` and
`2·B < p^b` (`hsum`/`hy`/`hsep`).  This is exactly the cancellation that makes
the *aggregated* column small even though individual high-bit cuts `Psi^a_b(z i)`
need not be: the per-element loose bound `|Psi^a_b(z i)| ≤ B` is *not* used and
would not give the tight `|T|/2` shape.
-/
theorem two_mul_natAbs_sum_psiCut_le
    {ι : Type*} (T : Finset ι) (p a b : Nat) (hpb : 0 < p ^ b)
    (z w : ι → Int) (y : Int) (B : Nat)
    (hw : ∀ i ∈ T, Hex.centeredResiduePow p a (z i) = w i)
    (hsum : ∑ i ∈ T, w i = y)
    (hy : y.natAbs ≤ B)
    (hsep : 2 * B < p ^ b) :
    2 * (∑ i ∈ T, Hex.psiCut p a b (z i)).natAbs ≤ T.card := by
  classical
  have hm0 : (p ^ b : Nat) ≠ 0 := hpb.ne'
  set col : Int := ∑ i ∈ T, Hex.psiCut p a b (z i) with hcol
  set lo : ι → Int := fun i => Hex.centeredResiduePow p b (w i) with hlodef
  -- Per element: `p^b · Psi(z i) = w i - lo i`.
  have hkey : ∀ i ∈ T, ((p ^ b : Nat) : Int) * Hex.psiCut p a b (z i) = w i - lo i := by
    intro i hi
    have hdec := Hex.centeredResiduePow_add_pow_mul_psiCut p a b (z i) hm0
    rw [hw i hi] at hdec
    simp only [hlodef]
    linarith [hdec]
  -- Aggregate: `p^b · col = y - Σ lo`.
  have hagg : ((p ^ b : Nat) : Int) * col = y - ∑ i ∈ T, lo i := by
    rw [hcol, Finset.mul_sum, Finset.sum_congr rfl hkey, Finset.sum_sub_distrib, hsum]
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
  -- Combine into `2 · p^b · |col| < (|T| + 1) · p^b`, then cancel `p^b`.
  have hyZ : 2 * |y| ≤ 2 * (B : Int) := by
    have : |y| ≤ (B : Int) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hy
    linarith
  have habs : ((p ^ b : Nat) : Int) * |col| = |y - ∑ i ∈ T, lo i| := by
    rw [← hagg, abs_mul]; congr 1
    rw [Int.abs_eq_natAbs]; simp
  have hstep : 2 * (((p ^ b : Nat) : Int) * |col|) ≤ 2 * (B : Int) + (T.card : Int) * (p ^ b : Nat) := by
    rw [habs]
    calc 2 * |y - ∑ i ∈ T, lo i| ≤ 2 * (|y| + |∑ i ∈ T, lo i|) := by
            linarith [abs_sub y (∑ i ∈ T, lo i)]
      _ = 2 * |y| + 2 * |∑ i ∈ T, lo i| := by ring
      _ ≤ 2 * (B : Int) + (T.card : Int) * (p ^ b : Nat) := by linarith
  -- `2·B < p^b` upgrades the bound to a strict one and cancels the factor `p^b`.
  have hsepZ : 2 * (B : Int) < ((p ^ b : Nat) : Int) := by exact_mod_cast hsep
  have hpbZ : (0 : Int) < ((p ^ b : Nat) : Int) := by exact_mod_cast hpb
  have hcolNat : 2 * |col| ≤ (T.card : Int) := by
    have hlt2 : ((p ^ b : Nat) : Int) * (2 * |col|) <
        ((p ^ b : Nat) : Int) * ((T.card : Int) + 1) := by
      nlinarith [hstep, hsepZ, hpbZ]
    have h2N : 2 * |col| < (T.card : Int) + 1 := lt_of_mul_lt_mul_left hlt2 (le_of_lt hpbZ)
    omega
  have : (2 * col.natAbs : Int) ≤ (T.card : Int) := by
    rw [Int.abs_eq_natAbs] at hcolNat; push_cast at hcolNat ⊢; linarith
  exact_mod_cast this

end BHKS

end

end HexBerlekampZassenhausMathlib
