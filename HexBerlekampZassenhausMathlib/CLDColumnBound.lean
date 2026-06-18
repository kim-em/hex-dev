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

/--
Product logarithmic-derivative sum identity over a selected support.

`supportProduct L S` is `∏_{i ∈ S} gᵢ` and `supportCldSum L S f p a` is
`Σ_{i ∈ S} (f · gᵢ' / gᵢ mod pᵃ)`; this says their product is congruent modulo
`pᵃ` to `f · (∏_{i ∈ S} gᵢ)'`.  It feeds the executable per-factor CLD
congruence (`selected_cldQuotientMod_congr_mul_derivative`) through the generic
list aggregation, and is the column-wise statement the tight-column work
(`#7651`) consumes: reading off coefficient `j` gives the pre-`psiCut`
true-factor CLD column entry, tied to the genuine product factor rather than to
an arbitrary lattice vector.
-/
theorem TrueFactorLiftSemantics.supportProduct_cldSum_congr
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (D : TrueFactorLift L S) (H : TrueFactorLiftSemantics D)
    (hk : 1 < D.p ^ D.a) :
    Hex.ZPoly.congr
      (supportProduct L S * supportCldSum L S D.f D.p D.a)
      (D.f * Hex.DensePoly.derivative (supportProduct L S))
      (D.p ^ D.a) := by
  classical
  have hfilter_mem : ∀ i ∈ (List.finRange L.factorCount).filter
        (fun i => decide (i ∈ S)), i ∈ S := by
    intro i hi
    rw [List.mem_filter] at hi
    exact of_decide_eq_true hi.2
  have hyps : ∀ g ∈ ((List.finRange L.factorCount).filter
        (fun i => decide (i ∈ S))).map (fun i => L.liftedFactors.getD i.val 1),
      Hex.ZPoly.congr (g * Hex.cldQuotientMod D.f g D.p D.a)
        (D.f * Hex.DensePoly.derivative g) (D.p ^ D.a) := by
    intro g hg
    rw [List.mem_map] at hg
    obtain ⟨i, hi_mem, rfl⟩ := hg
    have hi : i ∈ S := hfilter_mem i hi_mem
    rw [TrueFactorLift.liftedFactors_eq D]
    exact TrueFactorLiftSemantics.selected_cldQuotientMod_congr_mul_derivative D H hk i hi
  have key := congr_polyProduct_mul_listSum_derivative D.f
    (fun g => Hex.cldQuotientMod D.f g D.p D.a) (D.p ^ D.a)
    (((List.finRange L.factorCount).filter (fun i => decide (i ∈ S))).map
      (fun i => L.liftedFactors.getD i.val 1)) hyps
  rw [List.map_map] at key
  exact key

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
        ≤ T.card + 1 := by
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
  have hdNat : 2 * |d| ≤ (T.card : Int) + 1 := by
    have hlt2 : ((p ^ b : Nat) : Int) * (2 * |d|) <
        ((p ^ b : Nat) : Int) * ((T.card : Int) + 1) := by
      nlinarith [hstep, hsepZ, hpbZ]
    have h2N : 2 * |d| < (T.card : Int) + 1 := lt_of_mul_lt_mul_left hlt2 (le_of_lt hpbZ)
    omega
  have hfin : (2 * d.natAbs : Int) ≤ (T.card : Int) + 1 := by
    rw [Int.abs_eq_natAbs] at hdNat; push_cast at hdNat ⊢; linarith
  exact_mod_cast hfin

/-- The executable Pascal-recursion `Hex.Nat.choose` agrees with Mathlib's
`Nat.choose`; needed because `Hex.bhksCoeffBound` elaborates `Nat.choose` to the
executable shadow inside `namespace Hex`. -/
private theorem hex_choose_eq (n k : Nat) : Hex.Nat.choose n k = Nat.choose n k := by
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

/-- **Per-factor CLD residue bridge (issue deliverable 1).**  For a monic divisor
`g` of `f` whose precision `p^a` separates the Mignotte column bound, the centred
ambient residue of the executable CLD quotient coefficient is exactly the integer
`Phi`-column coefficient. -/
theorem residue_cldQuotientMod_eq_phi_coeff
    (f g : Hex.ZPoly) (p a j : Nat)
    (hg_monic : (HexPolyMathlib.toPolynomial g).Monic)
    (hgf : HexPolyMathlib.toPolynomial g ∣ HexPolyMathlib.toPolynomial f)
    (hsep : 2 * Hex.bhksCoeffBound f j < p ^ a)
    (hcongr : Hex.ZPoly.congr (g * Hex.cldQuotientMod f g p a)
        (f * Hex.DensePoly.derivative g) (p ^ a)) :
    Hex.centeredResiduePow p a ((Hex.cldQuotientMod f g p a).coeff j)
      = (phi (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)).coeff j := by
  obtain ⟨hpoly, hHpoly⟩ := hgf
  have hphi : phi (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)
      = hpoly * (HexPolyMathlib.toPolynomial g).derivative :=
    phi_eq_factor_mul_derivative _ _ hpoly hg_monic hHpoly
  have hC := C_dvd_toPolynomial_sub_of_congr (g * Hex.cldQuotientMod f g p a)
      (f * Hex.DensePoly.derivative g) (p ^ a) hcongr
  rw [HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_mul,
      HexPolyMathlib.toPolynomial_derivative] at hC
  have hfeq :
      (HexPolyMathlib.toPolynomial g * HexPolyMathlib.toPolynomial (Hex.cldQuotientMod f g p a)
        - HexPolyMathlib.toPolynomial f * (HexPolyMathlib.toPolynomial g).derivative)
      = HexPolyMathlib.toPolynomial g *
          (HexPolyMathlib.toPolynomial (Hex.cldQuotientMod f g p a)
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
        = (Hex.cldQuotientMod f g p a).coeff j % ((p ^ a : Nat) : Int) :=
    Int.modEq_iff_dvd.mpr hj
  exact Hex.centeredResiduePow_eq_of_natAbs_le p a _ _ (Hex.bhksCoeffBound f j)
    (abs_phi_coeff_le_bhksCoeffBound f g j hg_monic ⟨hpoly, hHpoly⟩) hsep hcongr_emod

/-- **Exact log-derivative support sum (issue deliverable 2).**  Over
`Polynomial ℤ`, the sum of the per-factor `Phi`-columns equals the `Phi`-column of
their product, for monic factors whose product divides `F`.  This is the Leibniz
product rule for `Phi`, with the leave-one-out cofactors supplied by
`Polynomial.derivative_prod_finset`. -/
theorem phi_sum_eq_phi_prod {ι : Type*} [DecidableEq ι]
    (F : Polynomial ℤ) (T : Finset ι) (P : ι → Polynomial ℤ)
    (hmonic : ∀ i ∈ T, (P i).Monic)
    (hdvd : (∏ i ∈ T, P i) ∣ F) :
    ∑ i ∈ T, phi F (P i) = phi F (∏ i ∈ T, P i) := by
  obtain ⟨C, hC⟩ := hdvd
  have hQ_monic : (∏ i ∈ T, P i).Monic := Polynomial.monic_prod_of_monic T P hmonic
  have hphiQ : phi F (∏ i ∈ T, P i) = C * (∏ i ∈ T, P i).derivative :=
    phi_eq_factor_mul_derivative F (∏ i ∈ T, P i) C hQ_monic hC
  have heach : ∀ i ∈ T, phi F (P i) = (C * ∏ k ∈ T.erase i, P k) * (P i).derivative := by
    intro i hi
    have hF : F = (P i) * (C * ∏ k ∈ T.erase i, P k) := by
      rw [hC, ← Finset.mul_prod_erase T P hi]; ring
    exact phi_eq_factor_mul_derivative F (P i) (C * ∏ k ∈ T.erase i, P k) (hmonic i hi) hF
  rw [Finset.sum_congr rfl heach, hphiQ, Polynomial.derivative_prod_finset, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

open Classical in
/-- **Tight BHKS CLD column bound (issue capstone).**  A genuine true-factor lift
package yields the tight per-column estimate `2·|col j| ≤ factorCount`.  The bound
is an aggregation phenomenon: each high-bit cut can be large, but the support sum
of the exact `Phi`-columns is a single Mignotte-bounded integer
(`phi_sum_eq_phi_prod`), so the carry-cancellation core
`two_mul_natAbs_sum_psiCut_le` collapses the column to half the support size. -/
theorem tightColumnBound_of_lift
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (D : TrueFactorLift L S)
    (H : TrueFactorLiftSemantics D)
    (hp : 2 ≤ D.p)
    (hk : 1 < D.p ^ D.a)
    (hsep : ∀ j, 2 * Hex.bhksCoeffBound D.f j < D.p ^ D.a) :
    TightColumnBound L S D := by
  classical
  refine ⟨fun j => ?_⟩
  set T : Finset (Fin L.factorCount) :=
    Finset.univ.filter (fun i => i ∈ S) with hT
  have hjlt : j.val < D.f.degree?.getD 0 := j.isLt.trans_eq D.coeffWidth_eq
  -- Rewrite the tail column as the support-restricted sum of high-bit cuts.
  have hcol : ((trueFactorCLDVector L S)[Fin.natAdd L.factorCount j] : ℤ)
      = ∑ i ∈ T, Hex.psiCut D.p D.a (Hex.bhksCoeffCutThreshold D.p D.f j.val)
          ((Hex.cldQuotientMod D.f (D.liftedFactors.getD i.val 1) D.p D.a).coeff j.val) := by
    rw [D.coeff_eq_cldCoeffs j, hT, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i ∈ S
    · rw [indicatorVector_apply_mem S hi, one_mul, if_pos hi,
        Hex.cldCoeffs_getD_of_lt D.f D.p D.a (D.liftedFactors.getD i.val 1) j.val hjlt]
    · rw [indicatorVector_apply_not_mem S hi, zero_mul, if_neg hi]
  -- Separation facts for the cut modulus `p^b`.
  have hcut := Hex.le_pow_ceilLogP hp (2 * Hex.bhksCoeffBound D.f j.val + 1)
  have hpb : 0 < D.p ^ Hex.bhksCoeffCutThreshold D.p D.f j.val := by
    have : 2 * Hex.bhksCoeffBound D.f j.val + 1
        ≤ D.p ^ Hex.bhksCoeffCutThreshold D.p D.f j.val := hcut
    omega
  have hsep_b : 2 * Hex.bhksCoeffBound D.f j.val
      < D.p ^ Hex.bhksCoeffCutThreshold D.p D.f j.val := by
    have : 2 * Hex.bhksCoeffBound D.f j.val + 1
        ≤ D.p ^ Hex.bhksCoeffCutThreshold D.p D.f j.val := hcut
    omega
  -- Monic / divisibility data for the represented factor and its lifted factors.
  have hfac_monic : (HexPolyMathlib.toPolynomial D.factor).Monic :=
    HexHenselMathlib.toPolynomial_monic_of_dense_monic D.factor H.factor_monic
  have hfac_dvd : HexPolyMathlib.toPolynomial D.factor ∣ HexPolyMathlib.toPolynomial D.f :=
    ⟨HexPolyMathlib.toPolynomial D.cofactor, by
      rw [← HexPolyMathlib.toPolynomial_mul, D.factor_mul]⟩
  have hLD : L.liftedFactors = D.liftedFactors := D.liftedFactors_eq
  -- The represented factor is the `T`-indexed product of lifted factors.
  have hprod : HexPolyMathlib.toPolynomial D.factor
      = ∏ i ∈ T, HexPolyMathlib.toPolynomial (D.liftedFactors.getD i.val 1) := by
    have heq : HexPolyZMathlib.toPolynomial (supportProduct L S)
        = ∏ i ∈ T, HexPolyZMathlib.toPolynomial (D.liftedFactors.getD i.val 1) := by
      unfold supportProduct
      rw [polyProduct_toPolynomial, List.toList_toArray, List.map_map]
      simp only [Function.comp_def, hLD]
      rw [← List.prod_toFinset
        (fun i => HexPolyZMathlib.toPolynomial (D.liftedFactors.getD i.val 1))
        ((List.nodup_finRange L.factorCount).filter _)]
      refine Finset.prod_congr ?_ (fun _ _ => rfl)
      ext i
      simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
        decide_eq_true_eq, hT, Finset.mem_filter, Finset.mem_univ]
    rw [← D.support_product_eq]
    exact heq
  have hgmonic : ∀ i ∈ T, (HexPolyMathlib.toPolynomial (D.liftedFactors.getD i.val 1)).Monic := by
    intro i hi
    have hiS : i ∈ S := by simpa [hT] using hi
    exact HexHenselMathlib.toPolynomial_monic_of_dense_monic _ (H.selected_monic i hiS)
  -- Apply the carry-cancellation core with the exact `Phi`-columns as `w`.
  have hcard : T.card ≤ L.factorCount := by
    calc T.card ≤ (Finset.univ : Finset (Fin L.factorCount)).card := Finset.card_filter_le _ _
      _ = L.factorCount := by simp
  rw [hcol]
  refine le_trans (two_mul_natAbs_sum_psiCut_le T D.p D.a
    (Hex.bhksCoeffCutThreshold D.p D.f j.val) hpb
    (fun i => (Hex.cldQuotientMod D.f (D.liftedFactors.getD i.val 1) D.p D.a).coeff j.val)
    (fun i => (phi (HexPolyMathlib.toPolynomial D.f)
      (HexPolyMathlib.toPolynomial (D.liftedFactors.getD i.val 1))).coeff j.val)
    ((phi (HexPolyMathlib.toPolynomial D.f) (HexPolyMathlib.toPolynomial D.factor)).coeff j.val)
    (Hex.bhksCoeffBound D.f j.val) ?_ ?_ ?_ hsep_b) hcard
  · -- hw: each centred ambient residue equals the integer `Phi`-column coefficient.
    intro i hi
    have hiS : i ∈ S := by simpa [hT] using hi
    have hgi_dvd : HexPolyMathlib.toPolynomial (D.liftedFactors.getD i.val 1)
        ∣ HexPolyMathlib.toPolynomial D.f := by
      refine (?_ : HexPolyMathlib.toPolynomial (D.liftedFactors.getD i.val 1)
        ∣ HexPolyMathlib.toPolynomial D.factor).trans hfac_dvd
      rw [hprod]; exact Finset.dvd_prod_of_mem _ hi
    have hcongr_i :=
      TrueFactorLiftSemantics.selected_cldQuotientMod_congr_mul_derivative D H hk i hiS
    exact residue_cldQuotientMod_eq_phi_coeff D.f (D.liftedFactors.getD i.val 1) D.p D.a j.val
      (hgmonic i hi) hgi_dvd (hsep j.val) hcongr_i
  · -- hsum: the support sum of exact `Phi`-columns is the factor's `Phi`-column.
    have hps := phi_sum_eq_phi_prod (HexPolyMathlib.toPolynomial D.f) T
      (fun i => HexPolyMathlib.toPolynomial (D.liftedFactors.getD i.val 1)) hgmonic
      (by rw [← hprod]; exact hfac_dvd)
    rw [← Polynomial.finset_sum_coeff, hps, ← hprod]
  · -- hy: the factor's `Phi`-column is Mignotte-bounded.
    exact abs_phi_coeff_le_bhksCoeffBound D.f D.factor j.val hfac_monic hfac_dvd

/--
**Single-support tight CLD norm certificate.**  A genuine true-factor lift
package directly yields `TrueFactorCLDTightNormBound` (the
`4·‖v‖² ≤ bhksCutRadiusSq4` cut-radius bound the prefix cut consumes), by
composing the tight per-column estimate `tightColumnBound_of_lift` with the
column-to-norm reducer `tightNormBound_of_lift`.

This lives in `CLDColumnBound` rather than `Lattice` because
`tightColumnBound_of_lift` is downstream of `Lattice` in the import graph
(`CLDColumnBound → BadVectorAuxiliary → BadVector → Lattice`); placing the
composition in `Lattice` would be circular.
-/
theorem trueFactorCLDTightNormBound_of_lift
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (D : TrueFactorLift L S) (H : TrueFactorLiftSemantics D)
    (hp : 2 ≤ D.p) (hk : 1 < D.p ^ D.a)
    (hsep : ∀ j, 2 * Hex.bhksCoeffBound D.f j < D.p ^ D.a) :
    TrueFactorCLDTightNormBound L S :=
  tightNormBound_of_lift D (tightColumnBound_of_lift D H hp hk hsep)

/--
**Per-support tight CLD norm-bound family.**  Assemble the `∀ S` certificate
family that `cutProjectionHypotheses_of_trueFactors` (`Lattice.lean`) consumes
as its `tight` argument, from a per-support family of genuine lift packages plus
the per-support separation facts.

The binder shape mirrors `cutProjectionHypotheses_of_trueFactors` exactly (same
`L`, same `trueSupports`), so the result drops straight into its `tight` slot
with no reshaping.  The separation facts `hp`/`hk`/`hsep` are taken per-support,
since they reference `(Dfam S).p`, `(Dfam S).a`, `(Dfam S).f`, which vary per
package and are not fields of `TrueFactorLift`/`TrueFactorLiftSemantics`.
-/
theorem trueFactorCLDTightNormBoundFamily_of_lift
    (L : Hex.BhksLatticeBasis) (hrows : 1 ≤ L.factorCount + L.coeffWidth)
    (trueSupports :
      Set (Set (Fin (Hex.bhksProjectedRows L hrows).factorCount)))
    (Dfam : ∀ S : trueSupports, TrueFactorLift L S.1)
    (Hfam : ∀ S : trueSupports, TrueFactorLiftSemantics (Dfam S))
    (hp : ∀ S : trueSupports, 2 ≤ (Dfam S).p)
    (hk : ∀ S : trueSupports, 1 < (Dfam S).p ^ (Dfam S).a)
    (hsep : ∀ S : trueSupports,
      ∀ j, 2 * Hex.bhksCoeffBound (Dfam S).f j < (Dfam S).p ^ (Dfam S).a) :
    ∀ S : trueSupports, TrueFactorCLDTightNormBound L S.1 :=
  fun S =>
    trueFactorCLDTightNormBound_of_lift (Dfam S) (Hfam S) (hp S) (hk S) (hsep S)

end BHKS

end

end HexBerlekampZassenhausMathlib
