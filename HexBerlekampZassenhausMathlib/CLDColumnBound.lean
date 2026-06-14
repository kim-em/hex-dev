import HexBerlekampZassenhaus
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

end

end HexBerlekampZassenhausMathlib
