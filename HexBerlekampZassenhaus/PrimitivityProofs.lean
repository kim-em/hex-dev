/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexArith.Nat.Prime
public meta import HexBerlekamp.Factor
public meta import HexBerlekamp.Irreducibility
public meta import HexHensel.Basic
public meta import HexHensel.Multifactor
public meta import HexHensel.QuadraticMultifactor
public meta import HexMatrix.Basic
public meta import HexPolyZ.Mignotte
public meta import HexLLL.Basic
public import HexArith.Nat.Prime
public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexHensel.Multifactor
public import HexHensel.QuadraticMultifactor
public import HexLLL.Basic
-- Needed so `decide`/`rfl` over `DensePoly`/`Array` equality reduces in the
-- kernel: the core `Array.instDecidableEq` delegates its nonempty case to the
-- non-`@[expose]` `Array.instDecidableEqImpl`, which is otherwise opaque under
-- the module system. Drop once that impl is exposed upstream (lean4).
import all Init.Data.Array.DecidableEq

public import HexBerlekampZassenhaus.QuadraticRootProofs
public meta import HexBerlekampZassenhaus.QuadraticRootProofs
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.ReassemblyProofs
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.BhksRecover
import all HexBerlekampZassenhaus.Recombination
import all HexBerlekampZassenhaus.FactorEntryPoints
import all HexBerlekampZassenhaus.IrreducibleCore
import all HexBerlekampZassenhaus.RecombineProofs
import all HexBerlekampZassenhaus.TrialProofs
import all HexBerlekampZassenhaus.QuadraticRootProofs

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
This module collects `squareFreeCore`/`expandRepeatedPart`/reassembly primitivity.
-/
namespace Hex

/-- Every factor emitted by `quadraticIntegerRootFactors?` has positive degree
when the input core is primitive with positive leading coefficient. Linear
entries are the splitter's `linearFactorForRoot` outputs; the optional residual
cannot be constant because then its positive constant coefficient would divide
the primitive core's content. -/
theorem quadraticIntegerRootFactors?_degree_pos_of_primitive
    {core : ZPoly} (hcore_pos : 0 < DensePoly.leadingCoeff core)
    (hcore_primitive : ZPoly.Primitive core)
    {factors : Array ZPoly}
    (hquad : quadraticIntegerRootFactors? core = some factors) :
    ∀ factor ∈ factors.toList, 0 < factor.degree?.getD 0 := by
  intro factor hmem
  unfold quadraticIntegerRootFactors? at hquad
  by_cases hdeg : core.degree?.getD 0 = 2
  · simp only [hdeg, if_true] at hquad
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    obtain ⟨rs, _hsub, hshape⟩ :=
      splitIntegerRootFactorsAux_factors_form (target := core) (roots := roots)
        (fuel := roots.length) (factors := split.1) (residual := split.2) rfl
    have hlinear_degree :
        ∀ factor ∈ split.1.toList, 0 < factor.degree?.getD 0 := by
      intro g hg
      rw [hshape] at hg
      rcases List.mem_map.mp hg with ⟨r, _hr, rfl⟩
      exact linearFactorForRoot_degree_pos r
    by_cases hsize : split.1.size = 0
    · simp [roots, split, hsize] at hquad
    · simp only [roots, split, hsize, if_false] at hquad
      by_cases hres_one : split.2 = 1
      · rw [if_pos hres_one] at hquad
        cases hquad
        exact hlinear_degree factor hmem
      · rw [if_neg hres_one] at hquad
        by_cases hres_deg : split.2.degree?.getD 0 ≤ 1
        · rw [if_pos hres_deg] at hquad
          cases hquad
          rw [Array.toList_push] at hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hsplit_mem | hres_mem
          · exact hlinear_degree factor hsplit_mem
          · subst factor
            have hsplit_prod :
                split.2 * Array.polyProduct split.1 = core :=
              splitIntegerRootFactorsAux_product core roots roots.length
                split.1 split.2 rfl
            have hpoly_lc_pos :
                0 < DensePoly.leadingCoeff (Array.polyProduct split.1) :=
              splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core roots
                roots.length split.1 split.2 rfl
            have hpoly_ne : Array.polyProduct split.1 ≠ 0 := by
              intro hz
              rw [hz] at hpoly_lc_pos
              rw [DensePoly.leadingCoeff_zero] at hpoly_lc_pos
              omega
            have hcore_ne : core ≠ 0 := by
              intro hz
              rw [hz] at hcore_pos
              rw [DensePoly.leadingCoeff_zero] at hcore_pos
              omega
            have hres_ne : split.2 ≠ 0 := by
              intro hz
              apply hcore_ne
              rw [← hsplit_prod, hz, DensePoly.zero_mul]
            have hcore_lc_eq :
                DensePoly.leadingCoeff core =
                  DensePoly.leadingCoeff split.2 *
                    DensePoly.leadingCoeff (Array.polyProduct split.1) := by
              rw [← hsplit_prod]
              exact ZPoly.leadingCoeff_mul_of_nonzero split.2 _ hres_ne hpoly_ne
            have hres_lc_pos : 0 < DensePoly.leadingCoeff split.2 := by
              have hres_lc_ne :
                  DensePoly.leadingCoeff split.2 ≠ 0 :=
                ZPoly.leadingCoeff_ne_zero_of_ne_zero split.2 hres_ne
              rcases Int.lt_or_lt_of_ne hres_lc_ne with hlt | hgt
              · exfalso
                have hcore_neg : DensePoly.leadingCoeff core < 0 := by
                  rw [hcore_lc_eq]
                  exact Int.mul_neg_of_neg_of_pos hlt hpoly_lc_pos
                omega
              · exact hgt
            by_cases hposdeg : 0 < split.2.degree?.getD 0
            · exact hposdeg
            exfalso
            have hres_deg_zero : split.2.degree?.getD 0 = 0 := by omega
            have hres_size_one : split.2.size = 1 := by
              unfold DensePoly.degree? at hres_deg_zero
              have hsize_ne : split.2.size ≠ 0 := by
                have hpos := ZPoly.size_pos_of_ne_zero split.2 hres_ne
                omega
              simp [hsize_ne] at hres_deg_zero
              omega
            have hres_eq : split.2 = DensePoly.C (split.2.coeff 0) :=
              ZPoly.eq_C_of_size_eq_one split.2 hres_size_one
            have hcore_expand :
                core = DensePoly.C (split.2.coeff 0) * Array.polyProduct split.1 := by
              rw [← hsplit_prod]
              exact congrArg (· * Array.polyProduct split.1) hres_eq
            have hcoeff_core : ∀ n, core.coeff n =
                split.2.coeff 0 * (Array.polyProduct split.1).coeff n := by
              intro n
              rw [hcore_expand, ZPoly.C_mul_eq_scale,
                DensePoly.coeff_scale (R := Int) (split.2.coeff 0) _ n (Int.mul_zero _)]
            have hc_dvd : ∀ n, ((split.2.coeff 0).natAbs : Int) ∣ core.coeff n := by
              intro n
              rw [hcoeff_core]
              exact Int.natAbs_dvd.mpr ⟨_, rfl⟩
            have hc_dvd_content :
                ((split.2.coeff 0).natAbs : Int) ∣ ZPoly.content core :=
              ZPoly.dvd_content_of_nat_dvd_coeff core _ hc_dvd
            rw [show ZPoly.content core = 1 from hcore_primitive] at hc_dvd_content
            have hc_ne : split.2.coeff 0 ≠ 0 := by
              intro h
              apply hres_ne
              rw [hres_eq, h]
              rfl
            have hres_lc : DensePoly.leadingCoeff split.2 = split.2.coeff 0 := by
              rw [DensePoly.leadingCoeff_eq_coeff_last split.2 (by omega)]
              congr 1
              omega
            have hc_pos : 0 < split.2.coeff 0 := by
              rw [← hres_lc]
              exact hres_lc_pos
            have hnat_dvd : (split.2.coeff 0).natAbs ∣ (1 : Nat) :=
              Int.ofNat_dvd.mp (by simpa using hc_dvd_content)
            have hnat_le : (split.2.coeff 0).natAbs ≤ 1 :=
              Nat.le_of_dvd (by omega) hnat_dvd
            have hnat_pos : 1 ≤ (split.2.coeff 0).natAbs := by
              rcases Nat.eq_zero_or_pos (split.2.coeff 0).natAbs with hz | hp
              · exact absurd (Int.natAbs_eq_zero.mp hz) hc_ne
              · exact hp
            have hnat_eq : (split.2.coeff 0).natAbs = 1 := by omega
            have hc_eq_one : split.2.coeff 0 = 1 := by
              rcases Int.natAbs_eq (split.2.coeff 0) with hpos_abs | hneg_abs
              · rw [hpos_abs, hnat_eq]
                rfl
              · exfalso
                have : split.2.coeff 0 = -1 := by
                  rw [hneg_abs, hnat_eq]
                  rfl
                omega
            apply hres_one
            rw [hres_eq, hc_eq_one]
            rfl
        · rw [if_neg hres_deg] at hquad
          contradiction
  · rw [if_neg hdeg] at hquad
    contradiction

theorem extractXPower_core_ne_zero_of_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    (ZPoly.extractXPower (ZPoly.primitivePart f)).core ≠ 0 :=
  ZPoly.ne_zero_of_primitive _ (extractXPower_core_primitive_of_ne_zero f hf)

theorem repeatedPart_ne_zero_of_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    (normalizeForFactor f).repeatedPart ≠ 0 := by
  unfold normalizeForFactor
  simp only
  intro hzero
  have hcore_ne := extractXPower_core_ne_zero_of_ne_zero f hf
  have hprod_primitive :=
    ZPoly.primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive _ hcore_ne
  have hprod_ne :
      (ZPoly.primitiveSquareFreeDecomposition
            (ZPoly.extractXPower (ZPoly.primitivePart f)).core).squareFreeCore *
        (ZPoly.primitiveSquareFreeDecomposition
            (ZPoly.extractXPower (ZPoly.primitivePart f)).core).repeatedPart ≠ 0 :=
    ZPoly.ne_zero_of_primitive _ hprod_primitive
  apply hprod_ne
  rw [hzero, DensePoly.mul_comm_poly (S := Int)]
  exact DensePoly.zero_mul _

private theorem repeatedPart_leadingCoeff_pos_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0) :
    0 < DensePoly.leadingCoeff (normalizeForFactor f).repeatedPart := by
  have hne := repeatedPart_ne_zero_of_ne_zero f hf
  have hnonneg :
      0 ≤ DensePoly.leadingCoeff (normalizeForFactor f).repeatedPart := by
    unfold normalizeForFactor
    exact ZPoly.leadingCoeff_repeatedPart_nonneg _
  have hne_lead :
      DensePoly.leadingCoeff (normalizeForFactor f).repeatedPart ≠ 0 :=
    ZPoly.leadingCoeff_ne_zero_of_ne_zero _ hne
  omega

private theorem repeatedPart_ne_C_neg_one_of_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    (normalizeForFactor f).repeatedPart ≠ DensePoly.C (-1 : Int) := by
  intro h
  have hpos := repeatedPart_leadingCoeff_pos_of_ne_zero f hf
  rw [h] at hpos
  have hneg : DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) = -1 := by simp
  rw [hneg] at hpos
  omega

private theorem repeatedPartFactorArray_normalizeFactorSign_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0)
    (factor : ZPoly)
    (h : factor ∈ (repeatedPartFactorArray (normalizeForFactor f).repeatedPart).toList) :
    normalizeFactorSign factor = factor := by
  rw [mem_repeatedPartFactorArray_eq _ factor h]
  apply normalizeFactorSign_eq_self_of_leadingCoeff_nonneg
  have hpos := repeatedPart_leadingCoeff_pos_of_ne_zero f hf
  omega

private theorem repeatedPartFactorArray_shouldRecord_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0)
    (factor : ZPoly)
    (h : factor ∈ (repeatedPartFactorArray (normalizeForFactor f).repeatedPart).toList) :
    shouldRecordPolynomialFactor factor = true := by
  have hfactor_eq := mem_repeatedPartFactorArray_eq _ factor h
  have hne_one := mem_repeatedPartFactorArray_ne_one _ factor h
  rw [hfactor_eq]
  unfold shouldRecordPolynomialFactor
  simp [repeatedPart_ne_zero_of_ne_zero f hf, hne_one,
    repeatedPart_ne_C_neg_one_of_ne_zero f hf]

private theorem polynomialNormalizationPrefixFactors_normalizeFactorSign_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0)
    (factor : ZPoly)
    (h : factor ∈ (polynomialNormalizationPrefixFactors (normalizeForFactor f)).toList) :
    normalizeFactorSign factor = factor := by
  unfold polynomialNormalizationPrefixFactors at h
  rw [Array.toList_append] at h
  simp only [List.mem_append] at h
  cases h with
  | inl hx =>
      exact xPowerFactorArray_normalizeFactorSign _ factor hx
  | inr hrep =>
      exact repeatedPartFactorArray_normalizeFactorSign_of_ne_zero f hf factor hrep

private theorem polynomialNormalizationPrefixFactors_shouldRecord_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0)
    (factor : ZPoly)
    (h : factor ∈ (polynomialNormalizationPrefixFactors (normalizeForFactor f)).toList) :
    shouldRecordPolynomialFactor factor = true := by
  unfold polynomialNormalizationPrefixFactors at h
  rw [Array.toList_append] at h
  simp only [List.mem_append] at h
  cases h with
  | inl hx =>
      exact xPowerFactorArray_shouldRecord _ factor hx
  | inr hrep =>
      exact repeatedPartFactorArray_shouldRecord_of_ne_zero f hf factor hrep

/-- Lift a per-coreFactor normalize property through the reassembly: any factor
appearing in `reassemblePolynomialFactors` is either a normalization-prefix
factor (handled by `polynomialNormalizationPrefixFactors_normalizeFactorSign_of_ne_zero`)
or appears in the supplied `coreFactors`. -/
private theorem reassemblePolynomialFactors_normalizeFactorSign_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0) (coreFactors : Array ZPoly)
    (hcore : ∀ factor ∈ coreFactors.toList, normalizeFactorSign factor = factor)
    (factor : ZPoly)
    (hmem : factor ∈
      (reassemblePolynomialFactors (normalizeForFactor f) coreFactors).toList) :
    normalizeFactorSign factor = factor := by
  rcases reassemblePolynomialFactors_mem _ _ _ hmem with hprefix | hcoreMem
  · exact polynomialNormalizationPrefixFactors_normalizeFactorSign_of_ne_zero
      f hf factor hprefix
  · exact hcore factor hcoreMem

/-- Lift a per-coreFactor `shouldRecord` property through the reassembly. -/
private theorem reassemblePolynomialFactors_shouldRecord_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0) (coreFactors : Array ZPoly)
    (hcore : ∀ factor ∈ coreFactors.toList, shouldRecordPolynomialFactor factor = true)
    (factor : ZPoly)
    (hmem : factor ∈
      (reassemblePolynomialFactors (normalizeForFactor f) coreFactors).toList) :
    shouldRecordPolynomialFactor factor = true := by
  rcases reassemblePolynomialFactors_mem _ _ _ hmem with hprefix | hcoreMem
  · exact polynomialNormalizationPrefixFactors_shouldRecord_of_ne_zero f hf factor hprefix
  · exact hcore factor hcoreMem

private theorem consumeExactPower_one (target : ZPoly) (fuel : Nat) :
    consumeExactPower target (1 : ZPoly) fuel = (target, 0) := by
  cases fuel with
  | zero => rfl
  | succ n =>
      unfold consumeExactPower
      have hexact : exactQuotient? target (1 : ZPoly) = none := by
        unfold exactQuotient?
        simp
      rw [hexact]

/-- The expansion against `#[1]` never emits any factors: `consumeExactPower _ 1`
returns multiplicity zero, so `expandRepeatedPartFactorArray rp #[1] = (#[], rp)`. -/
private theorem expandRepeatedPartFactorArray_singleton_one (rp : ZPoly) :
    expandRepeatedPartFactorArray rp #[1] = ((#[] : Array ZPoly), rp) := by
  unfold expandRepeatedPartFactorArray
  show expandRepeatedPartFactorsAux [(1 : ZPoly)] rp (rp.size + 1) = (#[], rp)
  unfold expandRepeatedPartFactorsAux
  rw [consumeExactPower_one]
  show ((List.replicate 0 (1 : ZPoly)).toArray ++
      (expandRepeatedPartFactorsAux [] rp (rp.size + 1)).1,
      (expandRepeatedPartFactorsAux [] rp (rp.size + 1)).2) = (#[], rp)
  show ((List.replicate 0 (1 : ZPoly)).toArray ++ ((#[] : Array ZPoly), rp).1,
      ((#[] : Array ZPoly), rp).2) = (#[], rp)
  simp

/-- **#4603 HO-1 support lemma — irreducibility/non-associate translation.** Two
irreducible integer polynomials that are not associated do not divide one
another: if `q₁` divides `q₂` and both are irreducible, the irreducibility
decomposition `q₂ = q₁ * w` forces either `q₁` or `w` to be a unit, and the
first case contradicts `Irreducible q₁`. Used by downstream HO-1 dischargers
to translate the Mathlib structural fact's "pairwise non-associate
irreducible factors" condition into the direct non-divisibility hypothesis
consumed by `expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition`. -/
theorem irreducible_not_dvd_of_not_associated
    {q₁ q₂ : ZPoly} (hq₁ : ZPoly.Irreducible q₁) (hq₂ : ZPoly.Irreducible q₂)
    (hassoc : ¬ ZPoly.Associated q₁ q₂) :
    ¬ q₁ ∣ q₂ := by
  intro hdvd
  rcases hdvd with ⟨w, hw⟩
  rcases hq₂.no_factors q₁ w hw with hunit_q | hunit_w
  · exact hq₁.not_unit hunit_q
  · exact hassoc ⟨w, hunit_w, hw⟩

/-- Converse of `exactQuotient?_product`: when `candidate` does not divide
`target` in `ZPoly`, the exact-quotient probe necessarily returns `none`.
A direct contrapositive of the witness extraction. -/
private theorem exactQuotient?_eq_none_of_not_dvd
    {target candidate : ZPoly}
    (hnot_dvd : ¬ candidate ∣ target) :
    exactQuotient? target candidate = none := by
  cases hcase : exactQuotient? target candidate with
  | none => rfl
  | some w =>
      exfalso
      apply hnot_dvd
      have hmul : w * candidate = target := exactQuotient?_product hcase
      refine ⟨w, ?_⟩
      rw [← hmul]
      exact DensePoly.mul_comm_poly (S := Int) w candidate

/-- Greedy peel of `candidate^?` from `target` exits at multiplicity zero
when `candidate` does not divide `target`. Combines
`exactQuotient?_eq_none_of_not_dvd` with one unfold of `consumeExactPower`. -/
private theorem consumeExactPower_eq_self_zero_of_not_dvd
    {target candidate : ZPoly}
    (hnot_dvd : ¬ candidate ∣ target) (fuel : Nat) :
    consumeExactPower target candidate fuel = (target, 0) := by
  cases fuel with
  | zero => rfl
  | succ n =>
      unfold consumeExactPower
      rw [exactQuotient?_eq_none_of_not_dvd hnot_dvd]

/-- **#4603 HO-1 support lemma — single-factor expansion helper.** For a monic
positive-degree integer polynomial `q` that does not divide a residual `r`,
the greedy `consumeExactPower` on `q ^ k * r` extracts exactly `k` copies of
`q` and returns `r` as the residual, provided the fuel covers `k + 1`
iterations. The monic positive-degree hypothesis is what makes
`exactQuotient?` agree with `ZPoly`-level divisibility (via
`exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree`); the
`¬ q ∣ r` hypothesis closes off the last `consumeExactPower` step at
multiplicity `k`. Used by
`expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition` to
recurse one head factor at a time. -/
private theorem consumeExactPower_pow_mul_of_not_dvd
    (q r : ZPoly) (k : Nat)
    (hq_monic : DensePoly.Monic q)
    (hq_degree : 0 < q.degree?.getD 0)
    (hnot_dvd : ¬ q ∣ r)
    (fuel : Nat) (hfuel : k + 1 ≤ fuel) :
    consumeExactPower (Factorization.polyPow q k * r) q fuel = (r, k) := by
  induction k generalizing fuel with
  | zero =>
      rw [polyPow_zero_lemma, ZPoly.one_mul_zpoly]
      exact consumeExactPower_eq_self_zero_of_not_dvd hnot_dvd fuel
  | succ m ih =>
      cases fuel with
      | zero => omega
      | succ fuel' =>
          have hfuel' : m + 1 ≤ fuel' := by omega
          have htarget_eq :
              (Factorization.polyPow q m * r) * q =
                Factorization.polyPow q (m + 1) * r := by
            rw [polyPow_succ_lemma,
              DensePoly.mul_assoc_poly (S := Int) (Factorization.polyPow q m) r q,
              DensePoly.mul_comm_poly (S := Int) r q,
              ← DensePoly.mul_assoc_poly (S := Int) (Factorization.polyPow q m) q r]
          have hquot :
              exactQuotient? (Factorization.polyPow q (m + 1) * r) q =
                some (Factorization.polyPow q m * r) :=
            exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree
              hq_monic hq_degree htarget_eq
          unfold consumeExactPower
          rw [hquot]
          simp only
          rw [ih fuel' hfuel']

/-- **#4778 HO-1 support lemma — non-monic single-factor expansion helper.**
Non-monic analogue of `consumeExactPower_pow_mul_of_not_dvd`: drops the
`Monic q` hypothesis in favour of `0 < leadingCoeff q`, routing the
divisibility-extraction step through
`exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq` (the non-monic
companion of `exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree`,
landed via #4773 → #4774). Used by
`expandRepeatedPartFactorsAux_residual_eq_one_of_pow_decomposition_of_pos_lc`
to handle quadratic-arm core factors emitted by
`quadraticIntegerRootFactors?` that are primitive, positive-leading, but
non-monic (e.g. the `2X + 3` residual from `(X-1)(2X+3) = 2X^2 + X - 3`).
Dependency chain: #4773 → #4774 → this. -/
private theorem consumeExactPower_pow_mul_of_not_dvd_of_pos_lc
    (q r : ZPoly) (k : Nat)
    (hq_pos_lc : 0 < DensePoly.leadingCoeff q)
    (hq_degree : 0 < q.degree?.getD 0)
    (hnot_dvd : ¬ q ∣ r)
    (fuel : Nat) (hfuel : k + 1 ≤ fuel) :
    consumeExactPower (Factorization.polyPow q k * r) q fuel = (r, k) := by
  induction k generalizing fuel with
  | zero =>
      rw [polyPow_zero_lemma, ZPoly.one_mul_zpoly]
      exact consumeExactPower_eq_self_zero_of_not_dvd hnot_dvd fuel
  | succ m ih =>
      cases fuel with
      | zero => omega
      | succ fuel' =>
          have hfuel' : m + 1 ≤ fuel' := by omega
          have htarget_eq :
              (Factorization.polyPow q m * r) * q =
                Factorization.polyPow q (m + 1) * r := by
            rw [polyPow_succ_lemma,
              DensePoly.mul_assoc_poly (S := Int) (Factorization.polyPow q m) r q,
              DensePoly.mul_comm_poly (S := Int) r q,
              ← DensePoly.mul_assoc_poly (S := Int) (Factorization.polyPow q m) q r]
          have hquot :
              exactQuotient? (Factorization.polyPow q (m + 1) * r) q =
                some (Factorization.polyPow q m * r) :=
            exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq
              hq_pos_lc hq_degree htarget_eq
          unfold consumeExactPower
          rw [hquot]
          simp only
          rw [ih fuel' hfuel']

/-- **#4603 HO-1 support lemma — list-level pow-decomposition expansion helper.**
Given a list of monic positive-degree polynomials and a matching list of
exponents, if the running residual `rp` factors as
`(∏ (qᵢ, eᵢ) ∈ pairs, qᵢ ^ eᵢ)` and each head factor fails to divide its
suffix product (the "tail non-divisibility" prefix witness), then
`expandRepeatedPartFactorsAux` reduces the residual to `1`. Proved by
induction on the core-factor list, peeling off one head factor at a time
via `consumeExactPower_pow_mul_of_not_dvd`. The fuel budget must cover each
individual exponent (which is automatic for the default
`rp.size + 1` budget when the core factors are nonzero). -/
private theorem expandRepeatedPartFactorsAux_residual_eq_one_of_pow_decomposition :
    ∀ (coreFactors : List ZPoly) (exponents : List Nat) (rp : ZPoly) (fuel : Nat),
      exponents.length = coreFactors.length →
      (∀ q ∈ coreFactors, DensePoly.Monic q) →
      (∀ q ∈ coreFactors, 0 < q.degree?.getD 0) →
      (∀ pre q e suf,
        coreFactors.zip exponents = pre ++ (q, e) :: suf →
        ¬ q ∣ (suf.map (fun (qe : ZPoly × Nat) =>
                Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1) →
      rp = ((coreFactors.zip exponents).map
              (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1 →
      (∀ (qe : ZPoly × Nat), qe ∈ coreFactors.zip exponents → qe.2 + 1 ≤ fuel) →
      (expandRepeatedPartFactorsAux coreFactors rp fuel).2 = 1 := by
  intro coreFactors
  induction coreFactors with
  | nil =>
      intro exponents rp fuel _ _ _ _ hdecomp _
      unfold expandRepeatedPartFactorsAux
      simp only [List.zip_nil_left, List.map_nil, List.foldl_nil] at hdecomp
      exact hdecomp
  | cons q qs ih =>
      intro exponents rp fuel hlen hmonic hdegree hnot_dvd_tail hdecomp hfuel
      cases exponents with
      | nil => simp at hlen
      | cons e es =>
          have hq_monic : DensePoly.Monic q := hmonic q List.mem_cons_self
          have hq_degree : 0 < q.degree?.getD 0 := hdegree q List.mem_cons_self
          have hzip_eq : (q :: qs).zip (e :: es) = (q, e) :: qs.zip es := rfl
          let tailProduct : ZPoly :=
            ((qs.zip es).map
              (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1
          have htail_def :
              tailProduct =
                ((qs.zip es).map
                  (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2)).foldl
                    (· * ·) 1 := rfl
          have hrp_eq : rp = Factorization.polyPow q e * tailProduct := by
            rw [hdecomp, hzip_eq]
            simp only [List.map_cons, List.foldl_cons]
            rw [ZPoly.one_mul_zpoly]
            exact ZPoly.list_foldl_mul_eq_mul_foldl_one
              (Factorization.polyPow q e)
              ((qs.zip es).map
                (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2))
          have hnot_dvd_head : ¬ q ∣ tailProduct := by
            rw [htail_def]
            exact hnot_dvd_tail [] q e (qs.zip es) (by rw [hzip_eq, List.nil_append])
          have hfuel_head : e + 1 ≤ fuel :=
            hfuel (q, e) (by rw [hzip_eq]; exact List.mem_cons_self)
          have hcep :
              consumeExactPower rp q fuel = (tailProduct, e) := by
            rw [hrp_eq]
            exact consumeExactPower_pow_mul_of_not_dvd q tailProduct e
              hq_monic hq_degree hnot_dvd_head fuel hfuel_head
          unfold expandRepeatedPartFactorsAux
          rw [hcep]
          simp only
          have hlen' : es.length = qs.length := by
            simpa using hlen
          have hmonic' : ∀ q' ∈ qs, DensePoly.Monic q' :=
            fun q' hq' => hmonic q' (List.mem_cons_of_mem _ hq')
          have hdegree' : ∀ q' ∈ qs, 0 < q'.degree?.getD 0 :=
            fun q' hq' => hdegree q' (List.mem_cons_of_mem _ hq')
          have hnot_dvd_tail' :
              ∀ pre q' e' suf,
                qs.zip es = pre ++ (q', e') :: suf →
                ¬ q' ∣ (suf.map (fun (qe : ZPoly × Nat) =>
                          Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1 := by
            intro pre q' e' suf hsplit
            apply hnot_dvd_tail ((q, e) :: pre) q' e' suf
            rw [hzip_eq, List.cons_append, hsplit]
          have hfuel' :
              ∀ (qe : ZPoly × Nat), qe ∈ qs.zip es → qe.2 + 1 ≤ fuel := by
            intro qe hqe
            apply hfuel qe
            rw [hzip_eq]
            exact List.mem_cons_of_mem _ hqe
          exact ih es tailProduct fuel hlen' hmonic' hdegree'
            hnot_dvd_tail' htail_def hfuel'

/-- **#4778 HO-1 support lemma — non-monic list-level pow-decomposition expansion
helper.** Non-monic analogue of
`expandRepeatedPartFactorsAux_residual_eq_one_of_pow_decomposition`: replaces
the per-factor `Monic q` hypothesis by `0 < leadingCoeff q`, routing the
single-factor extraction through `consumeExactPower_pow_mul_of_not_dvd_of_pos_lc`
(which itself uses `exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq` from
the #4773 → #4774 dependency chain). Used by the public array-level surface
`expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc`,
which is the quadratic-arm discharger
`reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero` (#4747
residual) precondition that needs to admit a non-monic primitive
positive-leading core factor such as `2X + 3`. -/
private theorem expandRepeatedPartFactorsAux_residual_eq_one_of_pow_decomposition_of_pos_lc :
    ∀ (coreFactors : List ZPoly) (exponents : List Nat) (rp : ZPoly) (fuel : Nat),
      exponents.length = coreFactors.length →
      (∀ q ∈ coreFactors, 0 < DensePoly.leadingCoeff q) →
      (∀ q ∈ coreFactors, 0 < q.degree?.getD 0) →
      (∀ pre q e suf,
        coreFactors.zip exponents = pre ++ (q, e) :: suf →
        ¬ q ∣ (suf.map (fun (qe : ZPoly × Nat) =>
                Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1) →
      rp = ((coreFactors.zip exponents).map
              (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1 →
      (∀ (qe : ZPoly × Nat), qe ∈ coreFactors.zip exponents → qe.2 + 1 ≤ fuel) →
      (expandRepeatedPartFactorsAux coreFactors rp fuel).2 = 1 := by
  intro coreFactors
  induction coreFactors with
  | nil =>
      intro exponents rp fuel _ _ _ _ hdecomp _
      unfold expandRepeatedPartFactorsAux
      simp only [List.zip_nil_left, List.map_nil, List.foldl_nil] at hdecomp
      exact hdecomp
  | cons q qs ih =>
      intro exponents rp fuel hlen hpos_lc hdegree hnot_dvd_tail hdecomp hfuel
      cases exponents with
      | nil => simp at hlen
      | cons e es =>
          have hq_pos_lc : 0 < DensePoly.leadingCoeff q := hpos_lc q List.mem_cons_self
          have hq_degree : 0 < q.degree?.getD 0 := hdegree q List.mem_cons_self
          have hzip_eq : (q :: qs).zip (e :: es) = (q, e) :: qs.zip es := rfl
          let tailProduct : ZPoly :=
            ((qs.zip es).map
              (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1
          have htail_def :
              tailProduct =
                ((qs.zip es).map
                  (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2)).foldl
                    (· * ·) 1 := rfl
          have hrp_eq : rp = Factorization.polyPow q e * tailProduct := by
            rw [hdecomp, hzip_eq]
            simp only [List.map_cons, List.foldl_cons]
            rw [ZPoly.one_mul_zpoly]
            exact ZPoly.list_foldl_mul_eq_mul_foldl_one
              (Factorization.polyPow q e)
              ((qs.zip es).map
                (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2))
          have hnot_dvd_head : ¬ q ∣ tailProduct := by
            rw [htail_def]
            exact hnot_dvd_tail [] q e (qs.zip es) (by rw [hzip_eq, List.nil_append])
          have hfuel_head : e + 1 ≤ fuel :=
            hfuel (q, e) (by rw [hzip_eq]; exact List.mem_cons_self)
          have hcep :
              consumeExactPower rp q fuel = (tailProduct, e) := by
            rw [hrp_eq]
            exact consumeExactPower_pow_mul_of_not_dvd_of_pos_lc q tailProduct e
              hq_pos_lc hq_degree hnot_dvd_head fuel hfuel_head
          unfold expandRepeatedPartFactorsAux
          rw [hcep]
          simp only
          have hlen' : es.length = qs.length := by
            simpa using hlen
          have hpos_lc' : ∀ q' ∈ qs, 0 < DensePoly.leadingCoeff q' :=
            fun q' hq' => hpos_lc q' (List.mem_cons_of_mem _ hq')
          have hdegree' : ∀ q' ∈ qs, 0 < q'.degree?.getD 0 :=
            fun q' hq' => hdegree q' (List.mem_cons_of_mem _ hq')
          have hnot_dvd_tail' :
              ∀ pre q' e' suf,
                qs.zip es = pre ++ (q', e') :: suf →
                ¬ q' ∣ (suf.map (fun (qe : ZPoly × Nat) =>
                          Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1 := by
            intro pre q' e' suf hsplit
            apply hnot_dvd_tail ((q, e) :: pre) q' e' suf
            rw [hzip_eq, List.cons_append, hsplit]
          have hfuel' :
              ∀ (qe : ZPoly × Nat), qe ∈ qs.zip es → qe.2 + 1 ≤ fuel := by
            intro qe hqe
            apply hfuel qe
            rw [hzip_eq]
            exact List.mem_cons_of_mem _ hqe
          exact ih es tailProduct fuel hlen' hpos_lc' hdegree'
            hnot_dvd_tail' htail_def hfuel'

/-- **#4603 HO-1 support lemma — array-level pow-decomposition expansion helper.**
Public surface for `expandRepeatedPartFactorsAux_residual_eq_one_of_pow_decomposition`
that targets `expandRepeatedPartFactorArray` directly. Given a list of monic
positive-degree core factors, a matching list of exponents, a head-product
decomposition `rp = ∏ qᵢ ^ eᵢ`, and pairwise tail-non-divisibility for each
head factor relative to the suffix product, the greedy expansion completely
consumes `rp` and reports residual `1`. The downstream discharger
`reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero` (HO-1
support-lemma sub-issue C) supplies the structural decomposition (Mathlib-side,
from sub-issue #4602) and uses this helper to conclude
`reassemblyExpansionComplete` on the quadratic arms. Compare the small-mod
singleton sibling `expandRepeatedPartFactorArray_pow_singleton` (#4597
deliverable 2), which specialises this shape to a single irreducible. -/
theorem expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition
    (rp : ZPoly) (coreFactors : Array ZPoly)
    (hmonic : ∀ q ∈ coreFactors.toList, DensePoly.Monic q)
    (hdegree : ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0)
    (exponents : List Nat)
    (hlen : exponents.length = coreFactors.size)
    (hnot_dvd_tail :
      ∀ pre q e suf,
        coreFactors.toList.zip exponents = pre ++ (q, e) :: suf →
        ¬ q ∣ (suf.map (fun (qe : ZPoly × Nat) =>
                Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1)
    (hdecomp :
      rp = ((coreFactors.toList.zip exponents).map
              (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1)
    (hfuel :
      ∀ (qe : ZPoly × Nat),
        qe ∈ coreFactors.toList.zip exponents → qe.2 + 1 ≤ rp.size + 1) :
    (expandRepeatedPartFactorArray rp coreFactors).2 = 1 := by
  unfold expandRepeatedPartFactorArray
  have hlen' : exponents.length = coreFactors.toList.length := by
    simpa using hlen
  exact expandRepeatedPartFactorsAux_residual_eq_one_of_pow_decomposition
    coreFactors.toList exponents rp (rp.size + 1)
    hlen' hmonic hdegree hnot_dvd_tail hdecomp hfuel

/-- Public `factorPower` spelling of
`expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition`.

The underlying expansion proof was developed against the private recursive
power helper used by `Factorization.product`; downstream Mathlib-side
assemblers cannot name that helper. This wrapper exposes the same contract
using `Factorization.factorPower`, whose definition is judgmentally the same
power operation and is part of the public API. -/
theorem expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition
    (rp : ZPoly) (coreFactors : Array ZPoly)
    (hmonic : ∀ q ∈ coreFactors.toList, DensePoly.Monic q)
    (hdegree : ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0)
    (exponents : List Nat)
    (hlen : exponents.length = coreFactors.size)
    (hnot_dvd_tail :
      ∀ pre q e suf,
        coreFactors.toList.zip exponents = pre ++ (q, e) :: suf →
        ¬ q ∣ (suf.map (fun (qe : ZPoly × Nat) =>
                Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1)
    (hdecomp :
      rp = ((coreFactors.toList.zip exponents).map
              (fun (qe : ZPoly × Nat) =>
                Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1)
    (hfuel :
      ∀ (qe : ZPoly × Nat),
        qe ∈ coreFactors.toList.zip exponents → qe.2 + 1 ≤ rp.size + 1) :
    (expandRepeatedPartFactorArray rp coreFactors).2 = 1 := by
  refine expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition
    rp coreFactors hmonic hdegree exponents hlen ?_ ?_ hfuel
  · intro pre q e suf hsplit
    simpa [Factorization.factorPower] using hnot_dvd_tail pre q e suf hsplit
  · simpa [Factorization.factorPower] using hdecomp

/-- **#4778 HO-1 support lemma — non-monic array-level pow-decomposition expansion
helper.** Non-monic analogue of
`expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition`:
replaces the per-factor `Monic q` hypothesis by `0 < leadingCoeff q`,
delegating to the list-level non-monic helper
`expandRepeatedPartFactorsAux_residual_eq_one_of_pow_decomposition_of_pos_lc`.
Intermediate between the list-level proof and the public-API factorPower
wrapper below; used by
`expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc`
(the surface used by the quadratic-arm discharger
`reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero`,
#4747 residual). Dependency chain: #4773 → #4774 → here. -/
theorem expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition_of_pos_lc
    (rp : ZPoly) (coreFactors : Array ZPoly)
    (hpos_lc : ∀ q ∈ coreFactors.toList, 0 < DensePoly.leadingCoeff q)
    (hdegree : ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0)
    (exponents : List Nat)
    (hlen : exponents.length = coreFactors.size)
    (hnot_dvd_tail :
      ∀ pre q e suf,
        coreFactors.toList.zip exponents = pre ++ (q, e) :: suf →
        ¬ q ∣ (suf.map (fun (qe : ZPoly × Nat) =>
                Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1)
    (hdecomp :
      rp = ((coreFactors.toList.zip exponents).map
              (fun (qe : ZPoly × Nat) => Factorization.polyPow qe.1 qe.2)).foldl (· * ·) 1)
    (hfuel :
      ∀ (qe : ZPoly × Nat),
        qe ∈ coreFactors.toList.zip exponents → qe.2 + 1 ≤ rp.size + 1) :
    (expandRepeatedPartFactorArray rp coreFactors).2 = 1 := by
  unfold expandRepeatedPartFactorArray
  have hlen' : exponents.length = coreFactors.toList.length := by
    simpa using hlen
  exact expandRepeatedPartFactorsAux_residual_eq_one_of_pow_decomposition_of_pos_lc
    coreFactors.toList exponents rp (rp.size + 1)
    hlen' hpos_lc hdegree hnot_dvd_tail hdecomp hfuel

/-- **#4778 HO-1 support lemma — non-monic public `factorPower` array-level
expansion-complete surface.** Non-monic analogue of
`expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition`:
replaces the per-factor `Monic q` hypothesis by `0 < leadingCoeff q`, exposing
the contract using `Factorization.factorPower` (the public-API power operation
referenced by Mathlib-side assemblers). Consumed by the quadratic-arm
discharger `reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero`
(#4747 residual) when the core factor emitted by `quadraticIntegerRootFactors?`
is primitive and positive-leading but non-monic (e.g. the `2X + 3` residual
from `(X-1)(2X+3) = 2X^2 + X - 3`). Dependency chain: #4773 → #4774 → here. -/
theorem expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc
    (rp : ZPoly) (coreFactors : Array ZPoly)
    (hpos_lc : ∀ q ∈ coreFactors.toList, 0 < DensePoly.leadingCoeff q)
    (hdegree : ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0)
    (exponents : List Nat)
    (hlen : exponents.length = coreFactors.size)
    (hnot_dvd_tail :
      ∀ pre q e suf,
        coreFactors.toList.zip exponents = pre ++ (q, e) :: suf →
        ¬ q ∣ (suf.map (fun (qe : ZPoly × Nat) =>
                Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1)
    (hdecomp :
      rp = ((coreFactors.toList.zip exponents).map
              (fun (qe : ZPoly × Nat) =>
                Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1)
    (hfuel :
      ∀ (qe : ZPoly × Nat),
        qe ∈ coreFactors.toList.zip exponents → qe.2 + 1 ≤ rp.size + 1) :
    (expandRepeatedPartFactorArray rp coreFactors).2 = 1 := by
  refine expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition_of_pos_lc
    rp coreFactors hpos_lc hdegree exponents hlen ?_ ?_ hfuel
  · intro pre q e suf hsplit
    simpa [Factorization.factorPower] using hnot_dvd_tail pre q e suf hsplit
  · simpa [Factorization.factorPower] using hdecomp

/-- An irreducible `ZPoly` does not divide the unit `1`. Used by the small-mod
singleton arm specialisation `expandRepeatedPartFactorArray_pow_singleton`
(#4597 deliverable 2) to discharge the wrapper's tail-non-divisibility
precondition for the singleton case, where the suffix product collapses to
`1` and the only obligation is `¬ q ∣ 1`. The proof is a direct size argument:
`size_le_of_dvd_nonzero` would force `q.size ≤ 1`, but irreducibility (via the
non-zero, non-unit conditions on the leading coefficient) forces `q.size ≥ 2`. -/
private theorem irreducible_not_dvd_one {q : ZPoly}
    (hq_irr : ZPoly.Irreducible q) : ¬ q ∣ (1 : ZPoly) := by
  intro hdvd
  have hq_ne : q ≠ 0 := hq_irr.not_zero
  have hone_ne : (1 : ZPoly) ≠ 0 := by
    intro h
    have : (1 : ZPoly).size = 1 := rfl
    rw [h] at this
    exact absurd this (by decide)
  have hq_size_le : q.size ≤ (1 : ZPoly).size :=
    ZPoly.size_le_of_dvd_nonzero hq_ne hone_ne hdvd
  have h1 : (1 : ZPoly).size = 1 := rfl
  have hq_pos : 0 < q.size := ZPoly.size_pos_of_ne_zero q hq_ne
  have hq_one : q.size = 1 := by omega
  -- A `q` of size 1 is constant, hence the leading coefficient appears at
  -- index 0; combined with `q ∣ 1` forcing the leading coefficient to be a
  -- unit in `ℤ`, this contradicts `not_unit`.
  have hq_eq : q = DensePoly.C (q.coeff 0) := ZPoly.eq_C_of_size_eq_one q hq_one
  rcases hdvd with ⟨w, hw⟩
  -- hw : (1 : ZPoly) = q * w
  have hw_ne : w ≠ 0 := by
    intro hw_zero
    rw [hw_zero] at hw
    -- (1 : ZPoly) = q * 0 = 0, contradicting hone_ne
    rw [DensePoly.mul_comm_poly, DensePoly.zero_mul] at hw
    exact hone_ne hw
  have hw_pos : 0 < w.size := ZPoly.size_pos_of_ne_zero w hw_ne
  have hqw_size : (q * w).size = q.size + w.size - 1 :=
    ZPoly.mul_size_eq_top_succ_of_nonzero q w hq_pos hw_pos
  rw [← hw, h1] at hqw_size
  have hw_one : w.size = 1 := by omega
  have hlead :
      DensePoly.leadingCoeff q * DensePoly.leadingCoeff w = (1 : Int) := by
    have := ZPoly.leadingCoeff_mul_of_nonzero q w hq_ne hw_ne
    rw [← hw] at this
    have : DensePoly.leadingCoeff q * DensePoly.leadingCoeff w =
        DensePoly.leadingCoeff (1 : ZPoly) := this.symm
    rw [this]
    rfl
  have hq_lead : DensePoly.leadingCoeff q = q.coeff 0 := by
    rw [DensePoly.leadingCoeff_eq_coeff_last q (by omega)]
    congr 1; omega
  rw [hq_lead] at hlead
  have hcoeff_unit : q.coeff 0 = 1 ∨ q.coeff 0 = -1 :=
    ZPoly.int_factor_one_eq_unit hlead
  apply hq_irr.not_unit
  rcases hcoeff_unit with h | h
  · left; rw [hq_eq, h]
  · right; rw [hq_eq, h]

/-- **#4597 HO-1 support lemma — small-mod singleton arm expansion specialisation.**
Singleton specialisation of
`expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition`:
when the repeated part `rp` is the `k`-th `Hex.Factorization.factorPower` of an
irreducible monic positive-degree `q`, expanding against the singleton core
`#[q]` consumes the repeated part exactly, emitting `k` copies of `q` and
reporting residual `1`. Used by the small-mod singleton arm public wrapper
`factor_small_mod_singleton_branch_entry_irreducible_of_choosePrimeData`
(#4564 / PR #4581) via the public discharger
`Hex.reassemblyExpansionComplete_singleton_of_irreducible` (#4597
deliverable 3). Sibling specialisations: constant arm
`reassemblyExpansionComplete_constant_of_ne_zero` (#4585 / PR #4598);
quadratic arm tracked by #4747. -/
theorem expandRepeatedPartFactorArray_pow_singleton
    (q : ZPoly) (k : Nat)
    (hq_monic : DensePoly.Monic q)
    (hq_degree : 0 < q.degree?.getD 0)
    (hq_irr : ZPoly.Irreducible q)
    (rp : ZPoly) (hrp : rp = Factorization.factorPower q k)
    (hfuel : k + 1 ≤ rp.size + 1) :
    expandRepeatedPartFactorArray rp #[q] =
      ((List.replicate k q).toArray, 1) := by
  have hnot_dvd : ¬ q ∣ (1 : ZPoly) := irreducible_not_dvd_one hq_irr
  have hmul : rp = Factorization.polyPow q k * 1 := by
    rw [hrp]; exact (DensePoly.mul_one_right_poly _).symm
  have hcep : consumeExactPower rp q (rp.size + 1) = (1, k) := by
    rw [hmul]
    apply consumeExactPower_pow_mul_of_not_dvd q 1 k hq_monic hq_degree hnot_dvd
    rw [← hmul]; exact hfuel
  unfold expandRepeatedPartFactorArray
  show expandRepeatedPartFactorsAux [q] rp (rp.size + 1) = _
  unfold expandRepeatedPartFactorsAux
  rw [hcep]
  show ((List.replicate k q).toArray ++
      (expandRepeatedPartFactorsAux [] (1 : ZPoly) (rp.size + 1)).1,
      (expandRepeatedPartFactorsAux [] (1 : ZPoly) (rp.size + 1)).2) =
    ((List.replicate k q).toArray, 1)
  unfold expandRepeatedPartFactorsAux
  simp

/-- **#4955 support lemma — non-monic singleton arm expansion specialisation.**
Non-monic counterpart of `expandRepeatedPartFactorArray_pow_singleton`:
replaces the `Monic q` premise by `0 < leadingCoeff q`, with a
**weakened conclusion** — only the residual projection `.2 = 1`, not the
full pair. The full-pair version has no non-monic counterpart at the
executable layer (`consumeExactPower_pow_mul_of_not_dvd` is genuinely
monic-only; under non-monic `q`, the recursive `consumeExactPower` step's
quotient is not in general a power of `q`, even if the residual collapses
to `1`). The residual-only form suffices for the mid-layer
`_of_pos_lc` sibling of
`reassemblyExpansionComplete_singleton_of_irreducible` (#4956), which
unfolds `reassemblyExpansionComplete` to `(expand ...).2 = 1`. The
proof routes through the array-level public surface
`expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc`
(#4778) specialised to `coreFactors = #[q]`, `exponents = [k]`. -/
theorem expandRepeatedPartFactorArray_pow_singleton_of_pos_lc
    (q : ZPoly) (k : Nat)
    (hq_pos_lc : 0 < DensePoly.leadingCoeff q)
    (hq_degree : 0 < q.degree?.getD 0)
    (hq_irr : ZPoly.Irreducible q)
    (rp : ZPoly) (hrp : rp = Factorization.factorPower q k)
    (hfuel : k + 1 ≤ rp.size + 1) :
    (expandRepeatedPartFactorArray rp #[q]).2 = 1 := by
  have hsingleton_toList : (#[q] : Array ZPoly).toList = [q] := rfl
  refine expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc
    rp #[q] ?hpos_lc ?hdegree [k] ?hlen ?hnot_dvd_tail ?hdecomp ?hfuel
  · intro q' hq'
    rw [hsingleton_toList] at hq'
    have : q' = q := by simpa using hq'
    rw [this]; exact hq_pos_lc
  · intro q' hq'
    rw [hsingleton_toList] at hq'
    have : q' = q := by simpa using hq'
    rw [this]; exact hq_degree
  · rfl
  · intro pre q' e suf hsplit
    -- The zip reduces to `[(q, k)]`; length forces `pre = []` and `suf = []`.
    rw [hsingleton_toList] at hsplit
    have hzip : ([q] : List ZPoly).zip [k] = [(q, k)] := rfl
    rw [hzip] at hsplit
    have hlen_eq : 1 = pre.length + (suf.length + 1) := by
      have := congrArg List.length hsplit
      simpa using this
    have hpre_len : pre.length = 0 := by omega
    have hsuf_len : suf.length = 0 := by omega
    have hpre : pre = [] := List.length_eq_zero_iff.mp hpre_len
    have hsuf : suf = [] := List.length_eq_zero_iff.mp hsuf_len
    subst hpre; subst hsuf
    -- hsplit : [(q, k)] = [(q', e)]
    have hq'_eq : q' = q := by
      have h := hsplit
      simp at h
      exact h.1.symm
    simp only [List.map_nil, List.foldl_nil]
    rw [hq'_eq]
    exact irreducible_not_dvd_one hq_irr
  · rw [hrp, hsingleton_toList]
    simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
      List.foldl_cons, List.foldl_nil, ZPoly.one_mul_zpoly]
  · intro qe hqe
    rw [hsingleton_toList] at hqe
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false] at hqe
    rw [hqe]
    exact hfuel

/-- The reassembled output for a single-`1` core list is exactly the
normalization prefix followed by `1`. Both branches of `reassemblePolynomialFactors`
collapse to this shape because the expansion never extracts anything when the
sole candidate is the unit `1`. -/
private theorem reassemblePolynomialFactors_singleton_one_eq
    (d : FactorNormalizationData) :
    reassemblePolynomialFactors d #[1] = polynomialNormalizationPrefixFactors d ++ #[1] := by
  unfold reassemblePolynomialFactors
  rw [expandRepeatedPartFactorArray_singleton_one]
  simp only
  by_cases hrp : d.repeatedPart = 1
  · rw [if_pos hrp]
    unfold polynomialNormalizationPrefixFactors repeatedPartFactorArray
    rw [hrp]
    simp
  · rw [if_neg hrp]

private theorem squareFreeCore_ne_zero_of_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    (normalizeForFactor f).squareFreeCore ≠ 0 := by
  unfold normalizeForFactor
  simp only
  intro hzero
  have hcore_ne := extractXPower_core_ne_zero_of_ne_zero f hf
  have hprod_primitive :=
    ZPoly.primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive _ hcore_ne
  have hprod_ne :
      (ZPoly.primitiveSquareFreeDecomposition
            (ZPoly.extractXPower (ZPoly.primitivePart f)).core).squareFreeCore *
        (ZPoly.primitiveSquareFreeDecomposition
            (ZPoly.extractXPower (ZPoly.primitivePart f)).core).repeatedPart ≠ 0 :=
    ZPoly.ne_zero_of_primitive _ hprod_primitive
  apply hprod_ne
  rw [hzero]
  exact DensePoly.zero_mul _

theorem squareFreeCore_leadingCoeff_pos_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0) :
    0 < DensePoly.leadingCoeff (normalizeForFactor f).squareFreeCore := by
  have hne := squareFreeCore_ne_zero_of_ne_zero f hf
  have hnonneg :
      0 ≤ DensePoly.leadingCoeff (normalizeForFactor f).squareFreeCore := by
    unfold normalizeForFactor
    exact ZPoly.leadingCoeff_squareFreeCore_nonneg _
  have hne_lead :
      DensePoly.leadingCoeff (normalizeForFactor f).squareFreeCore ≠ 0 :=
    ZPoly.leadingCoeff_ne_zero_of_ne_zero _ hne
  omega

/-- The schoolbook step for the constant coefficient leaves the accumulator
unchanged across any run of strictly positive inner indices: `i + j = 0` is
impossible once `0 < j`. -/
private theorem foldl_step_const_inner_pos (p q : ZPoly) (xs : List Nat) :
    (∀ j ∈ xs, 0 < j) → ∀ acc : Int,
      xs.foldl (DensePoly.mulCoeffStep p q 0 0) acc = acc := by
  induction xs with
  | nil => intro _ acc; rfl
  | cons j xs ih =>
      intro hpos acc
      rw [List.foldl_cons]
      have hj : 0 < j := hpos j List.mem_cons_self
      have hstep : DensePoly.mulCoeffStep p q 0 0 acc j = acc := by
        unfold DensePoly.mulCoeffStep
        rw [if_neg (by omega)]
      rw [hstep]
      exact ih (fun j' hj' => hpos j' (List.mem_cons_of_mem j hj')) acc

/-- The schoolbook step for the constant coefficient at a strictly positive
outer index `i` leaves the accumulator unchanged: `i + j = 0` is impossible once
`0 < i`. -/
private theorem foldl_step_const_pos_i (p q : ZPoly) (i : Nat) (hi : 0 < i)
    (xs : List Nat) (acc : Int) :
    xs.foldl (DensePoly.mulCoeffStep p q 0 i) acc = acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons j xs ih =>
      rw [List.foldl_cons]
      have hstep : DensePoly.mulCoeffStep p q 0 i acc j = acc := by
        unfold DensePoly.mulCoeffStep
        rw [if_neg (by omega)]
      rw [hstep]; exact ih acc

/-- The inner schoolbook fold for the constant coefficient at outer index `0`
contributes exactly `p.coeff 0 * q.coeff 0` once, when the inner index range is
nonempty: only `j = 0` satisfies `0 + j = 0`. -/
private theorem foldl_step_const_inner (p q : ZPoly) (m : Nat) (acc : Int) :
    (List.range m).foldl (DensePoly.mulCoeffStep p q 0 0) acc
      = if 0 < m then acc + p.coeff 0 * q.coeff 0 else acc := by
  cases m with
  | zero => simp
  | succ n =>
      rw [List.range_succ_eq_map, List.foldl_cons]
      have h0 : DensePoly.mulCoeffStep p q 0 0 acc 0 = acc + p.coeff 0 * q.coeff 0 := by
        unfold DensePoly.mulCoeffStep
        simp
      rw [h0]
      have hpos : ∀ j ∈ (List.range n).map Nat.succ, 0 < j := by
        intro j hj
        rw [List.mem_map] at hj
        obtain ⟨k, _, rfl⟩ := hj
        exact Nat.succ_pos k
      rw [foldl_step_const_inner_pos p q _ hpos]
      simp

/-- The outer schoolbook fold for the constant coefficient leaves the
accumulator unchanged across any run of strictly positive outer indices. -/
private theorem foldl_outer_const_pos (p q : ZPoly) (xs : List Nat) :
    (∀ i ∈ xs, 0 < i) → ∀ acc : Int,
      xs.foldl
          (fun acc i => (List.range q.size).foldl (DensePoly.mulCoeffStep p q 0 i) acc) acc
        = acc := by
  induction xs with
  | nil => intro _ acc; rfl
  | cons i xs ih =>
      intro hpos acc
      rw [List.foldl_cons]
      have hi : 0 < i := hpos i List.mem_cons_self
      rw [foldl_step_const_pos_i p q i hi]
      exact ih (fun i' hi' => hpos i' (List.mem_cons_of_mem i hi')) acc

/-- The schoolbook coefficient fold at degree `0` evaluates to the product of the
two constant terms: only the `(0, 0)` index pair contributes to `i + j = 0`. -/
private theorem mulCoeffSum_const (p q : ZPoly) :
    DensePoly.mulCoeffSum p q 0 = p.coeff 0 * q.coeff 0 := by
  unfold DensePoly.mulCoeffSum
  cases hp : p.size with
  | zero =>
      simp only [List.range_zero, List.foldl_nil]
      have hp0 : p.coeff 0 = 0 := DensePoly.coeff_eq_zero_of_size_le p (by omega)
      show (0 : Int) = p.coeff 0 * q.coeff 0
      rw [hp0, Int.zero_mul]
  | succ n =>
      have hpos : ∀ i ∈ (List.range n).map Nat.succ, 0 < i := by
        intro i hi
        rw [List.mem_map] at hi
        obtain ⟨k, _, rfl⟩ := hi
        exact Nat.succ_pos k
      rw [List.range_succ_eq_map, List.foldl_cons, foldl_outer_const_pos p q _ hpos,
        foldl_step_const_inner p q q.size]
      by_cases hq : 0 < q.size
      · rw [if_pos hq]
        show (0 : Int) + p.coeff 0 * q.coeff 0 = p.coeff 0 * q.coeff 0
        rw [Int.zero_add]
      · rw [if_neg hq]
        have hq0 : q.coeff 0 = 0 := DensePoly.coeff_eq_zero_of_size_le q (by omega)
        show (0 : Int) = p.coeff 0 * q.coeff 0
        rw [hq0, Int.mul_zero]

/-- The constant term of a product of integer polynomials is the product of the
constant terms. -/
private theorem coeff_mul_const (p q : ZPoly) :
    (p * q).coeff 0 = p.coeff 0 * q.coeff 0 := by
  rw [DensePoly.coeff_mul]
  exact mulCoeffSum_const p q

/-- Either the zero-stripped tail of a coefficient list is empty, or its head is
nonzero: `splitInitialZeros` removes exactly the leading zero run. -/
private theorem splitInitialZeros_tail_getD_ne_zero (coeffs : List Int) :
    (ZPoly.splitInitialZeros coeffs).2 = [] ∨
      (ZPoly.splitInitialZeros coeffs).2.getD 0 0 ≠ 0 := by
  induction coeffs with
  | nil => exact Or.inl rfl
  | cons c cs ih =>
      unfold ZPoly.splitInitialZeros
      by_cases hc : c = 0
      · rw [if_pos hc]; simpa using ih
      · rw [if_neg hc]; exact Or.inr (by simpa using hc)

/-- The `X`-power-free core extracted from a nonzero primitive part has a nonzero
constant term: `extractXPower` strips the leading zero run, so the lowest stored
coefficient is nonzero. -/
private theorem extractXPower_core_coeff_zero_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    (ZPoly.extractXPower (ZPoly.primitivePart f)).core.coeff 0 ≠ 0 := by
  have hcore_ne := extractXPower_core_ne_zero_of_ne_zero f hf
  rcases splitInitialZeros_tail_getD_ne_zero (ZPoly.primitivePart f).toArray.toList with
    hempty | hne
  · exfalso
    apply hcore_ne
    simp only [ZPoly.extractXPower]
    rw [hempty]
    simp [DensePoly.ofCoeffs_empty]
  · simp only [ZPoly.extractXPower]
    rw [DensePoly.coeff_ofCoeffs_list]
    exact hne

/-- The reachable square-free core has a nonzero constant term.
`normalizeForFactor` strips the visible power of `X` (via `extractXPower`) before
`primitiveSquareFreeDecomposition`, so the core fed to the prime/lift pipeline is
not divisible by `X`. Over `ℚ` the primitive part reassembles as a unit scalar
times `squareFreeCore * repeatedPart`; reading the constant term forces
`squareFreeCore.coeff 0 ≠ 0`. -/
theorem squareFreeCore_coeff_zero_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    (normalizeForFactor f).squareFreeCore.coeff 0 ≠ 0 := by
  have hcore0 : (ZPoly.extractXPower (ZPoly.primitivePart f)).core.coeff 0 ≠ 0 :=
    extractXPower_core_coeff_zero_ne_zero f hf
  obtain ⟨unit, hunit⟩ :=
    primitiveSquareFreeDecomposition_reassembles_xfree_over_rat
      (ZPoly.extractXPower (ZPoly.primitivePart f)).core
  show (ZPoly.primitiveSquareFreeDecomposition
      (ZPoly.extractXPower (ZPoly.primitivePart f)).core).squareFreeCore.coeff 0 ≠ 0
  intro hsfc0
  have hc :
      (ZPoly.extractXPower (ZPoly.primitivePart f)).core.toRatPoly.coeff 0 =
        (DensePoly.scale unit
          ((ZPoly.primitiveSquareFreeDecomposition
                (ZPoly.extractXPower (ZPoly.primitivePart f)).core).squareFreeCore *
              (ZPoly.primitiveSquareFreeDecomposition
                (ZPoly.extractXPower (ZPoly.primitivePart f)).core).repeatedPart).toRatPoly).coeff 0 :=
    congrArg (fun p : DensePoly Rat => p.coeff 0) hunit
  rw [ZPoly.coeff_toRatPoly] at hc
  rw [DensePoly.coeff_scale (R := Rat) unit _ 0 (Rat.mul_zero unit)] at hc
  rw [ZPoly.coeff_toRatPoly, coeff_mul_const, hsfc0] at hc
  simp at hc
  exact hcore0 (by exact_mod_cast hc)

/-- A left factor of a primitive `ZPoly` product is itself primitive. Integer
content is non-negative, so `content p * content q = 1` forces `content p = 1`.
Local helper for `squareFreeCore_primitive_of_ne_zero`. -/
private theorem ZPoly_primitive_left_of_mul (p q : ZPoly)
    (h : ZPoly.Primitive (p * q)) : ZPoly.Primitive p := by
  have hone : ZPoly.content p * ZPoly.content q = 1 := by
    rw [← ZPoly.content_mul]; exact h
  have hp_nn : 0 ≤ ZPoly.content p := by
    show 0 ≤ DensePoly.content p
    rw [DensePoly.content]
    exact Int.natCast_nonneg _
  have hdvd : ZPoly.content p ∣ (1 : Int) := ⟨ZPoly.content q, hone.symm⟩
  have habs : (ZPoly.content p).natAbs ∣ (1 : Nat) := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have habs_le : (ZPoly.content p).natAbs ≤ 1 := Nat.le_of_dvd (by omega) habs
  have hp_ne : ZPoly.content p ≠ 0 := by
    intro hzero
    rw [hzero, Int.zero_mul] at hone
    omega
  have habs_pos : 1 ≤ (ZPoly.content p).natAbs := by
    rcases Nat.eq_zero_or_pos (ZPoly.content p).natAbs with hz | hp
    · exact absurd (Int.natAbs_eq_zero.mp hz) hp_ne
    · exact hp
  have habs_eq : (ZPoly.content p).natAbs = 1 := by omega
  show ZPoly.content p = 1
  rcases Int.natAbs_eq (ZPoly.content p) with heq | heq
  · rw [heq, habs_eq]; rfl
  · rw [heq, habs_eq] at hp_nn
    omega

/-- The normalized square-free core is primitive whenever the input is nonzero.
Discharges the `ZPoly.Primitive core` precondition of
`exhaustiveIntegerTrialCoreFactorsWithBound_factor_irreducible` (`:13443`) and
`quadraticIntegerRootFactors?_factor_irreducible_of_primitive` (`:14060`) when
both are specialised to `(normalizeForFactor f).squareFreeCore`. The proof
extracts the left factor of the `squareFreeCore * repeatedPart` primitivity
invariant supplied by
`ZPoly.primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive`.
-/
theorem squareFreeCore_primitive_of_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    ZPoly.Primitive (normalizeForFactor f).squareFreeCore := by
  unfold normalizeForFactor
  simp only
  have hcore_ne := extractXPower_core_ne_zero_of_ne_zero f hf
  have hprod_primitive :=
    ZPoly.primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive _ hcore_ne
  exact ZPoly_primitive_left_of_mul _ _ hprod_primitive

/-- The normalized square-free core is square-free over `ℚ` whenever the input
is nonzero. Discharges the `Hex.ZPoly.SquareFreeRat core` precondition of
`exhaustiveIntegerTrialCoreFactorsWithBound_factor_irreducible` (`:13443`) and
`quadraticIntegerRootFactors?_factor_irreducible_of_primitive` (`:14060`) when
both are specialised to `(normalizeForFactor f).squareFreeCore`. The proof
forwards the recorded core's non-zeroness (from `squareFreeCore_ne_zero_of_ne_zero`)
to `ZPoly.primitiveSquareFreeDecomposition_squareFreeCore`, which gives the
intrinsic square-free-over-`ℚ` invariant of the decomposition. -/
theorem squareFreeCore_squareFreeRat_of_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    Hex.ZPoly.SquareFreeRat (normalizeForFactor f).squareFreeCore := by
  have hcore_ne := squareFreeCore_ne_zero_of_ne_zero f hf
  unfold normalizeForFactor at hcore_ne ⊢
  simp only at hcore_ne ⊢
  exact ZPoly.primitiveSquareFreeDecomposition_squareFreeCore _ hcore_ne

/-- When the normalized square-free core has degree zero (and `f ≠ 0`), the
primitive square-free decomposition forces the core to be exactly `1`.  Exposed
publicly so Mathlib-side per-branch wrappers (in particular the fast-path
constant arm) can rule out the singleton-core entry from the recorded factor
set. -/
theorem squareFreeCore_eq_one_of_constant_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0) :
    (normalizeForFactor f).squareFreeCore = 1 := by
  unfold normalizeForFactor at hdeg ⊢
  simpa using
    ZPoly.primitiveSquareFreeDecomposition_squareFreeCore_eq_one_of_degree_zero
      (ZPoly.extractXPower (ZPoly.primitivePart f)).core
      (by
        exact squareFreeCore_ne_zero_of_ne_zero f hf)
      hdeg

/-- Companion to `squareFreeCore_eq_one_of_constant_of_ne_zero`: the recorded
`repeatedPart` collapses to `1` in the constant branch. -/
private theorem normalizeForFactor_repeatedPart_eq_one_of_constant
    (f : ZPoly) (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0) :
    (normalizeForFactor f).repeatedPart = 1 := by
  unfold normalizeForFactor at hdeg ⊢
  simpa using
    ZPoly.primitiveSquareFreeDecomposition_repeatedPart_eq_one_of_squareFreeCore_degree_zero
      (ZPoly.extractXPower (ZPoly.primitivePart f)).core
      (by
        exact squareFreeCore_ne_zero_of_ne_zero f hf)
      hdeg

end Hex
