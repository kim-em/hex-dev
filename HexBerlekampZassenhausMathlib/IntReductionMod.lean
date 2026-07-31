/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampMathlib.Irreducibility
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Polynomial.Radical
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import HexBerlekampZassenhausMathlib.IntReductionMod.Transport
import all HexBerlekampZassenhausMathlib.IntReductionMod.Descent
import all HexBerlekampZassenhausMathlib.IntReductionMod.Transport
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.ModularPolynomial

public section
set_option backward.proofsInPublic true

/-!
Public trial-tier soundness built from the reduction-mod-`p` descent core and
the repeated-part/reassembly transport.
-/
namespace HexBerlekampZassenhausMathlib
set_option maxHeartbeats 8000000

set_option maxHeartbeats 4000000 in
set_option maxHeartbeats 8000000


/-- Divisibility propagation through `List.foldl (· * ·)` on `Hex.ZPoly`: if
`x` divides the accumulator at any point, it divides the final foldl. Used by
`mem_dvd_foldl_mul_zpoly`. -/
private theorem dvd_acc_foldl_mul_zpoly (x : Hex.ZPoly) :
    ∀ (l : List Hex.ZPoly) (acc : Hex.ZPoly),
      x ∣ acc → x ∣ l.foldl (· * ·) acc := by
  intro l
  induction l with
  | nil =>
      intro acc hacc
      simpa using hacc
  | cons head tail ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      refine ih (acc * head) ?_
      -- `x ∣ acc * head` from `x ∣ acc` via commutativity + `dvd_mul_left_poly`.
      have hcomm : acc * head = head * acc := Hex.DensePoly.mul_comm_poly (S := Int) acc head
      rw [hcomm]
      exact Hex.DensePoly.dvd_mul_left_poly head hacc

/-- An element of a `List Hex.ZPoly` divides the `List.foldl (· * ·)` of that
list. Used by the exhaustive-arm fuel-bound construction in
`reassemblyExpansionComplete_exhaustive_of_ne_zero`. -/
private theorem mem_dvd_foldl_mul_zpoly
    (l : List Hex.ZPoly) (acc : Hex.ZPoly) (x : Hex.ZPoly) (hx : x ∈ l) :
    x ∣ l.foldl (· * ·) acc := by
  induction l generalizing acc with
  | nil => exact absurd hx (List.not_mem_nil)
  | cons head tail ih =>
      rw [List.mem_cons] at hx
      simp only [List.foldl_cons]
      rcases hx with rfl | hx
      · -- `x = head`: divides `acc * x = acc * head`, and propagates through tail.
        refine dvd_acc_foldl_mul_zpoly x tail (acc * x) ?_
        have hcomm : acc * x = x * acc := Hex.DensePoly.mul_comm_poly (S := Int) acc x
        rw [hcomm]
        exact ⟨acc, rfl⟩
      · exact ih (acc * head) hx

/-- For a polynomial `q` of positive degree, the size of
`Hex.Factorization.factorPower q m` is at least `m + 1`. Each iteration of
`polyPow` multiplies the running product by `q`, increasing the size by at
least `q.size - 1 ≥ 1`. -/
private theorem factorPower_size_lower_bound
    {q : Hex.ZPoly} (hq_deg : 0 < q.degree?.getD 0) :
    ∀ m : Nat, m + 1 ≤ (Hex.Factorization.factorPower q m).size := by
  intro m
  -- From `0 < q.degree?.getD 0`, derive `2 ≤ q.size`.
  have hq_size_ge_two : 2 ≤ q.size := by
    have hdeg_unfold : q.degree?.getD 0 =
        (if q.size = 0 then 0 else q.size - 1) := by
      unfold Hex.DensePoly.degree?
      by_cases h : q.size = 0 <;> simp [h]
    rw [hdeg_unfold] at hq_deg
    by_cases h : q.size = 0
    · simp [h] at hq_deg
    · split at hq_deg <;> omega
  induction m with
  | zero =>
      show 1 ≤ (1 : Hex.ZPoly).size
      rfl
  | succ n ih =>
      rw [Hex.Factorization.factorPower_succ]
      have hprev_pos : 0 < (Hex.Factorization.factorPower q n).size := by
        omega
      have hq_pos : 0 < q.size := by omega
      have hmul_size :
          (Hex.Factorization.factorPower q n * q).size =
            (Hex.Factorization.factorPower q n).size + q.size - 1 :=
        Hex.ZPoly.mul_size_eq_top_succ_of_nonzero _ _ hprev_pos hq_pos
      omega

set_option maxHeartbeats 200000


/-- Mathlib-side abstract-bound wrapper for the slow-trial exhaustive arm.

Specialises the Mathlib-free
`Hex.exhaustiveIntegerTrialCoreFactorsWithBound_factor_irreducible`
(`HexBerlekampZassenhaus`) to the normalized square-free
core of an `f ≠ 0` input, discharging the four core-shape hypotheses
(`ne_zero`, `Primitive`, `0 < leadingCoeff`, `SquareFreeRat`) from `hf_ne`
via the existing helpers:

* `Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero` for `0 < leadingCoeff`
  (and `zpoly_ne_zero_of_pos_lc` for `ne_zero`);
* `normalizeForFactor_squareFreeCore_primitive_of_ne_zero` (Mathlib-side)
  for `Primitive`;
* `Hex.ZPoly.primitiveSquareFreeDecomposition_squareFreeCore` for
  `SquareFreeRat`.

The divisor coefficient bound `hbound` stays explicit because two natural
specialisations live downstream: the intrinsic-core form
(`B := Hex.ZPoly.defaultFactorCoeffBound (Hex.normalizeForFactor f).squareFreeCore`,
discharged below by `defaultFactorCoeffBound_valid` on the core) and the
public-bound form (`B := Hex.ZPoly.defaultFactorCoeffBound f`, required
by the slow-trial arm of the `h_raw` dispatch in
`factor_entry_zpolyIrreducible_of_chosen_raw_zpolyIrreducible`), which
needs the `g ∣ (Hex.normalizeForFactor f).squareFreeCore → g ∣ f`
divisibility chain through `primitiveSquareFreeDecomposition_reassembly_signed`
and the primitive-part divisibility relation. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_of_bound
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat)
    (hbound : ∀ g : Hex.ZPoly,
      g ∣ (Hex.normalizeForFactor f).squareFreeCore →
      ∀ i, (g.coeff i).natAbs ≤ B) :
    ∀ factor ∈ (Hex.exhaustiveIntegerTrialCoreFactorsWithBound
                  (Hex.normalizeForFactor f).squareFreeCore B).toList,
      Hex.ZPoly.Irreducible factor := by
  intro factor hmem
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_pos
  have hcore_prim :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf_ne
  have hcore_sq : Hex.ZPoly.SquareFreeRat (Hex.normalizeForFactor f).squareFreeCore := by
    have hsq :=
      Hex.ZPoly.primitiveSquareFreeDecomposition_squareFreeCore
        (Hex.ZPoly.extractXPower (Hex.ZPoly.primitivePart f)).core
        (by simpa [Hex.normalizeForFactor] using hcore_ne)
    simpa [Hex.normalizeForFactor] using hsq
  exact Hex.exhaustiveIntegerTrialCoreFactorsWithBound_factor_irreducible
    (Hex.normalizeForFactor f).squareFreeCore B
    hcore_ne hcore_prim hcore_pos hcore_sq hbound factor hmem

/-- Intrinsic-core default-bound specialisation of
`exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_of_bound`
at `B := Hex.ZPoly.defaultFactorCoeffBound (Hex.normalizeForFactor f).squareFreeCore`.

The divisor coefficient bound is discharged directly by
`defaultFactorCoeffBound_valid` applied to the (nonzero) square-free core.
This is the natural specialisation for callers that have already routed
through the core's intrinsic Mignotte data; the public slow-trial dispatch
in `Hex.factorTrialFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f)`
uses the outer bound `Hex.ZPoly.defaultFactorCoeffBound f`, which requires
an additional `(Hex.normalizeForFactor f).squareFreeCore ∣ f` divisibility
chain (tracked separately) to discharge against this wrapper's `hbound`. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_at_squareFreeCore_default
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) :
    ∀ factor ∈ (Hex.exhaustiveIntegerTrialCoreFactorsWithBound
                  (Hex.normalizeForFactor f).squareFreeCore
                  (Hex.ZPoly.defaultFactorCoeffBound
                    (Hex.normalizeForFactor f).squareFreeCore)).toList,
      Hex.ZPoly.Irreducible factor := by
  intro factor hmem
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_pos
  exact
    exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_of_bound
      f hf_ne
      (Hex.ZPoly.defaultFactorCoeffBound (Hex.normalizeForFactor f).squareFreeCore)
      (defaultFactorCoeffBound_valid
        (Hex.normalizeForFactor f).squareFreeCore hcore_ne)
      factor hmem

/-- Transitivity of `∣` on `Hex.ZPoly`, Mathlib-side.  Composes the witness
multiplications explicitly. -/
private theorem zpoly_dvd_trans {a b c : Hex.ZPoly} (hab : a ∣ b) (hbc : b ∣ c) :
    a ∣ c := by
  obtain ⟨q, hq⟩ := hab
  obtain ⟨r, hr⟩ := hbc
  exact ⟨q * r, by rw [hr, hq, Hex.DensePoly.mul_assoc_poly (S := Int)]⟩

/-- Public-bound specialisation of
`exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_of_bound`
at the outer bound `B := Hex.ZPoly.defaultFactorCoeffBound f` consumed by the
slow-trial arm of the `h_raw` dispatch.

The divisor coefficient bound is discharged by lifting
`defaultFactorCoeffBound_valid f` along `Hex.squareFreeCore_dvd_self`: any
divisor of the square-free core also divides `f`, so its coefficients are
bounded by `Hex.ZPoly.defaultFactorCoeffBound f`. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_at_default
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) :
    ∀ factor ∈ (Hex.exhaustiveIntegerTrialCoreFactorsWithBound
                  (Hex.normalizeForFactor f).squareFreeCore
                  (Hex.ZPoly.defaultFactorCoeffBound f)).toList,
      Hex.ZPoly.Irreducible factor := by
  intro factor hmem
  refine
    exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_of_bound
      f hf_ne (Hex.ZPoly.defaultFactorCoeffBound f) ?_ factor hmem
  intro g hg i
  exact defaultFactorCoeffBound_valid f hf_ne g
    (zpoly_dvd_trans hg (Hex.squareFreeCore_dvd_self f hf_ne)) i

/-- **Slow-trial exhaustive-arm reassembly discharger (Mathlib-side).**

When the slow trial path takes the exhaustive branch, the reassembly of the
integer-trial core factors of `(normalizeForFactor f).squareFreeCore` at the
public bound `B := Hex.ZPoly.defaultFactorCoeffBound f` is expansion-complete.
The integer-trial analog of
`reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero`: it
composes the public-bound core irreducibility wrapper, the polyProduct /
normalizeFactorSign / degree-positivity companions, and the non-monic
expansion-complete surface `reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc`.
Per-factor positive leading coefficient follows from the sign-normalisation
identity and irreducibility; the fuel bound from the per-factor
`factorPower` size lower bound and `size_le_of_dvd_nonzero`. -/
theorem reassemblyExpansionComplete_exhaustiveIntegerTrial_of_ne_zero
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
      (Hex.exhaustiveIntegerTrialCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)) := by
  classical
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_prim :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
  set coreFactors :=
    Hex.exhaustiveIntegerTrialCoreFactorsWithBound
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f) with hcf
  have hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q :=
    exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_at_default f hf
  have hprod :
      Array.polyProduct coreFactors = (Hex.normalizeForFactor f).squareFreeCore :=
    Hex.exhaustiveIntegerTrialCoreFactorsWithBound_polyProduct _ _
  have hnorm : ∀ q ∈ coreFactors.toList, Hex.normalizeFactorSign q = q :=
    Hex.exhaustiveIntegerTrialCoreFactorsWithBound_normalizeFactorSign _ _ hcore_pos
  have hdegree : ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0 :=
    Hex.exhaustiveIntegerTrialCoreFactorsWithBound_degree_pos _ _ hcore_prim hcore_pos
  -- Per-factor positive leading coefficient from `normalizeFactorSign q = q`
  -- and irreducibility (hence `q ≠ 0`).
  have hpos_lc : ∀ q ∈ coreFactors.toList, 0 < Hex.DensePoly.leadingCoeff q := by
    intro q hq
    have hq_ne : q ≠ 0 := (hirr q hq).not_zero
    have hq_norm := hnorm q hq
    have hq_nonneg : 0 ≤ Hex.DensePoly.leadingCoeff q := by
      by_contra hlt
      have hlt' : Hex.DensePoly.leadingCoeff q < 0 := lt_of_not_ge hlt
      unfold Hex.normalizeFactorSign at hq_norm
      rw [if_pos hlt'] at hq_norm
      apply hq_ne
      apply Hex.DensePoly.ext_coeff
      intro n
      have hcoeff :
          (Hex.DensePoly.scale (-1 : Int) q).coeff n = q.coeff n := by
        rw [hq_norm]
      rw [Hex.DensePoly.coeff_scale (R := Int) (-1) q n
        (by decide : (-1 : Int) * 0 = 0)] at hcoeff
      rw [Hex.DensePoly.coeff_zero]
      omega
    have hq_lc_ne : Hex.DensePoly.leadingCoeff q ≠ 0 :=
      Hex.ZPoly.leadingCoeff_ne_zero_of_ne_zero q hq_ne
    omega
  refine IntReductionMod.reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc
    f hf coreFactors hirr hprod hnorm hpos_lc hdegree ?_
  -- Fuel bound.
  intro exponents hlen hdecomp
  have hsize_ge : ∀ q ∈ coreFactors.toList, 2 ≤ q.size := by
    intro q hq
    have hq_ne : q ≠ 0 := (hirr q hq).not_zero
    have hq_size_pos : 0 < q.size := Hex.ZPoly.size_pos_of_ne_zero q hq_ne
    have hq_deg := hdegree q hq
    have hq_deg_eq : q.degree?.getD 0 = q.size - 1 := by
      unfold Hex.DensePoly.degree?
      simp [Nat.ne_of_gt hq_size_pos]
    omega
  have hrp_ne_zero : (Hex.normalizeForFactor f).repeatedPart ≠ 0 := by
    intro hzero
    have hR_prim :=
      IntReductionMod.normalizeForFactor_repeatedPart_toPolynomial_isPrimitive f hf
    apply hR_prim.ne_zero
    show HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart = 0
    rw [hzero]
    exact HexPolyZMathlib.toPolynomial_zero
  have dvd_foldl_one_of_mem :
      ∀ (x : Hex.ZPoly) (xs : List Hex.ZPoly),
        x ∈ xs → x ∣ xs.foldl (· * ·) (1 : Hex.ZPoly) := by
    intro x xs
    induction xs with
    | nil =>
        intro hmem
        exact absurd hmem List.not_mem_nil
    | cons y ys ih =>
        intro hmem
        rcases List.mem_cons.mp hmem with rfl | hin
        · rw [List.foldl_cons, Hex.ZPoly.one_mul_zpoly,
              Hex.ZPoly.list_foldl_mul_eq_mul_foldl_one]
          exact ⟨ys.foldl (· * ·) 1, rfl⟩
        · rw [List.foldl_cons, Hex.ZPoly.one_mul_zpoly,
              Hex.ZPoly.list_foldl_mul_eq_mul_foldl_one y ys]
          obtain ⟨k, hk⟩ := ih hin
          refine ⟨y * k, ?_⟩
          rw [hk, ← Hex.DensePoly.mul_assoc_poly (S := Int),
              Hex.DensePoly.mul_comm_poly (S := Int) y x,
              Hex.DensePoly.mul_assoc_poly (S := Int)]
  have factorPower_size_lb :
      ∀ (q : Hex.ZPoly) (e : Nat),
        2 ≤ q.size → e + 1 ≤ (Hex.Factorization.factorPower q e).size := by
    intro q e hq_size
    induction e with
    | zero =>
        show 1 ≤ (1 : Hex.ZPoly).size
        rfl
    | succ n ih =>
        rw [Hex.Factorization.factorPower_succ]
        have hprev_size_pos :
            0 < (Hex.Factorization.factorPower q n).size := by omega
        have hq_size_pos : 0 < q.size := by omega
        have hmul_size :
            (Hex.Factorization.factorPower q n * q).size =
              (Hex.Factorization.factorPower q n).size + q.size - 1 :=
          Hex.ZPoly.mul_size_eq_top_succ_of_nonzero _ _ hprev_size_pos hq_size_pos
        omega
  intro qe hqe_mem
  have hq_mem : qe.1 ∈ coreFactors.toList := List.of_mem_zip hqe_mem |>.1
  have hq_size := hsize_ge qe.1 hq_mem
  have hfp_size_lb :
      qe.2 + 1 ≤ (Hex.Factorization.factorPower qe.1 qe.2).size :=
    factorPower_size_lb qe.1 qe.2 hq_size
  have hfp_ne_zero : Hex.Factorization.factorPower qe.1 qe.2 ≠ 0 := by
    intro hzero
    rw [hzero] at hfp_size_lb
    have h0 : (0 : Hex.ZPoly).size = 0 := rfl
    omega
  have hfp_mem :
      Hex.Factorization.factorPower qe.1 qe.2 ∈
        ((coreFactors.toList.zip exponents).map
          (fun qe' => Hex.Factorization.factorPower qe'.1 qe'.2)) :=
    List.mem_map.mpr ⟨qe, hqe_mem, rfl⟩
  have hfp_dvd_rp :
      Hex.Factorization.factorPower qe.1 qe.2 ∣
        (Hex.normalizeForFactor f).repeatedPart := by
    rw [hdecomp]
    exact dvd_foldl_one_of_mem _ _ hfp_mem
  have hfp_size_le :
      (Hex.Factorization.factorPower qe.1 qe.2).size ≤
        (Hex.normalizeForFactor f).repeatedPart.size :=
    Hex.ZPoly.size_le_of_dvd_nonzero hfp_ne_zero hrp_ne_zero hfp_dvd_rp
  omega

/-- Reassembly expansion-completeness for successful BHKS recovery from the
recovery result and irreducibility of its factors.

The product, sign normalization, degree, leading-coefficient, and fuel facts
follow from `hcore`; only per-factor irreducibility is assumed separately. -/
theorem reassemblyComplete_of_bhksRecovery_irreducible
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat) (primeData : Hex.PrimeChoiceData)
    {expectedFactors : Array Hex.ZPoly}
    (hcore :
      Hex.bhksRecoveryCoreWithBound (Hex.normalizeForFactor f).squareFreeCore B
        primeData (Hex.initialHenselPrecision B)
        (Hex.ZPoly.quadraticDoublingSteps B + 2) =
          some expectedFactors)
    (hirr : ∀ q ∈ expectedFactors.toList, Hex.ZPoly.Irreducible q) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f) expectedFactors := by
  have hprod :
      Array.polyProduct expectedFactors =
        (Hex.normalizeForFactor f).squareFreeCore := by
    simpa using
      Hex.bhksRecoveryCoreWithBound_product
        (Hex.normalizeForFactor f).squareFreeCore B primeData
        (Hex.initialHenselPrecision B) (Hex.ZPoly.quadraticDoublingSteps B + 2)
        expectedFactors hcore
  have hnorm :
      ∀ q ∈ expectedFactors.toList, Hex.normalizeFactorSign q = q := by
    intro q hq
    exact Hex.bhksRecoveryCoreWithBound_some_normalizeFactorSign hcore q hq
  have hdegree :
      ∀ q ∈ expectedFactors.toList, 0 < q.degree?.getD 0 := by
    intro q hq
    exact Hex.bhksRecoveryCoreWithBound_some_degree_pos hcore q hq
  have hpos_lc :
      ∀ q ∈ expectedFactors.toList, 0 < Hex.DensePoly.leadingCoeff q := by
    intro q hq
    have hq_ne : q ≠ 0 := (hirr q hq).not_zero
    have hq_norm : Hex.normalizeFactorSign q = q := hnorm q hq
    have hq_nonneg : 0 ≤ Hex.DensePoly.leadingCoeff q := by
      rw [← hq_norm]
      exact leadingCoeff_normalizeFactorSign_nonneg q
    have hq_lc_ne : Hex.DensePoly.leadingCoeff q ≠ 0 :=
      Hex.ZPoly.leadingCoeff_ne_zero_of_ne_zero q hq_ne
    omega
  have hrp_ne :
      (Hex.normalizeForFactor f).repeatedPart ≠ 0 :=
    Hex.repeatedPart_ne_zero_of_ne_zero f hf_ne
  have hfuel :
      ∀ exponents : List Nat,
        exponents.length = expectedFactors.size →
        (Hex.normalizeForFactor f).repeatedPart =
          ((expectedFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 →
        ∀ (qe : Hex.ZPoly × Nat),
          qe ∈ expectedFactors.toList.zip exponents →
            qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    intro exponents _ hdecomp qe hqe
    have hq_mem : qe.1 ∈ expectedFactors.toList :=
      (List.of_mem_zip hqe).1
    have hq_deg : 0 < qe.1.degree?.getD 0 := hdegree qe.1 hq_mem
    have hfp_size_lb : qe.2 + 1 ≤
        (Hex.Factorization.factorPower qe.1 qe.2).size :=
      factorPower_size_lower_bound hq_deg qe.2
    have hfp_ne : Hex.Factorization.factorPower qe.1 qe.2 ≠ 0 := by
      intro h0
      have : (Hex.Factorization.factorPower qe.1 qe.2).size = 0 := by
        rw [h0]
        rfl
      omega
    have hfp_in_map :
        Hex.Factorization.factorPower qe.1 qe.2 ∈
          (expectedFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2) := by
      rw [List.mem_map]
      exact ⟨qe, hqe, rfl⟩
    have hfp_dvd :
        Hex.Factorization.factorPower qe.1 qe.2 ∣
          ((expectedFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 :=
      mem_dvd_foldl_mul_zpoly _ 1 _ hfp_in_map
    have hfp_dvd_rp :
        Hex.Factorization.factorPower qe.1 qe.2 ∣
          (Hex.normalizeForFactor f).repeatedPart := by
      rw [hdecomp]
      exact hfp_dvd
    have hsize_le : (Hex.Factorization.factorPower qe.1 qe.2).size ≤
        (Hex.normalizeForFactor f).repeatedPart.size :=
      Hex.ZPoly.size_le_of_dvd_nonzero hfp_ne hrp_ne hfp_dvd_rp
    omega
  exact IntReductionMod.reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc
    f hf_ne expectedFactors hirr hprod hnorm hpos_lc hdegree hfuel

/-- **Trial-branch raw-factor irreducibility (hybrid guard form).**

Trial-branch raw-factor irreducibility for the cost-based hybrid, where the
trial arm fires as the totality backstop.  Because the deg-0 (constant-core)
short-circuit is reachable, the raw output can contain the unit `1`, so the
statement carries the `shouldRecordPolynomialFactor` guard that excludes it.  The
two positive-degree arms reuse the quadratic and exhaustive integer-trial
completeness/irreducibility content. -/
theorem factorTrialFactorsWithBound_factor_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    {raw : Hex.ZPoly}
    (hmem : raw ∈ (Hex.factorTrialFactorsWithBound f
      (Hex.ZPoly.defaultFactorCoeffBound f)).toList)
    (hrec : Hex.shouldRecordPolynomialFactor (Hex.normalizeFactorSign raw) = true) :
    Hex.ZPoly.Irreducible raw := by
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_prim :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
  simp only [Hex.factorTrialFactorsWithBound] at hmem
  by_cases hdeg : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · rw [if_pos hdeg] at hmem
    have hcomplete := Hex.reassemblyExpansionComplete_constant_of_ne_zero f hf hdeg
    rcases Hex.reassemblePolynomialFactors_mem_xPower_or_core_of_expansionComplete
        _ _ raw hcomplete hmem with hx | hcore
    · exact Hex.xPowerFactorArray_irreducible _ raw hx
    · exfalso
      have hraw_one : raw = 1 := by
        have hraw_core : raw = (Hex.normalizeForFactor f).squareFreeCore := by
          simpa using hcore
        rw [hraw_core, Hex.squareFreeCore_eq_one_of_constant_of_ne_zero f hf hdeg]
      rw [hraw_one, Hex.normalizeFactorSign_one, Hex.shouldRecordPolynomialFactor_one] at hrec
      exact absurd hrec (by decide)
  · rw [if_neg hdeg] at hmem
    cases hquad :
        Hex.quadraticIntegerRootFactors? (Hex.normalizeForFactor f).squareFreeCore with
    | some coreFactors =>
        simp only [hquad] at hmem
        refine Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
          _ _ ?_ ?_ hmem
        · exact IntReductionMod.reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero
            f hf hquad
        · intro factor hfmem
          exact Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive
            hcore_pos hcore_prim hquad hfmem
    | none =>
        simp only [hquad] at hmem
        refine Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
          _ _ ?_ ?_ hmem
        · exact reassemblyExpansionComplete_exhaustiveIntegerTrial_of_ne_zero f hf
        · exact
            exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_at_default
              f hf

end HexBerlekampZassenhausMathlib
