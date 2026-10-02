/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.Unity
public import HexNumberFieldMathlib.IntegerSelection
public import HexNumberFieldMathlib.UnityBranch
public section

/-! Exact roots of unity and their fixed-field construction. -/
namespace Hex.AlgebraicNumber.Unity
open HexNumberFieldMathlib.Unity

/-- The executable binomial has the stated complex interpretation. -/
theorem polynomial_value (n : Nat) : HexRootsMathlib.toPolyℂ (polynomial n) =
    if n % 2 = 0 then Polynomial.X ^ (n / 2) + 1 else Polynomial.X ^ n - 1 := by
  unfold polynomial
  split <;> apply Polynomial.ext <;> intro k <;>
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_monomial]
    <;> split_ifs <;> norm_num <;> omega

theorem polynomial_ne_zero {n : Nat} (hn : 2 < n) : polynomial n ≠ 0 := by
  intro h
  have hv := polynomial_value n
  rw [h] at hv
  have hz : HexRootsMathlib.toPolyℂ (0 : ZPoly) = 0 := by simp [HexRootsMathlib.toPolyℂ]
  rw [hz] at hv
  split at hv
  · have hh := congrArg (fun p : Polynomial ℂ => p.coeff (n / 2)) hv
    simp [Polynomial.coeff_one, show n / 2 ≠ 0 by omega] at hh
  · exact Polynomial.X_pow_sub_C_ne_zero (show 0 < n by omega) (1 : ℂ) (by simpa using hv.symm)

theorem zeta_mem {n : Nat} (hn : 2 < n) :
    (HexRootsMathlib.toPolyℂ (polynomial n)).IsRoot (zeta n) := by
  rw [polynomial_value]
  split
  · rename_i heven
    have hnn : n = 2 * (n / 2) := by omega
    have hm : (n / 2 : Nat) ≠ 0 := by omega
    have he : zeta n ^ (n / 2) = -1 := by
      rw [zeta, ← Complex.exp_nat_mul]
      have hexp : ((n / 2 : Nat) : ℂ) * (2 * Real.pi * Complex.I / (n : ℂ)) =
          Real.pi * Complex.I := by
        rw [show (n : ℂ) = 2 * ((n / 2 : Nat) : ℂ) by exact_mod_cast hnn]
        field_simp [Nat.cast_ne_zero.mpr hm]
      rw [hexp, Complex.exp_pi_mul_I]
    simp [Polynomial.IsRoot, he]
  · simpa [Polynomial.IsRoot, sub_eq_zero] using (primitive (by omega : n ≠ 0)).pow_eq_one

theorem root_pow {n : Nat} (_hn : 2 < n) {z : ℂ}
    (hz : (HexRootsMathlib.toPolyℂ (polynomial n)).IsRoot z) : z ^ n = 1 := by
  rw [polynomial_value] at hz
  split at hz
  · have h : z ^ (n / 2) = -1 := by simpa [Polynomial.IsRoot, eq_neg_iff_add_eq_zero] using hz
    have hn' : n = (n / 2) * 2 := by omega
    rw [hn', pow_mul, h]; norm_num
  · simpa [Polynomial.IsRoot, sub_eq_zero] using hz

/-- Construction of the primitive generator is total and chooses the standard branch. -/
theorem generator?_value (n : Nat) :
    ∃ a, generator? n = some a ∧ a.toComplex = zeta n := by
  unfold generator?
  split
  · rename_i hn
    interval_cases n <;> refine ⟨1, rfl, ?_⟩
    · simp [zeta]
    · simp [zeta, Complex.exp_two_pi_mul_I]
  · split
    · rename_i hn h2
      subst n
      refine ⟨-1, rfl, ?_⟩
      have he : 2 * (Real.pi : ℂ) * Complex.I / 2 = Real.pi * Complex.I := by ring
      simp [zeta, he, Complex.exp_pi_mul_I, neg_toComplex]
    · split
      · rename_i hn h2 h4
        subst n
        refine ⟨I, rfl, ?_⟩
        have he : 2 * (Real.pi : ℂ) * Complex.I / 4 = (Real.pi / 2) * Complex.I := by ring
        simp [zeta, he, Complex.exp_pi_div_two_mul_I, I_toComplex]
      · rename_i hn h2 h4
        have hn3 : 2 < n := by omega
        obtain ⟨roots, hr⟩ := Option.isSome_iff_exists.mp (RootSelection.integerRoots?_isSome (polynomial n))
        rw [hr]
        simp only [Option.bind_eq_bind, Option.bind_some]
        let upper := roots.toList.filter (fun r => decide (r.side = .upper))
        have hmem (z : ℂ) : (∃ r ∈ roots.toList, r.toComplex = z) ↔
            (HexRootsMathlib.toPolyℂ (polynomial n)).IsRoot z :=
          RootSelection.integerRoots?_mem _ (polynomial_ne_zero hn3) hr z
        have side_iff (r : AlgebraicRoot) : r.side = .upper ↔ 0 < r.toComplex.im := by
          rw [AlgebraicRoot.side_value]
          split_ifs <;> simp_all
        obtain ⟨r, hrmem, hrz⟩ := (hmem _).mpr (zeta_mem hn3)
        have hrupper : r ∈ upper := List.mem_filter.mpr ⟨hrmem, by
          simpa only [decide_eq_true_eq] using (side_iff r).mpr (hrz ▸ im_zeta hn3)⟩
        have hne : upper ≠ [] := List.ne_nil_of_mem hrupper
        obtain ⟨a, ha, hamem, hmax⟩ := RootSelection.maximum?_spec upper hne
        refine ⟨a, ha, ?_⟩
        obtain ⟨s, hs, hsa⟩ := List.mem_map.mp hamem
        obtain ⟨hsroot, hsside⟩ := List.mem_filter.mp hs
        apply eq_of_max hn3
        · exact root_pow hn3 ((hmem _).mp ⟨s, hsroot, hsa⟩)
        · rw [← hsa]
          exact (side_iff s).mp (of_decide_eq_true hsside)
        · exact hmax _ (List.mem_map.mpr ⟨r, hrupper, hrz⟩)

@[simp] theorem generator_toComplex (n : Nat) : (generator n).toComplex = zeta n := by
  obtain ⟨a, ha, hv⟩ := generator?_value n
  simp only [generator, ha]
  exact hv

/-- A fixed-field power has the same value as an ordinary algebraic power. -/
@[simp] theorem power_toComplex (a : AlgebraicNumber) (k : Nat) :
    (power a k).toComplex = a.toComplex ^ k := by
  unfold power QAdjoin.toAlgebraicNumber
  rw [PolyQuot.toAlgebraicNumber_toComplex]
  exact (PolyQuot.map_natPow a.toQAdjoin k a.rep a.rep_mk).trans
    (congrArg (· ^ k) (toQAdjoin_toComplex a))

/-- Reduction of the rational angle modulo one preserves the complex exponential. -/
theorem turn_power (q : Rat) :
    zeta q.den ^ (q.num % (q.den : Int)).toNat =
      Complex.exp (2 * Real.pi * Complex.I * (q : ℂ)) := by
  rw [zeta, ← Complex.exp_nat_mul]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-(q.num / (q.den : Int)), ?_⟩
  have hden : (q.den : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hmod : (0 : Int) ≤ q.num % (q.den : Int) := Int.emod_nonneg _ (by exact_mod_cast q.den_nz)
  have hsplit : ((q.num % (q.den : Int)).toNat : ℂ) =
      (q.num : ℂ) - (q.den : ℂ) * ((q.num / (q.den : Int) : Int) : ℂ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hmod]
    have h := Int.emod_add_mul_ediv q.num (q.den : Int)
    exact_mod_cast (show q.num % (q.den : Int) = q.num - (q.den : Int) * (q.num / (q.den : Int)) by omega)
  rw [hsplit, show (q : ℂ) = (q.num : ℂ) / (q.den : ℂ) by
    exact_mod_cast (Rat.num_div_den q).symm]
  push_cast
  field_simp
  ring

end Hex.AlgebraicNumber.Unity

namespace Hex.AlgebraicNumber
open HexNumberFieldMathlib.Unity

/-- Rational turns agree exactly with Mathlib's complex exponential. -/
@[simp] theorem rootOfUnity_toComplex (q : Rat) :
    (rootOfUnity q).toComplex = Complex.exp (2 * Real.pi * Complex.I * (q : ℂ)) := by
  rw [← Unity.turn_power q]
  unfold rootOfUnity
  dsimp only
  split
  · rename_i hk
    simp [hk]
  · split
    · rename_i hk hk1
      simp [hk1]
    · split
      · rename_i hk hk1 hkn
        rw [conj_toComplex, Unity.generator_toComplex]
        have hp := (primitive q.den_nz).pow_eq_one
        have hp' : zeta q.den ^ ((q.num % (q.den : Int)).toNat + 1) = 1 := by
          rw [hkn]; exact hp
        rw [pow_succ] at hp'
        have hpow : zeta q.den ^ (q.num % (q.den : Int)).toNat = (zeta q.den)⁻¹ :=
          eq_inv_of_mul_eq_one_left hp'
        rw [hpow, Complex.inv_eq_conj ((primitive q.den_nz).norm'_eq_one q.den_nz)]
      · rw [Unity.power_toComplex, Unity.generator_toComplex]

/-- The reduced denominator is the exact multiplicative order. -/
theorem rootOfUnity_primitive (q : Rat) : IsPrimitiveRoot (rootOfUnity q) q.den := by
  apply (IsPrimitiveRoot.map_iff_of_injective (f := toComplexHom) toComplex_injective).mp
  simpa only [show toComplexHom (rootOfUnity q) = (rootOfUnity q).toComplex from rfl,
    rootOfUnity_toComplex] using Complex.isPrimitiveRoot_exp_rat q

@[simp] theorem rootOfUnity_zero : rootOfUnity 0 = 1 := by
  apply toComplex_injective
  simp

@[simp] theorem rootOfUnity_add (q r : Rat) : rootOfUnity (q + r) = rootOfUnity q * rootOfUnity r := by
  apply toComplex_injective
  simp [rootOfUnity_toComplex, mul_toComplex, mul_add, Complex.exp_add]

@[simp] theorem rootOfUnity_neg (q : Rat) : rootOfUnity (-q) = (rootOfUnity q).conj := by
  apply toComplex_injective
  rw [rootOfUnity_toComplex, conj_toComplex, rootOfUnity_toComplex, ← Complex.exp_conj]
  congr 1
  simp [map_ofNat]

/-- info: 'Hex.AlgebraicNumber.rootOfUnity_toComplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootOfUnity_toComplex

end Hex.AlgebraicNumber
