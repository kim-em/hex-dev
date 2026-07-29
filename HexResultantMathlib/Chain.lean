/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultantMathlib.Roots
public import Mathlib.Analysis.Complex.Polynomial.Basic

public section

/-!
Common-root consequences of the executable resultant correspondence.
-/
namespace Hex.DensePoly

/-- If the first integer dense polynomial is nonzero, the executable
resultant vanishes exactly when the two polynomials share a complex root. -/
theorem resultant_eq_zero_iff_common_root
    (f g : DensePoly Int) (hf : f ≠ 0) :
    resultant f g = 0 ↔
      ∃ z : ℂ,
        Polynomial.aeval z (HexPolyMathlib.toPolynomial f) = 0 ∧
        Polynomial.aeval z (HexPolyMathlib.toPolynomial g) = 0 := by
  let F := HexPolyMathlib.toPolynomial f
  let G := HexPolyMathlib.toPolynomial g
  let φ : Int →+* ℂ := Int.castRingHom ℂ
  let FC := F.map φ
  let GC := G.map φ
  have hφ : Function.Injective φ := Int.cast_injective
  have hF : F ≠ 0 := by
    intro hzero
    apply hf
    apply (HexPolyMathlib.equiv (R := Int)).injective
    simpa only [HexPolyMathlib.equiv_apply, HexPolyMathlib.toPolynomial_zero]
      using hzero
  have hFC : FC ≠ 0 := (Polynomial.map_ne_zero_iff hφ).2 hF
  have hdf : f.degree?.getD 0 = F.natDegree := by
    simpa only [F] using (HexPolyMathlib.natDegree_toPolynomial f).symm
  have hdg : g.degree?.getD 0 = G.natDegree := by
    simpa only [G] using (HexPolyMathlib.natDegree_toPolynomial g).symm
  have hFCdeg : FC.natDegree = F.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hφ F
  have hGCdeg : GC.natDegree = G.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hφ G
  rw [toPolynomial_resultant]
  constructor
  · intro hres
    rw [hdf, hdg] at hres
    have hres' : Polynomial.resultant F G F.natDegree G.natDegree = 0 := by
      simpa only [F, G] using hres
    have hresC : Polynomial.resultant FC GC = 0 := by
      rw [show Polynomial.resultant FC GC =
          φ (Polynomial.resultant F G F.natDegree G.natDegree) by
        simp [FC, GC, hFCdeg, hGCdeg]]
      simp [hres']
    rw [resultant_eq_leadingCoeff_mul_prod_roots FC GC] at hresC
    have hprod : (FC.roots.map GC.eval).prod = 0 := by
      rcases mul_eq_zero.mp hresC with hlc | hprod
      · exact (pow_ne_zero one_ne_zero
          (Polynomial.leadingCoeff_ne_zero.mpr hFC) _ hlc).elim
      · exact hprod
    obtain ⟨z, hzroot, hzG⟩ := Multiset.mem_map.mp
      (Multiset.prod_eq_zero_iff.mp hprod)
    have hzF : FC.eval z = 0 :=
      Polynomial.IsRoot.def.mp ((Polynomial.mem_roots hFC).mp hzroot)
    refine ⟨z, ?_, ?_⟩
    · simpa [F, FC, φ, Polynomial.aeval_def,
        Polynomial.eval₂_eq_eval_map] using hzF
    · simpa [G, GC, φ, Polynomial.aeval_def,
        Polynomial.eval₂_eq_eval_map] using hzG
  · rintro ⟨z, hzF, hzG⟩
    have hzFC : FC.eval z = 0 := by
      simpa [F, FC, φ, Polynomial.aeval_def,
        Polynomial.eval₂_eq_eval_map] using hzF
    have hzGC : GC.eval z = 0 := by
      simpa [G, GC, φ, Polynomial.aeval_def,
        Polynomial.eval₂_eq_eval_map] using hzG
    have hzroot : z ∈ FC.roots :=
      (Polynomial.mem_roots hFC).2 (Polynomial.IsRoot.def.mpr hzFC)
    have hzeroMem : 0 ∈ FC.roots.map GC.eval :=
      Multiset.mem_map.mpr ⟨z, hzroot, hzGC⟩
    have hresC : Polynomial.resultant FC GC = 0 := by
      rw [resultant_eq_leadingCoeff_mul_prod_roots FC GC]
      rw [Multiset.prod_eq_zero hzeroMem, mul_zero]
    have hcast : φ (Polynomial.resultant F G F.natDegree G.natDegree) = 0 := by
      simpa [FC, GC, hFCdeg, hGCdeg] using hresC
    rw [hdf, hdg]
    exact Int.cast_eq_zero.mp hcast

end Hex.DensePoly
