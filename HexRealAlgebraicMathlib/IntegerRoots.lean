/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraicMathlib.Roots

public section

/-! Distinct, ordered real roots of integer polynomials. -/

namespace Hex.ZPoly

/-- Integer real-root membership is the existing canonical complex-root membership. -/
theorem mem_realAlgebraicRoots (p : ZPoly) (a : RealAlgebraicNumber) :
    a ∈ p.realAlgebraicRoots ↔ a.toAlgebraic ∈ p.algebraicRoots := by
  simp only [realAlgebraicRoots, List.mem_toArray, List.mem_mergeSort, Array.toList_filterMap,
    List.mem_filterMap, RealAlgebraicNumber.ofAlgebraic?_eq_some, exists_eq_right,
    Array.mem_toList_iff]

/-- For nonzero integer polynomials, the real-root output is sound and complete. -/
theorem mem_realAlgebraicRoots_iff (p : ZPoly) (hp : p ≠ 0) (a : RealAlgebraicNumber) :
    a ∈ p.realAlgebraicRoots ↔ (HexRootsMathlib.toPolyℂ p).IsRoot (a.toReal : ℂ) := by
  rw [mem_realAlgebraicRoots, RealAlgebraicNumber.ofReal_toReal,
    ← mem_algebraicRoots_iff p hp]
  simp only [AlgebraicNumber.toComplex_injective.eq_iff, exists_eq_right, Array.mem_toList_iff]

/-- The integer real-root output has no repeated canonical value. -/
theorem realAlgebraicRoots_nodup (p : ZPoly) : p.realAlgebraicRoots.toList.Nodup := by
  rw [realAlgebraicRoots]
  simp only [Array.toList_filterMap]
  apply List.Pairwise.perm _ (List.mergeSort_perm _ _).symm (fun h => h.symm)
  apply List.pairwise_filterMap.mpr
  apply (algebraicRoots_nodup p).imp
  intro a b hab s hs t ht hst
  apply hab
  rw [(RealAlgebraicNumber.ofAlgebraic?_eq_some a s).mp hs,
    (RealAlgebraicNumber.ofAlgebraic?_eq_some b t).mp ht, hst]

/-- The integer real-root output is strictly increasing under exact comparison. -/
theorem realAlgebraicRoots_sorted (p : ZPoly) :
    p.realAlgebraicRoots.toList.Pairwise (fun a b => a < b) := by
  have hs : p.realAlgebraicRoots.toList.Pairwise (fun a b => a ≤ b) := by
    rw [realAlgebraicRoots]
    simpa only [decide_eq_true_eq] using
      (List.pairwise_mergeSort (le := fun a b : RealAlgebraicNumber => decide (a ≤ b))
        (fun a b c hab hbc => by simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
        (fun a b => by simpa using le_total a b) _)
  exact (hs.and (realAlgebraicRoots_nodup p)).imp (fun h => lt_of_le_of_ne h.1 h.2)

/-- Constants, including zero, use the integer API's empty-array convention. -/
theorem realAlgebraicRoots_eq_empty (p : ZPoly) (hp : p.natDegree = 0) :
    p.realAlgebraicRoots = #[] := by
  have h := algebraicRoots?_eq p
  unfold algebraicRoots? at h
  rw [ite_eq_left hp] at h
  have he : p.algebraicRoots = #[] := (Option.some.inj h).symm
  simp [realAlgebraicRoots, he]

end Hex.ZPoly
