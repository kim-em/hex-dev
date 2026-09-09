/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraicMathlib.Polynomial

public section

/-! Filtering and sorting preserve the complete real root set. -/

namespace Hex.RealRootSet

/-- Semantic membership, including the universal root set of zero. -/
@[expose] def Contains (roots : RealRootSet) (r : ℝ) : Prop :=
  match roots with
  | .all => True
  | .finite entries => ∃ entry ∈ entries.toList, entry.root.toReal = r

/-- Executable membership agrees with real-value membership. -/
theorem contains_iff (roots : RealRootSet) (a : RealAlgebraicNumber) :
    roots.contains a = true ↔ roots.Contains a.toReal := by
  cases roots with
  | all => simp [contains, Contains]
  | finite entries =>
    simp only [contains, Contains, ← Array.any_toList, List.any_eq_true, RealAlgebraicNumber.beq_iff,
      Array.mem_toList_iff, RealAlgebraicNumber.toReal_injective.eq_iff]

end Hex.RealRootSet

namespace Hex.RealAlgebraicPoly

/-- Retaining a root preserves its exact value and multiplicity. -/
theorem realRoot?_sound (r : RootCount) (s : RealRootCount) (h : realRoot? r = some s) :
    s.root.toAlgebraic = r.root.exact ∧ s.multiplicity = r.multiplicity := by
  change (RealAlgebraicNumber.ofRoot? r.root).bind (fun a =>
    some (RealRootCount.mk a r.multiplicity r.multiplicity_pos)) = some s at h
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨((RealAlgebraicNumber.ofAlgebraic?_eq_some _ _).mp ha).symm, rfl⟩

/-- Every real-valued lazy root passes exactification and the reality filter. -/
theorem realRoot?_complete (r : RootCount) (x : ℝ) (h : r.root.toComplex = (x : ℂ)) :
    ∃ s, realRoot? r = some s ∧ s.root.toReal = x := by
  have hr : r.root.exact.isReal = true := by
    rw [AlgebraicNumber.isReal_iff, AlgebraicRoot.exact_toComplex, h]
    rfl
  let a := RealAlgebraicNumber.ofAlgebraic r.root.exact hr
  refine ⟨⟨a, r.multiplicity, r.multiplicity_pos⟩, ?_, ?_⟩
  · simp only [realRoot?, RealAlgebraicNumber.ofRoot?, RealAlgebraicNumber.ofAlgebraic?,
      dite_eq_left hr]
    rfl
  · change r.root.exact.toComplex.re = x
    rw [AlgebraicRoot.exact_toComplex, h]
    rfl

/-- Filtering and sorting retain exactly the real members of a complex root set. -/
theorem contains_realRoots (roots : RootSet) (x : ℝ) :
    (realRoots roots).Contains x ↔ roots.Contains (x : ℂ) := by
  cases roots with
  | all => simp [realRoots, RealRootSet.Contains, RootSet.Contains]
  | finite entries =>
    simp only [realRoots, RealRootSet.Contains, RootSet.Contains,
      List.mem_mergeSort, Array.toList_filterMap, List.mem_filterMap]
    constructor
    · rintro ⟨s, ⟨r, hr, hs⟩, hx⟩
      refine ⟨r, hr, ?_⟩
      rw [← AlgebraicRoot.exact_toComplex, ← (realRoot?_sound r s hs).1,
        ← RealAlgebraicNumber.ofReal_toReal, hx]
    · rintro ⟨r, hr, hx⟩
      obtain ⟨s, hs, hsr⟩ := realRoot?_complete r x hx
      exact ⟨s, ⟨r, hr, hs⟩, hsr⟩

/-- Real polynomial roots are complete for every real value. -/
theorem contains_roots_iff (f : RealAlgebraicPoly) (x : ℝ) :
    f.roots.Contains x ↔ f.toPolynomial.eval x = 0 := by
  rw [roots, contains_realRoots, AlgebraicPoly.contains_roots_iff, ← ofReal_eval]
  exact Complex.ofReal_eq_zero

/-- Universal real roots occur exactly for the zero polynomial. -/
theorem roots_all_iff (f : RealAlgebraicPoly) :
    f.roots = .all ↔ f.toPolynomial = 0 := by
  rw [toPolynomial_eq_zero, ← AlgebraicPoly.roots_all_iff]
  unfold roots
  cases f.toAlgebraic.roots <;> simp [realRoots]

/-- The real comparison sort puts all retained roots in nondecreasing order. -/
theorem realRoots_sorted (roots : RootSet) :
    (realRoots roots).toArray.toList.Pairwise (fun a b => a.root ≤ b.root) := by
  cases roots with
  | all => simp [realRoots, RealRootSet.toArray, RealRootSet.finite?]
  | finite entries =>
    simp only [realRoots, RealRootSet.toArray, RealRootSet.finite?, Option.getD_some,
      List.toList_toArray]
    simpa only [decide_eq_true_eq] using
      (List.pairwise_mergeSort (le := fun a b : RealRootCount => decide (a.root ≤ b.root))
        (fun a b c hab hbc => by simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
        (fun a b => by simpa using le_total a.root b.root) _)

/-- Distinct complex roots remain distinct after retaining their real values and sorting. -/
theorem realRoots_noDuplicates (roots : RootSet) (h : roots.NoDuplicates) :
    (realRoots roots).toArray.toList.Pairwise (fun a b => a.root ≠ b.root) := by
  cases roots with
  | all => simp [realRoots, RealRootSet.toArray, RealRootSet.finite?]
  | finite entries =>
    simp only [realRoots, RealRootSet.toArray, RealRootSet.finite?, Option.getD_some,
      List.toList_toArray, Array.toList_filterMap]
    apply List.Pairwise.perm _ (List.mergeSort_perm _ _).symm (fun h => h.symm)
    apply List.pairwise_filterMap.mpr
    apply h.imp
    intro a b hab s hs t ht hst
    apply hab
    rw [← AlgebraicRoot.exact_toComplex a.root, ← AlgebraicRoot.exact_toComplex b.root,
      ← (realRoot?_sound a s hs).1, ← (realRoot?_sound b t ht).1, hst]

/-- A nonzero real polynomial has distinct roots in strictly increasing order. -/
theorem roots_sorted (f : RealAlgebraicPoly) :
    f.roots.toArray.toList.Pairwise (fun a b => a.root < b.root) := by
  exact ((realRoots_sorted f.toAlgebraic.roots).and
    (realRoots_noDuplicates f.toAlgebraic.roots (AlgebraicPoly.roots_noDuplicates _))).imp
      (fun h => lt_of_le_of_ne h.1 h.2)

end Hex.RealAlgebraicPoly
