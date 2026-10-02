/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraicMathlib.Sqrt
public import HexRealRootsMathlib.RealClosed

public section

/-! Real-closedness obtained from the executable square and polynomial root operations. -/

namespace Hex.RealAlgebraicNumber

/-- Every nonnegative canonical real algebraic number is a square. -/
theorem isSquare_of_nonneg {a : RealAlgebraicNumber} (ha : 0 ≤ a) : IsSquare a := by
  refine ⟨a.sqrt ha, ?_⟩
  simpa only [pow_two] using (sqrt_sq a ha).symm

/-- Every odd-degree polynomial has a canonical real root, supplied by the root driver. -/
theorem exists_isRoot_of_odd_natDegree {p : Polynomial RealAlgebraicNumber}
    (hp : Odd p.natDegree) : ∃ a, p.IsRoot a := by
  let f := RealAlgebraicPoly.ofPolynomial p
  have hf : f.toPolynomial = p.map toRealHom := RealAlgebraicPoly.toPolynomial_ofPolynomial p
  have hd : f.toPolynomial.natDegree = p.natDegree := by
    rw [hf, Polynomial.natDegree_map]
  obtain ⟨x, hx⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree
    (f := f.toPolynomial) (hd.symm ▸ hp)
  have hm := (RealAlgebraicPoly.contains_roots_iff f x).mpr hx
  cases hroots : f.roots with
  | all =>
    have hz := (RealAlgebraicPoly.roots_all_iff f).mp hroots
    have hn : p.natDegree = 0 := by rw [← hd, hz, Polynomial.natDegree_zero]
    simp [hn] at hp
  | finite entries =>
    rw [hroots] at hm
    obtain ⟨r, _, hr⟩ := hm
    refine ⟨r.root, toReal_injective ?_⟩
    change toRealHom (p.eval r.root) = toRealHom 0
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← hf]
    change f.toPolynomial.eval r.root.toReal = 0
    rwa [hr]

/-- The ordered executable field of canonical real algebraic numbers is real closed. -/
instance instIsRealClosed : IsRealClosed RealAlgebraicNumber :=
  IsRealClosed.of_linearOrderedField isSquare_of_nonneg exists_isRoot_of_odd_natDegree

/-- info: 'Hex.RealAlgebraicNumber.instIsRealClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instIsRealClosed

end Hex.RealAlgebraicNumber
