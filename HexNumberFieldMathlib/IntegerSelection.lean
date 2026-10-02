/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberFieldMathlib.RootSelection
public section

/-! The lazy integer pipeline is the prefix of the complete canonical root solver. -/
namespace Hex.RootSelection

/-- Exactifying the lazy isolations recovers the canonical integer-root computation. -/
theorem integerRoots?_eq (p : ZPoly) :
    ZPoly.algebraicRoots? p = (do
      let roots ← integerRoots? p
      let values ← roots.mapM AlgebraicRoot.exact?
      pure (values.toList.mergeSort AlgebraicNumber.rootLe).toArray) := by
  unfold ZPoly.algebraicRoots? integerRoots?
  split_ifs
  · simp
  · dsimp only
    split_ifs <;> simp [Option.bind_assoc, Array.mapM_map, Function.comp_def]

/-- Every integer polynomial has a successfully certified lazy root list. -/
theorem integerRoots?_isSome (p : ZPoly) : (integerRoots? p).isSome = true := by
  have h := ZPoly.algebraicRoots?_eq p
  rw [integerRoots?_eq] at h
  obtain ⟨roots, hr, _⟩ := Option.bind_eq_some_iff.mp h
  exact Option.isSome_iff_exists.mpr ⟨roots, hr⟩

/-- The lazy list contains exactly the complex roots of a nonzero integer polynomial. -/
theorem integerRoots?_mem (p : ZPoly) (hp : p ≠ 0) {roots : Array AlgebraicRoot}
    (h : integerRoots? p = some roots) (z : ℂ) :
    (∃ r ∈ roots.toList, r.toComplex = z) ↔ (HexRootsMathlib.toPolyℂ p).IsRoot z := by
  have he := ZPoly.algebraicRoots?_eq p
  rw [integerRoots?_eq, h] at he
  simp only [Option.bind_eq_bind, Option.bind_some] at he
  obtain ⟨values, hv, he⟩ := Option.bind_eq_some_iff.mp he
  have hout := (Option.some.inj he).symm
  obtain ⟨hsize, hget⟩ := HexRootsMathlib.array_mapM_some_get hv
  have hvalue (i : Nat) (hi : i < roots.size) (hj : i < values.size) :
      values[i].toComplex = roots[i].toComplex :=
    AlgebraicRoot.exact?_sound roots[i] (hget i hi hj)
  rw [← ZPoly.mem_algebraicRoots_iff p hp z, hout]
  simp only [List.mem_mergeSort]
  constructor
  · rintro ⟨r, hr, hrz⟩
    obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hr
    have hi' : i < roots.size := by simpa using hi
    have hj : i < values.size := by omega
    refine ⟨values[i], List.mem_iff_getElem.mpr ⟨i, by simpa using hj, by simp⟩, ?_⟩
    rw [hvalue i hi' hj]
    have hir' : roots[i] = r := by simpa only [Array.getElem_toList] using hir
    rw [hir']
    exact hrz
  · rintro ⟨a, ha, haz⟩
    obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha
    have hi' : i < values.size := by simpa using hi
    have hj : i < roots.size := by omega
    refine ⟨roots[i], List.mem_iff_getElem.mpr ⟨i, by simpa using hj, by simp⟩, ?_⟩
    rw [← hvalue i hj hi']
    have hia' : values[i] = a := by simpa only [Array.getElem_toList] using hia
    rw [hia']
    exact haz

end Hex.RootSelection
