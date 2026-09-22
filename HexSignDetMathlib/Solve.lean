/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Produce
public import HexMatrixMathlib.Algebra

public section

namespace Hex.SignDet

/-- Given a valid integer system, the scaled-inverse solver returns its exact
counts. This finite algebraic theorem rules out diagnostic failures once
actual-count moment identities and an inverse witness have been established. -/
theorem solveScaled_eq {r arity : Nat} (s : System r) (h : s.check arity = true) :
    solveScaled arity s.rows s.columns s.values s.denominator s.inverse = .ok s := by
  obtain ⟨hd, hi, hc⟩ := s.identities h
  have hn : s.inverse * s.values = s.denominator • s.counts := by
    rw [← hc, ← Matrix.mul_assoc_vec, hi, scale_identity_vec]
  have hdiv : (s.inverse * s.values).toList.all (fun z => z % s.denominator == 0) = true := by
    rw [hn]
    apply List.all_eq_true.mpr
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
    simp only [Vector.getElem_toList, Vector.getElem_smul, smul_eq_mul, Int.mul_emod_right,
      beq_self_eq_true]
  have hcounts : (s.inverse * s.values).map (· / s.denominator) = s.counts := by
    rw [hn]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_smul, smul_eq_mul]
    exact Int.mul_ediv_cancel_left _ hd
  have hpos : s.counts.toList.all (· ≥ 0) = true := by
    simp only [System.check, Bool.and_eq_true] at h
    exact h.1.1.2
  simp only [solveScaled, hd, ↓reduceIte, hdiv, Bool.not_true, Bool.false_eq_true,
    hcounts, hpos, h]
  rfl

end Hex.SignDet
