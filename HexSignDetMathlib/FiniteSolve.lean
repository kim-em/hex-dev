/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Induction
public import HexSignDetMathlib.RationalSolve

public section

namespace Hex.SignDet

/-- A nonzero scaled left inverse forces distinct candidate columns. This
derives the distinctness guard independently of a successful system check. -/
theorem columns_distinct {r : Nat} (rows : Vector (List Nat) r)
    (cols : Vector (List Int) r) (a : Matrix Int r r) (d : Int)
    (hd : d ≠ 0)
    (hi : a * momentMatrix rows cols = Matrix.scale d (Matrix.identity r)) :
    cols.toList.Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro i j hij
  have he : Matrix.col (momentMatrix rows cols) (i.cast (by simp)) =
      Matrix.col (momentMatrix rows cols) (j.cast (by simp)) := by
    apply Vector.ext
    intro k hk
    change (Matrix.col (momentMatrix rows cols) (i.cast (by simp)))[(⟨k, hk⟩ : Fin r)] =
      (Matrix.col (momentMatrix rows cols) (j.cast (by simp)))[(⟨k, hk⟩ : Fin r)]
    rw [Matrix.getElem_col, Matrix.getElem_col]
    simp only [momentMatrix, Matrix.getElem_ofFn]
    simpa only [List.get_eq_getElem, Vector.getElem_toList, Fin.getElem_fin, Fin.val_cast] using
      congrArg (entry rows[k]) hij
  rw [← Matrix.mulVec_unit, ← Matrix.mulVec_unit] at he
  have he := congrArg (fun v : Vector Int r => a * v) he
  rw [← Matrix.mul_assoc_vec, ← Matrix.mul_assoc_vec, hi,
    scale_identity_vec, scale_identity_vec] at he
  by_contra hne
  have hv := congrArg (fun v : Vector Int r => v[i.val]'(by simpa using i.isLt)) he
  have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
  simp [Vector.getElem_smul, Vector.unit, Fin.ext_iff, Ne.symm hne'] at hv
  change (1 : Int) = 0 ∨ d = 0 at hv
  norm_num at hv
  exact hd hv

theorem counts_nonneg {r : Nat} (cols : Vector (List Int) r) (xs : List (List Int)) :
    (counts cols xs).toList.all (· ≥ 0) = true := by
  apply List.all_eq_true.mpr
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
  simp only [Vector.getElem_toList, counts, Vector.getElem_ofFn]
  exact decide_eq_true (Int.natCast_nonneg _)

/-- Shape, a scaled inverse and independently complete candidate support
construct a checked moment system for the finite observations. In particular,
the distinctness and count guards are conclusions, not supplied assumptions. -/
theorem system_counts {r arity : Nat} (rows : Vector (List Nat) r)
    (cols : Vector (List Int) r) (a : Matrix Int r r) (d : Int)
    (hr : rows.toList.all (fun e => decide (e.length = arity) && e.all (· ≤ 2)) = true)
    (hc : cols.toList.all (fun c => decide (c.length = arity) &&
      c.all (fun x => decide (x = -1 ∨ x = 0 ∨ x = 1))) = true)
    (hd : d ≠ 0)
    (hi : a * momentMatrix rows cols = Matrix.scale d (Matrix.identity r))
    (xs : List (List Int)) (cover : ∀ x ∈ xs, x ∈ cols.toList) :
    (System.mk rows cols (counts cols xs) (moments rows xs) a d).check arity = true := by
  have hn := columns_distinct rows cols a d hd hi
  simp only [System.check, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨hr, hc⟩, decide_eq_true hn⟩, counts_nonneg cols xs⟩, decide_eq_true hd⟩,
    decide_eq_true hi, decide_eq_true (count_moments rows cols hn xs cover)⟩

/-- A complete candidate support and a checked inverse suffice for the true
finite counts to pass the system checker. No count or moment equality is
assumed for the new observations. -/
theorem System.check_counts {r arity : Nat} (s : System r) (h : s.check arity = true)
    (xs : List (List Int)) (cover : ∀ x ∈ xs, x ∈ s.columns.toList) :
    ({s with counts := SignDet.counts s.columns xs, values := moments s.rows xs} : System r).check arity =
      true := by
  have hn : s.columns.toList.Nodup := by
    simp only [System.check, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.2
  have hc := counts_nonneg s.columns xs
  have hm := count_moments s.rows s.columns hn xs cover
  simp only [System.check, Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨h.1.1.1, hc⟩, h.1.2⟩, h.2.1, decide_eq_true hm⟩

/-- The empty-query leaf has a checked full candidate system for every finite
family of empty observations, including no observations at all. -/
theorem empty_system (xs : List (List Int)) (ho : Observations 0 xs) :
    ∃ s : System 1, s.check 0 = true ∧ s.rows = #v[[]] ∧ s.columns = #v[[]] ∧
      s.counts = counts #v[[]] xs ∧ s.values = moments #v[[]] xs := by
  let s : System 1 := {
    rows := #v[[]], columns := #v[[]], counts := #v[0], values := #v[0]
    inverse := Matrix.identity 1, denominator := 1 }
  have hs : s.check 0 = true := by decide +kernel
  have cover : ∀ x ∈ xs, x ∈ s.columns.toList := by
    intro x hx
    have he : x = [] := List.eq_nil_of_length_eq_zero (ho x hx).1
    simp [s, he]
  exact ⟨{s with counts := counts s.columns xs, values := moments s.rows xs},
    s.check_counts hs xs cover, rfl, rfl, rfl, rfl⟩

/-- The singleton-query leaf has the full three-column system. Its explicit
inverse and observation coverage precede solving, so no omitted-support
assumption is extracted from the final matrix equations. -/
theorem singleton_system (xs : List (List Int)) (ho : Observations 1 xs) :
    ∃ s : System 3, s.check 1 = true ∧ s.rows = #v[[0], [1], [2]] ∧
      s.columns = #v[[-1], [0], [1]] ∧ s.counts = counts #v[[-1], [0], [1]] xs ∧
      s.values = moments #v[[0], [1], [2]] xs := by
  let s : System 3 := {
    rows := #v[[0], [1], [2]], columns := #v[[-1], [0], [1]]
    counts := #v[0, 0, 0], values := #v[0, 0, 0]
    inverse := Matrix.ofRows #v[#v[0, -1, 1], #v[2, 0, -2], #v[0, 1, 1]]
    denominator := 2 }
  have hs : s.check 1 = true := by decide +kernel
  have cover : ∀ x ∈ xs, x ∈ s.columns.toList := by
    intro x hx
    obtain ⟨hl, hv⟩ := ho x hx
    obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hl
    rcases hv v (by simp) with h | h | h <;> simp [s, h]
  exact ⟨{s with counts := counts s.columns xs, values := moments s.rows xs},
    s.check_counts hs xs cover, rfl, rfl, rfl, rfl⟩

end Hex.SignDet
