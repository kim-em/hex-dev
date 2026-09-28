/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.RationalSolve
public import HexSignDet.Counts
public import TauCeti.Data.Matrix.OccCount
public import Mathlib.Data.List.OfFn

public section

namespace Hex.SignDet

open HexMatrixMathlib

/-- List positions, rather than distinct values, are the finite samples in
the imported BKR counting foundation. Repeated sign words retain multiplicity. -/
theorem occurrences_get (xs : List (List Int)) (word : List Int) :
    Function.occCount (fun i : Fin xs.length => xs[(i : Nat)]) word =
      xs.countP (fun x => decide (x = word)) := by
  rw [Function.occCount_eq_sum]
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_succ, List.getElem_cons_succ, Fin.val_zero,
      List.getElem_cons_zero, ih, List.countP_cons, decide_eq_true_eq]
    split_ifs <;> simp_all [Nat.add_comm]

/-- The literal list sum used by the executable moment vector is the sum
over sample positions used by the foundation, including an empty list. -/
theorem moments_get {R : Type*} [AddCommMonoid R] (xs : List (List Int))
    (weight : List Int → R) :
    ∑ i : Fin xs.length, weight xs[(i : Nat)] = (xs.map weight).sum := by
  rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]

/-- Tau Ceti's finite BKR moment identity applied to the actual ordered
exponent and candidate vectors. Coverage is independent of matrix rank. -/
theorem foundation_moments {r : Nat} (rows : Vector (List Nat) r)
    (columns : Vector (List Int) r) (hn : columns.toList.Nodup)
    (xs : List (List Int)) (cover : ∀ x ∈ xs, x ∈ columns.toList) :
    momentMatrix rows columns * counts columns xs = moments rows xs := by
  have hinj : Function.Injective (fun i : Fin r => columns[i]) := by
    intro i j hij
    apply Fin.ext
    exact hn.eq_of_getElem_eq (by simp) (by simp) (by simpa using hij)
  have hc : ∀ i : Fin xs.length, ∃ j : Fin r, columns[j] = xs[i] := by
    intro i
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp (cover xs[i] (List.getElem_mem i.isLt))
    exact ⟨⟨j, by simpa using hj⟩, by simpa using he⟩
  have h := Function.mulVec_occCount (fun i : Fin xs.length => xs[i])
    (fun j : Fin r => columns[j]) hinj hc (fun i : Fin r => entry rows[i])
      (K := Int)
  have hmatrix : matrixEquiv (momentMatrix rows columns) =
      _root_.Matrix.of (fun i j : Fin r => entry rows[i] columns[j]) := by
    rw [momentMatrix, matrixEquiv_ofFn]
    ext i j
    rw [_root_.Matrix.of_apply]
  rw [← hmatrix] at h
  apply vectorEquiv.injective
  rw [vectorEquiv_mulVec]
  simpa [matrixEquiv_ofFn, momentMatrix, counts, moments, occurrences_get,
    moments_get, vectorEquiv, _root_.Matrix.of_apply, Fin.getElem_fin] using h

/-- The imported count-recovery theorem identifies an accepted system's
literal integer counts. The actual rational inverse supplies its left inverse;
the caller supplies observation coverage separately from both matrix identities. -/
theorem System.foundation_counts {r arity : Nat} (s : System r)
    (checked : s.check arity = true) (xs : List (List Int))
    (cover : ∀ x ∈ xs, x ∈ s.columns.toList)
    (hm : s.values = moments s.rows xs) :
    SignDet.counts s.columns xs = s.counts := by
  have hn : s.columns.toList.Nodup := by
    simp only [System.check, Bool.and_eq_true, decide_eq_true_eq] at checked
    exact checked.1.1.1.2
  have hinj : Function.Injective (fun i : Fin r => s.columns[i]) := by
    intro i j hij
    apply Fin.ext
    exact hn.eq_of_getElem_eq (by simp) (by simp) (by simpa using hij)
  have hc : ∀ i : Fin xs.length, ∃ j : Fin r, s.columns[j] = xs[i] := by
    intro i
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp (cover xs[i] (List.getElem_mem i.isLt))
    exact ⟨⟨j, by simpa using hj⟩, by simpa using he⟩
  obtain ⟨inv, hinv⟩ := s.rationalInverse checked
  let m : Matrix Rat r r := Matrix.ofFn fun i j => (entry s.rows[i] s.columns[j] : Rat)
  have hmatrix : matrixEquiv m = _root_.Matrix.of
      (fun i j : Fin r => (entry s.rows[i] s.columns[j] : Rat)) := by
    dsimp only [m]
    rw [matrixEquiv_ofFn]
    ext i j
    simp only [_root_.Matrix.of_apply]
  have hi : matrixEquiv inv * matrixEquiv m = 1 := by
    rw [← matrixEquiv_mul, (Matrix.inverse?_spec m inv hinv).2, matrixEquiv_identity]
  have he : m * s.counts.map (fun z : Int => (z : Rat)) =
      s.values.map (fun z : Int => (z : Rat)) := by
    have ht := (Matrix.inverse?_spec m inv hinv).1
    rw [← s.rationalCounts checked inv hinv, ← Matrix.mul_assoc_vec,
      ht, Matrix.identity_mulVec]
  have hsolve : (matrixEquiv m).mulVec (fun i => (s.counts[i] : Rat)) =
      fun i => ∑ j : Fin xs.length, (entry s.rows[i] xs[j] : Rat) := by
    funext i
    rw [show (∑ j : Fin xs.length, (entry s.rows[i] xs[j] : Rat)) =
      (xs.map fun word => (entry s.rows[i] word : Rat)).sum from
        by simpa only [Fin.getElem_fin] using
          moments_get xs (fun word => (entry s.rows[i] word : Rat))]
    have hv := congrArg vectorEquiv he
    rw [vectorEquiv_mulVec] at hv
    simpa [hm, moments, vectorEquiv, Int.cast_list_sum,
      List.map_map, Function.comp_def, Fin.getElem_fin] using congrFun hv i
  have h := Function.eq_occCount (fun i : Fin xs.length => xs[i])
    (fun j : Fin r => s.columns[j]) hinj hc
    (fun i : Fin r => fun word => (entry s.rows[i] word : Rat))
    (matrixEquiv inv) (by rw [← hmatrix]; exact hi)
    (fun i => (s.counts[i] : Rat))
    (by rw [← hmatrix]; exact hsolve)
  apply Vector.ext
  intro i hi
  have he := congrFun h (⟨i, hi⟩ : Fin r)
  simp only [Fin.getElem_fin] at he
  rw [occurrences_get] at he
  simp only [SignDet.counts, Vector.getElem_ofFn]
  exact_mod_cast he.symm

end Hex.SignDet
