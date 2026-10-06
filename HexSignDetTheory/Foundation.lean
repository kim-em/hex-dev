/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexMatrixTheory.Algebra
public import HexRankTheory.Sound
public import Mathlib.Data.Rat.Cast.Order
public import HexSignDet.Induction
public import HexSignDet.Counts
public import TauCeti.Data.Matrix.OccCount
public import Mathlib.Data.List.OfFn

public section

namespace Hex.SignDet

open HexMatrixTheory

/-- List positions, rather than distinct values, are the finite samples in
the imported BKR counting foundation. Repeated sign words retain multiplicity. -/
theorem occCount_getElem {α : Type*} [DecidableEq α] (xs : List α) (word : α) :
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
theorem sum_getElem {α R : Type*} [AddCommMonoid R] (xs : List α)
    (weight : α → R) :
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
  simpa [matrixEquiv_ofFn, momentMatrix, counts, moments, occCount_getElem,
    sum_getElem, vectorEquiv, _root_.Matrix.of_apply, Fin.getElem_fin] using h

/-- The imported count-recovery theorem identifies an accepted system's
literal integer counts. The supplied scaled integer inverse supplies its rational left inverse;
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
  let m := (matrixEquiv (momentMatrix s.rows s.columns)).map (Int.castRingHom Rat)
  let a := (s.denominator : Rat)⁻¹ • (matrixEquiv s.inverse).map (Int.castRingHom Rat)
  obtain ⟨hd, hi, solve⟩ := s.identities checked
  have hden : (s.denominator : Rat) ≠ 0 := by exact_mod_cast hd
  have hint : matrixEquiv s.inverse * matrixEquiv (momentMatrix s.rows s.columns) =
      s.denominator • (1 : _root_.Matrix (Fin r) (Fin r) Int) := by
    rw [← matrixEquiv_mul, hi, Matrix.scale_eq_smul, matrixEquiv_smul, matrixEquiv_identity]
  have hrat : (matrixEquiv s.inverse).map (Int.castRingHom Rat) * m =
      (s.denominator : Rat) • (1 : _root_.Matrix (Fin r) (Fin r) Rat) := by
    dsimp only [m]
    rw [← _root_.Matrix.map_mul, hint]
    ext i j
    simp only [_root_.Matrix.map_apply, Int.coe_castRingHom, _root_.Matrix.smul_apply,
      smul_eq_mul, Int.cast_mul, _root_.Matrix.one_apply]
    split_ifs <;> simp
  have hleft : a * m = 1 := by
    dsimp only [a]
    rw [_root_.Matrix.smul_mul, hrat, smul_smul, inv_mul_cancel₀ hden, one_smul]
  have hmatrix : m = _root_.Matrix.of
      (fun i j : Fin r => (entry s.rows[i] s.columns[j] : Rat)) := by
    dsimp only [m]
    rw [momentMatrix, matrixEquiv_ofFn]
    ext i j
    rw [_root_.Matrix.of_apply]
    rfl
  have hsolveInt : (matrixEquiv (momentMatrix s.rows s.columns)).mulVec
      (vectorEquiv s.counts) = vectorEquiv s.values := by
    rw [← vectorEquiv_mulVec, solve]
  have hsolveRat : m.mulVec (fun i => ((s.counts[i] : Int) : Rat)) =
      fun i => ((s.values[i] : Int) : Rat) := by
    funext i
    change ((matrixEquiv (momentMatrix s.rows s.columns)).map (Int.castRingHom Rat)).mulVec
      ((Int.castRingHom Rat) ∘ vectorEquiv s.counts) i = _
    rw [← RingHom.map_mulVec, hsolveInt]
    rfl
  have hsolve : m.mulVec (fun i => ((s.counts[i] : Int) : Rat)) =
      fun i => ∑ j : Fin xs.length, (entry s.rows[i] xs[j] : Rat) := by
    funext i
    rw [show (∑ j : Fin xs.length, (entry s.rows[i] xs[j] : Rat)) =
      (xs.map fun word => (entry s.rows[i] word : Rat)).sum from
        by simpa only [Fin.getElem_fin] using
          sum_getElem xs (fun word => (entry s.rows[i] word : Rat))]
    simpa [hm, moments, Int.cast_list_sum, List.map_map, Function.comp_def] using
      congrFun hsolveRat i
  have h := Function.eq_occCount (fun i : Fin xs.length => xs[i])
    (fun j : Fin r => s.columns[j]) hinj hc
    (fun i : Fin r => fun word => (entry s.rows[i] word : Rat))
    a (by rw [← hmatrix]; exact hleft)
    (fun i => ((s.counts[i] : Int) : Rat))
    (by rw [← hmatrix]; exact hsolve)
  apply Vector.ext
  intro i hi
  have he := congrFun h (⟨i, hi⟩ : Fin r)
  simp only [Fin.getElem_fin] at he
  rw [occCount_getElem] at he
  simp only [SignDet.counts, Vector.getElem_ofFn]
  exact_mod_cast he.symm

/-- Specialize the existing replay induction to Tau Ceti count recovery at
every node, before pruning that node. Candidate coverage comes from the leaf
columns or the already complete child supports, never the parent solve. -/
theorem Replay.foundation_complete {E : Type u} {Ctx : Type v}
    [Zero E] [One E] [Add E] [Sub E] [Mul E] [NatCast E]
    [DecidableEq E] [DecidableEq Ctx]
    {sign : E → Int} {context : Ctx} {p : DensePoly E} {a b : Endpoint E}
    {qs : List (DensePoly E)} (t : Replay E Ctx) {xs : List (List Int)}
    (checked : t.check sign context p a b qs = true)
    (observations : Observations qs.length xs) (interpreted : t.Interprets qs.length xs) :
    (∀ x ∈ xs, x ∈ t.node.system.support) ∧
      counts t.node.system.columns xs = t.node.system.counts :=
  t.support_counts (@System.foundation_counts) checked observations interpreted

end Hex.SignDet
