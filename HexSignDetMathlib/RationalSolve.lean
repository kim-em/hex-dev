/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Produce
public import HexMatrixMathlib.Algebra
public import HexMatrixMathlib.Rational
public import HexRankMathlib.Sound
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace Hex.SignDet

open HexMatrixMathlib

/-- An accepted integer system makes the actual rational inversion succeed.
This statement includes the empty matrix and does not assume a root semantics. -/
theorem System.rationalInverse {r arity : Nat} (s : System r) (h : s.check arity = true) :
    ∃ inv, Matrix.inverse? (Matrix.ofFn fun (i j : Fin r) =>
      (entry s.rows[i] s.columns[j] : Rat)) = some inv := by
  obtain ⟨hd, hi, _⟩ := s.identities h
  have he : matrixEquiv s.inverse * matrixEquiv (momentMatrix s.rows s.columns) =
      s.denominator • (1 : _root_.Matrix (Fin r) (Fin r) Int) := by
    rw [← matrixEquiv_mul, hi, Matrix.scale_eq_smul, matrixEquiv_smul, matrixEquiv_identity]
  have hdet : (matrixEquiv (momentMatrix s.rows s.columns)).det ≠ 0 := by
    intro hz
    have he := congrArg _root_.Matrix.det he
    simp only [_root_.Matrix.det_mul, _root_.Matrix.det_smul, _root_.Matrix.det_one,
      mul_one, hz, mul_zero, Fintype.card_fin] at he
    exact pow_ne_zero r hd he.symm
  let m : Matrix Rat r r := Matrix.ofFn fun i j => (entry s.rows[i] s.columns[j] : Rat)
  have hm : matrixEquiv m = (matrixEquiv (momentMatrix s.rows s.columns)).map
      (Int.castRingHom Rat) := by
    simp only [m, momentMatrix, matrixEquiv_ofFn]
    rfl
  have hrat : (matrixEquiv m).det ≠ 0 := by
    rw [hm]
    change ((Int.castRingHom Rat).mapMatrix
      (matrixEquiv (momentMatrix s.rows s.columns))).det ≠ 0
    rw [← RingHom.map_det]
    change ((matrixEquiv (momentMatrix s.rows s.columns)).det : Rat) ≠ 0
    exact_mod_cast hdet
  have hright : m * matrixEquiv.symm (matrixEquiv m)⁻¹ = Matrix.identity r := by
    apply matrixEquiv.injective
    rw [matrixEquiv_mul, Equiv.apply_symm_apply, matrixEquiv_identity]
    exact _root_.Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hrat)
  have hrank := Matrix.rowReduce_rank_eq_n_of_rightInverse _ _ hright
  cases he : Matrix.inverse? m with
  | none => exact False.elim (((Matrix.inverse?_eq_none m).mp he) hrank)
  | some inv => exact ⟨inv, rfl⟩

/-- Rational inversion returns the original integer counts before the producer
tests denominators or signs. The inverse call is the one used by `solveSystem`. -/
theorem System.rationalCounts {r arity : Nat} (s : System r) (h : s.check arity = true)
    (inv : Matrix Rat r r)
    (hinv : Matrix.inverse? (Matrix.ofFn fun (i j : Fin r) =>
      (entry s.rows[i] s.columns[j] : Rat)) = some inv) :
    inv * s.values.map (fun (z : Int) => (z : Rat)) = s.counts.map (fun (z : Int) => (z : Rat)) := by
  let m : Matrix Rat r r := Matrix.ofFn fun i j => (entry s.rows[i] s.columns[j] : Rat)
  have hm : matrixEquiv m = (matrixEquiv (momentMatrix s.rows s.columns)).map
      (Int.castRingHom Rat) := by
    simp only [m, momentMatrix, matrixEquiv_ofFn]
    rfl
  have hv (v : Vector Int r) : vectorEquiv (v.map fun (z : Int) => (z : Rat)) =
      (Int.castRingHom Rat) ∘ vectorEquiv v := by
    funext i
    simp
  have hc : m * s.counts.map (fun (z : Int) => (z : Rat)) = s.values.map (fun (z : Int) => (z : Rat)) := by
    apply vectorEquiv.injective
    rw [vectorEquiv_mulVec, hm, hv, hv]
    funext i
    rw [← RingHom.map_mulVec, ← vectorEquiv_mulVec, s.identities h |>.2.2]
    rfl
  have hi := (Matrix.inverse?_spec m inv hinv).2
  rw [← hc, ← Matrix.mul_assoc_vec, hi, Matrix.identity_mulVec]

private theorem clear_scalar (q : Rat) (d : Nat) (h : q.den ∣ d) :
    ((q.num * (d / q.den : Nat) : Int) : Rat) = (d : Rat) * q := by
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div_charZero h,
    ← mul_div_assoc, mul_comm (q.num : Rat), mul_div_assoc, Rat.num_div_den]

/-- The denominator and integer entries constructed by the actual rational
solver represent the same inverse, scaled by a strictly positive integer. -/
theorem inverse_den {r : Nat} (inv : Matrix Rat r r) :
    let d := ((List.finRange r).flatMap fun i =>
      (List.finRange r).map fun j => inv[(i, j)].den).foldl Nat.lcm 1
    0 < d ∧ ∀ i j : Fin r, ((inv[(i, j)].num * (d / inv[(i, j)].den : Nat) : Int) : Rat) =
      (d : Rat) * inv[(i, j)] := by
  let xs := (List.finRange r).flatMap fun i =>
    (List.finRange r).map fun j => inv[(i, j)]
  have he : ((List.finRange r).flatMap fun i =>
      (List.finRange r).map fun j => inv[(i, j)].den).foldl Nat.lcm 1 =
      (Matrix.Lists.Scaled.encode xs).denom := by
    simp [Matrix.Lists.Scaled.encode, xs, List.foldl_flatMap, List.foldl_map]
  dsimp only
  rw [he]
  refine ⟨encode_denom_pos xs, fun i j => clear_scalar _ _ ?_⟩
  apply encode_denom_dvd xs
  exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
    List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩⟩

/-- Clearing the actual rational inverse gives the literal integer identity
checked by the sign-system replay, without changing either index order. -/
theorem clear_inverse {r : Nat} (m : Matrix Int r r) (inv : Matrix Rat r r)
    (h : inv * m.map (fun (z : Int) => (z : Rat)) = Matrix.identity r) :
    let d := ((List.finRange r).flatMap fun i =>
      (List.finRange r).map fun j => inv[(i, j)].den).foldl Nat.lcm 1
    (Matrix.ofFn fun (i j : Fin r) => inv[(i, j)].num * (d / inv[(i, j)].den : Nat)) * m =
      Matrix.scale (d : Int) (Matrix.identity r) := by
  dsimp only
  let d := ((List.finRange r).flatMap fun i =>
    (List.finRange r).map fun j => inv[(i, j)].den).foldl Nat.lcm 1
  let a : Matrix Int r r := Matrix.ofFn fun i j =>
    inv[(i, j)].num * (d / inv[(i, j)].den : Nat)
  have ha : (matrixEquiv a).map (Int.castRingHom Rat) =
      (d : Rat) • matrixEquiv inv := by
    rw [show a = Matrix.ofFn (fun (i j : Fin r) =>
      inv[(i, j)].num * (d / inv[(i, j)].den : Nat)) from rfl, matrixEquiv_ofFn]
    ext i j
    exact (inverse_den inv).2 i j
  have hm : matrixEquiv (m.map fun (z : Int) => (z : Rat)) =
      (matrixEquiv m).map (Int.castRingHom Rat) := by
    ext i j
    simp only [_root_.Matrix.map_apply, Int.coe_castRingHom, matrixEquiv_apply,
      Matrix.getElem_map]
  have he : (matrixEquiv (a * m)).map (Int.castRingHom Rat) = (d : Rat) • 1 := by
    rw [matrixEquiv_mul, _root_.Matrix.map_mul, ha, ← hm,
      _root_.Matrix.smul_mul, ← matrixEquiv_mul, h, matrixEquiv_identity]
  have hr : (matrixEquiv (Matrix.scale (d : Int) (Matrix.identity r))).map
      (Int.castRingHom Rat) = (d : Rat) • (1 : _root_.Matrix (Fin r) (Fin r) Rat) := by
    rw [Matrix.scale_eq_smul, matrixEquiv_smul, matrixEquiv_identity]
    ext i j
    simp only [_root_.Matrix.map_apply, Int.coe_castRingHom, _root_.Matrix.smul_apply,
      smul_eq_mul, _root_.Matrix.one_apply, Int.cast_mul, Int.cast_natCast]
    split_ifs <;> simp
  apply matrixEquiv.injective
  ext i j
  have hij := congrFun (congrFun (he.trans hr.symm) i) j
  simp only [_root_.Matrix.map_apply, Int.coe_castRingHom] at hij
  exact_mod_cast hij

/-- The rational solver cannot fail on a checked integer moment system. It
preserves all literal input orders and returns the same nonnegative counts;
its chosen denominator and inverse need not match the supplied witnesses. -/
theorem solveSystem_complete {r arity : Nat} (s : System r) (h : s.check arity = true) :
    ∃ t, solveSystem arity s.rows s.columns s.values = .ok t ∧
      t.rows = s.rows ∧ t.columns = s.columns ∧ t.values = s.values ∧
      t.counts = s.counts ∧ t.check arity = true := by
  obtain ⟨inv, hinv⟩ := s.rationalInverse h
  have hc := s.rationalCounts h inv hinv
  let d := ((List.finRange r).flatMap fun i =>
    (List.finRange r).map fun j => inv[(i, j)].den).foldl Nat.lcm 1
  let a : Matrix Int r r := Matrix.ofFn fun i j =>
    inv[(i, j)].num * (d / inv[(i, j)].den : Nat)
  let t : System r := {
    rows := s.rows, columns := s.columns, values := s.values
    counts := s.counts, denominator := d, inverse := a }
  have hd : (d : Int) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (inverse_den inv).1)
  have hi : a * momentMatrix s.rows s.columns =
      Matrix.scale (d : Int) (Matrix.identity r) := by
    apply clear_inverse
    have hm : (momentMatrix s.rows s.columns).map (fun (z : Int) => (z : Rat)) =
        Matrix.ofFn (fun (i j : Fin r) => (entry s.rows[i] s.columns[j] : Rat)) := by
      apply Matrix.ext_getElem
      intro i j
      simp only [Matrix.getElem_map, momentMatrix, Matrix.getElem_ofFn]
    rw [hm]
    exact (Matrix.inverse?_spec _ inv hinv).2
  have ht : t.check arity = true := by
    have hh := h
    simp only [System.check, Bool.and_eq_true, decide_eq_true_eq] at hh
    simp only [System.check, t, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hh.1.1, hd⟩, hi, hh.2.2⟩
  have hnum : (inv * s.values.map (fun (z : Int) => (z : Rat))).map (·.num) = s.counts := by
    apply Vector.ext
    intro i hi
    simp only [hc, Vector.getElem_map, Rat.num_intCast]
  have hden : (inv * s.values.map (fun (z : Int) => (z : Rat))).toList.all
      (fun q => q.den == 1) = true := by
    rw [hc]
    simp
  have hpos : (inv * s.values.map (fun (z : Int) => (z : Rat))).toList.all
      (fun q => q.num ≥ 0) = true := by
    have hh := h
    simp only [System.check, Bool.and_eq_true] at hh
    rw [hc]
    simp only [Vector.toList_map]
    apply List.all_eq_true.mpr
    intro q hq
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
    simp only [Rat.num_intCast]
    exact List.all_eq_true.mp hh.1.1.2 z hz
  refine ⟨t, ?_, rfl, rfl, rfl, rfl, ht⟩
  simp only [solveSystem, hinv, bind, Except.bind, hden, hpos, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, hnum]
  change (if t.check arity then pure t else throw BuildError.system) = Except.ok t
  rw [ht]
  rfl

end Hex.SignDet
