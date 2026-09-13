/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexMinPolyMathlib.Polynomial
public import HexMinPolyMathlib.EvalVec

public section

/-! Integer Krylov powers and denominator-cleared order certificates. -/

namespace HexMinPolyMathlib

open Hex.Matrix.Lists Hex.Matrix.MinPolyLists HexMatrixMathlib HexPolyMathlib

local instance : Lean.Grind.Field ℚ := Field.toGrindField

/-- Integer lists viewed as rational vectors in transport proofs. -/
@[expose] def integerVector (n : Nat) (xs : List Int) : Fin n → ℚ :=
  fun i => ((entry (0 : Int) xs i : Int) : ℚ)

/-- Integer row lists viewed as a rational matrix. -/
@[expose] def integerMatrix (n : Nat) (xs : List (List Int)) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (get xs i j : ℚ)

theorem mulVec_sound {n : Nat} (z : List (List Int)) (v : List Int)
    (hz : shape n n z = true) :
    integerVector n (mulVec z v) = (integerMatrix n z).mulVec (integerVector n v) := by
  funext i
  have hn := (shape_iff _ _ _).mp hz |>.1
  have hi : i.val < z.length := by omega
  have he : entry 0 (mulVec z v) i = dot (entry [] z i) v := by
    simp only [mulVec, entry_eq_getD]
    rw [getD_eq_getElem' (z.map (dot · v)) i 0 (by simpa using hi),
      List.getElem_map, getD_eq_getElem' z i [] hi]
  change ((entry (0 : Int) (mulVec z v) i : Int) : ℚ) = _
  rw [he, dot_eq_sum, row_length hz i, Int.cast_sum]
  simp only [integerMatrix, integerVector, Matrix.mulVec, dotProduct, Int.cast_mul,
    Hex.Matrix.Lists.get, entry_eq_getD]

theorem powers_length (z : List (List Int)) (r : Nat) (v : List Int) :
    (powers z r v).length = r := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih => simp only [powers, List.length_cons, ih]

theorem powers_sound {n : Nat} (z : List (List Int)) (hz : shape n n z = true)
    (r : Nat) (v : List Int) (k : Nat) (hk : k < r) :
    integerVector n (entry [] (powers z r v) k) =
      ((integerMatrix n z) ^ k).mulVec (integerVector n v) := by
  induction r generalizing v k with
  | zero => omega
  | succ r ih =>
    cases k with
    | zero => simp [powers, entry]
    | succ k =>
      rw [powers, entry, ih _ k (by omega), mulVec_sound z v hz,
        Matrix.mulVec_mulVec, ← pow_succ]

theorem integerMatrix_scale {n : Nat} (z : ScaledRows) (hd : 0 < z.denom) :
    integerMatrix n z.nums = (z.denom : ℚ) • ofLists n n (decodeRows z) := by
  ext i j
  simp only [integerMatrix, ofLists_apply, decodeRows_getD, Matrix.smul_apply,
    smul_eq_mul, decodeScalar, Hex.Matrix.Lists.get, entry_eq_getD]
  have hd' : (z.denom : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  field_simp

theorem basis_sound (n : Nat) (i : Fin n) :
    integerVector n (basis n i) = vectorEquiv (Hex.Matrix.basisVec n i) := by
  funext j
  rw [integerVector, basis, entry_eq_getD,
    getD_eq_getElem' ((List.range n).map (identity i ·)) j 0 (by simp),
    List.getElem_map, List.getElem_range]
  simp only [identity, Nat.beq_eq, vectorEquiv_apply, Hex.Matrix.basisVec,
    Hex.Matrix.getElem_row, Hex.Matrix.getElem_identity]
  by_cases h : i = j
  · subst j
    simp
  · have hv : i.val ≠ j.val := fun hv => h (Fin.ext hv)
    simp [h, hv]

/-- Decode the input at the proof boundary, never in certificate reduction. -/
@[expose] def inputMatrix (n : Nat) (z : ScaledRows) : Hex.Matrix ℚ n n :=
  matrixEquiv.symm (ofLists n n (decodeRows z))

theorem scaled_powers {n : Nat} (z : ScaledRows) (hz : shape n n z.nums = true)
    (hd : 0 < z.denom) (i : Fin n) (r k : Nat) (hk : k < r) :
    integerVector n (entry [] (powers z.nums r (basis n i)) k) =
      (z.denom : ℚ) ^ k • vectorEquiv (Hex.Matrix.krylovVec (inputMatrix n z)
        (Hex.Matrix.basisVec n i) k) := by
  rw [powers_sound _ hz _ _ _ hk, basis_sound, integerMatrix_scale z hd, smul_pow,
    Matrix.smul_mulVec, vectorEquiv_krylovVec]
  simp only [inputMatrix, Equiv.apply_symm_apply]

theorem evaluate_sum (D d : Nat) (a v : List Int) :
    evaluate D d a v = ∑ k : Fin a.length,
      a.getD k 0 * (D : Int) ^ (d - k.val) * v.getD k 0 := by
  induction a generalizing d v with
  | nil => simp [evaluate]
  | cons a as ih =>
    cases v with
    | nil => simp [evaluate]
    | cons v vs =>
      simp only [evaluate, Int.add_def, Int.mul_def, Int.ofNat_eq_natCast,
        Nat.pow_eq, Nat.cast_pow, List.length_cons, Fin.sum_univ_succ, Fin.val_zero,
        Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ, ih, Nat.sub_zero, Nat.sub_sub]
      simp only [Nat.add_comm 1]

theorem evalVec_entry (p : Hex.DensePoly ℚ) (A : Hex.Matrix ℚ n n) (v : Vector ℚ n)
    (r : Nat) (hr : p.size ≤ r) (j : Fin n) :
    (Hex.Matrix.evalVec p A v)[j] =
      ∑ k : Fin r, p.coeff k.val * (Hex.Matrix.krylovVec A v k.val)[j] := by
  rw [Hex.Matrix.evalVec_eq_vecMul_krylov p A v r hr]
  have h := congrFun (vectorEquiv_vecMul_krylov (p.coeffVec r) A v) j
  have hc (k : Fin r) : (p.coeffVec r)[k] = p.coeff k.val := by
    change (Vector.ofFn fun i : Fin r => p.coeff i.val)[k.val] = _
    rw [Vector.getElem_ofFn]
  simpa only [vectorEquiv_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    hc] using h

theorem annihilation_of_check {n : Nat} (z : ScaledRows) (hz : shape n n z.nums = true)
    (hd : 0 < z.denom) (i : Fin n) (o : Hex.Matrix.OrderWitness)
    (hv : valid o.poly = true) (hl : o.poly.nums.length = o.deg + 1)
    (h : all (fun j => decide (evaluate z.denom o.deg o.poly.nums
      (column j (powers z.nums (o.deg + 1) (basis n i))) = 0)) n = true) :
    Hex.Matrix.evalVec (decodeBlock o.poly) (inputMatrix n z) (Hex.Matrix.basisVec n i) = 0 := by
  apply Vector.ext
  intro j hj
  let jj : Fin n := ⟨j, hj⟩
  have he := of_decide_eq_true ((all_iff _ _).mp h j hj)
  have hs := evaluate_sum z.denom o.deg o.poly.nums
    (column j (powers z.nums (o.deg + 1) (basis n i)))
  rw [hl, he] at hs
  have hs' : (∑ k : Fin (o.deg + 1),
      (o.poly.nums.getD k 0 : ℚ) * (z.denom : ℚ) ^ (o.deg - k.val) *
        ((column j (powers z.nums (o.deg + 1) (basis n i))).getD k 0 : ℚ)) = 0 := by
    exact_mod_cast hs.symm
  have hd' : (z.denom : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hp' : (o.poly.denom : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (valid_pos _ hv))
  have hm : (o.poly.denom : ℚ) * (z.denom : ℚ) ^ o.deg ≠ 0 :=
    mul_ne_zero hp' (pow_ne_zero _ hd')
  have hterm (k : Fin (o.deg + 1)) :
      (o.poly.nums.getD k 0 : ℚ) * (z.denom : ℚ) ^ (o.deg - k.val) *
        ((column j (powers z.nums (o.deg + 1) (basis n i))).getD k 0 : ℚ) =
      ((o.poly.denom : ℚ) * (z.denom : ℚ) ^ o.deg) *
        ((decodeBlock o.poly).coeff k.val *
          (Hex.Matrix.krylovVec (inputMatrix n z) (Hex.Matrix.basisVec n i) k.val)[jj]) := by
    have hk := congrFun (scaled_powers z hz hd i (o.deg + 1) k k.isLt) jj
    simp only [integerVector, Pi.smul_apply, smul_eq_mul, vectorEquiv_apply,
      entry_eq_getD] at hk
    rw [column_getD, hk, decodeBlock_coeff, decodeScalar, entry_eq_getD]
    have hpow : (z.denom : ℚ) ^ (o.deg - k.val) * (z.denom : ℚ) ^ k.val =
        (z.denom : ℚ) ^ o.deg := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [← hpow]
    field_simp
  simp_rw [hterm] at hs'
  rw [← Finset.mul_sum, mul_eq_zero] at hs'
  have hsum := hs'.resolve_left hm
  change (Hex.Matrix.evalVec (decodeBlock o.poly) (inputMatrix n z)
    (Hex.Matrix.basisVec n i))[jj] = (0 : Vector ℚ n)[jj]
  rw [evalVec_entry _ _ _ (o.deg + 1) (by rw [decodeBlock_size _ hv, hl])]
  have hz : (0 : Vector ℚ n)[jj] = 0 := by
    change (0 : Vector ℚ n)[jj.val] = 0
    rw [Vector.getElem_zero]
  exact hsum.trans hz.symm

theorem powers_row_length {n : Nat} (z : List (List Int)) (hz : shape n n z = true)
    (r : Nat) (v : List Int) (hv : v.length = n) (k : Nat) (hk : k < r) :
    (entry [] (powers z r v) k).length = n := by
  induction r generalizing v k with
  | zero => omega
  | succ r ih =>
    cases k with
    | zero => exact hv
    | succ k =>
      rw [powers, entry]
      apply ih _ _ k (by omega)
      simpa only [mulVec, List.length_map] using (shape_iff _ _ _).mp hz |>.1

/-- Decode a supplied inverse block, outside the reduction path. -/
@[expose] def inverseMatrix (n d : Nat) (s : ScaledRows) : Hex.Matrix ℚ n d :=
  matrixEquiv.symm (ofLists n d (decodeRows s))

theorem rightInverse_of_check {n : Nat} (z : ScaledRows) (hz : shape n n z.nums = true)
    (hd : 0 < z.denom) (i : Fin n) (o : Hex.Matrix.OrderWitness)
    (hi : 0 < o.inv.denom)
    (h : all (fun k => all (fun j => decide (
      dot (entry [] (powers z.nums (o.deg + 1) (basis n i)) k) (column j o.inv.nums) =
        Int.mul (Int.mul (Int.ofNat (Nat.pow z.denom k)) (Int.ofNat o.inv.denom))
          (identity k j))) o.deg) o.deg = true) :
    Hex.Matrix.krylovMat (inputMatrix n z) (Hex.Matrix.basisVec n i) o.deg *
      inverseMatrix n o.deg o.inv = Hex.Matrix.identity o.deg := by
  apply matrixEquiv.injective
  change matrixEquiv (_ * _) = matrixEquiv (1 : Hex.Matrix ℚ o.deg o.deg)
  rw [matrixEquiv_mul, matrixEquiv_one]
  ext k l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hc := of_decide_eq_true ((all_iff _ _).mp ((all_iff _ _).mp h k k.isLt) l l.isLt)
  rw [dot_eq_sum, powers_row_length _ hz _ _ (by simp [basis]) _ (by omega)] at hc
  have hs : (∑ j : Fin n,
      ((entry [] (powers z.nums (o.deg + 1) (basis n i)) k).getD j 0 : ℚ) *
      ((column l o.inv.nums).getD j 0 : ℚ)) =
      ((z.denom : ℚ) ^ k.val * (o.inv.denom : ℚ)) * (if k = l then 1 else 0) := by
    have hid : (identity k l : Int) = if k = l then 1 else 0 := by
      simp only [identity, Nat.beq_eq, Fin.ext_iff]
    rw [hid] at hc
    exact_mod_cast hc
  have hd' : (z.denom : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hi' : (o.inv.denom : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hi)
  have hm : (z.denom : ℚ) ^ k.val * (o.inv.denom : ℚ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hd') hi'
  apply mul_left_cancel₀ hm
  rw [Finset.mul_sum]
  rw [← hs]
  apply Finset.sum_congr rfl
  intro j _
  have hp := congrFun (scaled_powers z hz hd i (o.deg + 1) k (by omega)) j
  simp only [integerVector, entry_eq_getD, Pi.smul_apply, smul_eq_mul, vectorEquiv_apply] at hp
  have hk : matrixEquiv (Hex.Matrix.krylovMat (inputMatrix n z) (Hex.Matrix.basisVec n i)
      o.deg) k j = (Hex.Matrix.krylovVec (inputMatrix n z) (Hex.Matrix.basisVec n i) k.val)[j] := by
    rw [matrixEquiv_apply, Hex.Matrix.getElem_eq_getRow, Hex.Matrix.getRow_krylovMat]
  rw [hk]
  simp only [inverseMatrix, Equiv.apply_symm_apply, ofLists_apply, decodeRows_getD,
    decodeScalar, column_getD, entry_eq_getD]
  rw [hp]
  field_simp

end HexMinPolyMathlib
