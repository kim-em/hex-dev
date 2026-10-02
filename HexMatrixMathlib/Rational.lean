/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexMatrix.Scaled
public import HexMatrixMathlib.Literal
public import Mathlib.Data.Rat.Lemmas

public section

/-! Proved common-denominator decoding for structural tactic frontends. -/

namespace HexMatrixMathlib

open Hex.Matrix.Lists

/-- Decode a scalar; used only in the soundness layer. -/
@[expose] def decodeScalar (d : Nat) (z : Int) : ℚ := (z : ℚ) / d

theorem decodeScalar_zero (d : Nat) : decodeScalar d 0 = 0 := by
  simp [decodeScalar]

/-- Decode a common-denominator vector. -/
@[expose] def decodeList (s : Scaled) : List ℚ := s.nums.map (decodeScalar s.denom)

/-- Decode a common-denominator matrix. -/
@[expose] def decodeRows (s : ScaledRows) : List (List ℚ) :=
  s.nums.map (fun row => row.map (decodeScalar s.denom))

theorem decodeScalar_eq (q : ℚ) (z : Int) (d : Nat) (hd : 0 < d)
    (h : q.num * (d : Int) = z * (q.den : Int)) :
    q = decodeScalar d z := by
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hq' : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hc : (q.num : ℚ) * (d : ℚ) = (z : ℚ) * (q.den : ℚ) := by exact_mod_cast h
  rw [← Rat.num_div_den q]
  exact (div_eq_div_iff hq' hd').mpr hc

theorem scaleRow_sound (d : Nat) (q : List Rat) (z : List Int) (hd : 0 < d)
    (h : scaleRow d q z = true) : q = z.map (decodeScalar d) := by
  induction q generalizing z with
  | nil => cases z <;> simp_all [scaleRow]
  | cons q qs ih =>
    cases z with
    | nil => simp [scaleRow] at h
    | cons z zs =>
      simp only [scaleRow, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [List.map_cons]
      exact congrArg₂ List.cons (decodeScalar_eq q z d hd h.1) (ih zs h.2)

theorem scaleRows_sound (d : Nat) (q : List (List Rat)) (z : List (List Int))
    (hd : 0 < d) (h : scaleRows d q z = true) :
    q = decodeRows ⟨d, z⟩ := by
  induction q generalizing z with
  | nil => cases z <;> simp_all [scaleRows, decodeRows]
  | cons q qs ih =>
    cases z with
    | nil => simp [scaleRows] at h
    | cons z zs =>
      simp only [scaleRows, Bool.and_eq_true] at h
      exact congrArg₂ List.cons (scaleRow_sound d q z hd h.1) (ih zs h.2)

theorem decodeList_getD (s : Scaled) (i : Nat) :
    (decodeList s).getD i 0 = decodeScalar s.denom (s.nums.getD i 0) := by
  simp only [decodeList, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases s.nums[i]? <;> simp [decodeScalar]

theorem decodeRows_getD (s : ScaledRows) (i j : Nat) :
    ((decodeRows s).getD i []).getD j 0 =
      decodeScalar s.denom ((s.nums.getD i []).getD j 0) := by
  simp only [decodeRows, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : s.nums[i]? with
  | none => simp [decodeScalar]
  | some row =>
    simp only [Option.map_some, Option.getD_some, List.getElem?_map]
    cases row[j]? <;> simp [decodeScalar]

private theorem fold_lcm_pos (xs : List Rat) (d : Nat) (hd : 0 < d) :
    0 < xs.foldl (fun d q => Nat.lcm d q.den) d := by
  induction xs generalizing d with
  | nil => exact hd
  | cons q qs ih => exact ih _ (Nat.lcm_pos hd q.den_pos)

private theorem dvd_fold_lcm (xs : List Rat) (d : Nat) :
    d ∣ xs.foldl (fun d q => Nat.lcm d q.den) d := by
  induction xs generalizing d with
  | nil => exact dvd_refl d
  | cons q qs ih => exact (Nat.dvd_lcm_left d q.den).trans (ih _)

private theorem den_dvd_fold (xs : List Rat) (d : Nat) (q : Rat) (hq : q ∈ xs) :
    q.den ∣ xs.foldl (fun d q => Nat.lcm d q.den) d := by
  induction xs generalizing d with
  | nil => simp at hq
  | cons x xs ih =>
    rcases List.mem_cons.mp hq with rfl | hq
    · exact (Nat.dvd_lcm_right d q.den).trans (dvd_fold_lcm xs _)
    · exact ih _ hq

/-- The actual common-denominator producer always chooses a positive denominator,
including for the empty list. -/
theorem encode_denom_pos (xs : List Rat) : 0 < (Scaled.encode xs).denom := by
  unfold Scaled.encode
  exact fold_lcm_pos xs 1 (by decide)

/-- Every entry denominator divides the denominator chosen by the producer. -/
theorem encode_denom_dvd (xs : List Rat) (q : Rat) (hq : q ∈ xs) :
    q.den ∣ (Scaled.encode xs).denom := by
  unfold Scaled.encode
  exact den_dvd_fold xs 1 q hq

private theorem scaleRow_map (d : Nat) (xs : List Rat)
    (h : ∀ q ∈ xs, q.den ∣ d) :
    scaleRow d xs (xs.map fun q => q.num * Int.ofNat (d / q.den)) = true := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.map_cons, scaleRow, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · change q.num * (d : Int) = q.num * (d / q.den : Nat) * (q.den : Int)
      rw [mul_assoc, ← Nat.cast_mul, Nat.div_mul_cancel (h q (by simp))]
    · exact ih fun x hx => h x (by simp [hx])

/-- Clearing denominators in the shared producer passes the literal integer
cross-product checker. -/
theorem encode_scaleRow (xs : List Rat) :
    scaleRow (Scaled.encode xs).denom xs (Scaled.encode xs).nums = true := by
  unfold Scaled.encode
  exact scaleRow_map _ xs fun q hq => den_dvd_fold xs 1 q hq

/-- Decoding the producer output recovers every rational entry in its original order. -/
theorem decode_encode (xs : List Rat) : decodeList (Scaled.encode xs) = xs := by
  exact (scaleRow_sound _ _ _ (encode_denom_pos xs) (encode_scaleRow xs)).symm

theorem encodeRows_denom_pos (xs : List (List Rat)) :
    0 < (ScaledRows.encode xs).denom := by
  unfold ScaledRows.encode
  exact encode_denom_pos xs.flatten

theorem encode_scaleRows (xs : List (List Rat)) :
    scaleRows (ScaledRows.encode xs).denom xs (ScaledRows.encode xs).nums = true := by
  unfold ScaledRows.encode
  change scaleRows (Scaled.encode xs.flatten).denom xs
    (xs.map fun row => row.map fun q => q.num *
      Int.ofNat ((Scaled.encode xs.flatten).denom / q.den)) = true
  have h : ∀ row ∈ xs, ∀ q ∈ row, q.den ∣ (Scaled.encode xs.flatten).denom := by
    intro row hr q hq
    unfold Scaled.encode
    exact den_dvd_fold xs.flatten 1 q (List.mem_flatten.mpr ⟨row, hr, hq⟩)
  generalize (Scaled.encode xs.flatten).denom = d at *
  induction xs with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons, scaleRows, Bool.and_eq_true]
    exact ⟨scaleRow_map d row (h row (by simp)), ih fun r hr => h r (by simp [hr])⟩

/-- Matrix encoding preserves empty rows, dimensions and entry order. -/
theorem decodeRows_encode (xs : List (List Rat)) :
    decodeRows (ScaledRows.encode xs) = xs := by
  exact (scaleRows_sound _ _ _ (encodeRows_denom_pos xs) (encode_scaleRows xs)).symm

end HexMatrixMathlib
