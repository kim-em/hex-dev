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

end HexMatrixMathlib
