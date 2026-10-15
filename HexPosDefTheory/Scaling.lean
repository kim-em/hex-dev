/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDefTheory.Soundness

public section

/-! Transport through one positive common denominator. -/

open Matrix
open scoped ComplexOrder

namespace Hex.PosDefTheory

variable {R : Type*} [CommRing R] [PartialOrder R] [StarRing R]
variable [IsStrictOrderedRing R] [StarOrderedRing R] [NoZeroDivisors R] [PosMulReflectLT R]
variable {n : Type*} [Fintype n]

/-- Positive scalar multiplication preserves and reflects positive definiteness. -/
theorem smul_posDef_iff (A : _root_.Matrix n n R) {s : R} (hs : 0 < s) :
    (s • A).PosDef ↔ A.PosDef := by
  have hstar : star s = s := IsSelfAdjoint.of_nonneg hs.le
  constructor
  · intro h
    have hA : A.IsHermitian := by
      ext i j
      have he := congrFun (congrFun h.isHermitian i) j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul,
        hstar] at he
      exact mul_left_cancel₀ hs.ne' (by simpa only [Matrix.conjTranspose_apply, mul_comm] using he)
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hA fun x hx => ?_
    have hp := h.dotProduct_mulVec_pos hx
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hp
    exact lt_of_mul_lt_mul_left (by simpa only [mul_zero] using hp) hs.le
  · intro h
    exact h.smul hs

namespace Int

variable (R) [CharZero R]

/-- Apply an integer certificate after identifying a positive common scaling. -/
theorem positive_of_scaled {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) R)
    (s : Nat) (rows : List (List Int)) (c : Hex.PosDef.PositiveCert Int)
    (hs : 0 < s) (he : (s : R) • A = Lists.matrix (intModel R) n rows)
    (hc : Hex.PosDef.Int.checkPositive n rows c = true) : A.PosDef := by
  apply (smul_posDef_iff A (Nat.cast_pos.mpr hs)).mp
  rw [he]
  exact checkPositive_sound R n rows c hc

/-- Positive scaling transports a checked refutation as well. -/
theorem negative_of_scaled {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) R)
    (s : Nat) (rows : List (List Int)) (c : Hex.PosDef.NegativeCert Int)
    (hs : 0 < s) (he : (s : R) • A = Lists.matrix (intModel R) n rows)
    (hc : Hex.PosDef.Int.checkNegative n rows c = true) : ¬ A.PosDef := by
  intro h
  apply checkNegative_sound R n rows c hc
  rw [← he]
  exact (smul_posDef_iff A (Nat.cast_pos.mpr hs)).mpr h

end Int

namespace Gaussian

/-- Gaussian certificates apply to a complex matrix after one checked common scaling. -/
theorem positive_of_scaled {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Complex)
    (s : Nat) (rows : List (List Hex.PosDef.Gaussian)) (c : Hex.PosDef.PositiveCert Hex.PosDef.Gaussian)
    (hs : 0 < s) (he : (s : Complex) • A = Lists.matrix gaussianModel n rows)
    (hc : Hex.PosDef.Gaussian.checkPositive n rows c = true) : A.PosDef := by
  apply (smul_posDef_iff A (Nat.cast_pos.mpr hs)).mp
  rw [he]
  exact checkPositive_sound n rows c hc

/-- A checked complex refutation also descends through positive scaling. -/
theorem negative_of_scaled {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Complex)
    (s : Nat) (rows : List (List Hex.PosDef.Gaussian)) (c : Hex.PosDef.NegativeCert Hex.PosDef.Gaussian)
    (hs : 0 < s) (he : (s : Complex) • A = Lists.matrix gaussianModel n rows)
    (hc : Hex.PosDef.Gaussian.checkNegative n rows c = true) : ¬ A.PosDef := by
  intro h
  apply checkNegative_sound n rows c hc
  rw [← he]
  exact (smul_posDef_iff A (Nat.cast_pos.mpr hs)).mpr h

end Gaussian

end Hex.PosDefTheory
