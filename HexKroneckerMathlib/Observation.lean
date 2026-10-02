/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.Preflight

public section

namespace Hex.Kronecker

theorem code_mono (ss a b : List Nat) (hlen : a.length = b.length)
    (h : ∀ i, a.getD i 0 ≤ b.getD i 0) : code ss a ≤ code ss b := by
  induction a generalizing ss b with
  | nil => cases ss <;> simp [code]
  | cons a as ih =>
    cases b with
    | nil => simp at hlen
    | cons b bs =>
      cases ss with
      | nil => simp [code]
      | cons s ss =>
        apply Nat.add_le_add (Nat.mul_le_mul_right s (h 0))
        exact ih ss bs (by simpa using hlen) (fun i => h (i + 1))

theorem Bounds.bits_mono (ss : List Nat) (w : Nat) (a b : Bounds)
    (hlen : a.degrees.length = b.degrees.length)
    (hd : ∀ i, a.degrees.getD i 0 ≤ b.degrees.getD i 0)
    (hh : a.height ≤ b.height) : a.bits ss w ≤ b.bits ss w := by
  have hc := Nat.mul_le_mul_right w (code_mono ss a.degrees b.degrees hlen hd)
  have hl : a.height.log2 ≤ b.height.log2 := by
    by_cases ha : a.height = 0
    · simp [ha]
    · exact (Nat.le_log2 (by omega : b.height ≠ 0)).mpr ((Nat.log2_self_le ha).trans hh)
  exact Nat.add_le_add_right (Nat.add_le_add hc hl) 2

theorem Bounds.bits_add (cap : Nat) (ss : List Nat) (w : Nat) (a b : Bounds)
    (hlen : a.degrees.length = b.degrees.length) (ha : a.height ≤ cap) (hb : b.height ≤ cap) :
    max (a.bits ss w) (b.bits ss w) ≤ (a.add cap b).bits ss w := by
  apply max_le
  · apply Bounds.bits_mono
    · simp [Bounds.add, hlen]
    · intro i; simp only [Bounds.add, getD_maxDegrees]; omega
    · exact Saturating.le_add_left cap _ _ ha
  · apply Bounds.bits_mono
    · simp [Bounds.add, hlen]
    · intro i; simp only [Bounds.add, getD_maxDegrees]; omega
    · exact Saturating.le_add_right cap _ _ hb

theorem Bounds.bits_mul (cap : Nat) (ss : List Nat) (w : Nat) (a b : Bounds)
    (hlen : a.degrees.length = b.degrees.length) (ha : a.height ≤ cap) (hb : b.height ≤ cap)
    (hza : a.height ≠ 0) (hzb : b.height ≠ 0) :
    max (a.bits ss w) (b.bits ss w) ≤ (a.mul cap b).bits ss w := by
  apply max_le
  · apply Bounds.bits_mono
    · simp [Bounds.mul, hlen]
    · intro i; simp only [Bounds.mul, getD_addDegrees]; omega
    · simp only [Bounds.mul, Saturating.mul_eq]
      exact le_min (Nat.le_mul_of_pos_right _ (by omega)) ha
  · apply Bounds.bits_mono
    · simp [Bounds.mul, hlen]
    · intro i; simp only [Bounds.mul, getD_addDegrees]; omega
    · simp only [Bounds.mul, Saturating.mul_eq]
      exact le_min (Nat.le_mul_of_pos_left _ (by omega)) hb

theorem Bounds.bits_pow (cap : Nat) (ss : List Nat) (w : Nat) (a : Bounds)
    (ha : a.height ≤ cap) (n : Nat) (hn : n ≠ 0) :
    a.bits ss w ≤ (a.pow cap n).bits ss w := by
  apply Bounds.bits_mono
  · simp [Bounds.pow]
  · intro i; simp only [Bounds.pow, getD_scaleDegrees]
    exact Nat.le_mul_of_pos_left _ (by omega)
  · simp only [Bounds.pow, Saturating.pow_eq]
    exact le_min (Nat.le_self_pow hn _) ha

@[simp] theorem maxBits_nil (ss : List Nat) (w : Nat) : maxBits ss w [] = 0 := rfl

@[simp] theorem maxBits_cons (ss : List Nat) (w : Nat) (b : Bounds) (bs : List Bounds) :
    maxBits ss w (b :: bs) = max (b.bits ss w) (maxBits ss w bs) := rfl

@[simp] theorem maxBits_append (ss : List Nat) (w : Nat) (as bs : List Bounds) :
    maxBits ss w (as ++ bs) = max (maxBits ss w as) (maxBits ss w bs) := by
  induction as <;> simp [*, max_assoc]

/-- Reference maximum over every subtree, including operands below a zero power. -/
def Expr.subtreeBits (cap k : Nat) (ss : List Nat) (w : Nat) (e : Expr) : Nat :=
  let root := (e.analyzeCore cap k).1.bits ss w
  match e with
  | .int _ | .atom _ => root
  | .add a b | .sub a b | .mul a b =>
    max root (max (a.subtreeBits cap k ss w) (b.subtreeBits cap k ss w))
  | .neg a | .pow a _ => max root (a.subtreeBits cap k ss w)

theorem Expr.analyzeCore_height (cap k : Nat) (e : Expr) :
    (e.analyzeCore cap k).1.height ≤ cap := by
  rw [e.analyzeCore_bound]
  exact (e.cappedHeight_eq cap).trans_le (Nat.min_le_right _ _)

theorem Expr.analyzeCore_length (cap k : Nat) (e : Expr) :
    (e.analyzeCore cap k).1.degrees.length = k := by
  rw [e.analyzeCore_bound]
  exact e.length_degrees k

theorem Expr.analyzeCore_add (cap k : Nat) (a b : Expr) :
    (.add a b : Expr).analyzeCore cap k =
      ((a.analyzeCore cap k).1.add cap (b.analyzeCore cap k).1,
        (a.analyzeCore cap k).2 ++ (b.analyzeCore cap k).2) := rfl

theorem Expr.analyzeCore_sub (cap k : Nat) (a b : Expr) :
    (.sub a b : Expr).analyzeCore cap k =
      ((a.analyzeCore cap k).1.add cap (b.analyzeCore cap k).1,
        (a.analyzeCore cap k).2 ++ (b.analyzeCore cap k).2) := rfl

theorem Expr.analyzeCore_neg (cap k : Nat) (a : Expr) :
    (.neg a : Expr).analyzeCore cap k = a.analyzeCore cap k := rfl

theorem Expr.analyzeCore_mul (cap k : Nat) (a b : Expr) :
    (.mul a b : Expr).analyzeCore cap k =
      ((a.analyzeCore cap k).1.mul cap (b.analyzeCore cap k).1,
        if (a.analyzeCore cap k).1.height == 0 || (b.analyzeCore cap k).1.height == 0 then
          (a.analyzeCore cap k).1 :: (b.analyzeCore cap k).1 ::
            ((a.analyzeCore cap k).2 ++ (b.analyzeCore cap k).2)
        else (a.analyzeCore cap k).2 ++ (b.analyzeCore cap k).2) := rfl

theorem Expr.analyzeCore_pow (cap k : Nat) (a : Expr) (n : Nat) :
    (.pow a n : Expr).analyzeCore cap k =
      ((a.analyzeCore cap k).1.pow cap n,
        if n == 0 then (a.analyzeCore cap k).1 :: (a.analyzeCore cap k).2
        else (a.analyzeCore cap k).2) := rfl

/-- Pruning preserves the exact maximum, rather than replacing it by an estimate. -/
theorem Expr.analyzeCore_bits (cap k : Nat) (ss : List Nat) (w : Nat) (e : Expr) :
    max ((e.analyzeCore cap k).1.bits ss w) (maxBits ss w (e.analyzeCore cap k).2) =
      e.subtreeBits cap k ss w := by
  induction e with
  | int | atom => simp [Expr.analyzeCore, Expr.subtreeBits]
  | add a b ha hb | sub a b ha hb =>
    have hd := Bounds.bits_add cap ss w (a.analyzeCore cap k).1 (b.analyzeCore cap k).1
      (by rw [a.analyzeCore_length, b.analyzeCore_length])
      (a.analyzeCore_height cap k) (b.analyzeCore_height cap k)
    simp only [Expr.subtreeBits, Expr.analyzeCore_add, Expr.analyzeCore_sub, maxBits_append]
    rw [← ha, ← hb]
    omega
  | neg a ha =>
    simp only [Expr.subtreeBits, Expr.analyzeCore_neg]
    rw [← ha]
    omega
  | mul a b ha hb =>
    simp only [Expr.subtreeBits, Expr.analyzeCore_mul]
    rw [← ha, ← hb]
    split_ifs with hz
    · simp only [maxBits_cons, maxBits_append]
      omega
    · have hza : (a.analyzeCore cap k).1.height ≠ 0 := by
        intro h; simp [h] at hz
      have hzb : (b.analyzeCore cap k).1.height ≠ 0 := by
        intro h; simp [h] at hz
      have hd := Bounds.bits_mul cap ss w (a.analyzeCore cap k).1 (b.analyzeCore cap k).1
        (by rw [a.analyzeCore_length, b.analyzeCore_length])
        (a.analyzeCore_height cap k) (b.analyzeCore_height cap k) hza hzb
      simp only [maxBits_append]
      omega
  | pow a n ha =>
    simp only [Expr.subtreeBits, Expr.analyzeCore_pow]
    rw [← ha]
    split_ifs with hn
    · simp only [maxBits_cons]
    · have hn : n ≠ 0 := by simpa using hn
      have hd := Bounds.bits_pow cap ss w (a.analyzeCore cap k).1
        (a.analyzeCore_height cap k) n hn
      omega

/-- The public accumulator reports precisely the maximum over every subtree
and the preceding observations. -/
theorem Expr.analyze_bits (cap k : Nat) (ss : List Nat) (w : Nat) (e : Expr)
    (acc : List Bounds) :
    maxBits ss w (e.analyze cap k acc).2 =
      max (e.subtreeBits cap k ss w) (maxBits ss w acc) := by
  simp only [Expr.analyze_eq, maxBits_cons, maxBits_append, ← max_assoc, e.analyzeCore_bits]

end Hex.Kronecker
