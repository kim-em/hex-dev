/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPoly.PseudoGcd
public import HexPoly.Interpret
import all Init.Data.Zero

public section

/-! Noninjective interpretation of the actual fraction-free coefficient recurrence. -/
namespace Hex.DensePoly.Interpret

universe u v
variable {E : Type u} {F : Type v}
variable [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]
variable [Zero F] [DecidableEq F] [One F] [Add F] [Sub F] [Mul F]
variable (f : E → F) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f (1 : E) = 1)
variable (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)

omit [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]
  [Zero F] [DecidableEq F] [One F] [Add F] [Sub F] [Mul F] in
private theorem getD_map (xs : Array E) (i : Nat) (fallback : E) :
    (xs.map f).getD i (f fallback) = f (xs.getD i fallback) := by
  by_cases h : i < xs.size <;> simp [Array.getD, h]

include hz in
omit [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]
  [DecidableEq F] [One F] [Add F] [Sub F] [Mul F] in
private theorem getD_zero_map (xs : Array E) (i : Nat) :
    (xs.map f).getD i (0 : F) = f (xs.getD i (0 : E)) := by
  rw [← (hz (0 : E)).mpr rfl]
  exact getD_map f xs i 0

include h1 hm in
omit [Zero E] [DecidableEq E] [Add E] [Sub E]
  [Zero F] [DecidableEq F] [Add F] [Sub F] in
private theorem powers_map (d : Nat) (b : E) :
    ((Array.range d).foldl
      (fun powers _ => powers.push (powers.getD (powers.size - 1) 1 * b)) #[1]).map f =
    (Array.range d).foldl
      (fun powers _ => powers.push (powers.getD (powers.size - 1) 1 * f b)) #[1] := by
  have h := Array.foldl_hom (fun xs : Array E => xs.map f)
    (xs := Array.range d) (init := #[1])
    (g₁ := fun powers _ => powers.push (powers.getD (powers.size - 1) 1 * b))
    (g₂ := fun powers _ => powers.push (powers.getD (powers.size - 1) 1 * f b))
    (by intro xs i; simp only [Array.map_push, Array.size_map, hm, ← h1, getD_map])
  simpa only [Array.map_singleton, h1] using h.symm

include hz ha in
omit [DecidableEq E] [One E] [Sub E] [Mul E]
  [DecidableEq F] [One F] [Sub F] [Mul F] in
private theorem sum_map (xs : Array Nat) (g : Nat → E) :
    f (xs.foldl (fun acc i => acc + g i) 0) =
      xs.foldl (fun acc i => acc + f (g i)) 0 := by
  have h := Array.foldl_hom f (xs := xs) (init := 0)
    (g₁ := fun acc i => acc + g i) (g₂ := fun acc i => acc + f (g i))
    (by intro acc i; exact (ha acc (g i)).symm)
  simpa only [(hz (0 : E)).mpr rfl] using h.symm

include ha hs hm in
omit [One E] [One F] in
private theorem active_map (d m n : Nat) (powers : Array E) (p q : DensePoly E) :
    ((Array.range d).foldl
      (fun active i =>
        let first := i - m
        let correction := (Array.range (i - first)).foldl
          (fun acc offset =>
            let j := first + offset
            acc + active.getD j 0 * powers.getD (i - 1 - j) 0 * q.coeff (m + j - i)) 0
        active.push (powers.getD i 0 * p.coeff (n - i) - correction)) #[]).map f =
    (Array.range d).foldl
      (fun active i =>
        let first := i - m
        let correction := (Array.range (i - first)).foldl
          (fun acc offset =>
            let j := first + offset
            acc + active.getD j 0 * (powers.map f).getD (i - 1 - j) 0 *
              (map f hz q).coeff (m + j - i)) 0
        active.push ((powers.map f).getD i 0 * (map f hz p).coeff (n - i) - correction)) #[] := by
  symm
  change _ = _
  rw [← (Array.map_empty (f := f))]
  apply Array.foldl_hom (fun xs : Array E => xs.map f)
  intro xs i
  simp only [Array.map_push, hs, hm, map_coeff, sum_map f hz ha, getD_zero_map f hz]

include hz hm in
omit [DecidableEq E] [One E] [Add E] [Sub E]
  [DecidableEq F] [One F] [Add F] [Sub F] in
private theorem quotient_map (d : Nat) (active powers : Array E) :
    ((Array.range d).foldl (fun coeffs k =>
      coeffs.push (active.getD (d - 1 - k) 0 * powers.getD k 0)) #[]).map f =
    (Array.range d).foldl (fun coeffs k =>
      coeffs.push ((active.map f).getD (d - 1 - k) 0 * (powers.map f).getD k 0)) #[] := by
  symm
  rw [← (Array.map_empty (f := f))]
  apply Array.foldl_hom (fun xs : Array E => xs.map f)
  intro xs k
  simp only [Array.map_push, hm, getD_zero_map f hz]

include ha hs hm in
omit [One E] [One F] in
private theorem remainder_map (d m : Nat) (powers quotient : Array E) (p q : DensePoly E) :
    ((Array.range m).foldl (fun coeffs t =>
      let correction := (Array.range (min (t + 1) d)).foldl
        (fun acc k => acc + quotient.getD k 0 * q.coeff (t - k)) 0
      coeffs.push (powers.getD d 0 * p.coeff t - correction)) #[]).map f =
    (Array.range m).foldl (fun coeffs t =>
      let correction := (Array.range (min (t + 1) d)).foldl
        (fun acc k => acc + (quotient.map f).getD k 0 * (map f hz q).coeff (t - k)) 0
      coeffs.push ((powers.map f).getD d 0 * (map f hz p).coeff t - correction)) #[] := by
  symm
  rw [← (Array.map_empty (f := f))]
  apply Array.foldl_hom (fun xs : Array E => xs.map f)
  intro xs t
  simp only [Array.map_push, hs, hm, map_coeff, sum_map f hz ha, getD_zero_map f hz]

include h1 ha hs hm in
set_option maxHeartbeats 800000 in
/-- Interpretation commutes with every fold in fraction-free pseudo-division,
including the fixed leading-coefficient scaling after a defective degree drop. -/
theorem map_pseudoDivMod (p q : DensePoly E) :
    (map f hz (pseudoDivMod p q).1, map f hz (pseudoDivMod p q).2) =
      pseudoDivMod (map f hz p) (map f hz q) := by
  simp only [pseudoDivMod, map_isZero, map_size, map_leading]
  split
  · simp only [map_zero_poly]
  · split
    · simp only [map_zero_poly]
    · simp only [map_ofCoeffs, quotient_map f hz hm, remainder_map f hz ha hs hm,
        active_map f hz ha hs hm, powers_map f h1 hm]

include h1 hm in
omit [Zero E] [DecidableEq E] [Add E] [Sub E]
  [Zero F] [DecidableEq F] [Add F] [Sub F] in
private theorem map_npowRec (a : E) (n : Nat) :
    f (npowRec n a) = npowRec n (f a) := by
  induction n with
  | zero => exact h1
  | succ n ih => simp only [npowRec, hm, ih]

omit [One E] [Add E] [Sub E] [Mul E] [One F] [Add F] [Sub F] [Mul F] in
@[simp] theorem map_pseudoExponent (p q : DensePoly E) :
    pseudoExponent (map f hz p) (map f hz q) = pseudoExponent p q := by
  simp only [pseudoExponent, map_isZero, map_size]

include h1 ha hs hm in
/-- The interpretation preserves the recorded multiplier and both outputs. -/
theorem map_pseudoDiv (p q : DensePoly E) :
    ({ multiplier := f (pseudoDiv p q).multiplier,
       quotient := map f hz (pseudoDiv p q).quotient,
       remainder := map f hz (pseudoDiv p q).remainder } : PseudoResult F) =
      pseudoDiv (map f hz p) (map f hz q) := by
  have hq := congrArg Prod.fst (map_pseudoDivMod f hz h1 ha hs hm p q)
  have hr := congrArg Prod.snd (map_pseudoDivMod f hz h1 ha hs hm p q)
  dsimp only at hq hr
  simp only [pseudoDiv, map_pseudoExponent, map_leading, map_npowRec f h1 hm, hq, hr]

include h1 ha hs hm in
/-- Positive sign correction preserves the multiplier, quotient and remainder together. -/
theorem map_positivePseudoDiv [Neg E] [Neg F]
    (hn : ∀ a, f (-a) = -f a) (signE : E → Int) (signF : F → Int)
    (hsign : ∀ a, signF (f a) = signE a) (p q : DensePoly E) :
    ({ multiplier := f (positivePseudoDiv signE p q).multiplier,
       quotient := map f hz (positivePseudoDiv signE p q).quotient,
       remainder := map f hz (positivePseudoDiv signE p q).remainder } : PseudoResult F) =
      positivePseudoDiv signF (map f hz p) (map f hz q) := by
  simp only [positivePseudoDiv, ← map_pseudoDiv f hz h1 ha hs hm p q, hsign]
  split
  · simp only [hn, map_neg f hz hs]
  · rfl

include h1 ha hs hm in
/-- The fraction-free gcd follows the same strictly descending remainder sequence. -/
theorem map_pseudoGcd (p q : DensePoly E) :
    map f hz (pseudoGcd p q) = pseudoGcd (map f hz p) (map f hz q) := by
  induction n : q.size using Nat.strongRecOn generalizing p q with
  | ind n ih =>
    by_cases hq : q = 0
    · subst q
      simp only [pseudoGcd_zero_right, map_zero_poly]
    · rw [pseudoGcd_step p q hq,
        pseudoGcd_step (map f hz p) (map f hz q) (fun h => hq ((map_eq_zero f hz q).mp h))]
      have hr := congrArg Prod.snd (map_pseudoDivMod f hz h1 ha hs hm p q)
      dsimp only at hr
      rw [← hr]
      apply ih (pseudoDivMod p q).2.size
      · simpa only [← n] using pseudoDivMod_remainder_lt p q hq
      · rfl

end Hex.DensePoly.Interpret
