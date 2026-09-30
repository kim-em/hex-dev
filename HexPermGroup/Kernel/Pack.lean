/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Perm
public import HexBasic.Kernel

public section

/-!
Packed permutations for kernel certificates.

A permutation of `Fin n` is stored as one natural number with `W` bits per
image: image `i` occupies bits `[i*W, (i+1)*W)`. The width `W = width n` is the
least positive number with `n < 2^W`, so a field holds every value in `0..n`.
Every function here that the kernel evaluates is spelled with the raw `Nat`
functions and loops through one `Nat.rec` step per image.
-/

namespace Hex.PermGroup.Kernel

open Hex.Kernel

/-- The field width for degree `n`: the least `W ≥ 1` with `n < 2^W`. It is
computed by `n` doubling steps rather than `Nat.log2`, which the kernel
reduces through well-founded recursion. -/
@[expose] def width (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1
    (fun _ w => cond (Nat.ble (Nat.shiftLeft 1 w) n) (Nat.succ w) w) n

/-- `2^W - 1`, the mask of one field. -/
@[expose] def mask (W : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 W) 1

/-- Field `i` of `x`. -/
@[expose] def field (W x i : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul i W)) (mask W)

/-- The number whose field `i` is `f i` for `i < k`, with no higher bits,
assuming every `f i` is below `2^W`. -/
@[expose] def packFn (W : Nat) (f : Nat → Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.add acc (Nat.shiftLeft (f i) (Nat.mul i W))) k

/-- Composition `(x * y)(i) = x(y(i))` of packed permutations of degree `n`. -/
@[expose] def comp (n W x y : Nat) : Nat :=
  packFn W (fun i => field W x (field W y i)) n

/-- The packed identity of degree `n`. -/
@[expose] def ident (n W : Nat) : Nat := packFn W (fun i => i) n

/-- The packing of a permutation of `Fin n`, with the width `width n`. -/
@[expose] def pack (p : Perm n) : Nat :=
  packFn (width n) (fun i => if h : i < n then (p.get ⟨i, h⟩).val else 0) n

/-! # Arithmetic facts -/

theorem one_le_width_go (n : Nat) : ∀ k, 1 ≤
    Nat.rec (motive := fun _ => Nat) 1
      (fun _ w => cond (Nat.ble (Nat.shiftLeft 1 w) n) (Nat.succ w) w) k
  | 0 => Nat.le_refl 1
  | k + 1 => by
    have ih := one_le_width_go n k
    show 1 ≤ cond _ _ _
    generalize Nat.rec (motive := fun _ => Nat) 1
      (fun _ w => cond (Nat.ble (Nat.shiftLeft 1 w) n) (Nat.succ w) w) k = w at ih ⊢
    cases Nat.ble (Nat.shiftLeft 1 w) n <;> simp <;> omega

theorem one_le_width (n : Nat) : 1 ≤ width n := one_le_width_go n n

/-- After `k` steps the width is either `k + 1` or already large enough. -/
theorem width_go_spec (n : Nat) : ∀ k,
    let w := Nat.rec (motive := fun _ => Nat) 1
      (fun _ w => cond (Nat.ble (Nat.shiftLeft 1 w) n) (Nat.succ w) w) k
    n < 2 ^ w ∨ w = k + 1
  | 0 => Or.inr rfl
  | k + 1 => by
    have ih := width_go_spec n k
    simp only at ih ⊢
    generalize Nat.rec (motive := fun _ => Nat) 1
      (fun _ w => cond (Nat.ble (Nat.shiftLeft 1 w) n) (Nat.succ w) w) k = w at ih ⊢
    rw [Hex.Kernel.ble_eq_decide, Hex.Kernel.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul]
    by_cases hb : 2 ^ w ≤ n
    · simp only [hb, decide_true, Bool.cond_true]
      rcases ih with ih | ih
      · omega
      · right; omega
    · simp only [hb, decide_false, Bool.cond_false]
      left; omega

theorem lt_two_pow_width (n : Nat) : n < 2 ^ width n := by
  rcases width_go_spec n n with h | h
  · exact h
  · rw [width, h]
    exact Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by omega) (by omega))

theorem mask_eq (W : Nat) : mask W = 2 ^ W - 1 := by
  simp [mask, Nat.shiftLeft_eq]

theorem field_eq (W x i : Nat) : field W x i = x / 2 ^ (i * W) % 2 ^ W := by
  simp only [field, mask_eq, Hex.Kernel.land_eq, Hex.Kernel.mul_eq, Hex.Kernel.shiftRight_eq,
    Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem field_lt (W x i : Nat) : field W x i < 2 ^ W := by
  rw [field_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos W)

theorem packFn_succ (W : Nat) (f : Nat → Nat) (k : Nat) :
    packFn W f (k + 1) = packFn W f k + f k * 2 ^ (k * W) := by
  simp [packFn, Nat.shiftLeft_eq]

theorem packFn_lt (W : Nat) (f : Nat → Nat) :
    ∀ k, (∀ i < k, f i < 2 ^ W) → packFn W f k < 2 ^ (k * W)
  | 0, _ => Nat.two_pow_pos _
  | k + 1, hf => by
    rw [packFn_succ, Nat.succ_mul, Nat.pow_add]
    have ih := packFn_lt W f k (fun i hi => hf i (by omega))
    have hk := hf k (by omega)
    calc packFn W f k + f k * 2 ^ (k * W)
        < 2 ^ (k * W) + f k * 2 ^ (k * W) := by omega
      _ = (f k + 1) * 2 ^ (k * W) := by rw [Nat.succ_mul, Nat.add_comm]
      _ ≤ 2 ^ W * 2 ^ (k * W) := Nat.mul_le_mul_right _ hk
      _ = 2 ^ (k * W) * 2 ^ W := Nat.mul_comm _ _

/-- Reading back a field of a packed value. -/
theorem field_packFn (W : Nat) (f : Nat → Nat) :
    ∀ k, (∀ i < k, f i < 2 ^ W) → ∀ i, i < k → field W (packFn W f k) i = f i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, hf, i, h => by
    rw [field_eq, packFn_succ]
    have hf' : ∀ i < k, f i < 2 ^ W := fun i hi => hf i (by omega)
    have hlow := packFn_lt W f k hf'
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hi | rfl
    · have := field_packFn W f k hf' i hi
      rw [field_eq] at this
      obtain ⟨d, hd⟩ : ∃ d, k * W = i * W + W + d := by
        refine ⟨k * W - (i * W + W), ?_⟩
        have : (i + 1) * W ≤ k * W := Nat.mul_le_mul_right _ hi
        rw [Nat.succ_mul] at this
        omega
      rw [hd, Nat.pow_add, Nat.pow_add, ← Nat.mul_assoc, ← Nat.mul_assoc,
        Nat.mul_comm (f k), Nat.mul_assoc (2 ^ (i * W)), Nat.mul_assoc (2 ^ (i * W)),
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
      rw [show f k * 2 ^ W * 2 ^ d = 2 ^ W * (f k * 2 ^ d) by
        rw [Nat.mul_comm (f k), Nat.mul_assoc], Nat.add_mul_mod_self_left]
      exact this
    · rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt hlow, Nat.zero_add, Nat.mod_eq_of_lt (hf _ (by omega))]

theorem field_ident {n W i : Nat} (hn : n < 2 ^ W) (hi : i < n) :
    field W (ident n W) i = i :=
  field_packFn W (fun i => i) n (fun _ h => by omega) i hi

theorem field_comp (n W x y : Nat) {i : Nat} (hi : i < n) :
    field W (comp n W x y) i = field W x (field W y i) :=
  field_packFn W _ n (fun _ _ => field_lt _ _ _) i hi

theorem field_pack (p : Perm n) (i : Fin n) :
    field (width n) (pack p) i.val = (p.get i).val := by
  rw [pack, field_packFn _ _ n (fun j hj => by
    simp only [hj, ↓reduceDIte]
    exact Nat.lt_trans (p.get _).isLt (lt_two_pow_width n)) _ i.isLt]
  simp

end Hex.PermGroup.Kernel
