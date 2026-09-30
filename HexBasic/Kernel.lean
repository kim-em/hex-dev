/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public section

/-!
Primitives for code that the kernel evaluates.

The kernel has GMP-accelerated `Nat` arithmetic and bit operations, each one
reduction step whatever the operand size, but it unfolds the typeclass
instances behind `+`, `&&&`, `==` and friends on every use, reduces structural
recursion through `Nat.brecOn`, and builds `List.range` before folding over it.
Definitions meant for kernel evaluation are therefore spelled with the raw
`Nat.add`, `Nat.land`, `Nat.beq`, ... functions and `cond`, and loop through the
`Nat.rec` drivers below. The scoped `simp` lemmas turn the raw spellings back
into the usual notation in proofs; open `Hex.Kernel` to use them.
-/

namespace Hex.Kernel

/-! # Raw operation spellings -/

@[scoped simp] theorem land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl
@[scoped simp] theorem lor_eq (a b : Nat) : Nat.lor a b = a ||| b := rfl
@[scoped simp] theorem xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
@[scoped simp] theorem shiftRight_eq (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
@[scoped simp] theorem shiftLeft_eq (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl
@[scoped simp] theorem mul_eq (a b : Nat) : Nat.mul a b = a * b := rfl
@[scoped simp] theorem add_eq (a b : Nat) : Nat.add a b = a + b := rfl
@[scoped simp] theorem sub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
@[scoped simp] theorem div_eq (a b : Nat) : Nat.div a b = a / b := rfl
@[scoped simp] theorem mod_eq (a b : Nat) : Nat.mod a b = a % b := rfl

theorem cond_beq {α : Type} (a b : Nat) (x y : α) :
    cond (Nat.beq a b) x y = if a = b then x else y := by
  rcases hb : Nat.beq a b with _ | _
  · rw [ite_eq_right (Nat.ne_of_beq_eq_false hb)]
    rfl
  · rw [ite_eq_left (Nat.eq_of_beq_eq_true hb)]
    rfl

theorem cond_blt {α : Type} (a b : Nat) (x y : α) :
    cond (Nat.blt a b) x y = if a < b then x else y := by
  rcases Decidable.em (a < b) with h | h
  · simp [h, Nat.blt_eq]
  · simp [h, Nat.blt_eq]

theorem cond_ble {α : Type} (a b : Nat) (x y : α) :
    cond (Nat.ble a b) x y = if a ≤ b then x else y := by
  rcases Decidable.em (a ≤ b) with h | h
  · simp [h, Nat.ble_eq]
  · simp [h, Nat.ble_eq]

theorem beq_eq_beq (a b : Nat) : Nat.beq a b = (a == b) := by
  rcases hb : Nat.beq a b with _ | _
  · exact (beq_eq_false_iff_ne.mpr (Nat.ne_of_beq_eq_false hb)).symm
  · exact (beq_iff_eq.mpr (Nat.eq_of_beq_eq_true hb)).symm

theorem blt_eq_decide (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rcases Decidable.em (a < b) with h | h
  · rw [decide_eq_true h]
    exact Nat.blt_eq.mpr h
  · rw [decide_eq_false h]
    rcases hb : Nat.blt a b with _ | _
    · rfl
    · exact absurd (Nat.blt_eq.mp hb) h

theorem ble_eq_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  rcases Decidable.em (a ≤ b) with h | h
  · rw [decide_eq_true h]
    exact Nat.ble_eq.mpr h
  · rw [decide_eq_false h]
    rcases hb : Nat.ble a b with _ | _
    · rfl
    · exact absurd (Nat.ble_eq.mp hb) h

theorem beq_eq_decide (a b : Nat) : Nat.beq a b = decide (a = b) := by
  rcases Decidable.em (a = b) with h | h
  · rw [decide_eq_true h]
    exact Nat.beq_eq.mpr h
  · rw [decide_eq_false h]
    rcases hb : Nat.beq a b with _ | _
    · rfl
    · exact absurd (Nat.beq_eq.mp hb) h

theorem cond_beq_true {α : Type} (a : Bool) (x y : α) :
    cond a x y = if a = true then x else y := by
  cases a <;> rfl

/-! # The loop driver

Structural recursion on a `Nat` fuel unfolds through `Nat.brecOn`,
which costs several reduction steps per iteration, and a loop written
over `List.range` makes the kernel build that list first. `iterUp` is
the ascending counted loop as one `Nat.rec` step per iteration. The
range-driven folds and maps of the replay go through it and its two
derived forms, `mapRange` and `allRange`. -/

/-- The compiled form of `iterUp`. -/
def iterUpImpl {α : Type} (k : Nat) (f : Nat → α → α) (a : α) : α :=
  go k 0 a
where
  go : Nat → Nat → α → α
    | 0, _, a => a
    | j + 1, i, a => go j (i + 1) (f i a)

/-- `iterUp k f a = f (k - 1) (… (f 0 a))`, one `Nat.rec` step per
iteration. -/
@[expose, implemented_by iterUpImpl] def iterUp {α : Type} (k : Nat)
    (f : Nat → α → α) (a : α) : α :=
  Nat.rec (motive := fun _ => α → α) (fun a => a)
    (fun i ih a => ih (f (Nat.sub (Nat.sub k 1) i) a)) k a

theorem iterUp_go {α : Type} (k : Nat) (f : Nat → α → α) :
    ∀ (j : Nat) (a : α), j ≤ k →
      Nat.rec (motive := fun _ => α → α) (fun a => a)
        (fun i ih a => ih (f (Nat.sub (Nat.sub k 1) i) a)) j a =
      (List.range' (k - j) j).foldl (fun a i => f i a) a
  | 0, _, _ => rfl
  | j + 1, a, h => by
    show Nat.rec (motive := fun _ => α → α) (fun a => a)
        (fun i ih a => ih (f (Nat.sub (Nat.sub k 1) i) a)) j
        (f (Nat.sub (Nat.sub k 1) j) a) = _
    rw [iterUp_go k f j _ (by omega), List.range'_succ, List.foldl_cons]
    have h1 : Nat.sub (Nat.sub k 1) j = k - (j + 1) := by simp only [sub_eq]; omega
    have h2 : k - j = k - (j + 1) + 1 := by omega
    rw [h1, h2]

theorem iterUp_eq_foldl {α : Type} (k : Nat) (f : Nat → α → α) (a : α) :
    iterUp k f a = (List.range k).foldl (fun a i => f i a) a := by
  rw [iterUp, iterUp_go k f k a (Nat.le_refl k), Nat.sub_self, List.range_eq_range']

/-- The compiled form of `fuelRec`. -/
def fuelRecImpl {β : Type} : Nat → β → (β → β) → β
  | 0, base, _ => base
  | k + 1, base, step => step (fuelRecImpl k base step)

/-- `fuelRec k base step = step (… (step base))`, `k` times: the
fuel-bounded recursion of a loop with an early exit as one `Nat.rec`
step per unfolding (`β` is the loop's function type). -/
@[expose, implemented_by fuelRecImpl] def fuelRec {β : Type} (k : Nat) (base : β)
    (step : β → β) : β :=
  Nat.rec (motive := fun _ => β) base (fun _ ih => step ih) k

theorem fuelRec_zero {β : Type} (base : β) (step : β → β) :
    fuelRec 0 base step = base := rfl

theorem fuelRec_succ {β : Type} (k : Nat) (base : β) (step : β → β) :
    fuelRec (k + 1) base step = step (fuelRec k base step) := rfl

/-- `(List.range k).map f`, built by the loop driver. -/
@[expose] def mapRange {α : Type} (k : Nat) (f : Nat → α) : List α :=
  (iterUp k (fun o acc => f o :: acc) []).reverse

theorem mapRange_eq {α : Type} (k : Nat) (f : Nat → α) :
    mapRange k f = (List.range k).map f := by
  rw [mapRange, iterUp_eq_foldl]
  have hfold : ∀ (l : List Nat) (acc : List α),
      l.foldl (fun acc o => f o :: acc) acc = (l.map f).reverse ++ acc := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons x xs ih => intro acc; simp [ih]
  rw [hfold]
  simp

/-- `(List.range k).all p`, by the loop driver. -/
@[expose] def allRange (k : Nat) (p : Nat → Bool) : Bool :=
  iterUp k (fun v b => b && p v) true

theorem allRange_eq (k : Nat) (p : Nat → Bool) :
    allRange k p = (List.range k).all p := by
  rw [allRange, iterUp_eq_foldl]
  have hfold : ∀ (l : List Nat) (b : Bool),
      l.foldl (fun b v => b && p v) b = (b && l.all p) := by
    intro l
    induction l with
    | nil => intro b; simp
    | cons x xs ih => intro b; rw [List.foldl_cons, ih, List.all_cons, Bool.and_assoc]
  rw [hfold, Bool.true_and]

end Hex.Kernel
