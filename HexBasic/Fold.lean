/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Std

public section

/-!
General `List.foldl` algebra shared across the Mathlib-free `hex` libraries.

The computational libraries repeatedly fold an accumulator with a single
operation, `xs.foldl (fun acc x => acc + f x) z` or its multiplicative twin.
Lean core already proves the underlying facts — `List.foldl_assoc`,
`List.sum_eq_foldl`, `List.foldl_map` — but those need `Std.Associative` /
`Std.LawfulIdentity` instances on the carrier, which a bare
`Lean.Grind.Semiring` does not carry. This module supplies those four
instances **file-locally** (just enough to prove the lemmas below) and then
states the fold-algebra the libraries actually use.

The lemmas live in the `List` namespace and follow the standard-library
naming: name the operation, not the use site (`foldl_add_*`, `foldl_mul_*`),
mirror `List.foldl_assoc`/`List.foldl_map`, and keep `foldl_add_eq_add_foldl`
symmetric with `foldl_mul_eq_mul_foldl`. The one exception is
`foldl_const_step`: core/Mathlib already use `List.foldl_const` for the
unrelated iterate lemma, so reusing that name here would collide in the
Mathlib bridge layers (which import both this module and Mathlib). These are
candidates to migrate up to lean4; the Grind `Std` instances in particular
belong with the Grind algebra hierarchy.
-/

namespace List

universe u v w

variable {α : Type v} {β : Type w} {R : Type u}

/-!
The `Std.Associative` / `Std.LawfulIdentity` instances that `List.foldl_assoc`
and friends need are kept **file-local**: they are used only to prove the
lemmas below, which state their conclusions over `Lean.Grind.Ring` / `CommRing`
without exposing the instances. Keeping them local avoids adding a second
global `Std.Associative` resolution path for every `Grind.Semiring` (e.g.
`Nat`/`Int` in the Mathlib bridge layers, where Mathlib already supplies its
own). Promote / upstream them separately if a consumer ever needs them.
-/

/-- Addition in a `Grind.Semiring` is an associative operation. -/
local instance {R : Type u} [Lean.Grind.Semiring R] : Std.Associative (· + · : R → R → R) :=
  ⟨Lean.Grind.Semiring.add_assoc⟩

/-- Multiplication in a `Grind.Semiring` is an associative operation. -/
local instance {R : Type u} [Lean.Grind.Semiring R] : Std.Associative (· * · : R → R → R) :=
  ⟨Lean.Grind.Semiring.mul_assoc⟩

/-- `0` is a two-sided identity for addition in a `Grind.Semiring`. -/
local instance {R : Type u} [Lean.Grind.Semiring R] : Std.LawfulIdentity (· + · : R → R → R) 0 where
  left_id a := (Lean.Grind.Semiring.add_comm 0 a).trans (Lean.Grind.Semiring.add_zero a)
  right_id := Lean.Grind.Semiring.add_zero

/-- `1` is a two-sided identity for multiplication in a `Grind.Semiring`. -/
local instance {R : Type u} [Lean.Grind.Semiring R] : Std.LawfulIdentity (· * · : R → R → R) 1 where
  left_id := Lean.Grind.Semiring.one_mul
  right_id := Lean.Grind.Semiring.mul_one

/-! ### Congruence -/

/-- Two folds over `xs` agree when their step functions agree pointwise on the
elements of `xs` (for every accumulator). The fully general fold congruence. -/
theorem foldl_congr (xs : List α) (f g : β → α → β) (z : β)
    (h : ∀ acc x, x ∈ xs → f acc x = g acc x) :
    xs.foldl f z = xs.foldl g z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [h z x (List.mem_cons_self ..)]
    exact ih _ fun acc y hy => h acc y (List.mem_cons_of_mem _ hy)

/-- Congruence for an additive fold-sum under its summand `f`. -/
theorem foldl_add_congr [Add R] (xs : List α) (f g : α → R) (z : R)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc + f x) z = xs.foldl (fun acc x => acc + g x) z :=
  foldl_congr xs _ _ z fun acc x hx => by rw [h x hx]

/-- Congruence for a multiplicative fold-product under its factor `f`. -/
theorem foldl_mul_congr [Mul R] (xs : List α) (f g : α → R) (z : R)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc * f x) z = xs.foldl (fun acc x => acc * g x) z :=
  foldl_congr xs _ _ z fun acc x hx => by rw [h x hx]

/-! ### Constant step -/

/-- Folding with a step that discards the element and returns the accumulator
unchanged yields the initial accumulator. (Core's `List.foldl_const` is the
unrelated iterate lemma, hence the name.) -/
theorem foldl_const_step (xs : List α) (z : β) :
    xs.foldl (fun acc _ => acc) z = z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; exact ih z

/-! ### Permutation invariance -/

/-- An additive fold-sum is invariant under permuting the list. -/
theorem foldl_add_perm [Lean.Grind.Ring R] (f : α → R) {xs ys : List α}
    (h : xs.Perm ys) (z : R) :
    xs.foldl (fun acc x => acc + f x) z = ys.foldl (fun acc x => acc + f x) z := by
  induction h generalizing z with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldl_cons]; exact ih (z + _)
  | swap x y xs => simp only [List.foldl_cons]; congr 1; grind
  | trans _ _ ih₁ ih₂ => exact (ih₁ z).trans (ih₂ z)

/-- A multiplicative fold-product is invariant under permuting the list. -/
theorem foldl_mul_perm [Lean.Grind.CommRing R] (f : α → R) {xs ys : List α}
    (h : xs.Perm ys) (z : R) :
    xs.foldl (fun acc x => acc * f x) z = ys.foldl (fun acc x => acc * f x) z := by
  induction h generalizing z with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldl_cons]; exact ih (z * _)
  | swap x y xs => simp only [List.foldl_cons]; congr 1; grind
  | trans _ _ ih₁ ih₂ => exact (ih₁ z).trans (ih₂ z)

section Ring

variable [Lean.Grind.Ring R]

/-! ### Accumulator extraction -/

/-- Pull the running accumulator out of an additive fold-sum, taking the sum
from a `0` start. The additive twin of `foldl_mul_eq_mul_foldl`. -/
theorem foldl_add_eq_add_foldl (xs : List α) (f : α → R) (z : R) :
    xs.foldl (fun acc x => acc + f x) z
      = z + xs.foldl (fun acc x => acc + f x) 0 :=
  calc xs.foldl (fun acc x => acc + f x) z
      = (xs.map f).foldl (· + ·) z :=
        (List.foldl_map (l := xs) (f := f) (g := (· + ·)) (init := z)).symm
    _ = (xs.map f).foldl (· + ·) (z + 0) := by rw [Lean.Grind.Semiring.add_zero]
    _ = z + (xs.map f).foldl (· + ·) 0 := List.foldl_assoc
    _ = z + xs.foldl (fun acc x => acc + f x) 0 := by
        rw [List.foldl_map (l := xs) (f := f) (g := (· + ·)) (init := 0)]

/-- Pull the running accumulator out of a multiplicative fold-product, taking
the product from a `1` start. -/
theorem foldl_mul_eq_mul_foldl (xs : List α) (f : α → R) (z : R) :
    xs.foldl (fun acc x => acc * f x) z
      = z * xs.foldl (fun acc x => acc * f x) 1 :=
  calc xs.foldl (fun acc x => acc * f x) z
      = (xs.map f).foldl (· * ·) z :=
        (List.foldl_map (l := xs) (f := f) (g := (· * ·)) (init := z)).symm
    _ = (xs.map f).foldl (· * ·) (z * 1) := by rw [Lean.Grind.Semiring.mul_one]
    _ = z * (xs.map f).foldl (· * ·) 1 := List.foldl_assoc
    _ = z * xs.foldl (fun acc x => acc * f x) 1 := by
        rw [List.foldl_map (l := xs) (f := f) (g := (· * ·)) (init := 1)]

/-! ### All-zero collapse -/

/-- An additive fold-sum whose every summand vanishes on `xs` returns the
initial accumulator. -/
theorem foldl_add_eq_self (xs : List α) (f : α → R) (z : R)
    (h : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) z = z := by
  rw [foldl_add_congr xs f (fun _ => 0) z h]
  simp only [Lean.Grind.Semiring.add_zero]
  exact foldl_const_step xs z

/-- An additive fold-sum whose body adds a literal `0` returns the initial
accumulator. -/
theorem foldl_add_zero (xs : List α) (z : R) :
    xs.foldl (fun acc _ => acc + 0) z = z :=
  foldl_add_eq_self xs (fun _ => 0) z fun _ _ => rfl

/-! ### Scalar factoring -/

/-- Factor a left scalar out of an additive fold-sum. -/
theorem foldl_add_mul_left (xs : List α) (c : R) (f : α → R) (z : R) :
    xs.foldl (fun acc x => acc + c * f x) (c * z) =
      c * xs.foldl (fun acc x => acc + f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [← show c * (z + f x) = c * z + c * f x by grind]
    exact ih (z + f x)

/-- Factor a left scalar out of an additive fold-sum started from `0`. -/
theorem foldl_add_mul_left_zero (xs : List α) (c : R) (f : α → R) :
    xs.foldl (fun acc x => acc + c * f x) 0 =
      c * xs.foldl (fun acc x => acc + f x) 0 := by
  have hzero : c * 0 = 0 := by grind
  simpa [hzero] using foldl_add_mul_left xs c f 0

/-! ### Additivity -/

/-- An additive fold-sum of a pointwise sum splits into two folds, distributing
the starting accumulator. -/
theorem foldl_add_add_start (xs : List α) (f g : α → R) (a b : R) :
    xs.foldl (fun acc x => acc + (f x + g x)) (a + b) =
      xs.foldl (fun acc x => acc + f x) a + xs.foldl (fun acc x => acc + g x) b := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    calc xs.foldl (fun acc x => acc + (f x + g x)) (a + b + (f x + g x))
        = xs.foldl (fun acc x => acc + (f x + g x)) ((a + f x) + (b + g x)) := by
          congr 1; grind
      _ = xs.foldl (fun acc x => acc + f x) (a + f x)
            + xs.foldl (fun acc x => acc + g x) (b + g x) := ih (a + f x) (b + g x)

/-- An additive fold-sum of a pointwise sum from `0` splits into the sum of the
two separate folds from `0`. -/
theorem foldl_add_add (xs : List α) (f g : α → R) :
    xs.foldl (fun acc x => acc + (f x + g x)) 0 =
      xs.foldl (fun acc x => acc + f x) 0 + xs.foldl (fun acc x => acc + g x) 0 := by
  calc xs.foldl (fun acc x => acc + (f x + g x)) 0
      = xs.foldl (fun acc x => acc + (f x + g x)) ((0 : R) + 0) := by congr 1; grind
    _ = xs.foldl (fun acc x => acc + f x) 0 + xs.foldl (fun acc x => acc + g x) 0 :=
        foldl_add_add_start xs f g 0 0

/-! ### Fubini -/

/-- Sum-swap (Fubini) for nested additive fold-sums. -/
theorem foldl_add_comm {γ : Type w} (xs : List α) (ys : List γ) (f : α → γ → R) :
    xs.foldl (fun acc x => acc + ys.foldl (fun acc' y => acc' + f x y) 0) 0 =
      ys.foldl (fun acc y => acc + xs.foldl (fun acc' x => acc' + f x y) 0) 0 := by
  induction xs with
  | nil =>
    simp only [List.foldl_nil]
    exact (foldl_add_zero ys 0).symm
  | cons x xs ih =>
    have hLHS :
        (x :: xs).foldl
            (fun acc x' => acc + ys.foldl (fun acc' y => acc' + f x' y) 0) 0 =
          ys.foldl (fun acc' y => acc' + f x y) 0 +
            xs.foldl
              (fun acc x' => acc + ys.foldl (fun acc' y => acc' + f x' y) 0) 0 := by
      simp only [List.foldl_cons]
      rw [foldl_add_eq_add_foldl xs
            (fun x' => ys.foldl (fun acc' y => acc' + f x' y) 0)
            (0 + ys.foldl (fun acc' y => acc' + f x y) 0)]
      grind
    have hRHS :
        ys.foldl
            (fun acc y => acc + (x :: xs).foldl
              (fun acc' x' => acc' + f x' y) 0) 0 =
          ys.foldl (fun acc' y => acc' + f x y) 0 +
            ys.foldl
              (fun acc y => acc + xs.foldl
                (fun acc' x' => acc' + f x' y) 0) 0 := by
      have hfun :
          (fun (acc : R) y =>
              acc + (x :: xs).foldl (fun acc' x' => acc' + f x' y) 0) =
            (fun (acc : R) y =>
              acc + (f x y + xs.foldl (fun acc' x' => acc' + f x' y) 0)) := by
        funext acc y
        congr 1
        simp only [List.foldl_cons]
        rw [foldl_add_eq_add_foldl xs (fun x' => f x' y) (0 + f x y)]
        grind
      rw [hfun]
      exact foldl_add_add ys (fun y => f x y)
        (fun y => xs.foldl (fun acc' x' => acc' + f x' y) 0)
    rw [hLHS, hRHS, ih]

end Ring

section CommRing

variable [Lean.Grind.CommRing R]

/-- Factor a right scalar out of an additive fold-sum started from `0`. -/
theorem foldl_add_mul_right_zero (xs : List α) (f : α → R) (c : R) :
    xs.foldl (fun acc x => acc + f x * c) 0 =
      xs.foldl (fun acc x => acc + f x) 0 * c := by
  calc xs.foldl (fun acc x => acc + f x * c) 0
      = xs.foldl (fun acc x => acc + c * f x) 0 := by
        apply foldl_add_congr; intro x _; grind
    _ = c * xs.foldl (fun acc x => acc + f x) 0 := foldl_add_mul_left_zero xs c f
    _ = xs.foldl (fun acc x => acc + f x) 0 * c := by grind

end CommRing

/-! ### flatMap -/

/-- An additive fold-sum over `xs.flatMap f` equals the fold over `xs` whose
body folds each sublist `f x` into the accumulator. -/
theorem foldl_add_flatMap [Add R] {γ : Type w}
    (xs : List α) (f : α → List γ) (g : γ → R) (z : R) :
    (xs.flatMap f).foldl (fun acc x => acc + g x) z =
      xs.foldl (fun acc x => (f x).foldl (fun acc y => acc + g y) acc) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons]
    exact ih ((f x).foldl (fun acc y => acc + g y) z)

/-! ### Indicator pickout -/

/-- An additive fold-sum over a `Nodup` list whose summand is supported at a
single matching element collects exactly that summand. -/
theorem foldl_add_single [Lean.Grind.CommRing R] [DecidableEq α]
    (xs : List α) (z : R) (q : α) (f : α → R)
    (hmem : q ∈ xs) (hnodup : xs.Nodup) :
    xs.foldl (fun acc x => acc + (if x = q then f x else 0)) z = z + f q := by
  induction xs generalizing z with
  | nil => simp at hmem
  | cons x xs ih =>
    simp only [List.foldl_cons]
    by_cases hxq : x = q
    · subst hxq
      rw [if_pos rfl]
      have hxs_nomem : x ∉ xs := (List.nodup_cons.mp hnodup).1
      apply foldl_add_eq_self xs (fun y => if y = x then f y else 0) (z + f x)
      intro y hy
      have hyne : y ≠ x := fun heq => hxs_nomem (heq ▸ hy)
      exact if_neg hyne
    · rw [if_neg hxq]
      have hzero_step : z + (0 : R) = z := by grind
      rw [hzero_step]
      have hmem' : q ∈ xs := by
        cases List.mem_cons.mp hmem with
        | inl h => exact absurd h.symm hxq
        | inr h => exact h
      exact ih z hmem' (List.nodup_cons.mp hnodup).2

/-! ### Monotone bounds (`Nat`) -/

/-- An additive fold-sum over `Nat` is at least its starting accumulator. -/
theorem le_foldl_add_self (xs : List α) (g : α → Nat) (init : Nat) :
    init ≤ xs.foldl (fun acc x => acc + g x) init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (Nat.le_add_right _ _) (ih (init + g x))

/-- Every summand is bounded by an additive fold-sum over `Nat` that contains it. -/
theorem le_foldl_add_of_mem (xs : List α) (g : α → Nat) {x : α} {init : Nat}
    (hx : x ∈ xs) : g x ≤ xs.foldl (fun acc y => acc + g y) init := by
  induction xs generalizing init with
  | nil => simp at hx
  | cons y xs ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hx with
    | inl h => subst h; exact Nat.le_trans (Nat.le_add_left _ _) (le_foldl_add_self xs g _)
    | inr h => exact ih h

/-- A `Nat` fold-max is at least its starting accumulator. -/
theorem le_foldl_max_self (xs : List α) (g : α → Nat) (init : Nat) :
    init ≤ xs.foldl (fun acc x => max acc (g x)) init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih (max init (g x)))

/-- Every element's value is bounded by a `Nat` fold-max that contains it. -/
theorem le_foldl_max_of_mem (xs : List α) (g : α → Nat) {x : α} {init : Nat}
    (hx : x ∈ xs) : g x ≤ xs.foldl (fun acc y => max acc (g y)) init := by
  induction xs generalizing init with
  | nil => simp at hx
  | cons y xs ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hx with
    | inl h => subst h; exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_max_self xs g _)
    | inr h => exact ih h

end List
