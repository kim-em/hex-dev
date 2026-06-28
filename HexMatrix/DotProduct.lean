/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Basic
public import Batteries.Data.List.Lemmas

public section

/-!
Algebraic properties of dense vector dot products.
-/

namespace Hex

universe u v

namespace Vector

/-- Two fold-sums agree when their summand functions agree pointwise on the index list. -/
private theorem foldl_sum_congr_aux {R : Type u} [Add R]
    {α : Type v} (xs : List α) (f g : α → R) (acc : R)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc + f x) acc =
      xs.foldl (fun acc x => acc + g x) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = g x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = g y := fun y hy => h y (List.mem_cons_of_mem _ hy)
      rw [hx]
      exact ih (acc + g x) hxs

/-- Left multiplication by `c` distributes through a fold-sum. -/
private theorem foldl_sum_mul_left_aux {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f : α → R) (c acc : R) :
    c * xs.foldl (fun acc x => acc + f x) acc =
    xs.foldl (fun acc x => acc + c * f x) (c * acc) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc := acc + f x)]
      have hdist : c * (acc + f x) = c * acc + c * f x := by
        grind
      rw [hdist]

/-- The fold-sum of a pointwise sum splits into the sum of fold-sums. -/
private theorem foldl_sum_add_aux {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f g : α → R) (acc accF accG : R)
    (h : acc = accF + accG) :
    xs.foldl (fun acc x => acc + (f x + g x)) acc =
    xs.foldl (fun acc x => acc + f x) accF +
    xs.foldl (fun acc x => acc + g x) accG := by
  induction xs generalizing acc accF accG with
  | nil =>
      simp only [List.foldl_nil]
      exact h
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih (acc := acc + (f x + g x)) (accF := accF + f x) (accG := accG + g x)
      rw [h]
      grind

/-- Dot product is additive in its left argument. -/
theorem dotProduct_add_left {R : Type u} [Lean.Grind.Ring R]
    (u v w : Vector R n) :
    dotProduct (u + v) w = dotProduct u w + dotProduct v w := by
  unfold dotProduct
  rw [show (List.finRange n).foldl
        (fun acc i => acc + (u + v)[i] * w[i]) 0 =
      (List.finRange n).foldl
        (fun acc i => acc + (u[i] * w[i] + v[i] * w[i])) 0 from ?_]
  · rw [foldl_sum_add_aux (xs := List.finRange n)
        (f := fun i => u[i] * w[i])
        (g := fun i => v[i] * w[i])
        (acc := 0) (accF := 0) (accG := 0) (h := by grind)]
  · apply foldl_sum_congr_aux
    intro i _
    have hentry : (u + v)[i] = u[i] + v[i] := by
      change (u + v)[i.val] = u[i.val] + v[i.val]
      rw [Vector.getElem_add]
    rw [hentry]
    grind

/-- Dot product is homogeneous in a pointwise left scalar multiple. -/
theorem dotProduct_mul_left {R : Type u} [Lean.Grind.Ring R]
    (c : R) (u w : Vector R n) :
    dotProduct (Vector.ofFn fun i => c * u[i]) w = c * dotProduct u w := by
  unfold dotProduct
  rw [foldl_sum_mul_left_aux (xs := List.finRange n)
        (f := fun i => u[i] * w[i]) (c := c) (acc := 0)]
  have hzero : c * (0 : R) = 0 := by
    grind
  rw [hzero]
  apply foldl_sum_congr_aux
  intro i _
  have hentry : (Vector.ofFn (fun i : Fin n => c * u[i]))[i] = c * u[i] := by
    simp
  rw [hentry]
  exact Lean.Grind.Semiring.mul_assoc c u[i] w[i]

/-- Dot product is symmetric over a commutative coefficient type. -/
theorem dotProduct_comm {R : Type u} [Lean.Grind.CommRing R]
    (u v : Vector R n) :
    dotProduct u v = dotProduct v u := by
  unfold dotProduct
  apply foldl_sum_congr_aux
  intro i _
  grind

/-- Dot product is additive in its right argument. -/
theorem dotProduct_add_right {R : Type u} [Lean.Grind.CommRing R]
    (u v w : Vector R n) :
    dotProduct u (v + w) = dotProduct u v + dotProduct u w := by
  rw [dotProduct_comm u (v + w)]
  rw [dotProduct_add_left]
  rw [dotProduct_comm v u, dotProduct_comm w u]

/-- Dot product is homogeneous in a pointwise right scalar multiple. -/
theorem dotProduct_mul_right {R : Type u} [Lean.Grind.CommRing R]
    (c : R) (u v : Vector R n) :
    dotProduct u (Vector.ofFn fun i => c * v[i]) = c * dotProduct u v := by
  rw [dotProduct_comm u (Vector.ofFn fun i => c * v[i])]
  rw [dotProduct_mul_left]
  rw [dotProduct_comm v u]

/-- Dot product is homogeneous in its left argument. -/
theorem dotProduct_smul_left {R : Type u} [Lean.Grind.Ring R]
    (c : R) (u w : Vector R n) :
    dotProduct (c • u) w = c * dotProduct u w := by
  rw [show c • u = Vector.ofFn (fun i : Fin n => c * u[i]) by
    ext i hi
    let ii : Fin n := ⟨i, hi⟩
    show (c • u)[ii] = (Vector.ofFn (fun i : Fin n => c * u[i]))[ii]
    change (c • u)[i] = (Vector.ofFn (fun i : Fin n => c * u[i]))[i]
    rw [Vector.getElem_smul]
    change c * u[i] = (Vector.ofFn (fun i : Fin n => c * u[i]))[i]
    simp]
  exact dotProduct_mul_left c u w

/-- Dot product is homogeneous in its right argument. -/
theorem dotProduct_smul_right {R : Type u} [Lean.Grind.CommRing R]
    (c : R) (u v : Vector R n) :
    dotProduct u (c • v) = c * dotProduct u v := by
  rw [dotProduct_comm u (c • v)]
  rw [dotProduct_smul_left]
  rw [dotProduct_comm v u]

/-- Dot product is additive over subtraction in its left argument. -/
theorem dotProduct_sub_left {R : Type u} [Lean.Grind.Ring R]
    (u v w : Vector R n) :
    dotProduct (u - v) w = dotProduct u w - dotProduct v w := by
  rw [show u - v = u + (-1 : R) • v by
    ext i hi
    let ii : Fin n := ⟨i, hi⟩
    show (u - v)[ii] = (u + (-1 : R) • v)[ii]
    change (u - v)[i] = (u + (-1 : R) • v)[i]
    rw [Vector.getElem_sub, Vector.getElem_add, Vector.getElem_smul]
    change u[i] - v[i] = u[i] + (-1 : R) * v[i]
    grind]
  rw [dotProduct_add_left, dotProduct_smul_left]
  change dotProduct u w + (-1 : R) * dotProduct v w =
    dotProduct u w - dotProduct v w
  grind

/-- Dot product is additive over subtraction in its right argument. -/
theorem dotProduct_sub_right {R : Type u} [Lean.Grind.CommRing R]
    (u v w : Vector R n) :
    dotProduct u (v - w) = dotProduct u v - dotProduct u w := by
  rw [dotProduct_comm u (v - w)]
  rw [dotProduct_sub_left]
  rw [dotProduct_comm v u, dotProduct_comm w u]

/-- Dot product distributes over subtracting a scalar multiple in the left argument. -/
theorem dotProduct_sub_smul_left {R : Type u} [Lean.Grind.Ring R]
    (u v w : Vector R n) (c : R) :
    dotProduct (u - c • v) w = dotProduct u w - c * dotProduct v w := by
  rw [dotProduct_sub_left, dotProduct_smul_left]

/-- Dot product distributes over subtracting a scalar multiple in the right argument. -/
theorem dotProduct_sub_smul_right {R : Type u} [Lean.Grind.CommRing R]
    (u v w : Vector R n) (c : R) :
    dotProduct u (v - c • w) = dotProduct u v - c * dotProduct u w := by
  rw [dotProduct_sub_right, dotProduct_smul_right]

end Vector

end Hex
