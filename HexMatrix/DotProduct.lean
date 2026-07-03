/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Basic

public section

/-!
Algebraic properties of dense vector dot products.
-/

universe u v

namespace Vector

/-- Dot product is additive in its left argument. -/
theorem dotProduct_add_left {R : Type u} [Lean.Grind.Ring R]
    (u v w : Vector R n) :
    dotProduct (u + v) w = dotProduct u w + dotProduct v w := by
  simp only [dotProduct]
  rw [show (List.finRange n).foldl
        (fun acc i => acc + (u + v)[i] * w[i]) 0 =
      (List.finRange n).foldl
        (fun acc i => acc + (u[i] * w[i] + v[i] * w[i])) 0 from ?_]
  · rw [List.foldl_add_add (xs := List.finRange n)
        (f := fun i => u[i] * w[i])
        (g := fun i => v[i] * w[i])]
  · apply List.foldl_add_congr
    intro i _
    have hentry : (u + v)[i] = u[i] + v[i] := by
      change (u + v)[i.val] = u[i.val] + v[i.val]
      rw [Vector.getElem_add]
    rw [hentry]
    grind

/-- Dot product is homogeneous in its left argument. -/
theorem dotProduct_smul_left {R : Type u} [Lean.Grind.Ring R]
    (c : R) (u w : Vector R n) :
    dotProduct (c • u) w = c * dotProduct u w := by
  simp only [dotProduct]
  rw [← List.foldl_add_mul_left (xs := List.finRange n)
        (f := fun i => u[i] * w[i]) (c := c)]
  have hzero : c * (0 : R) = 0 := by
    grind
  rw [hzero]
  apply List.foldl_add_congr
  intro i _
  -- `getElem_smul` rewrites the entry to `c • u[i]`, which is defeq to `c * u[i]`
  -- for the scalar action on the coefficient ring.
  have hentry : (c • u)[i] = c * u[i] := by
    simp only [Fin.getElem_fin, Vector.getElem_smul]; rfl
  rw [hentry]
  exact Lean.Grind.Semiring.mul_assoc c u[i] w[i]

/-- Dot product is symmetric over a commutative coefficient type. -/
theorem dotProduct_comm {R : Type u} [Lean.Grind.CommRing R]
    (u v : Vector R n) :
    dotProduct u v = dotProduct v u := by
  simp only [dotProduct]
  apply List.foldl_add_congr
  intro i _
  grind

/-- Dot product is additive in its right argument. -/
theorem dotProduct_add_right {R : Type u} [Lean.Grind.Ring R]
    (u v w : Vector R n) :
    dotProduct u (v + w) = dotProduct u v + dotProduct u w := by
  simp only [dotProduct]
  rw [show (List.finRange n).foldl
        (fun acc i => acc + u[i] * (v + w)[i]) 0 =
      (List.finRange n).foldl
        (fun acc i => acc + (u[i] * v[i] + u[i] * w[i])) 0 from ?_]
  · rw [List.foldl_add_add (xs := List.finRange n)
        (f := fun i => u[i] * v[i])
        (g := fun i => u[i] * w[i])]
  · apply List.foldl_add_congr
    intro i _
    have hentry : (v + w)[i] = v[i] + w[i] := by
      change (v + w)[i.val] = v[i.val] + w[i.val]
      rw [Vector.getElem_add]
    rw [hentry]
    grind

/-- Dot product is homogeneous in its right argument. -/
theorem dotProduct_smul_right {R : Type u} [Lean.Grind.CommRing R]
    (c : R) (u v : Vector R n) :
    dotProduct u (c • v) = c * dotProduct u v := by
  rw [dotProduct_comm u (c • v), dotProduct_smul_left, dotProduct_comm v u]

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
theorem dotProduct_sub_right {R : Type u} [Lean.Grind.Ring R]
    (u v w : Vector R n) :
    dotProduct u (v - w) = dotProduct u v - dotProduct u w := by
  simp only [dotProduct]
  rw [show (List.finRange n).foldl
        (fun acc i => acc + u[i] * (v - w)[i]) 0 =
      (List.finRange n).foldl
        (fun acc i => acc + (u[i] * v[i] - u[i] * w[i])) 0 from ?_]
  · rw [List.foldl_add_sub_zero (xs := List.finRange n)
        (f := fun i => u[i] * v[i])
        (g := fun i => u[i] * w[i])]
  · apply List.foldl_add_congr
    intro i _
    have hentry : (v - w)[i] = v[i] - w[i] := by
      change (v - w)[i.val] = v[i.val] - w[i.val]
      rw [Vector.getElem_sub]
    rw [hentry]
    grind

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
