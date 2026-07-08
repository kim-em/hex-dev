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

/-- A dot product of two `ofFn` vectors is the `List.finRange` fold of their
pointwise products. The reference `dotProduct` reduction that keeps `ofFn`-built
rows and columns visible to the fold-algebra lemmas. -/
theorem dotProduct_ofFn {R : Type u} [Mul R] [Add R] [OfNat R 0] {n : Nat}
    (f g : Fin n → R) :
    dotProduct (Vector.ofFn f) (Vector.ofFn g)
      = (List.finRange n).foldl (fun acc i => acc + f i * g i) 0 := by
  simp only [dotProduct, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

/-- Peel the final index off an additive fold over `List.finRange (n+1)`. -/
private theorem foldl_finRange_succ_last {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (F : Fin (n + 1) → R) :
    (List.finRange (n + 1)).foldl (fun acc i => acc + F i) 0
      = (List.finRange n).foldl (fun acc i => acc + F i.castSucc) 0 + F (Fin.last n) := by
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]

/-- Trailing zeros in a fold of pointwise products vanish: folding the products of
two length-`m + d` zero-extensions equals folding the length-`m` products. -/
private theorem foldl_extend_zero {R : Type u} [Lean.Grind.Ring R] (m d : Nat)
    (F G : Fin m → R) :
    (List.finRange (m + d)).foldl
        (fun acc i => acc
          + (if h : i.val < m then F ⟨i.val, h⟩ else 0)
            * (if h : i.val < m then G ⟨i.val, h⟩ else 0)) 0
      = (List.finRange m).foldl (fun acc i => acc + F i * G i) 0 := by
  induction d with
  | zero =>
    apply List.foldl_add_congr
    intro i _
    have hi : i.val < m := i.isLt
    rw [dif_pos hi, dif_pos hi]
    congr 1
  | succ d ih =>
    show (List.finRange ((m + d) + 1)).foldl
        (fun acc i => acc
          + (if h : i.val < m then F ⟨i.val, h⟩ else 0)
            * (if h : i.val < m then G ⟨i.val, h⟩ else 0)) 0 = _
    rw [foldl_finRange_succ_last]
    have hlast : ¬ ((Fin.last (m + d)).val < m) := by simp [Fin.last]
    rw [dif_neg hlast]
    have hpre : (List.finRange (m + d)).foldl
        (fun acc i => acc
          + (if h : (Fin.castSucc i).val < m then F ⟨(Fin.castSucc i).val, h⟩ else 0)
            * (if h : (Fin.castSucc i).val < m then G ⟨(Fin.castSucc i).val, h⟩ else 0)) 0
        = (List.finRange (m + d)).foldl
        (fun acc i => acc
          + (if h : i.val < m then F ⟨i.val, h⟩ else 0)
            * (if h : i.val < m then G ⟨i.val, h⟩ else 0)) 0 := by
      apply List.foldl_add_congr
      intro i _
      rfl
    rw [hpre, ih]
    grind

/-- Zero-extending two vectors on the right (to a common larger length `m + d`)
leaves their dot product unchanged: every added term is `0 * _` or `_ * 0`. This
is the vector-level engine behind the matrix padding lemma. -/
theorem dotProduct_extendZero {R : Type u} [Lean.Grind.Ring R] (m d : Nat)
    (F G : Fin m → R) :
    dotProduct
        (Vector.ofFn fun i : Fin (m + d) => if h : i.val < m then F ⟨i.val, h⟩ else 0)
        (Vector.ofFn fun i : Fin (m + d) => if h : i.val < m then G ⟨i.val, h⟩ else 0)
      = dotProduct (Vector.ofFn F) (Vector.ofFn G) := by
  rw [dotProduct_ofFn, dotProduct_ofFn, foldl_extend_zero]

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
