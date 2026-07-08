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

namespace List

/-- Split `List.finRange (p + q)` into the first `p` indices (embedded by
`Fin.castAdd`) followed by the last `q` indices (embedded by `Fin.natAdd`). This
is the list-level fact behind splitting a length-`(p + q)` dot product into its
first-half and second-half parts. -/
private theorem finRange_add (p q : Nat) :
    List.finRange (p + q) =
      (List.finRange p).map (Fin.castAdd q) ++ (List.finRange q).map (Fin.natAdd p) := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    rw [List.getElem_finRange, List.getElem_append]
    split
    · rename_i hlt
      rw [List.getElem_map, List.getElem_finRange]
      apply Fin.ext
      simp [Fin.castAdd, Fin.castLE]
    · rename_i hge
      rw [List.getElem_map, List.getElem_finRange]
      apply Fin.ext
      simp only [List.length_map, List.length_finRange] at hge ⊢
      simp only [Fin.natAdd, Fin.cast]
      omega

end List

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

/-- Splitting a dot product along a sum-shaped dimension: the dot product of two
concatenated vectors is the sum of the dot products of the halves. This is the
vector-level decomposition behind the 2×2 block product of matrices. -/
theorem dotProduct_append {R : Type u} [Lean.Grind.Ring R] {p q : Nat}
    (u : Vector R p) (v : Vector R q) (x : Vector R p) (y : Vector R q) :
    dotProduct (u ++ v) (x ++ y) = dotProduct u x + dotProduct v y := by
  have hleft : ∀ i : Fin p, (u ++ v)[Fin.castAdd q i] * (x ++ y)[Fin.castAdd q i] = u[i] * x[i] := by
    intro i
    have hlt : (Fin.castAdd q i).val < p := i.isLt
    simp only [Fin.getElem_fin]
    rw [Vector.getElem_append_left hlt, Vector.getElem_append_left hlt]
    rfl
  have hright : ∀ i : Fin q, (u ++ v)[Fin.natAdd p i] * (x ++ y)[Fin.natAdd p i] = v[i] * y[i] := by
    intro i
    have hge : p ≤ (Fin.natAdd p i).val := Nat.le_add_right p i.val
    have hlt : (Fin.natAdd p i).val < p + q := (Fin.natAdd p i).isLt
    have hidx : (Fin.natAdd p i).val - p = i.val := by simp [Fin.natAdd]
    simp only [Fin.getElem_fin, Vector.getElem_append_right hlt hge, hidx]
  have hA : (List.map (Fin.castAdd q) (List.finRange p)).foldl
        (fun acc i => acc + (u ++ v)[i] * (x ++ y)[i]) 0 = dotProduct u x := by
    simp only [List.foldl_map, dotProduct]
    apply List.foldl_add_congr
    intro i _
    exact hleft i
  have hB : (List.map (Fin.natAdd p) (List.finRange q)).foldl
        (fun acc i => acc + (u ++ v)[i] * (x ++ y)[i]) (dotProduct u x) =
      dotProduct u x + dotProduct v y := by
    simp only [List.foldl_map]
    rw [show (List.finRange q).foldl
          (fun acc i => acc + (u ++ v)[Fin.natAdd p i] * (x ++ y)[Fin.natAdd p i]) (dotProduct u x) =
        (List.finRange q).foldl (fun acc i => acc + v[i] * y[i]) (dotProduct u x) from
      List.foldl_add_congr (List.finRange q) _ _ _ (fun i _ => hright i)]
    rw [List.foldl_add_eq_add_foldl (List.finRange q) (fun i => v[i] * y[i])]
    rfl
  simp only [dotProduct]
  rw [List.finRange_add p q, List.foldl_append]
  rw [hA, hB]
  simp only [dotProduct]

end Vector
