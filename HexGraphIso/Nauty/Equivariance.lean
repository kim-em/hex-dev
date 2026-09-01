/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Refine
public import HexGraphIso.Nauty.Image

public section

/-!
Equivariance of the ported nauty refinement.

A `Renaming` of the vertices carries the graph rows to their images and
the labelling to its composition, and leaves every position-level datum —
`ptn`, `active`, cell boundaries, counts, and refinement codes —
literally unchanged. This file proves that invariant through each
explicit recursion of `Nauty.Refine`, culminating in `refine_map`: the
whole refinement commutes with a renaming. This is stage 1 of the
certificate plan in the library README.
-/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- `g'` holds the `σ`-images of the rows of `g`, both bounded. -/
def RowsMap (σ : Renaming n) (g g' : Array Nat) : Prop :=
  g.size = n ∧ g'.size = n ∧
    ∀ v, v < n → g'[σ v]! = image σ n g[v]!

/-- Every entry is a vertex. -/
def LabOk (lab : Array Nat) (n : Nat) : Prop :=
  ∀ i, i < lab.size → lab[i]! < n

/-! # Array transport helpers -/

theorem getElem!_map_of_lt (f : Nat → Nat) (a : Array Nat) {i : Nat}
    (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD, Array.getD,
    Array.getD]
  rw [dif_pos (by simpa using hi), dif_pos hi]
  simp

theorem map_set! (f : Nat → Nat) (a : Array Nat) (i : Nat) (x : Nat) :
    (a.set! i x).map f = (a.map f).set! i (f x) := by
  simp

theorem labOk_set! {lab : Array Nat} (h : LabOk lab n) {x : Nat}
    (hx : x < n) (i : Nat) : LabOk (lab.set! i x) n := by
  intro j hj
  rw [Array.size_set!] at hj
  rcases Decidable.em (i = j) with rfl | hne
  · rw [Array.getElem!_set!_self _ _ _ hj]
    exact hx
  · rw [Array.getElem!_set!_ne _ _ _ _ hne]
    exact h j hj

/-! # The two-pointer partition -/

/-- Map a renaming over a loop result. -/
def mapResult (σ : Renaming n) (r : Array Nat × Int × Int) :
    Array Nat × Int × Int :=
  (r.1.map σ.toFun, r.2.1, r.2.2)

theorem splitCellLoop_map (σ : Renaming n) {gRow : Nat} :
    ∀ (fuel : Nat) (lab : Array Nat) (c1 c2 : Int),
      LabOk lab n → 0 ≤ c1 → c2 < (lab.size : Int) →
      splitCellLoop (image σ n gRow) fuel (lab.map σ.toFun) c1 c2 =
        mapResult σ (splitCellLoop gRow fuel lab c1 c2)
  | 0, lab, c1, c2, hlab, h1, h2 => rfl
  | fuel + 1, lab, c1, c2, hlab, h1, h2 => by
    rw [splitCellLoop, splitCellLoop]
    rcases Decidable.em (c1 ≤ c2) with hle | hgt
    · rw [if_pos hle, if_pos hle]
      have hc1 : c1.toNat < lab.size := by omega
      have hc2 : c2.toNat < lab.size := by omega
      rw [getElem!_map_of_lt _ _ hc1]
      have hlt : lab[c1.toNat]! < n := hlab _ hc1
      rw [show elem (image σ n gRow) (σ.toFun lab[c1.toNat]!)
          = elem gRow lab[c1.toNat]! from testBit_image_apply σ gRow hlt]
      rcases hadj : elem gRow lab[c1.toNat]! with _ | _
      · simp only [Bool.false_eq_true, if_false]
        rw [getElem!_map_of_lt _ _ hc2, ← map_set!, ← map_set!]
        exact splitCellLoop_map σ fuel _ c1 (c2 - 1)
          (labOk_set! (labOk_set! hlab (hlab _ hc2) _) hlt _)
          h1 (by rw [Array.size_set!, Array.size_set!]; omega)
      · simp only [if_true]
        exact splitCellLoop_map σ fuel lab (c1 + 1) c2 hlab (by omega) h2
    · rw [if_neg hgt, if_neg hgt]
      rfl

end Hex.GraphIso.Nauty
