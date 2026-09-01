/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Bits
public import HexGraphIso.Lex

public section

/-!
Vertex-set images under a renaming, and the counting bridge between
`popCount` and per-vertex bit tests.

These are the leaf lemmas of the port equivariance argument: a renaming
carries the bitset rows of a graph to the rows of the renamed graph,
membership transports along it, images commute with intersection, and
population counts are preserved. Sets are `Nat` bitsets with bit `v`
for vertex `v`, as in `Nauty.Bits`. A `Renaming` is globally injective
and preserves the vertex range in both directions; the renaming induced
by a `Perm n` extends it by the identity above `n`.
-/

namespace Hex.GraphIso.Nauty

/-- A vertex renaming: injective everywhere and range-preserving in both
directions. -/
structure Renaming (n : Nat) where
  /-- The underlying vertex map. -/
  toFun : Nat → Nat
  /-- Global injectivity. -/
  inj : ∀ a b, toFun a = toFun b → a = b
  /-- The vertex range is preserved in both directions. -/
  maps : ∀ v, v < n ↔ toFun v < n

instance {n : Nat} : CoeFun (Renaming n) (fun _ => Nat → Nat) :=
  ⟨Renaming.toFun⟩

/-- The number of set bits below `n`. -/
def bitCount (n s : Nat) : Nat :=
  (List.range n).countP s.testBit

/-- `popCount` counts exactly the bits below any bound dominating the
set. -/
theorem popCount_eq_bitCount : ∀ (n s : Nat), s < 2 ^ n →
    popCount s = bitCount n s
  | 0, s, hs => by
    have h0 : s = 0 := by omega
    subst h0
    rw [popCount_zero, bitCount]
    simp
  | n + 1, s, hs => by
    rw [popCount_eq s]
    have hdiv : s / 2 < 2 ^ n := by
      rw [Nat.pow_succ] at hs
      omega
    rw [popCount_eq_bitCount n (s / 2) hdiv]
    unfold bitCount
    rw [List.range_succ_eq_map, List.countP_cons, List.countP_map]
    have hsucc : (s.testBit ∘ Nat.succ) = (s / 2).testBit := by
      funext v
      simp [Function.comp, Nat.testBit_add_one]
    rw [hsucc]
    have h0 : (if s.testBit 0 = true then 1 else 0) = s % 2 := by
      rcases hb : s.testBit 0 with _ | _
      · simp only [Nat.testBit_zero] at hb
        simp at hb
        simp
        omega
      · simp only [Nat.testBit_zero] at hb
        simp at hb
        simp
        omega
    rw [h0]
    omega

/-- Membership in an insertion. -/
theorem testBit_insert (t x w : Nat) :
    (insert t x).testBit w = (t.testBit w || x == w) := by
  show (t ||| (1 <<< x)).testBit w = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  rcases Decidable.em (x = w) with rfl | hne
  · simp
  · have hbeq : (x == w) = false := by
      simp [hne]
    rcases Decidable.em (x ≤ w) with hle | hgt
    · have hz : w - x ≠ 0 := by omega
      have h1 : Nat.testBit 1 (w - x) = false := by
        rcases hb : Nat.testBit 1 (w - x) with _ | _
        · rfl
        · exact absurd (Nat.testBit_one_eq_true_iff_self_eq_zero.mp hb) hz
      rw [h1, hbeq]
      simp
    · have h2 : decide (x ≤ w) = false := by simp [hgt]
      rw [h2, hbeq]
      simp

/-- The image of a vertex set under a renaming: one insertion per set
bit below `n`. -/
@[expose] def image (σ : Nat → Nat) (n s : Nat) : Nat :=
  (List.range n).foldl (fun t v => if s.testBit v then insert t (σ v) else t) 0

theorem testBit_image_foldl (σ : Nat → Nat) (s w : Nat) :
    ∀ (l : List Nat) (t : Nat),
      ((l.foldl (fun t v => if s.testBit v then insert t (σ v) else t)
        t).testBit w) =
        (t.testBit w || l.any fun v => s.testBit v && σ v == w)
  | [], t => by simp
  | v :: l, t => by
    rw [List.foldl_cons, List.any_cons]
    rcases hb : s.testBit v with _ | _
    · rw [if_neg (by simp [hb]), testBit_image_foldl σ s w l t]
      simp [hb]
    · rw [if_pos (by simp [hb]),
        testBit_image_foldl σ s w l (insert t (σ v)), testBit_insert]
      simp [hb, Bool.or_assoc]

/-- Membership in an image. -/
theorem testBit_image (σ : Nat → Nat) (n s w : Nat) :
    (image σ n s).testBit w =
      (List.range n).any fun v => s.testBit v && σ v == w := by
  rw [image, testBit_image_foldl]
  simp

/-- Membership transports along a renaming. -/
theorem testBit_image_apply {n : Nat} (σ : Renaming n) (s : Nat) {v : Nat}
    (hv : v < n) : (image σ n s).testBit (σ v) = s.testBit v := by
  rw [testBit_image]
  rcases hb : s.testBit v with _ | _
  · rw [List.any_eq_false]
    intro u hu
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    intro hbu heq
    exact absurd (σ.inj u v heq ▸ hbu) (by simp [hb])
  · rw [List.any_eq_true]
    exact ⟨v, List.mem_range.mpr hv, by simp [hb]⟩

/-- Images of range-bounded sets commute with intersection, for a
renaming. -/
theorem image_and {n : Nat} (σ : Renaming n) (s t : Nat) :
    image σ n (s &&& t) = image σ n s &&& image σ n t := by
  refine Nat.eq_of_testBit_eq fun w => ?_
  rw [Nat.testBit_and, testBit_image, testBit_image, testBit_image]
  rw [Bool.eq_iff_iff, List.any_eq_true, Bool.and_eq_true,
    List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨v, hv, hb⟩
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.testBit_and] at hb
    exact ⟨⟨v, hv, by simp [hb.1.1, hb.2]⟩, ⟨v, hv, by simp [hb.1.2, hb.2]⟩⟩
  · rintro ⟨⟨v, hv, hbv⟩, ⟨u, hu, hbu⟩⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hbv hbu
    have huv : u = v := σ.inj u v (hbu.2.trans hbv.2.symm)
    subst huv
    exact ⟨u, hu, by simp [Nat.testBit_and, hbv.1, hbu.1, hbv.2]⟩

/-- Bit counts below `n` are preserved by a renaming. -/
theorem bitCount_image {n : Nat} (σ : Renaming n) (s : Nat) :
    bitCount n (image σ n s) = bitCount n s := by
  rw [bitCount, bitCount, List.countP_eq_length_filter,
    List.countP_eq_length_filter]
  have hperm : List.Perm
      ((List.range n).filter (image σ n s).testBit)
      (((List.range n).filter s.testBit).map σ) := by
    refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
    · exact List.filter_sublist.nodup (List.nodup_range)
    · refine List.pairwise_map.mpr ?_
      refine (List.filter_sublist.nodup (List.nodup_range)).imp ?_
      intro a b hne heq
      exact hne (σ.inj a b heq)
    · intro w
      rw [List.mem_filter, List.mem_range, List.mem_map]
      constructor
      · rintro ⟨hw, hbit⟩
        rw [testBit_image, List.any_eq_true] at hbit
        rcases hbit with ⟨v, hv, hb⟩
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        refine ⟨v, ?_, hb.2⟩
        rw [List.mem_filter, List.mem_range]
        exact ⟨List.mem_range.mp hv, hb.1⟩
      · rintro ⟨v, hv, rfl⟩
        rw [List.mem_filter, List.mem_range] at hv
        refine ⟨(σ.maps v).mp hv.1, ?_⟩
        rw [testBit_image_apply σ s hv.1]
        exact hv.2
  rw [hperm.length_eq, List.length_map]

/-- Population counts of range-bounded sets are preserved by a
renaming. -/
theorem popCount_image {n : Nat} (σ : Renaming n) {s : Nat}
    (hs : s < 2 ^ n) (himg : image σ n s < 2 ^ n) :
    popCount (image σ n s) = popCount s := by
  rw [popCount_eq_bitCount n _ himg, popCount_eq_bitCount n s hs,
    bitCount_image]

end Hex.GraphIso.Nauty
