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

/-- The single-bit set. -/
theorem testBit_one_shift (v w : Nat) :
    Nat.testBit (1 <<< v) w = (v == w) := by
  rw [Nat.testBit_shiftLeft]
  rcases Decidable.em (v = w) with rfl | hne
  · simp
  · have hbeq : (v == w) = false := by simp [hne]
    rcases Decidable.em (v ≤ w) with hle | hgt
    · have hz : w - v ≠ 0 := by omega
      have h1 : Nat.testBit 1 (w - v) = false := by
        rcases hb : Nat.testBit 1 (w - v) with _ | _
        · rfl
        · exact absurd (Nat.testBit_one_eq_true_iff_self_eq_zero.mp hb) hz
      rw [h1, hbeq]
      simp
    · have h2 : decide (v ≤ w) = false := by simp [hgt]
      rw [h2, hbeq]
      simp

/-- Membership in a deletion. -/
theorem testBit_erase (s v w : Nat) :
    (erase s v).testBit w = (s.testBit w && !(v == w)) := by
  show (if s.testBit v then s ^^^ (1 <<< v) else s).testBit w = _
  rcases hb : s.testBit v with _ | _
  · simp only [Bool.false_eq_true, if_false]
    rcases Decidable.em (v = w) with rfl | hne
    · simp [hb]
    · simp [show (v == w) = false by simp [hne]]
  · simp only [if_true]
    rw [Nat.testBit_xor, testBit_one_shift]
    rcases Decidable.em (v = w) with rfl | hne
    · simp [hb]
    · simp [show (v == w) = false by simp [hne]]

/-- The least set bit is a member. -/
theorem testBit_lowBit : ∀ (s : Nat), s ≠ 0 → s.testBit (lowBit s) = true
  | s, hs => by
    rw [lowBit_eq, if_neg hs]
    rcases Decidable.em (s % 2 = 1) with ho | ho
    · rw [if_pos ho]
      simp [Nat.testBit_zero, ho]
    · rw [if_neg ho]
      have hs2 : s / 2 ≠ 0 := by omega
      rw [Nat.add_comm 1 (lowBit (s / 2)), Nat.testBit_add_one]
      exact testBit_lowBit (s / 2) hs2
  termination_by s => s
  decreasing_by omega

/-- Any member of a bounded set is a vertex. -/
theorem lt_of_testBit_of_lt {s v n : Nat} (hs : s < 2 ^ n)
    (hv : s.testBit v = true) : v < n := by
  rcases Nat.lt_or_ge v n with h | h
  · exact h
  · rw [Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by omega) h))] at hv
    cases hv

/-- A set whose bits all lie below `n` is bounded by `2 ^ n`. -/
theorem lt_two_pow_of_bits {s n : Nat}
    (h : ∀ i, n ≤ i → s.testBit i = false) : s < 2 ^ n := by
  rcases Nat.lt_or_ge s (2 ^ n) with hlt | hge
  · exact hlt
  · rcases Nat.exists_ge_and_testBit_of_ge_two_pow hge with ⟨i, hi, hb⟩
    rw [h i hi] at hb
    exact absurd hb (by simp)

/-- Deletion keeps a vertex set bounded. -/
theorem erase_lt {s v n : Nat} (hs : s < 2 ^ n) : erase s v < 2 ^ n := by
  refine lt_two_pow_of_bits fun i hi => ?_
  rw [testBit_erase, Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by omega) hi))]
  simp

/-- `nextElem` yields members. -/
theorem nextElem_mem {s : Nat} {pos : Option Nat} {v : Nat} :
    nextElem s pos = some v → s.testBit v = true := by
  rw [nextElem.eq_def]
  rcases pos with _ | p
  · dsimp only
    split
    · intro h
      cases h
    · next hs0 =>
      intro h
      injection h with h
      subst h
      exact testBit_lowBit s hs0
  · dsimp only
    split
    · intro h
      cases h
    · next hs0 =>
      intro h
      injection h with h
      subst h
      have hmem := testBit_lowBit _ hs0
      revert hmem
      generalize lowBit ((s >>> (p + 1)) <<< (p + 1)) = w
      intro hmem
      rw [Nat.testBit_shiftLeft] at hmem
      rcases Decidable.em (p + 1 ≤ w) with hle | hgt
      · rw [Nat.testBit_shiftRight] at hmem
        have hplus : p + 1 + (w - (p + 1)) = w := by omega
        rw [hplus] at hmem
        simp at hmem
        exact hmem.2
      · rw [show decide (p + 1 ≤ w) = false by simp [hgt]] at hmem
        simp at hmem

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

/-- Inserting a vertex keeps a vertex set bounded. -/
theorem insert_lt {s v n : Nat} (hs : s < 2 ^ n) (hv : v < n) :
    insert s v < 2 ^ n := by
  refine lt_two_pow_of_bits fun i hi => ?_
  rw [testBit_insert,
    Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by omega) hi))]
  simp [show v ≠ i by omega]

@[simp] theorem image_zero (σ : Nat → Nat) (n : Nat) : image σ n 0 = 0 := by
  refine Nat.eq_of_testBit_eq fun w => ?_
  rw [testBit_image]
  simp

/-- An image is a vertex set. -/
theorem image_lt {n : Nat} (σ : Renaming n) (s : Nat) :
    image σ n s < 2 ^ n := by
  refine lt_two_pow_of_bits fun i hi => ?_
  rw [testBit_image, List.any_eq_false]
  intro v hv
  simp only [Bool.and_eq_true, beq_iff_eq, not_and]
  intro _ heq
  have := (σ.maps v).mp (List.mem_range.mp hv)
  omega

/-- Images commute with insertion of a vertex. -/
theorem image_insert {n : Nat} (σ : Renaming n) (s : Nat) {v : Nat}
    (hv : v < n) :
    image σ n (insert s v) = insert (image σ n s) (σ v) := by
  refine Nat.eq_of_testBit_eq fun w => ?_
  rw [testBit_image, testBit_insert, testBit_image, Bool.eq_iff_iff,
    Bool.or_eq_true, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨u, hu, hb⟩
    simp only [testBit_insert, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at hb
    rcases hb with ⟨hbu | huv, hw⟩
    · exact Or.inl ⟨u, hu, by simp [hbu, hw]⟩
    · right
      simp [huv, hw]
  · rintro (⟨u, hu, hb⟩ | hw)
    · simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact ⟨u, hu, by simp [testBit_insert, hb.1, hb.2]⟩
    · simp only [beq_iff_eq] at hw
      exact ⟨v, List.mem_range.mpr hv, by simp [testBit_insert, hw]⟩

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

/-- Images of bounded sets are injective. -/
theorem image_inj {n : Nat} (σ : Renaming n) {s t : Nat} (hs : s < 2 ^ n)
    (ht : t < 2 ^ n) (h : image σ n s = image σ n t) : s = t := by
  refine Nat.eq_of_testBit_eq fun v => ?_
  rcases Nat.lt_or_ge v n with hv | hv
  · rw [← testBit_image_apply σ s hv, ← testBit_image_apply σ t hv, h]
  · rw [Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by omega) hv)),
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le ht (Nat.pow_le_pow_right (by omega) hv))]

/-- A bounded set has a null image exactly when it is empty. -/
theorem image_eq_zero_iff {n : Nat} (σ : Renaming n) {s : Nat}
    (hs : s < 2 ^ n) : image σ n s = 0 ↔ s = 0 := by
  constructor
  · intro h
    exact image_inj σ hs (Nat.two_pow_pos n) (by rw [h, image_zero])
  · intro h
    subst h
    exact image_zero σ.toFun n

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
