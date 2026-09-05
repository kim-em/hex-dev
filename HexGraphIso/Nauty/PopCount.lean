/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Image

public section

/-!
The comparative `popCount` toolkit for the bitset-cardinality core of
`checkAutom_of_isautom` (SPEC § Verified search refinement, layer two).

The refinement programme's finite-injection counting argument needs to
compare population counts across a submask relation, which the
existing `popCount` lemmas — all computational — do not provide. The
central characterization is already in place: `popCount_eq_bitCount`
expresses `popCount s` as `bitCount n s = (List.range n).countP
s.testBit`, the number of set bits below any bound dominating `s`. All
comparison facts fall out of `countP` reasoning over that form:

* `popCount_le_of_submask`: a submask has no more set bits;
* `eq_of_submask_of_popCount_eq`: a submask with equal population is
  equal — the reverse-inclusion step the counting core turns on.

Deliverable three of the toolkit, the renaming-reindexed identity
`popCount_image`, already lives in `Image.lean` (`bitCount_image`);
these two comparison lemmas complete the set.
-/

namespace Hex.GraphIso.Nauty

/-- The submask constructor: bitwise implication packages as `&&&`. -/
theorem submask_of_testBit {a b : Nat}
    (h : ∀ i, a.testBit i = true → b.testBit i = true) :
    a &&& b = a := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_and]
  rcases ha : a.testBit i with _ | _
  · rfl
  · rw [h i ha]
    rfl

/-- The submask relation as a bitwise implication: if `a &&& b = a`
then every set bit of `a` is a set bit of `b`. -/
theorem testBit_of_submask {a b : Nat} (h : a &&& b = a) {i : Nat}
    (hi : a.testBit i = true) : b.testBit i = true := by
  have := congrArg (fun x => Nat.testBit x i) h
  simp only [Nat.testBit_and] at this
  rw [hi] at this
  simpa using this.symm

/-- `countP` is monotone under pointwise implication of the predicate
on the list's elements. -/
theorem countP_le_of_imp {α : Type _} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) →
      l.countP p ≤ l.countP q
  | [], _ => by simp
  | x :: l, h => by
    have hrec : l.countP p ≤ l.countP q :=
      countP_le_of_imp fun y hy => h y (List.mem_cons_of_mem x hy)
    rcases hp : p x with _ | _
    · rw [List.countP_cons_of_neg (by simp [hp])]
      exact Nat.le_trans hrec ((List.sublist_cons_self x l).countP_le)
    · have hq : q x = true := h x (List.mem_cons_self ..) hp
      rw [List.countP_cons_of_pos (by simp [hp]),
        List.countP_cons_of_pos (by simp [hq])]
      omega

/-- Two `filter`s ordered by pointwise implication are equal when they
have the same length: the weaker filter keeps at least the same
elements in the same order, so equal counts force the extra elements
to be absent. -/
theorem filter_eq_of_imp_of_length_eq {α : Type _} {p q : α → Bool}
    {l : List α} (himp : ∀ x ∈ l, p x = true → q x = true)
    (hlen : (l.filter p).length = (l.filter q).length) :
    l.filter p = l.filter q := by
  have hsub : List.Sublist (l.filter p) (l.filter q) := by
    clear hlen
    induction l with
    | nil => simp
    | cons x l ih =>
      rw [List.filter_cons, List.filter_cons]
      have ih' := ih fun y hy => himp y (List.mem_cons_of_mem x hy)
      rcases hp : p x with _ | _
      · rcases hq : q x with _ | _
        · simpa using ih'
        · exact ih'.trans (List.sublist_cons_self _ _)
      · have hq : q x = true := himp x (List.mem_cons_self ..) hp
        simpa [hq] using ih'.cons_cons x
  exact hsub.eq_of_length hlen

/-- A submask has no more set bits below a bound than its mask. -/
theorem bitCount_le_of_submask {a b : Nat} (h : a &&& b = a) (n : Nat) :
    bitCount n a ≤ bitCount n b := by
  unfold bitCount
  exact countP_le_of_imp fun i _ hi => testBit_of_submask h hi

/-- A bounded bitset with population zero is empty. -/
theorem eq_zero_of_popCount_zero {n s : Nat} (hs : s < 2 ^ n)
    (hp : popCount s = 0) : s = 0 := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.zero_testBit]
  rcases Nat.lt_or_ge i n with hi | hi
  · rw [popCount_eq_bitCount n s hs, bitCount,
      List.countP_eq_zero] at hp
    have := hp i (List.mem_range.mpr hi)
    simpa using this
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hs
      (Nat.pow_le_pow_right (by omega) hi))

/-- A submask has no larger population than its mask. -/
theorem popCount_le_of_submask {a b n : Nat} (h : a &&& b = a)
    (ha : a < 2 ^ n) (hb : b < 2 ^ n) : popCount a ≤ popCount b := by
  rw [popCount_eq_bitCount n a ha, popCount_eq_bitCount n b hb]
  exact bitCount_le_of_submask h n

/-- The reverse-inclusion step: a submask with equal population equals
its mask. Below the shared bound the two sets agree by a length
argument on their filtered index lists; above it both are zero. -/
theorem eq_of_submask_of_popCount_eq {a b n : Nat} (h : a &&& b = a)
    (hpop : popCount a = popCount b) (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    a = b := by
  have hlen : ((List.range n).filter a.testBit).length =
      ((List.range n).filter b.testBit).length := by
    have hb2 := hpop
    rw [popCount_eq_bitCount n a ha, popCount_eq_bitCount n b hb] at hb2
    simp only [bitCount, List.countP_eq_length_filter] at hb2
    exact hb2
  have hfilter : (List.range n).filter a.testBit =
      (List.range n).filter b.testBit :=
    filter_eq_of_imp_of_length_eq
      (fun i _ hi => testBit_of_submask h hi) hlen
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hin : i < n
  · have hmem : i ∈ List.range n := List.mem_range.mpr hin
    have hiff := congrArg (fun l => i ∈ l) hfilter
    simp only [List.mem_filter, hmem, true_and, eq_iff_iff] at hiff
    rcases ha' : a.testBit i with _ | _
    · rcases hb' : b.testBit i with _ | _
      · rfl
      · exact absurd (hiff.mpr hb') (by simp [ha'])
    · exact (testBit_of_submask h ha').symm
  · have hni : n ≤ i := by omega
    have hpow : (2 : Nat) ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hni
    have hai : a.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha hpow)
    have hbi : b.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb hpow)
    rw [hai, hbi]

end Hex.GraphIso.Nauty
