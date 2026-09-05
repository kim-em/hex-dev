/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

This file contains code translated from the nauty 2.9.3 sources
(https://users.cecs.anu.edu.au/~bdm/nauty/), copyright Brendan McKay and Adolfo
Piperno, released under the Apache 2.0 license.
-/

module

public import HexGraphIso.Nauty.Bits

public section

/-!
Vertex sets of an `n`-vertex graph as packed 63-bit words.

nauty stores a vertex set as an array of `m = ⌈n/64⌉` machine words
(`setword`s) and loops over words, so every set operation costs `O(m)`
word operations and allocates nothing. This module is the same design
on Lean's small natural numbers: a `VSet n` is an array of `⌈n/63⌉`
limbs, each below `2^63` so that it is an unboxed scalar at runtime,
with vertex `v` at bit `v % 63` of limb `v / 63`. Bits at or above `n`
are always clear. Vertex `0` sits at the least significant bit, so the
least vertex of a set is the lowest set bit of its first nonzero limb,
and `rowCmp` reads the least differing vertex from the lowest set bit
of the first differing limb of the symmetric difference. (nauty puts
vertex `0` at the most significant bit so that unsigned word comparison
is the row order; only the direction inside a word differs, and the
observable order is the same.)

The interface is membership-based: `mem` is the specification lens,
`ext` identifies sets with the same members, and every operation has a
`mem_` lemma. Nothing downstream sees a limb. The word-level primitives
(`popCount`, `lowBit` and their byte-table implementations) are in
`Bits`.
-/

namespace Hex.GraphIso.Nauty

/-- The number of 63-bit limbs holding `n` vertices. -/
@[expose] def limbCount (n : Nat) : Nat := (n + 62) / 63

theorem lt_limbCount_mul {n v : Nat} (h : v < n) : v / 63 < limbCount n := by
  rw [limbCount]; omega

theorem limbCount_pos {n : Nat} (h : 0 < n) : 0 < limbCount n := by
  rw [limbCount]; omega

/-- A vertex set over `n` vertices: `limbCount n` limbs, each an unboxed
63-bit word, with no vertex at or above `n`. -/
structure VSet (n : Nat) where
  /-- The limbs, least significant first. -/
  limbs : Array Nat
  size_eq : limbs.size = limbCount n
  bounded : ∀ i : Nat, limbs[i]! < 2 ^ 63
  clear_of_ge : ∀ v : Nat, n ≤ v → (limbs[v / 63]!).testBit (v % 63) = false

namespace VSet

variable {n : Nat}

/-- Membership: the specification lens of the whole interface. -/
@[expose, inline] def mem (s : VSet n) (v : Nat) : Bool :=
  (s.limbs[v / 63]!).testBit (v % 63)

theorem mem_lt {s : VSet n} {v : Nat} (h : s.mem v = true) : v < n := by
  rcases Nat.lt_or_ge v n with hv | hv
  · exact hv
  · rw [mem, s.clear_of_ge v hv] at h
    cases h

theorem mem_of_ge {s : VSet n} {v : Nat} (h : n ≤ v) : s.mem v = false :=
  s.clear_of_ge v h

/-! # Extensionality -/

private theorem getElem!_bounded (s : VSet n) (i : Nat) :
    s.limbs[i]! < 2 ^ 63 := s.bounded i

private theorem testBit_limb_eq_mem (s : VSet n) (i j : Nat) (hj : j < 63) :
    (s.limbs[i]!).testBit j = s.mem (63 * i + j) := by
  rw [mem, show (63 * i + j) / 63 = i by omega,
    show (63 * i + j) % 63 = j by omega]

theorem limbs_ext {s t : VSet n} (h : s.limbs = t.limbs) : s = t := by
  cases s; cases t
  cases h
  rfl

/-- Sets with the same members are equal. -/
theorem ext {s t : VSet n} (h : ∀ v, s.mem v = t.mem v) : s = t := by
  refine limbs_ext (Array.ext (by rw [s.size_eq, t.size_eq]) fun i hi _ => ?_)
  rw [← getElem!_pos s.limbs i hi, ← getElem!_pos t.limbs i (by
    rw [t.size_eq, ← s.size_eq]; exact hi)]
  refine Nat.eq_of_testBit_eq fun j => ?_
  rcases Nat.lt_or_ge j 63 with hj | hj
  · rw [testBit_limb_eq_mem s i j hj, testBit_limb_eq_mem t i j hj, h]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (getElem!_bounded s i)
      (Nat.pow_le_pow_right (by omega) hj)),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (getElem!_bounded t i)
      (Nat.pow_le_pow_right (by omega) hj))]

theorem ext_iff {s t : VSet n} : s = t ↔ ∀ v, s.mem v = t.mem v :=
  ⟨fun h v => by rw [h], ext⟩

instance : DecidableEq (VSet n) := fun s t =>
  if h : s.limbs = t.limbs then isTrue (limbs_ext h)
  else isFalse fun heq => h (by rw [heq])

/-! # Construction -/

/-- A limb array is well formed for `n` vertices when it has `limbCount n`
limbs, every limb is a 63-bit word, and no bit at or above `n` is set.
The runtime never checks this; each operation preserves it by proof. -/
structure Wf (n : Nat) (limbs : Array Nat) : Prop where
  size_eq : limbs.size = limbCount n
  bounded : ∀ i : Nat, limbs[i]! < 2 ^ 63
  clear_of_ge : ∀ v : Nat, n ≤ v → (limbs[v / 63]!).testBit (v % 63) = false

/-- Assemble a set from a well-formed limb array. -/
@[expose, inline] def ofLimbs (limbs : Array Nat) (h : Wf n limbs) : VSet n :=
  ⟨limbs, h.size_eq, h.bounded, h.clear_of_ge⟩

theorem wf (s : VSet n) : Wf n s.limbs := ⟨s.size_eq, s.bounded, s.clear_of_ge⟩

@[simp] theorem limbs_ofLimbs (limbs : Array Nat) (h : Wf n limbs) :
    (ofLimbs limbs h).limbs = limbs := rfl

theorem mem_ofLimbs (limbs : Array Nat) (h : Wf n limbs) (v : Nat) :
    (ofLimbs limbs h).mem v = (limbs[v / 63]!).testBit (v % 63) := rfl

theorem wf_replicate_zero : Wf n (Array.replicate (limbCount n) 0) := by
  refine ⟨Array.size_replicate .., fun i => ?_, fun v _ => ?_⟩
  · rcases Nat.lt_or_ge i (limbCount n) with hi | hi
    · rw [getElem!_pos _ i (by rw [Array.size_replicate]; exact hi),
        Array.getElem_replicate]
      exact Nat.two_pow_pos 63
    · rw [getElem!_neg _ i (by rw [Array.size_replicate]; omega)]
      exact Nat.two_pow_pos 63
  · rcases Nat.lt_or_ge (v / 63) (limbCount n) with hi | hi
    · rw [getElem!_pos _ _ (by rw [Array.size_replicate]; exact hi),
        Array.getElem_replicate, Nat.zero_testBit]
    · rw [getElem!_neg _ _ (by rw [Array.size_replicate]; omega)]
      exact Nat.zero_testBit _

/-- The empty set. -/
@[expose] def empty : VSet n := ofLimbs (Array.replicate (limbCount n) 0) wf_replicate_zero

instance : Inhabited (VSet n) := ⟨empty⟩

@[simp] theorem mem_empty (v : Nat) : (empty : VSet n).mem v = false := by
  rw [empty, mem_ofLimbs]
  rcases Nat.lt_or_ge (v / 63) (limbCount n) with hi | hi
  · rw [getElem!_pos _ _ (by rw [Array.size_replicate]; exact hi),
      Array.getElem_replicate, Nat.zero_testBit]
  · rw [getElem!_neg _ _ (by rw [Array.size_replicate]; omega)]
    exact Nat.zero_testBit _

theorem eq_empty_iff {s : VSet n} : s = empty ↔ ∀ v, s.mem v = false := by
  rw [ext_iff]
  simp only [mem_empty]

/-! # Insertion and deletion

Both act only on vertices below `n`: an out-of-range insertion is the
identity, so the invariant needs no runtime check beyond the one
comparison. -/

theorem wf_set_or {limbs : Array Nat} (h : Wf n limbs) {v : Nat}
    (hv : v < n) :
    Wf n (limbs.set! (v / 63) (limbs[v / 63]! ||| (1 <<< (v % 63)))) := by
  obtain ⟨hsize, hbd, hclr⟩ := h
  have hidx : v / 63 < limbs.size := by rw [hsize]; exact lt_limbCount_mul hv
  refine ⟨by rw [Array.size_set!, hsize], fun i => ?_, fun w hw => ?_⟩
  · rcases Decidable.em (i = v / 63) with rfl | hne
    · rw [Array.getElem!_set!_self _ _ _ hidx]
      exact or_shift_lt (hbd _) (Nat.mod_lt _ (by omega))
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
      exact hbd i
  · rcases Decidable.em (w / 63 = v / 63) with heq | hne
    · rw [heq, Array.getElem!_set!_self _ _ _ hidx, Nat.testBit_or,
        testBit_one_shift, ← heq, hclr w hw,
        show (v % 63 == w % 63) = false by
          simp only [beq_eq_false_iff_ne, ne_eq]; omega]
      rfl
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
      exact hclr w hw

/-- Insert a vertex. -/
@[expose] def insert (s : VSet n) (v : Nat) : VSet n :=
  if hv : v < n then
    ofLimbs (s.limbs.set! (v / 63) (s.limbs[v / 63]! ||| (1 <<< (v % 63))))
      (wf_set_or s.wf hv)
  else s

theorem mem_insert (s : VSet n) (v w : Nat) :
    (s.insert v).mem w = (s.mem w || (v == w && decide (v < n))) := by
  rw [insert]
  rcases Decidable.em (v < n) with hv | hv
  · rw [dite_eq_left hv, mem_ofLimbs, mem]
    have hidx : v / 63 < s.limbs.size := by
      rw [s.size_eq]; exact lt_limbCount_mul hv
    rcases Decidable.em (w / 63 = v / 63) with heq | hne
    · rw [heq, Array.getElem!_set!_self _ _ _ hidx, Nat.testBit_or,
        testBit_one_shift]
      rcases Decidable.em (v = w) with rfl | hvw
      · simp [hv]
      · rw [show (v % 63 == w % 63) = false by
            simp only [beq_eq_false_iff_ne, ne_eq]; omega,
          show (v == w) = false by simp [hvw]]
        simp
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne),
        show (v == w) = false by
          simp only [beq_eq_false_iff_ne, ne_eq]; omega]
      simp
  · rw [dite_eq_right hv, show decide (v < n) = false by simp [hv]]
    simp

theorem mem_insert_of_lt (s : VSet n) {v : Nat} (hv : v < n) (w : Nat) :
    (s.insert v).mem w = (s.mem w || v == w) := by
  rw [mem_insert, show decide (v < n) = true by simp [hv], Bool.and_true]

theorem insert_of_ge (s : VSet n) {v : Nat} (hv : n ≤ v) : s.insert v = s := by
  rw [insert, dite_eq_right (by omega)]

theorem wf_erase_step {limbs : Array Nat} (h : Wf n limbs) {v : Nat}
    (hv : v < n) :
    Wf n (limbs.set! (v / 63) (limbs[v / 63]! ^^^ (1 <<< (v % 63)))) := by
  obtain ⟨hsize, hbd, hclr⟩ := h
  have hidx : v / 63 < limbs.size := by rw [hsize]; exact lt_limbCount_mul hv
  refine ⟨by rw [Array.size_set!, hsize], fun i => ?_, fun w hw => ?_⟩
  · rcases Decidable.em (i = v / 63) with rfl | hne
    · rw [Array.getElem!_set!_self _ _ _ hidx]
      refine lt_two_pow_of_bits fun j hj => ?_
      rw [Nat.testBit_xor, testBit_one_shift,
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hbd _)
          (Nat.pow_le_pow_right (by omega) hj)),
        show (v % 63 == j) = false by
          simp only [beq_eq_false_iff_ne, ne_eq]; omega]
      rfl
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
      exact hbd i
  · rcases Decidable.em (w / 63 = v / 63) with heq | hne
    · rw [heq, Array.getElem!_set!_self _ _ _ hidx, Nat.testBit_xor,
        testBit_one_shift, ← heq, hclr w hw,
        show (v % 63 == w % 63) = false by
          simp only [beq_eq_false_iff_ne, ne_eq]; omega]
      rfl
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
      exact hclr w hw

/-- Delete a vertex. -/
@[expose] def erase (s : VSet n) (v : Nat) : VSet n :=
  if hv : v < n then
    if s.mem v then
      ofLimbs (s.limbs.set! (v / 63) (s.limbs[v / 63]! ^^^ (1 <<< (v % 63))))
        (wf_erase_step s.wf hv)
    else s
  else s

theorem mem_erase (s : VSet n) (v w : Nat) :
    (s.erase v).mem w = (s.mem w && !(v == w)) := by
  rw [erase]
  rcases Decidable.em (v < n) with hv | hv
  · rw [dite_eq_left hv]
    rcases hm : s.mem v with _ | _
    · simp only [Bool.false_eq_true, ite_false]
      rcases Decidable.em (v = w) with rfl | hne
      · simp [hm]
      · simp [show (v == w) = false by simp [hne]]
    · simp only [ite_true]
      rw [mem_ofLimbs, mem]
      have hidx : v / 63 < s.limbs.size := by
        rw [s.size_eq]; exact lt_limbCount_mul hv
      rcases Decidable.em (w / 63 = v / 63) with heq | hne
      · rw [heq, Array.getElem!_set!_self _ _ _ hidx, Nat.testBit_xor,
          testBit_one_shift]
        rcases Decidable.em (v = w) with rfl | hvw
        · rw [mem] at hm
          simp [hm]
        · rw [show (v % 63 == w % 63) = false by
              simp only [beq_eq_false_iff_ne, ne_eq]; omega,
            show (v == w) = false by simp [hvw]]
          simp
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne),
          show (v == w) = false by
            simp only [beq_eq_false_iff_ne, ne_eq]; omega]
        simp
  · rw [dite_eq_right hv]
    rcases Decidable.em (v = w) with rfl | hne
    · rw [mem_of_ge (s := s) (by omega)]
      simp
    · simp [show (v == w) = false by simp [hne]]

/-! # Limbwise binary operations -/

theorem size_zipWith_limbs (op : Nat → Nat → Nat) (s t : VSet n) :
    (Array.zipWith op s.limbs t.limbs).size = limbCount n := by
  rw [Array.size_zipWith, s.size_eq, t.size_eq, Nat.min_self]

theorem getElem!_zipWith (op : Nat → Nat → Nat) (s t : VSet n)
    (i : Nat) (hi : i < limbCount n) :
    (Array.zipWith op s.limbs t.limbs)[i]! = op s.limbs[i]! t.limbs[i]! := by
  have h1 : i < (Array.zipWith op s.limbs t.limbs).size := by
    rw [size_zipWith_limbs]; exact hi
  have h2 : i < s.limbs.size := by rw [s.size_eq]; exact hi
  have h3 : i < t.limbs.size := by rw [t.size_eq]; exact hi
  rw [getElem!_pos _ i h1, Array.getElem_zipWith, getElem!_pos s.limbs i h2,
    getElem!_pos t.limbs i h3]

theorem getElem!_zipWith_of_ge (op : Nat → Nat → Nat) (s t : VSet n)
    (i : Nat) (hi : limbCount n ≤ i) :
    (Array.zipWith op s.limbs t.limbs)[i]! = 0 := by
  rw [getElem!_neg _ i (by rw [size_zipWith_limbs]; omega)]
  rfl

theorem getElem!_limbs_of_ge (s : VSet n) (i : Nat) (hi : limbCount n ≤ i) :
    s.limbs[i]! = 0 := by
  rw [getElem!_neg _ i (by rw [s.size_eq]; omega)]
  rfl

theorem wf_zipWith (op : Nat → Nat → Nat)
    (hop : ∀ a b, a < 2 ^ 63 → b < 2 ^ 63 → op a b < 2 ^ 63)
    (hbit : ∀ a b j, (op a b).testBit j = true →
      a.testBit j = true ∨ b.testBit j = true)
    (s t : VSet n) : Wf n (Array.zipWith op s.limbs t.limbs) := by
  refine ⟨size_zipWith_limbs op s t, fun i => ?_, fun v hv => ?_⟩
  · rcases Nat.lt_or_ge i (limbCount n) with hi | hi
    · rw [getElem!_zipWith op s t i hi]
      exact hop _ _ (s.bounded i) (t.bounded i)
    · rw [getElem!_zipWith_of_ge op s t i hi]
      exact Nat.two_pow_pos 63
  · rcases Nat.lt_or_ge (v / 63) (limbCount n) with hi | hi
    · rw [getElem!_zipWith op s t _ hi]
      rcases hb : (op s.limbs[v / 63]! t.limbs[v / 63]!).testBit (v % 63)
        with _ | _
      · rfl
      · exfalso
        rcases hbit _ _ _ hb with h | h
        · rw [s.clear_of_ge v hv] at h
          cases h
        · rw [t.clear_of_ge v hv] at h
          cases h
    · rw [getElem!_zipWith_of_ge op s t _ hi]
      exact Nat.zero_testBit _

/-- Intersection. -/
@[expose] def inter (s t : VSet n) : VSet n :=
  ofLimbs (Array.zipWith (· &&& ·) s.limbs t.limbs)
    (wf_zipWith _ (fun a b ha _ => Nat.lt_of_le_of_lt (Nat.and_le_left) ha)
      (fun a b j h => by rw [Nat.testBit_and] at h; simp at h; exact Or.inl h.1)
      s t)

theorem mem_inter (s t : VSet n) (w : Nat) :
    (s.inter t).mem w = (s.mem w && t.mem w) := by
  rw [inter, mem_ofLimbs, mem, mem]
  rcases Nat.lt_or_ge (w / 63) (limbCount n) with hi | hi
  · rw [getElem!_zipWith _ s t _ hi, Nat.testBit_and]
  · rw [getElem!_zipWith_of_ge _ s t _ hi, getElem!_limbs_of_ge s _ hi]
    simp

/-- Symmetric difference. -/
@[expose] def xor (s t : VSet n) : VSet n :=
  ofLimbs (Array.zipWith (· ^^^ ·) s.limbs t.limbs)
    (wf_zipWith _ (fun a b ha hb => Nat.xor_lt_two_pow ha hb)
      (fun a b j h => by
        rw [Nat.testBit_xor] at h
        rcases ha : a.testBit j with _ | _
        · rw [ha] at h; simp at h; exact Or.inr h
        · exact Or.inl rfl)
      s t)

theorem mem_xor (s t : VSet n) (w : Nat) :
    (s.xor t).mem w = (s.mem w ^^ t.mem w) := by
  rw [xor, mem_ofLimbs, mem, mem]
  rcases Nat.lt_or_ge (w / 63) (limbCount n) with hi | hi
  · rw [getElem!_zipWith _ s t _ hi, Nat.testBit_xor]
  · rw [getElem!_zipWith_of_ge _ s t _ hi, getElem!_limbs_of_ge s _ hi,
      getElem!_limbs_of_ge t _ hi]
    simp

/-! # Fused predicates and counts

The refinement inner loops never materialize an intersection: they
count it, test it for emptiness, or test containment, each in one
pass over the limbs. -/

/-- Fold a function of corresponding limb pairs over all limbs. -/
@[specialize] def foldLimbs (f : Nat → Nat → α → α) (s t : VSet n)
    (init : α) : α :=
  go s.limbs.size 0 init
where
  go : Nat → Nat → α → α
    | 0, _, acc => acc
    | fuel + 1, i, acc => go fuel (i + 1) (f s.limbs[i]! t.limbs[i]! acc)

/-- Whether every limb satisfies a predicate of the limb pair, with early
exit. -/
@[specialize] def allLimbs (p : Nat → Nat → Bool) (s t : VSet n) : Bool :=
  go s.limbs.size 0
where
  go : Nat → Nat → Bool
    | 0, _ => true
    | fuel + 1, i => p s.limbs[i]! t.limbs[i]! && go fuel (i + 1)

/-- The number of members. -/
@[expose] def card (s : VSet n) : Nat :=
  s.limbs.foldl (fun acc x => acc + popCount x) 0

/-- `card (s.inter t)` without materializing the intersection. -/
@[expose] def cardInter (s t : VSet n) : Nat :=
  foldLimbs (fun a b acc => acc + popCount (a &&& b)) s t 0

/-- Emptiness. -/
@[expose] def isEmpty (s : VSet n) : Bool :=
  s.limbs.all (· == 0)

/-- `isEmpty (s.inter t)` without materializing the intersection. -/
@[expose] def interIsEmpty (s t : VSet n) : Bool :=
  allLimbs (fun a b => a &&& b == 0) s t

/-- Containment: every member of `s` is a member of `t`. -/
@[expose] def subset (s t : VSet n) : Bool :=
  allLimbs (fun a b => a &&& b == a) s t

/-- The number of members below a bound: the counting specification of
`card`. -/
@[expose] def countBelow (s : VSet n) (k : Nat) : Nat :=
  (List.range k).countP s.mem

theorem card_eq_countBelow (s : VSet n) : s.card = s.countBelow n := by
  sorry

theorem cardInter_eq (s t : VSet n) : s.cardInter t = (s.inter t).card := by
  sorry

theorem isEmpty_iff {s : VSet n} : s.isEmpty = true ↔ s = empty := by
  sorry

theorem interIsEmpty_eq (s t : VSet n) :
    s.interIsEmpty t = (s.inter t).isEmpty := by
  sorry

theorem subset_iff {s t : VSet n} :
    s.subset t = true ↔ ∀ v, s.mem v = true → t.mem v = true := by
  sorry

theorem subset_iff_inter {s t : VSet n} : s.subset t = true ↔ s.inter t = s := by
  sorry

/-! # Least element and ascending iteration -/

/-- The least vertex at or after limb `i`, if any. -/
def firstFrom (s : VSet n) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, i =>
    let x := s.limbs[i]!
    if x != 0 then some (63 * i + lowBit x) else firstFrom s fuel (i + 1)

/-- The least member; `0` for the empty set (callers guard on
nonemptiness). nauty's `FIRSTBITNZ` over the words. -/
@[expose] def minElem (s : VSet n) : Nat :=
  (firstFrom s s.limbs.size 0).getD 0

/-- The least member greater than `pos`, or `none`: nauty's
`nextelement`, iterating a set in ascending vertex order. `pos = none`
starts from the least member. -/
@[expose] def nextElem (s : VSet n) (pos : Option Nat) : Option Nat :=
  match pos with
  | none => firstFrom s s.limbs.size 0
  | some p =>
    let q := p + 1
    let i := q / 63
    let k := q % 63
    if i < s.limbs.size then
      let x := (s.limbs[i]! >>> k) <<< k
      if x != 0 then some (63 * i + lowBit x)
      else firstFrom s (s.limbs.size - (i + 1)) (i + 1)
    else none

theorem mem_minElem {s : VSet n} (h : s ≠ empty) : s.mem s.minElem = true := by
  sorry

theorem not_mem_of_lt_minElem {s : VSet n} {v : Nat} (h : v < s.minElem) :
    s.mem v = false := by
  sorry

theorem minElem_eq_of {s : VSet n} {d : Nat} (hd : s.mem d = true)
    (hlow : ∀ i, i < d → s.mem i = false) : s.minElem = d := by
  sorry

@[simp] theorem minElem_empty : (empty : VSet n).minElem = 0 := by
  sorry

/-- The lower bound of a `nextElem` scan. -/
@[expose] def scanStart : Option Nat → Nat
  | none => 0
  | some p => p + 1

theorem nextElem_eq_some_iff {s : VSet n} {pos : Option Nat} {v : Nat} :
    s.nextElem pos = some v ↔
      s.mem v = true ∧ scanStart pos ≤ v ∧
        ∀ w, scanStart pos ≤ w → w < v → s.mem w = false := by
  sorry

theorem nextElem_eq_none_iff {s : VSet n} {pos : Option Nat} :
    s.nextElem pos = none ↔ ∀ w, scanStart pos ≤ w → s.mem w = false := by
  sorry

theorem nextElem_mem {s : VSet n} {pos : Option Nat} {v : Nat}
    (h : s.nextElem pos = some v) : s.mem v = true :=
  (nextElem_eq_some_iff.mp h).1

theorem nextElem_none_eq_minElem {s : VSet n} (h : s ≠ empty) :
    s.nextElem none = some s.minElem := by
  sorry

/-! # Enumeration -/

/-- The members in ascending order, one byte-chunked word walk per limb. -/
@[expose] def toList (s : VSet n) : List Nat :=
  (go s.limbs.size 0 []).reverse
where
  go : Nat → Nat → List Nat → List Nat
    | 0, _, acc => acc
    | fuel + 1, i, acc => go fuel (i + 1) (toListGo (63 * i) 63 s.limbs[i]! acc)

theorem toList_eq (s : VSet n) : s.toList = (List.range n).filter s.mem := by
  sorry

theorem mem_toList {s : VSet n} {v : Nat} : v ∈ s.toList ↔ s.mem v = true := by
  rw [toList_eq, List.mem_filter, List.mem_range]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨mem_lt h, h⟩

/-! # Row order

nauty compares adjacency rows as packed words with vertex `0` most
significant: the least differing vertex decides, and the row containing
it is the greater. -/

/-- The row order. -/
@[expose] def rowCmp (s t : VSet n) : Ordering :=
  go s.limbs.size 0
where
  go : Nat → Nat → Ordering
    | 0, _ => .eq
    | fuel + 1, i =>
      let a := s.limbs[i]!
      let b := t.limbs[i]!
      if a == b then go fuel (i + 1)
      else if a.testBit (lowBit (a ^^^ b)) then .gt else .lt

theorem rowCmp_eq_iff {s t : VSet n} : s.rowCmp t = .eq ↔ s = t := by
  sorry

theorem rowCmp_gt_iff {s t : VSet n} :
    s.rowCmp t = .gt ↔ ∃ d, s.mem d = true ∧ t.mem d = false ∧
      ∀ i, i < d → s.mem i = t.mem i := by
  sorry

theorem rowCmp_lt_iff {s t : VSet n} :
    s.rowCmp t = .lt ↔ ∃ d, s.mem d = false ∧ t.mem d = true ∧
      ∀ i, i < d → s.mem i = t.mem i := by
  sorry

theorem rowCmp_gt_iff_lt {s t : VSet n} : s.rowCmp t = .gt ↔ t.rowCmp s = .lt := by
  rw [rowCmp_gt_iff, rowCmp_lt_iff]
  constructor
  · rintro ⟨d, h1, h2, h3⟩
    exact ⟨d, h2, h1, fun i hi => (h3 i hi).symm⟩
  · rintro ⟨d, h1, h2, h3⟩
    exact ⟨d, h2, h1, fun i hi => (h3 i hi).symm⟩

/-! # Bulk construction -/

/-- The set of vertices below `n` satisfying a predicate. -/
@[expose] def ofFn (f : Nat → Bool) : VSet n :=
  (List.range n).foldl (fun s v => if f v then s.insert v else s) empty

theorem mem_ofFn (f : Nat → Bool) (v : Nat) :
    (ofFn f : VSet n).mem v = (decide (v < n) && f v) := by
  sorry

/-- The set of the vertices of a list. -/
@[expose] def ofList (l : List Nat) : VSet n :=
  l.foldl insert empty

theorem mem_ofList (l : List Nat) (v : Nat) :
    (ofList l : VSet n).mem v = (decide (v < n) && l.contains v) := by
  sorry

/-- `ofFn` built one limb at a time by Horner accumulation over the
vertices of the limb, most significant first: allocation-free and
without the `List.range` fold. -/
def ofFnFast (f : Nat → Bool) : VSet n :=
  sorry

@[csimp] theorem ofFn_eq_ofFnFast : @ofFn = @ofFnFast := by
  sorry

/-! # Images under vertex maps -/

/-- The image of a set under a vertex map, dropping targets outside the
range: nauty's `permset`. -/
@[expose] def image (σ : Nat → Nat) (s : VSet n) : VSet n :=
  (List.range n).foldl (fun t v => if s.mem v then t.insert (σ v) else t) empty

theorem mem_image (σ : Nat → Nat) (s : VSet n) (w : Nat) :
    (s.image σ).mem w =
      (List.range n).any fun v => s.mem v && σ v == w && decide (σ v < n) := by
  sorry

/-- `image` walking the set bits of each limb by repeated lowest-bit
extraction, so the cost is proportional to the members and the limbs,
never to `n` bit tests. -/
def imageFast (σ : Nat → Nat) (s : VSet n) : VSet n :=
  sorry

@[csimp] theorem image_eq_imageFast : @image = @imageFast := by
  sorry

/-- The image under a permutation array: nauty's `permset`. -/
@[expose, inline] def permset (s : VSet n) (perm : Array Nat) : VSet n :=
  s.image (perm[·]!)

/-! # The `Nat` bitset view

The certificate checker and the kernel work with adjacency rows as
natural numbers (bit `v` for vertex `v`), where the kernel's bignum
arithmetic is fast and arrays are not. `toNat` is the boundary. -/

/-- The bitset with bit `v` set exactly for the members `v`. -/
@[expose] def toNat (s : VSet n) : Nat :=
  s.limbs.foldr (fun limb acc => (acc <<< 63) ||| limb) 0

theorem testBit_toNat (s : VSet n) (v : Nat) : s.toNat.testBit v = s.mem v := by
  sorry

theorem toNat_lt (s : VSet n) : s.toNat < 2 ^ n := by
  refine lt_two_pow_of_bits fun v hv => ?_
  rw [testBit_toNat]
  exact mem_of_ge hv

theorem toNat_inj {s t : VSet n} (h : s.toNat = t.toNat) : s = t :=
  ext fun v => by rw [← testBit_toNat, ← testBit_toNat, h]

end VSet

end Hex.GraphIso.Nauty
