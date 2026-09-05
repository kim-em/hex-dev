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

/-- A vertex renaming: injective everywhere and range-preserving in both
directions. Images under renamings are the equivariance the search
theory works with. -/
structure Renaming (n : Nat) where
  /-- The underlying vertex map. -/
  toFun : Nat → Nat
  /-- Global injectivity. -/
  inj : ∀ a b, toFun a = toFun b → a = b
  /-- The vertex range is preserved in both directions. -/
  maps : ∀ v, v < n ↔ toFun v < n

instance {n : Nat} : CoeFun (Renaming n) (fun _ => Nat → Nat) := ⟨Renaming.toFun⟩

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

theorem mem_insert_self (s : VSet n) {v : Nat} (hv : v < n) : (s.insert v).mem v = true := by
  rw [mem_insert_of_lt s hv, beq_self_eq_true, Bool.or_true]

theorem mem_insert_mono (s : VSet n) {u : Nat} (w : Nat) (h : s.mem u = true) :
    (s.insert w).mem u = true := by
  rw [mem_insert, h, Bool.true_or]

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

/-- Union. -/
@[expose] def union (s t : VSet n) : VSet n :=
  ofLimbs (Array.zipWith (· ||| ·) s.limbs t.limbs)
    (wf_zipWith _ (fun a b ha hb => Nat.or_lt_two_pow ha hb)
      (fun a b j h => by
        rw [Nat.testBit_or] at h
        rcases ha : a.testBit j with _ | _
        · rw [ha] at h; simp at h; exact Or.inr h
        · exact Or.inl rfl)
      s t)

theorem mem_union (s t : VSet n) (w : Nat) :
    (s.union t).mem w = (s.mem w || t.mem w) := by
  rw [union, mem_ofLimbs, mem, mem]
  rcases Nat.lt_or_ge (w / 63) (limbCount n) with hi | hi
  · rw [getElem!_zipWith _ s t _ hi, Nat.testBit_or]
  · rw [getElem!_zipWith_of_ge _ s t _ hi, getElem!_limbs_of_ge s _ hi,
      getElem!_limbs_of_ge t _ hi]
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

/-! # Limb-level views of membership -/

theorem mem_eq (s : VSet n) (v : Nat) :
    s.mem v = (s.limbs[v / 63]!).testBit (v % 63) := rfl

theorem testBit_limb (s : VSet n) (i j : Nat) (hj : j < 63) :
    (s.limbs[i]!).testBit j = s.mem (63 * i + j) := testBit_limb_eq_mem s i j hj

theorem testBit_limb_of_ge (s : VSet n) (i j : Nat) (hj : 63 ≤ j) :
    (s.limbs[i]!).testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (s.bounded i)
    (Nat.pow_le_pow_right (by omega) hj))

theorem limb_eq_of_mem {s t : VSet n} (i : Nat)
    (h : ∀ j, j < 63 → s.mem (63 * i + j) = t.mem (63 * i + j)) :
    s.limbs[i]! = t.limbs[i]! := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rcases Nat.lt_or_ge j 63 with hj | hj
  · rw [testBit_limb s i j hj, testBit_limb t i j hj, h j hj]
  · rw [testBit_limb_of_ge s i j hj, testBit_limb_of_ge t i j hj]

theorem limb_eq_zero_iff (s : VSet n) (i : Nat) :
    s.limbs[i]! = 0 ↔ ∀ j, j < 63 → s.mem (63 * i + j) = false := by
  constructor
  · intro h j hj
    rw [← testBit_limb s i j hj, h, Nat.zero_testBit]
  · intro h
    refine Nat.eq_of_testBit_eq fun j => ?_
    rw [Nat.zero_testBit]
    rcases Nat.lt_or_ge j 63 with hj | hj
    · rw [testBit_limb s i j hj, h j hj]
    · exact testBit_limb_of_ge s i j hj

theorem mem_of_ge_limbCount (s : VSet n) {v : Nat} (h : limbCount n ≤ v / 63) :
    s.mem v = false := by
  rw [mem_eq, getElem!_limbs_of_ge s _ h, Nat.zero_testBit]

theorem limbs_toList_eq (s : VSet n) :
    s.limbs.toList = (List.range (limbCount n)).map (fun i => s.limbs[i]!) := by
  refine List.ext_getElem (by simp [s.size_eq]) fun i h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range, Array.getElem_toList,
    getElem!_pos _ i (by simpa [Array.length_toList] using h1)]

/-- The members of limb `i`, in order, as vertex numbers. -/
def limbMembers (s : VSet n) (i : Nat) : List Nat :=
  ((List.range 63).filter (s.limbs[i]!).testBit).map (63 * i + ·)

theorem filter_range'_limb (s : VSet n) (i : Nat) :
    (List.range' (63 * i) 63).filter s.mem = limbMembers s i := by
  rw [limbMembers, List.range'_eq_map_range, List.filter_map]
  congr 1
  apply List.filter_congr
  intro j hj
  rw [List.mem_range] at hj
  simp only [Function.comp]
  rw [testBit_limb s i j hj]

/-- The members below `63 * k`, as the concatenation of the limb blocks. -/
theorem filter_range_blocks (s : VSet n) :
    ∀ k : Nat, (List.range (63 * k)).filter s.mem =
      (List.range k).flatMap (limbMembers s)
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.flatMap_append, ← filter_range_blocks s k,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      ← filter_range'_limb, List.range_eq_range', List.range_eq_range',
      show 63 * (k + 1) = 63 * k + 63 by omega, ← List.range'_append,
      List.filter_append, Nat.zero_add, Nat.one_mul]

theorem filter_range_eq_blocks (s : VSet n) :
    (List.range n).filter s.mem =
      (List.range (limbCount n)).flatMap (limbMembers s) := by
  rw [← filter_range_blocks]
  have hle : n ≤ 63 * limbCount n := by rw [limbCount]; omega
  have hnil : (List.range' n (63 * limbCount n - n)).filter s.mem = [] := by
    rw [List.filter_eq_nil_iff]
    intro v hv
    rw [List.mem_range'] at hv
    simp only [Bool.not_eq_true]
    exact mem_of_ge (by omega)
  rw [show 63 * limbCount n = n + (63 * limbCount n - n) by omega,
    List.range_eq_range', List.range_eq_range', ← List.range'_append,
    List.filter_append, Nat.zero_add, Nat.one_mul, hnil, List.append_nil]

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

private theorem foldl_add_popCount :
    ∀ (l : List Nat) (acc : Nat),
      l.foldl (fun a x => a + popCount x) acc = acc + (l.map popCount).sum
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, foldl_add_popCount l, List.map_cons, List.sum_cons]
    omega

theorem card_eq_sum (s : VSet n) :
    s.card = ((List.range (limbCount n)).map fun i => popCount s.limbs[i]!).sum := by
  rw [card, ← Array.foldl_toList, foldl_add_popCount, Nat.zero_add, limbs_toList_eq,
    List.map_map]
  rfl

theorem popCount_limb (s : VSet n) (i : Nat) :
    popCount s.limbs[i]! = (limbMembers s i).length := by
  rw [popCount_eq_bitCount 63 _ (s.bounded i), bitCount, limbMembers, List.length_map,
    List.countP_eq_length_filter]

theorem card_eq_countBelow (s : VSet n) : s.card = s.countBelow n := by
  rw [countBelow, List.countP_eq_length_filter, filter_range_eq_blocks, card_eq_sum,
    List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro i _
  exact popCount_limb s i

private theorem foldLimbs_go_add (f : Nat → Nat → Nat) (s t : VSet n) :
    ∀ (fuel i acc : Nat),
      foldLimbs.go (fun a b acc => acc + f a b) s t fuel i acc =
        acc + ((List.range fuel).map fun k => f s.limbs[i + k]! t.limbs[i + k]!).sum
  | 0, _, acc => by simp [foldLimbs.go]
  | fuel + 1, i, acc => by
    have hr : List.range (fuel + 1) = 0 :: (List.range fuel).map Nat.succ :=
      List.range_succ_eq_map
    rw [foldLimbs.go, foldLimbs_go_add f s t fuel (i + 1), hr, List.map_cons,
      List.sum_cons, List.map_map]
    have : ((fun k => f s.limbs[i + k]! t.limbs[i + k]!) ∘ Nat.succ) =
        fun k => f s.limbs[i + 1 + k]! t.limbs[i + 1 + k]! := by
      funext k
      simp only [Function.comp, Nat.succ_eq_add_one]
      rw [show i + (k + 1) = i + 1 + k by omega]
    rw [this]
    simp only [Nat.add_zero]
    omega

theorem cardInter_eq (s t : VSet n) : s.cardInter t = (s.inter t).card := by
  rw [cardInter, foldLimbs, foldLimbs_go_add, Nat.zero_add, s.size_eq, card_eq_sum]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [Nat.zero_add, inter, limbs_ofLimbs, getElem!_zipWith _ s t i hi]

private theorem allLimbs_go_iff (p : Nat → Nat → Bool) (s t : VSet n) :
    ∀ (fuel i : Nat),
      allLimbs.go p s t fuel i = true ↔
        ∀ k, k < fuel → p s.limbs[i + k]! t.limbs[i + k]! = true
  | 0, _ => by simp [allLimbs.go]
  | fuel + 1, i => by
    rw [allLimbs.go, Bool.and_eq_true, allLimbs_go_iff p s t fuel (i + 1)]
    constructor
    · rintro ⟨h0, hrest⟩ k hk
      cases k with
      | zero => simpa using h0
      | succ k =>
        rw [show i + (k + 1) = i + 1 + k by omega]
        exact hrest k (by omega)
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun k hk => ?_⟩
      rw [show i + 1 + k = i + (k + 1) by omega]
      exact h (k + 1) (by omega)

theorem allLimbs_iff (p : Nat → Nat → Bool) (s t : VSet n) :
    allLimbs p s t = true ↔ ∀ i, i < limbCount n → p s.limbs[i]! t.limbs[i]! = true := by
  rw [allLimbs, allLimbs_go_iff, s.size_eq]
  simp only [Nat.zero_add]

theorem isEmpty_iff {s : VSet n} : s.isEmpty = true ↔ s = empty := by
  rw [isEmpty, Array.all_eq_true, eq_empty_iff]
  constructor
  · intro h v
    rcases Nat.lt_or_ge (v / 63) (limbCount n) with hi | hi
    · have := h (v / 63) (by rw [s.size_eq]; exact hi)
      rw [← getElem!_pos] at this
      rw [mem_eq, show s.limbs[v / 63]! = 0 by simpa using this, Nat.zero_testBit]
    · exact mem_of_ge_limbCount s hi
  · intro h i hi
    rw [← getElem!_pos, beq_iff_eq, limb_eq_zero_iff]
    intro j _
    exact h _

theorem interIsEmpty_eq (s t : VSet n) :
    s.interIsEmpty t = (s.inter t).isEmpty := by
  rw [Bool.eq_iff_iff, interIsEmpty, allLimbs_iff, isEmpty, Array.all_eq_true]
  constructor
  · intro h i hi
    rw [← getElem!_pos, inter, limbs_ofLimbs]
    rw [inter, limbs_ofLimbs, size_zipWith_limbs] at hi
    rw [getElem!_zipWith _ s t i hi]
    exact h i hi
  · intro h i hi
    have := h i (by rw [inter, limbs_ofLimbs, size_zipWith_limbs]; exact hi)
    rw [← getElem!_pos, inter, limbs_ofLimbs, getElem!_zipWith _ s t i hi] at this
    exact this

theorem subset_iff {s t : VSet n} :
    s.subset t = true ↔ ∀ v, s.mem v = true → t.mem v = true := by
  rw [subset, allLimbs_iff]
  constructor
  · intro h v hv
    have hi : v / 63 < limbCount n := lt_limbCount_mul (mem_lt hv)
    have := h _ hi
    rw [beq_iff_eq] at this
    rw [mem_eq] at hv ⊢
    have hb := congrArg (fun x => x.testBit (v % 63)) this
    simp only [Nat.testBit_and, hv, Bool.true_and] at hb
    exact hb
  · intro h i _
    rw [beq_iff_eq]
    refine Nat.eq_of_testBit_eq fun j => ?_
    rw [Nat.testBit_and]
    rcases Nat.lt_or_ge j 63 with hj | hj
    · rw [testBit_limb s i j hj, testBit_limb t i j hj]
      rcases hm : s.mem (63 * i + j) with _ | _
      · rfl
      · simp [h _ hm]
    · rw [testBit_limb_of_ge s i j hj]
      rfl

theorem subset_iff_inter {s t : VSet n} : s.subset t = true ↔ s.inter t = s := by
  rw [subset_iff, ext_iff]
  simp only [mem_inter]
  constructor
  · intro h v
    rcases hm : s.mem v with _ | _
    · rfl
    · simp [h v hm]
  · intro h v hv
    have := h v
    rw [hv] at this
    simpa using this

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
    if (p + 1) / 63 < s.limbs.size then
      if (s.limbs[(p + 1) / 63]! >>> ((p + 1) % 63)) <<< ((p + 1) % 63) != 0 then
        some (63 * ((p + 1) / 63) +
          lowBit ((s.limbs[(p + 1) / 63]! >>> ((p + 1) % 63)) <<< ((p + 1) % 63)))
      else firstFrom s (s.limbs.size - ((p + 1) / 63 + 1)) ((p + 1) / 63 + 1)
    else none

theorem lowBit_lt_of_lt {x k : Nat} (hx : x < 2 ^ k) (h0 : x ≠ 0) :
    lowBit x < k := by
  rcases Nat.lt_or_ge (lowBit x) k with h | h
  · exact h
  · have := testBit_lowBit x h0
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx
      (Nat.pow_le_pow_right (by omega) h))] at this
    cases this

/-- What a `firstFrom` hit is: a member at or after the start limb with
no member in between. -/
theorem firstFrom_some (s : VSet n) :
    ∀ (fuel i v : Nat), firstFrom s fuel i = some v →
      s.mem v = true ∧ 63 * i ≤ v ∧ ∀ w, 63 * i ≤ w → w < v → s.mem w = false
  | 0, _, _, h => by cases h
  | fuel + 1, i, v, h => by
    rw [firstFrom] at h
    split at h
    · next hx =>
      simp only [Option.some.injEq] at h
      subst h
      have hne : s.limbs[i]! ≠ 0 := by simpa using hx
      have hlt : lowBit s.limbs[i]! < 63 := lowBit_lt_of_lt (s.bounded i) hne
      refine ⟨?_, by omega, fun w hw1 hw2 => ?_⟩
      · rw [← testBit_limb s i _ hlt]
        exact testBit_lowBit _ hne
      · rw [show w = 63 * i + (w - 63 * i) by omega, ← testBit_limb s i _ (by omega)]
        exact testBit_lt_lowBit _ _ (by omega)
    · next hx =>
      have ih := firstFrom_some s fuel (i + 1) v h
      refine ⟨ih.1, by omega, fun w hw1 hw2 => ?_⟩
      rcases Nat.lt_or_ge w (63 * (i + 1)) with hw | hw
      · have hz : s.limbs[i]! = 0 := by simpa using hx
        rw [limb_eq_zero_iff] at hz
        rw [show w = 63 * i + (w - 63 * i) by omega]
        exact hz _ (by omega)
      · exact ih.2.2 w hw hw2

/-- A `firstFrom` miss: no member from the start limb to the fuel's end. -/
theorem firstFrom_none (s : VSet n) :
    ∀ (fuel i : Nat), firstFrom s fuel i = none →
      ∀ w, 63 * i ≤ w → w < 63 * (i + fuel) → s.mem w = false
  | 0, _, _, _, _, h2 => by omega
  | fuel + 1, i, h, w, hw1, hw2 => by
    rw [firstFrom] at h
    split at h
    · cases h
    · next hx =>
      rcases Nat.lt_or_ge w (63 * (i + 1)) with hw | hw
      · have hz : s.limbs[i]! = 0 := by simpa using hx
        rw [limb_eq_zero_iff] at hz
        rw [show w = 63 * i + (w - 63 * i) by omega]
        exact hz _ (by omega)
      · exact firstFrom_none s fuel (i + 1) h w hw (by omega)

theorem firstFrom_full_none {s : VSet n} (h : firstFrom s s.limbs.size 0 = none) :
    s = empty := by
  rw [eq_empty_iff]
  intro w
  rcases Nat.lt_or_ge w (63 * limbCount n) with hw | hw
  · rw [s.size_eq] at h
    exact firstFrom_none s _ 0 h w (by omega) (by omega)
  · exact mem_of_ge (by rw [limbCount] at hw; omega)

theorem mem_minElem {s : VSet n} (h : s ≠ empty) : s.mem s.minElem = true := by
  rw [minElem]
  rcases hf : firstFrom s s.limbs.size 0 with _ | v
  · exact absurd (firstFrom_full_none hf) h
  · exact (firstFrom_some s _ 0 v hf).1

theorem not_mem_of_lt_minElem {s : VSet n} {v : Nat} (h : v < s.minElem) :
    s.mem v = false := by
  rw [minElem] at h
  rcases hf : firstFrom s s.limbs.size 0 with _ | u
  · rw [hf] at h
    simp at h
  · rw [hf] at h
    exact (firstFrom_some s _ 0 u hf).2.2 v (by omega) (by simpa using h)

theorem minElem_eq_of {s : VSet n} {d : Nat} (hd : s.mem d = true)
    (hlow : ∀ i, i < d → s.mem i = false) : s.minElem = d := by
  have hne : s ≠ empty := by
    intro h
    rw [h, mem_empty] at hd
    cases hd
  rcases Nat.lt_trichotomy s.minElem d with h | h | h
  · have := hlow _ h
    rw [mem_minElem hne] at this
    cases this
  · exact h
  · have := not_mem_of_lt_minElem h
    rw [hd] at this
    cases this

@[simp] theorem minElem_empty : (empty : VSet n).minElem = 0 := by
  rw [minElem]
  rcases hf : firstFrom (empty : VSet n) (empty : VSet n).limbs.size 0 with _ | v
  · rfl
  · have := (firstFrom_some _ _ 0 v hf).1
    rw [mem_empty] at this
    cases this

/-- The lower bound of a `nextElem` scan. -/
@[expose] def scanStart : Option Nat → Nat
  | none => 0
  | some p => p + 1

/-- The bits of the masked limb `(x >>> k) <<< k`: those of `x` at or
above `k`. -/
private theorem testBit_mask_low (x k j : Nat) :
    ((x >>> k) <<< k).testBit j = (decide (k ≤ j) && x.testBit j) := by
  rw [Nat.testBit_shiftLeft]
  rcases Decidable.em (k ≤ j) with h | h
  · rw [Nat.testBit_shiftRight, show k + (j - k) = j by omega, decide_eq_true h,
      Bool.true_and]
  · simp [h]

/-- The scan property: `v` is the least member at or after `a`. -/
def IsNextFrom (s : VSet n) (a v : Nat) : Prop :=
  s.mem v = true ∧ a ≤ v ∧ ∀ w, a ≤ w → w < v → s.mem w = false

theorem IsNextFrom.unique {s : VSet n} {a v v' : Nat} (h : IsNextFrom s a v)
    (h' : IsNextFrom s a v') : v = v' := by
  rcases Nat.lt_trichotomy v v' with hlt | heq | hgt
  · have := h'.2.2 v h.2.1 hlt
    rw [h.1] at this
    cases this
  · exact heq
  · have := h.2.2 v' h'.2.1 hgt
    rw [h'.1] at this
    cases this

theorem nextElem_some {s : VSet n} {pos : Option Nat} {v : Nat}
    (h : s.nextElem pos = some v) : IsNextFrom s (scanStart pos) v := by
  rcases pos with _ | p
  · rw [nextElem] at h
    exact firstFrom_some s _ 0 v h
  · rw [nextElem] at h
    rw [scanStart]
    split at h
    · next hi =>
      split at h
      · next hx =>
        generalize hxe : (s.limbs[(p + 1) / 63]! >>> ((p + 1) % 63)) <<< ((p + 1) % 63) = x
          at h hx
        simp only [Option.some.injEq] at h
        subst h
        have hne : x ≠ 0 := bne_iff_ne.mp hx
        have hxbit : ∀ j, x.testBit j =
            (decide ((p + 1) % 63 ≤ j) && (s.limbs[(p + 1) / 63]!).testBit j) := fun j => by
          rw [← hxe, testBit_mask_low]
        have hlt : lowBit x < 63 := by
          refine lowBit_lt_of_lt ?_ hne
          refine lt_two_pow_of_bits fun j hj => ?_
          rw [hxbit, testBit_limb_of_ge s _ j hj, Bool.and_false]
        have hbit := testBit_lowBit _ hne
        rw [hxbit, Bool.and_eq_true, decide_eq_true_eq] at hbit
        obtain ⟨hk, hb⟩ := hbit
        refine ⟨?_, by omega, fun w hw1 hw2 => ?_⟩
        · rw [← testBit_limb s _ _ hlt]
          exact hb
        · rw [mem_eq, show w / 63 = (p + 1) / 63 by omega]
          have := testBit_lt_lowBit x (w % 63) (by omega)
          rw [hxbit, Bool.and_eq_false_imp, decide_eq_true_eq] at this
          exact this (by omega)
      · next hx =>
        have ih := firstFrom_some s _ _ v h
        refine ⟨ih.1, by omega, fun w hw1 hw2 => ?_⟩
        rcases Nat.lt_or_ge w (63 * ((p + 1) / 63 + 1)) with hw | hw
        · have hz : (s.limbs[(p + 1) / 63]! >>> ((p + 1) % 63)) <<< ((p + 1) % 63) = 0 := by
            simpa using hx
          have hb := congrArg (fun y => y.testBit (w % 63)) hz
          simp only [testBit_mask_low, Nat.zero_testBit, Bool.and_eq_false_imp,
            decide_eq_true_eq] at hb
          rw [mem_eq, show w / 63 = (p + 1) / 63 by omega]
          exact hb (by omega)
        · exact ih.2.2 w hw hw2
    · cases h

theorem nextElem_none {s : VSet n} {pos : Option Nat} (h : s.nextElem pos = none) :
    ∀ w, scanStart pos ≤ w → s.mem w = false := by
  intro w hw
  rcases pos with _ | p
  · rw [nextElem] at h
    rw [scanStart] at hw
    rcases Nat.lt_or_ge w (63 * limbCount n) with hw' | hw'
    · rw [s.size_eq] at h
      exact firstFrom_none s _ 0 h w (by omega) (by omega)
    · exact mem_of_ge (by rw [limbCount] at hw'; omega)
  · rw [nextElem] at h
    rw [scanStart] at hw
    split at h
    · next hi =>
      split at h
      · cases h
      · next hx =>
        rcases Nat.lt_or_ge w (63 * ((p + 1) / 63 + 1)) with hw' | hw'
        · have hz : (s.limbs[(p + 1) / 63]! >>> ((p + 1) % 63)) <<< ((p + 1) % 63) = 0 := by
            simpa using hx
          have hb := congrArg (fun y => y.testBit (w % 63)) hz
          simp only [testBit_mask_low, Nat.zero_testBit, Bool.and_eq_false_imp,
            decide_eq_true_eq] at hb
          rw [mem_eq, show w / 63 = (p + 1) / 63 by omega]
          exact hb (by omega)
        · rcases Nat.lt_or_ge w (63 * limbCount n) with hw'' | hw''
          · rw [s.size_eq] at h hi
            exact firstFrom_none s _ _ h w hw' (by omega)
          · exact mem_of_ge (by rw [limbCount] at hw''; omega)
    · next hi =>
      rw [s.size_eq] at hi
      exact mem_of_ge_limbCount s (by omega)

theorem nextElem_eq_some_iff {s : VSet n} {pos : Option Nat} {v : Nat} :
    s.nextElem pos = some v ↔
      s.mem v = true ∧ scanStart pos ≤ v ∧
        ∀ w, scanStart pos ≤ w → w < v → s.mem w = false := by
  constructor
  · exact nextElem_some
  · intro hv
    rcases h : s.nextElem pos with _ | u
    · have := nextElem_none h v hv.2.1
      rw [hv.1] at this
      cases this
    · rw [(nextElem_some h).unique hv]

theorem nextElem_eq_none_iff {s : VSet n} {pos : Option Nat} :
    s.nextElem pos = none ↔ ∀ w, scanStart pos ≤ w → s.mem w = false := by
  constructor
  · exact nextElem_none
  · intro hall
    rcases h : s.nextElem pos with _ | u
    · rfl
    · have hu := nextElem_some h
      have := hall u hu.2.1
      rw [hu.1] at this
      cases this

theorem nextElem_mem {s : VSet n} {pos : Option Nat} {v : Nat}
    (h : s.nextElem pos = some v) : s.mem v = true :=
  (nextElem_some h).1

theorem nextElem_none_eq_minElem {s : VSet n} (h : s ≠ empty) :
    s.nextElem none = some s.minElem := by
  rw [nextElem_eq_some_iff, scanStart]
  exact ⟨mem_minElem h, Nat.zero_le _, fun w _ hw => not_mem_of_lt_minElem hw⟩

/-! # Enumeration -/

/-- The members in ascending order, one byte-chunked word walk per limb. -/
@[expose] def toList (s : VSet n) : List Nat :=
  (go s.limbs.size 0 []).reverse
where
  go : Nat → Nat → List Nat → List Nat
    | 0, _, acc => acc
    | fuel + 1, i, acc => go fuel (i + 1) (toListGo (63 * i) 63 s.limbs[i]! acc)

private theorem toList_go_eq (s : VSet n) :
    ∀ (fuel i : Nat) (acc : List Nat),
      toList.go s fuel i acc =
        ((List.range fuel).flatMap fun k => limbMembers s (i + k)).reverse ++ acc
  | 0, _, acc => by simp [toList.go]
  | fuel + 1, i, acc => by
    have hr : List.range (fuel + 1) = 0 :: (List.range fuel).map Nat.succ :=
      List.range_succ_eq_map
    have hshift : (List.range fuel).flatMap (fun k => limbMembers s (i + 1 + k)) =
        (List.range fuel).flatMap ((fun k => limbMembers s (i + k)) ∘ Nat.succ) := by
      congr 1
      funext k
      simp only [Function.comp, Nat.succ_eq_add_one]
      rw [show i + (k + 1) = i + 1 + k by omega]
    rw [toList.go, toList_go_eq s fuel (i + 1), toListGo_eq, hr,
      List.flatMap_cons, List.flatMap_map, List.reverse_append, List.append_assoc,
      Nat.add_zero, hshift, limbMembers]
    rfl

theorem toList_eq (s : VSet n) : s.toList = (List.range n).filter s.mem := by
  rw [toList, toList_go_eq, List.append_nil, List.reverse_reverse, s.size_eq,
    filter_range_eq_blocks]
  simp only [Nat.zero_add]

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

/-- The outcome of the limb scan from `i` with `fuel` limbs: equal
prefixes give `.eq`; otherwise the first differing limb decides by its
least differing bit. -/
theorem rowCmp_go_eq_of {s t : VSet n} :
    ∀ (fuel i : Nat), (∀ k, k < fuel → s.limbs[i + k]! = t.limbs[i + k]!) →
      rowCmp.go s t fuel i = .eq
  | 0, _, _ => rfl
  | fuel + 1, i, h => by
    rw [rowCmp.go, show (s.limbs[i]! == t.limbs[i]!) = true by
      simpa using h 0 (by omega)]
    simp only [↓reduceIte]
    exact rowCmp_go_eq_of fuel (i + 1) fun k hk => by
      rw [show i + 1 + k = i + (k + 1) by omega]
      exact h (k + 1) (by omega)

theorem rowCmp_go_ne_of {s t : VSet n} :
    ∀ (fuel i k : Nat), k < fuel → (∀ k', k' < k → s.limbs[i + k']! = t.limbs[i + k']!) →
      s.limbs[i + k]! ≠ t.limbs[i + k]! →
      rowCmp.go s t fuel i =
        if (s.limbs[i + k]!).testBit (lowBit (s.limbs[i + k]! ^^^ t.limbs[i + k]!))
        then .gt else .lt
  | 0, _, _, hk, _, _ => by omega
  | fuel + 1, i, k, hk, hpre, hne => by
    rw [rowCmp.go]
    cases k with
    | zero =>
      simp only [Nat.add_zero] at hne ⊢
      rw [show (s.limbs[i]! == t.limbs[i]!) = false by simpa using hne]
      simp only [Bool.false_eq_true, ite_false]
    | succ k =>
      rw [show (s.limbs[i]! == t.limbs[i]!) = true by
        simpa using hpre 0 (by omega)]
      simp only [↓reduceIte]
      rw [rowCmp_go_ne_of fuel (i + 1) k (by omega)
        (fun k' hk' => by
          rw [show i + 1 + k' = i + (k' + 1) by omega]
          exact hpre (k' + 1) (by omega))
        (by rw [show i + 1 + k = i + (k + 1) by omega]; exact hne)]
      rw [show i + 1 + k = i + (k + 1) by omega]

/-- A differing limb has a least differing limb below it. -/
private theorem exists_least_diff (s t : VSet n) :
    ∀ k : Nat, s.limbs[k]! ≠ t.limbs[k]! →
      ∃ m : Nat, m ≤ k ∧ s.limbs[m]! ≠ t.limbs[m]! ∧
        ∀ k' : Nat, k' < m → s.limbs[k']! = t.limbs[k']!
  | 0, h => ⟨0, Nat.le_refl 0, h, fun (k' : Nat) (h' : k' < 0) => absurd h' (Nat.not_lt_zero k')⟩
  | k + 1, h => by
    rcases Decidable.em (∀ k' : Nat, k' ≤ k → s.limbs[k']! = t.limbs[k']!) with hall | hnot
    · exact ⟨k + 1, Nat.le_refl _, h, fun k' hk' => hall k' (by omega)⟩
    · -- some earlier limb differs: recurse on the largest candidate
      have : ∃ k', k' ≤ k ∧ s.limbs[k']! ≠ t.limbs[k']! := by
        rcases Classical.not_forall.mp hnot with ⟨k', hk'⟩
        exact ⟨k', Classical.byContradiction fun h1 => hk' fun h2 => absurd h2 h1,
          fun heq => hk' fun _ => heq⟩
      obtain ⟨k', hk', hne'⟩ := this
      obtain ⟨m, hm, hmne, hpre⟩ := exists_least_diff s t k' hne'
      exact ⟨m, by omega, hmne, hpre⟩

theorem rowCmp_eq_iff {s t : VSet n} : s.rowCmp t = .eq ↔ s = t := by
  constructor
  · intro h
    refine ext fun v => ?_
    rcases Nat.lt_or_ge (v / 63) (limbCount n) with hi | hi
    · refine Classical.byContradiction fun hne => ?_
      have hkne : s.limbs[v / 63]! ≠ t.limbs[v / 63]! :=
        fun heq => hne (by rw [mem_eq, mem_eq, heq])
      obtain ⟨m, hm, hmne, hpre⟩ := exists_least_diff s t _ hkne
      rw [rowCmp, s.size_eq, rowCmp_go_ne_of _ 0 m (by omega)
        (fun k' hk' => by rw [Nat.zero_add]; exact hpre k' hk')
        (by rw [Nat.zero_add]; exact hmne)] at h
      split at h <;> cases h
    · rw [mem_of_ge_limbCount s hi, mem_of_ge_limbCount t hi]
  · rintro rfl
    rw [rowCmp]
    exact rowCmp_go_eq_of _ 0 fun _ _ => rfl

private theorem rowCmp_ne_char {s t : VSet n} (hne : s ≠ t) :
    ∃ d, s.mem d ≠ t.mem d ∧ (∀ i, i < d → s.mem i = t.mem i) ∧
      s.rowCmp t = (if s.mem d then .gt else .lt) := by
  have hex : ∃ k, k < limbCount n ∧ s.limbs[k]! ≠ t.limbs[k]! := by
    refine Classical.byContradiction fun hall => hne ?_
    refine limbs_ext (Array.ext (by rw [s.size_eq, t.size_eq]) fun i hi _ => ?_)
    rw [← getElem!_pos, ← getElem!_pos]
    refine Classical.byContradiction fun hne' => hall ⟨i, ?_, hne'⟩
    rw [← s.size_eq]
    exact hi
  obtain ⟨k, hk, hkne⟩ := hex
  obtain ⟨m, hmk, hmne, hpre⟩ := exists_least_diff s t k hkne
  have hmlt : m < limbCount n := by omega
  have hx : s.limbs[m]! ^^^ t.limbs[m]! ≠ 0 := xor_ne_zero_of_ne hmne
  have hlt : lowBit (s.limbs[m]! ^^^ t.limbs[m]!) < 63 :=
    lowBit_lt_of_lt (Nat.xor_lt_two_pow (s.bounded m) (t.bounded m)) hx
  refine ⟨63 * m + lowBit (s.limbs[m]! ^^^ t.limbs[m]!), ?_, ?_, ?_⟩
  · rw [← testBit_limb s m _ hlt, ← testBit_limb t m _ hlt]
    exact testBit_ne_at_lowBit_xor hmne
  · intro i hi
    rcases Nat.lt_or_ge (i / 63) m with him | him
    · rw [mem_eq, mem_eq, hpre _ him]
    · have heq : i / 63 = m := by omega
      rw [mem_eq, mem_eq, heq]
      exact testBit_eq_of_lt_lowBit_xor (by omega)
  · rw [rowCmp, s.size_eq, rowCmp_go_ne_of _ 0 m hmlt
      (fun k' hk' => by rw [Nat.zero_add]; exact hpre k' hk')
      (by rw [Nat.zero_add]; exact hmne), Nat.zero_add,
      testBit_limb s m _ hlt]

theorem rowCmp_gt_iff {s t : VSet n} :
    s.rowCmp t = .gt ↔ ∃ d, s.mem d = true ∧ t.mem d = false ∧
      ∀ i, i < d → s.mem i = t.mem i := by
  constructor
  · intro h
    have hne : s ≠ t := fun heq => by
      rw [rowCmp_eq_iff.mpr heq] at h
      cases h
    obtain ⟨d, hd, hpre, hcmp⟩ := rowCmp_ne_char hne
    refine ⟨d, ?_, ?_, hpre⟩
    · rcases hs : s.mem d with _ | _
      · rw [hs] at hcmp
        rw [hcmp] at h
        cases h
      · rfl
    · rcases hs : s.mem d with _ | _
      · rw [hs] at hcmp
        rw [hcmp] at h
        cases h
      · rcases ht : t.mem d with _ | _
        · rfl
        · exact absurd (hs.trans ht.symm) hd
  · rintro ⟨d, hs, ht, hpre⟩
    have hne : s ≠ t := fun heq => by
      rw [heq] at hs
      rw [hs] at ht
      cases ht
    obtain ⟨d', hd', hpre', hcmp⟩ := rowCmp_ne_char hne
    have hdd : d = d' := by
      rcases Nat.lt_trichotomy d d' with hlt | heq | hgt
      · have := hpre' d hlt
        rw [hs, ht] at this
        cases this
      · exact heq
      · exact absurd (hpre d' hgt) hd'
    subst hdd
    rw [hcmp, hs]
    rfl

theorem rowCmp_lt_iff {s t : VSet n} :
    s.rowCmp t = .lt ↔ ∃ d, s.mem d = false ∧ t.mem d = true ∧
      ∀ i, i < d → s.mem i = t.mem i := by
  constructor
  · intro h
    have hne : s ≠ t := fun heq => by
      rw [rowCmp_eq_iff.mpr heq] at h
      cases h
    obtain ⟨d, hd, hpre, hcmp⟩ := rowCmp_ne_char hne
    refine ⟨d, ?_, ?_, hpre⟩
    · rcases hs : s.mem d with _ | _
      · rfl
      · rw [hs] at hcmp
        rw [hcmp] at h
        cases h
    · rcases hs : s.mem d with _ | _
      · rcases ht : t.mem d with _ | _
        · exact absurd (hs.trans ht.symm) hd
        · rfl
      · rw [hs] at hcmp
        rw [hcmp] at h
        cases h
  · rintro ⟨d, hs, ht, hpre⟩
    have hne : s ≠ t := fun heq => by
      rw [heq] at hs
      rw [hs] at ht
      cases ht
    obtain ⟨d', hd', hpre', hcmp⟩ := rowCmp_ne_char hne
    have hdd : d = d' := by
      rcases Nat.lt_trichotomy d d' with hlt | heq | hgt
      · have := hpre' d hlt
        rw [hs, ht] at this
        cases this
      · exact heq
      · exact absurd (hpre d' hgt) hd'
    subst hdd
    rw [hcmp, hs]
    rfl

theorem rowCmp_gt_iff_lt {s t : VSet n} : s.rowCmp t = .gt ↔ t.rowCmp s = .lt := by
  rw [rowCmp_gt_iff, rowCmp_lt_iff]
  constructor
  · rintro ⟨d, h1, h2, h3⟩
    exact ⟨d, h2, h1, fun i hi => (h3 i hi).symm⟩
  · rintro ⟨d, h1, h2, h3⟩
    exact ⟨d, h2, h1, fun i hi => (h3 i hi).symm⟩

/-- The row order is transitive. -/
theorem rowCmp_gt_trans {s t u : VSet n} (h1 : s.rowCmp t = .gt) (h2 : t.rowCmp u = .gt) :
    s.rowCmp u = .gt := by
  rw [rowCmp_gt_iff] at h1 h2 ⊢
  obtain ⟨d1, hs1, ht1, hpre1⟩ := h1
  obtain ⟨d2, ht2, hu2, hpre2⟩ := h2
  rcases Nat.lt_trichotomy d1 d2 with hlt | heq | hgt
  · refine ⟨d1, hs1, by rw [← hpre2 d1 hlt]; exact ht1, fun i hi => ?_⟩
    rw [hpre1 i hi, hpre2 i (Nat.lt_trans hi hlt)]
  · subst heq
    rw [ht1] at ht2
    cases ht2
  · refine ⟨d2, by rw [hpre1 d2 hgt]; exact ht2, hu2, fun i hi => ?_⟩
    rw [hpre1 i (Nat.lt_trans hi hgt), hpre2 i hi]

/-! # Bulk construction -/

/-- The set of vertices below `n` satisfying a predicate. -/
@[expose] def ofFn (f : Nat → Bool) : VSet n :=
  (List.range n).foldl (fun s v => if f v then s.insert v else s) empty

/-- Membership after a guarded insertion fold. -/
theorem mem_foldl_insert_if (f : Nat → Bool) :
    ∀ (l : List Nat) (init : VSet n) (w : Nat),
      (l.foldl (fun s v => if f v then s.insert v else s) init).mem w =
        (init.mem w || (l.contains w && f w && decide (w < n)))
  | [], init, w => by simp
  | v :: l, init, w => by
    rw [List.foldl_cons, mem_foldl_insert_if f l, List.contains_cons]
    rcases Decidable.em (v = w) with rfl | hne
    · rcases hf : f v with _ | _
      · rw [ite_eq_right (by simp [hf])]
        cases init.mem v <;> cases hc : l.contains v <;> simp [hf, hc]
      · rw [ite_eq_left (by simp [hf]), mem_insert]
        cases init.mem v <;> cases hc : l.contains v <;> cases hd : decide (v < n) <;>
          simp [hf, hc, hd]
    · have hbeq : (w == v) = false := by simp [Ne.symm hne]
      have hbeq' : (v == w) = false := by simp [hne]
      rcases hf : f v with _ | _
      · rw [ite_eq_right (by simp [hf])]
        simp [hbeq]
      · rw [ite_eq_left (by simp [hf]), mem_insert]
        simp [hbeq, hbeq']

theorem mem_ofFn (f : Nat → Bool) (v : Nat) :
    (ofFn f : VSet n).mem v = (decide (v < n) && f v) := by
  rw [ofFn, mem_foldl_insert_if, mem_empty, Bool.false_or]
  rcases Decidable.em (v < n) with hv | hv
  · have hc : (List.range n).contains v = true := by simp [hv]
    rw [hc, decide_eq_true hv]
    simp
  · have hc : (List.range n).contains v = false := by simp [hv]
    rw [hc, decide_eq_false hv]
    simp

/-- The set of the vertices of a list. -/
@[expose] def ofList (l : List Nat) : VSet n :=
  l.foldl insert empty

theorem mem_foldl_insert :
    ∀ (l : List Nat) (init : VSet n) (w : Nat),
      (l.foldl insert init).mem w = (init.mem w || (l.contains w && decide (w < n)))
  | [], init, w => by simp
  | v :: l, init, w => by
    rw [List.foldl_cons, mem_foldl_insert l, List.contains_cons, mem_insert]
    rcases Decidable.em (v = w) with rfl | hne
    · simp only [beq_self_eq_true, Bool.true_or, Bool.true_and]
      cases init.mem v <;> cases decide (v < n) <;> cases l.contains v <;> rfl
    · rw [show (v == w) = false by simp [hne], show (w == v) = false by simp [Ne.symm hne]]
      simp only [Bool.false_and, Bool.or_false, Bool.false_or]

theorem mem_ofList (l : List Nat) (v : Nat) :
    (ofList l : VSet n).mem v = (decide (v < n) && l.contains v) := by
  rw [ofList, mem_foldl_insert, mem_empty, Bool.false_or, Bool.and_comm]

/-- One limb of `ofFn`: Horner accumulation over the limb's vertices,
most significant first, so the accumulator stays a scalar throughout. -/
def ofFnLimb (f : Nat → Bool) (base : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | j + 1, acc =>
    ofFnLimb f base j (2 * acc + if base + j < n ∧ f (base + j) then 1 else 0)

/-- The limbs of `ofFn`, least significant first. -/
def ofFnLimbs (f : Nat → Bool) : Nat → Array Nat → Array Nat
  | 0, acc => acc
  | i + 1, acc => ofFnLimbs f i (acc.push (ofFnLimb (n := n) f (63 * acc.size) 63 0))

/-- The bit of a vertex under the limb predicate: set exactly when the
vertex exists and satisfies `f`. -/
private def fnBit (f : Nat → Bool) (v : Nat) : Bool := decide (v < n) && f v

private theorem ofFnLimb_shift (f : Nat → Bool) (base : Nat) :
    ∀ (j acc : Nat), ofFnLimb (n := n) f base j acc =
      acc * 2 ^ j + ofFnLimb (n := n) f base j 0
  | 0, acc => by simp [ofFnLimb]
  | j + 1, acc => by
    rw [ofFnLimb, ofFnLimb, ofFnLimb_shift f base j (2 * acc + _),
      ofFnLimb_shift f base j (2 * 0 + _)]
    simp only [Nat.mul_zero, Nat.zero_add]
    have h1 : 2 * acc * 2 ^ j = acc * 2 ^ (j + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm 2 acc, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ j)]
    rw [Nat.add_mul, h1]
    omega

private theorem ofFnLimb_lt (f : Nat → Bool) (base : Nat) :
    ∀ j : Nat, ofFnLimb (n := n) f base j 0 < 2 ^ j
  | 0 => Nat.zero_lt_one
  | j + 1 => by
    rw [ofFnLimb, ofFnLimb_shift f base j]
    have := ofFnLimb_lt f base j
    rw [Nat.pow_succ]
    split <;> omega

private theorem testBit_ofFnLimb (f : Nat → Bool) (base : Nat) :
    ∀ (j t : Nat), (ofFnLimb (n := n) f base j 0).testBit t =
      (decide (t < j) && fnBit (n := n) f (base + t))
  | 0, t => by simp [ofFnLimb]
  | j + 1, t => by
    rw [ofFnLimb, ofFnLimb_shift f base j]
    have hlt := ofFnLimb_lt (n := n) f base j
    have hp : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ]; omega
    simp only [Nat.mul_zero, Nat.zero_add]
    rcases Nat.lt_trichotomy t j with htj | htj | htj
    · rw [decide_eq_true (by omega : t < j + 1)]
      have := testBit_ofFnLimb f base j t
      rw [decide_eq_true htj] at this
      rw [← this]
      split
      · rw [Nat.one_mul, Nat.testBit_two_pow_add_gt htj]
      · rw [Nat.zero_mul, Nat.zero_add]
    · subst htj
      rw [decide_eq_true (Nat.lt_succ_self t), Bool.true_and, fnBit]
      split
      · next h =>
        rw [Nat.one_mul, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt,
          decide_eq_true h.1, h.2]
        rfl
      · next h =>
        rw [Nat.zero_mul, Nat.zero_add, Nat.testBit_lt_two_pow hlt]
        rcases Decidable.em (base + t < n) with h1 | h1
        · rw [decide_eq_true h1, Bool.true_and]
          rcases hf : f (base + t) with _ | _
          · rfl
          · exact absurd ⟨h1, hf⟩ h
        · rw [decide_eq_false h1]
          rfl
    · rw [decide_eq_false (by omega : ¬ t < j + 1), Bool.false_and]
      have h2 : 2 ^ (j + 1) ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) htj
      split
      · rw [Nat.one_mul]
        exact Nat.testBit_lt_two_pow (by omega)
      · rw [Nat.zero_mul, Nat.zero_add]
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt
          (Nat.pow_le_pow_right (by omega) (by omega)))

private theorem ofFnLimbs_size (f : Nat → Bool) :
    ∀ (fuel : Nat) (acc : Array Nat),
      (ofFnLimbs (n := n) f fuel acc).size = acc.size + fuel
  | 0, acc => by simp [ofFnLimbs]
  | fuel + 1, acc => by
    rw [ofFnLimbs, ofFnLimbs_size f fuel, Array.size_push]
    omega

private theorem getElem!_ofFnLimbs (f : Nat → Bool) :
    ∀ (fuel : Nat) (acc : Array Nat) (i : Nat),
      (ofFnLimbs (n := n) f fuel acc)[i]! =
        if i < acc.size then acc[i]!
        else if i < acc.size + fuel then ofFnLimb (n := n) f (63 * i) 63 0
        else 0
  | 0, acc, i => by
    rw [ofFnLimbs]
    rcases Nat.lt_or_ge i acc.size with h | h
    · rw [ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), getElem!_neg _ _ (by omega)]
      rfl
  | fuel + 1, acc, i => by
    rw [ofFnLimbs, getElem!_ofFnLimbs f fuel, Array.size_push]
    rcases Nat.lt_or_ge i acc.size with h | h
    · rw [ite_eq_left (by omega : i < acc.size + 1), ite_eq_left h,
        getElem!_pos _ i (by rw [Array.size_push]; omega), getElem!_pos acc i h,
        Array.getElem_push_lt]
    · rw [ite_eq_right (by omega : ¬ i < acc.size)]
      rcases Decidable.em (i = acc.size) with rfl | hne
      · rw [ite_eq_left (by omega : acc.size < acc.size + 1),
          ite_eq_left (by omega : acc.size < acc.size + (fuel + 1)),
          getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]
      · rw [ite_eq_right (by omega : ¬ i < acc.size + 1)]
        rcases Nat.lt_or_ge i (acc.size + (fuel + 1)) with h2 | h2
        · rw [ite_eq_left (by omega : i < acc.size + 1 + fuel), ite_eq_left h2]
        · rw [ite_eq_right (by omega : ¬ i < acc.size + 1 + fuel),
            ite_eq_right (by omega : ¬ i < acc.size + (fuel + 1))]

theorem mem_ofFnFast_limbs (f : Nat → Bool) (v : Nat) :
    ((ofFnLimbs (n := n) f (limbCount n) #[])[v / 63]!).testBit (v % 63) =
      (decide (v < n) && f v) := by
  rw [getElem!_ofFnLimbs, Array.size_empty, ite_eq_right (by omega), Nat.zero_add]
  rcases Nat.lt_or_ge (v / 63) (limbCount n) with hi | hi
  · rw [ite_eq_left hi, testBit_ofFnLimb, decide_eq_true (Nat.mod_lt _ (by omega)),
      Bool.true_and, fnBit, Nat.div_add_mod]
  · rw [ite_eq_right (by omega), Nat.zero_testBit,
      decide_eq_false (by rw [limbCount] at hi; omega), Bool.false_and]

theorem wf_ofFnLimbs (f : Nat → Bool) :
    Wf n (ofFnLimbs (n := n) f (limbCount n) #[]) := by
  refine ⟨by rw [ofFnLimbs_size, Array.size_empty, Nat.zero_add], fun i => ?_, fun v hv => ?_⟩
  · rw [getElem!_ofFnLimbs, Array.size_empty, ite_eq_right (by omega), Nat.zero_add]
    split
    · exact ofFnLimb_lt f _ 63
    · exact Nat.two_pow_pos 63
  · rw [mem_ofFnFast_limbs, decide_eq_false (by omega), Bool.false_and]

/-- `ofFn` built one limb at a time: allocation-free and without the
`List.range` fold. -/
def ofFnFast (f : Nat → Bool) : VSet n :=
  ofLimbs (ofFnLimbs (n := n) f (limbCount n) #[]) (wf_ofFnLimbs f)

@[csimp] theorem ofFn_eq_ofFnFast : @ofFn = @ofFnFast := by
  funext n f
  refine ext fun v => ?_
  rw [mem_ofFn, ofFnFast, mem_ofLimbs, mem_ofFnFast_limbs]

/-! # Images under vertex maps -/

/-- The image of a set under a vertex map, dropping targets outside the
range: nauty's `permset`. -/
@[expose] def image (σ : Nat → Nat) (s : VSet n) : VSet n :=
  (List.range n).foldl (fun t v => if s.mem v then t.insert (σ v) else t) empty

theorem mem_foldl_image (σ : Nat → Nat) (s : VSet n) :
    ∀ (l : List Nat) (init : VSet n) (w : Nat),
      (l.foldl (fun t v => if s.mem v then t.insert (σ v) else t) init).mem w =
        (init.mem w || l.any fun v => s.mem v && σ v == w && decide (σ v < n))
  | [], init, w => by simp
  | v :: l, init, w => by
    rw [List.foldl_cons, mem_foldl_image σ s l, List.any_cons]
    rcases hm : s.mem v with _ | _
    · simp only [Bool.false_eq_true, ite_false, Bool.false_and, Bool.false_or]
    · simp only [ite_true, mem_insert, Bool.true_and]
      cases init.mem w <;> cases hb : (σ v == w) <;> cases hd : decide (σ v < n) <;>
        cases hl : l.any (fun v => s.mem v && σ v == w && decide (σ v < n)) <;> simp [hb, hd, hl]

theorem mem_image (σ : Nat → Nat) (s : VSet n) (w : Nat) :
    (s.image σ).mem w =
      (List.range n).any fun v => s.mem v && σ v == w && decide (σ v < n) := by
  rw [image, mem_foldl_image, mem_empty, Bool.false_or]

/-- The set bits of one limb, by repeated lowest-bit extraction, each
inserted through `σ`. -/
def imageLimb (σ : Nat → Nat) (base : Nat) : Nat → Nat → VSet n → VSet n
  | 0, _, acc => acc
  | fuel + 1, x, acc =>
    if x = 0 then acc
    else
      let j := lowBit x
      imageLimb σ base fuel (x ^^^ (1 <<< j)) (acc.insert (σ (base + j)))

/-- `image` walking the set bits of each limb by repeated lowest-bit
extraction, so the cost is proportional to the members and the limbs,
never to `n` bit tests. -/
def imageFast (σ : Nat → Nat) (s : VSet n) : VSet n :=
  go s.limbs.size 0 empty
where
  go : Nat → Nat → VSet n → VSet n
    | 0, _, acc => acc
    | fuel + 1, i, acc => go fuel (i + 1) (imageLimb σ (63 * i) 63 s.limbs[i]! acc)

/-- Clearing the lowest set bit of a nonzero word. -/
private theorem testBit_clear_lowBit {x : Nat} (hx : x ≠ 0) (j : Nat) :
    (x ^^^ (1 <<< lowBit x)).testBit j = (x.testBit j && !(lowBit x == j)) := by
  rw [Nat.testBit_xor, testBit_one_shift]
  rcases Decidable.em (lowBit x = j) with rfl | hne
  · rw [testBit_lowBit x hx]
    simp
  · rw [show (lowBit x == j) = false by simp [hne]]
    simp

/-- Membership after one limb's extraction walk: the fuel must cover the
remaining bits, which it does because each step clears the lowest one. -/
private theorem mem_imageLimb (σ : Nat → Nat) (base : Nat) :
    ∀ (fuel x : Nat) (acc : VSet n) (w : Nat), x < 2 ^ 63 →
      (∀ j, j < 63 - fuel → x.testBit j = false) →
      (imageLimb σ base fuel x acc).mem w =
        (acc.mem w || (List.range 63).any fun j =>
          x.testBit j && σ (base + j) == w && decide (σ (base + j) < n))
  | 0, x, acc, w, hx, hlow => by
    have hz : x = 0 := by
      refine Nat.eq_of_testBit_eq fun j => ?_
      rw [Nat.zero_testBit]
      rcases Nat.lt_or_ge j 63 with hj | hj
      · exact hlow j (by omega)
      · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx
          (Nat.pow_le_pow_right (by omega) hj))
    subst hz
    rw [imageLimb]
    simp
  | fuel + 1, x, acc, w, hx, hlow => by
    rw [imageLimb]
    rcases Decidable.em (x = 0) with rfl | hne
    · simp
    · rw [ite_eq_right hne]
      have hlt : lowBit x < 63 := lowBit_lt_of_lt hx hne
      have hlow' : ∀ j, j < 63 - fuel → (x ^^^ (1 <<< lowBit x)).testBit j = false := by
        intro j hj
        rw [testBit_clear_lowBit hne]
        rcases Nat.lt_trichotomy j (lowBit x) with h | h | h
        · rw [testBit_lt_lowBit x j h]
          rfl
        · subst h
          simp
        · exfalso
          have := hlow (lowBit x) (by omega)
          rw [testBit_lowBit x hne] at this
          cases this
      have h1 : 1 <<< lowBit x < 2 ^ 63 := by
        rw [Nat.one_shiftLeft]
        exact Nat.pow_lt_pow_right (by omega) hlt
      rw [mem_imageLimb σ base fuel _ _ w (Nat.xor_lt_two_pow hx h1) hlow', mem_insert]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq, testBit_clear_lowBit hne, Bool.not_eq_true']
      constructor
      · rintro ((h | ⟨h1, h2⟩) | ⟨j, hj, ⟨⟨hb, hne'⟩, hσ⟩, hlt'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨lowBit x, hlt, ⟨testBit_lowBit x hne, h1⟩, h2⟩
        · exact Or.inr ⟨j, hj, ⟨hb, hσ⟩, hlt'⟩
      · rintro (h | ⟨j, hj, ⟨hb, hσ⟩, hlt'⟩)
        · exact Or.inl (Or.inl h)
        · rcases Decidable.em (lowBit x = j) with rfl | hne'
          · exact Or.inl (Or.inr ⟨hσ, hlt'⟩)
          · exact Or.inr ⟨j, hj, ⟨⟨hb, beq_eq_false_iff_ne.mpr hne'⟩, hσ⟩, hlt'⟩

private theorem mem_imageFast_go (σ : Nat → Nat) (s : VSet n) :
    ∀ (fuel i : Nat) (acc : VSet n) (w : Nat),
      (imageFast.go σ s fuel i acc).mem w =
        (acc.mem w || (List.range fuel).any fun k => (List.range 63).any fun j =>
          (s.limbs[i + k]!).testBit j && σ (63 * (i + k) + j) == w &&
            decide (σ (63 * (i + k) + j) < n))
  | 0, _, acc, w => by simp [imageFast.go]
  | fuel + 1, i, acc, w => by
    have hr : List.range (fuel + 1) = 0 :: (List.range fuel).map Nat.succ :=
      List.range_succ_eq_map
    have hfun : (fun k => (List.range 63).any fun j =>
          (s.limbs[i + 1 + k]!).testBit j && σ (63 * (i + 1 + k) + j) == w &&
            decide (σ (63 * (i + 1 + k) + j) < n)) =
        ((fun k => (List.range 63).any fun j =>
          (s.limbs[i + k]!).testBit j && σ (63 * (i + k) + j) == w &&
            decide (σ (63 * (i + k) + j) < n)) ∘ Nat.succ) := by
      funext k
      simp only [Function.comp, Nat.succ_eq_add_one]
      rw [show i + (k + 1) = i + 1 + k by omega]
    rw [imageFast.go, mem_imageFast_go σ s fuel (i + 1), hr, List.any_cons, List.any_map,
      mem_imageLimb σ _ 63 _ acc w (s.bounded i) (fun j hj => by omega), hfun,
      Bool.or_assoc]
    simp only [Nat.add_zero]

@[csimp] theorem image_eq_imageFast : @image = @imageFast := by
  funext n σ s
  refine ext fun w => ?_
  rw [mem_image, imageFast, mem_imageFast_go, mem_empty, Bool.false_or, s.size_eq,
    Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, Nat.zero_add]
  constructor
  · rintro ⟨v, hv, ⟨hm, hσ⟩, hlt⟩
    refine ⟨v / 63, lt_limbCount_mul hv, v % 63, Nat.mod_lt _ (by omega), ?_⟩
    rw [Nat.div_add_mod]
    exact ⟨⟨hm, hσ⟩, hlt⟩
  · rintro ⟨k, hk, j, hj, ⟨⟨hb, hσ⟩, hlt⟩⟩
    have hm : s.mem (63 * k + j) = true := by rw [← testBit_limb s k j hj]; exact hb
    exact ⟨63 * k + j, mem_lt hm, ⟨hm, hσ⟩, hlt⟩

/-- The image under a permutation array: nauty's `permset`. -/
@[expose, inline] def permset (s : VSet n) (perm : Array Nat) : VSet n :=
  s.image (perm[·]!)

/-! # Images under renamings -/

@[simp] theorem image_empty (σ : Nat → Nat) : (empty : VSet n).image σ = empty := by
  refine ext fun w => ?_
  rw [mem_image, mem_empty, List.any_eq_false]
  intro v _
  simp

/-- Membership transports along a renaming. -/
theorem mem_image_apply (σ : Renaming n) (s : VSet n) {v : Nat} (hv : v < n) :
    (s.image σ).mem (σ v) = s.mem v := by
  rw [mem_image]
  rcases hb : s.mem v with _ | _
  · rw [List.any_eq_false]
    intro u _
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    rintro ⟨⟨hbu, heq⟩, _⟩
    have := σ.inj u v heq
    subst this
    rw [hb] at hbu
    cases hbu
  · rw [List.any_eq_true]
    refine ⟨v, List.mem_range.mpr hv, ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨hb, rfl⟩, (σ.maps v).mp hv⟩

/-- Images commute with insertion of a vertex. -/
theorem image_insert (σ : Renaming n) (s : VSet n) {v : Nat} (hv : v < n) :
    (s.insert v).image σ = (s.image σ).insert (σ v) := by
  refine ext fun w => ?_
  rw [mem_image, mem_insert, mem_image, Bool.eq_iff_iff, Bool.or_eq_true,
    List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨u, hu, hb⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, mem_insert,
      Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
    rcases hb with ⟨⟨hbu | ⟨huv, _⟩, hw⟩, hlt⟩
    · refine Or.inl ⟨u, hu, ?_⟩
      rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact ⟨⟨hbu, hw⟩, hlt⟩
    · subst huv
      right
      rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact ⟨hw, hlt⟩
  · rintro (⟨u, hu, hb⟩ | hw)
    · rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
      refine ⟨u, hu, ?_⟩
      rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, mem_insert,
        Bool.or_eq_true]
      exact ⟨⟨Or.inl hb.1.1, hb.1.2⟩, hb.2⟩
    · rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
      refine ⟨v, List.mem_range.mpr hv, ?_⟩
      rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        mem_insert_of_lt s hv, Bool.or_eq_true, beq_self_eq_true]
      exact ⟨⟨Or.inr rfl, hw.1⟩, hw.2⟩

/-- Images commute with intersection, for a renaming. -/
theorem image_inter (σ : Renaming n) (s t : VSet n) :
    (s.inter t).image σ = (s.image σ).inter (t.image σ) := by
  refine ext fun w => ?_
  rw [mem_inter, mem_image, mem_image, mem_image, Bool.eq_iff_iff, List.any_eq_true,
    Bool.and_eq_true, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨v, hv, hb⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, mem_inter,
      Bool.and_eq_true] at hb
    refine ⟨⟨v, hv, ?_⟩, ⟨v, hv, ?_⟩⟩
    · rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact ⟨⟨hb.1.1.1, hb.1.2⟩, hb.2⟩
    · rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact ⟨⟨hb.1.1.2, hb.1.2⟩, hb.2⟩
  · rintro ⟨⟨v, hv, hbv⟩, ⟨u, hu, hbu⟩⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hbv hbu
    have huv : u = v := σ.inj u v (hbu.1.2.trans hbv.1.2.symm)
    subst huv
    refine ⟨u, hu, ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, mem_inter,
      Bool.and_eq_true]
    exact ⟨⟨⟨hbv.1.1, hbu.1.1⟩, hbv.1.2⟩, hbv.2⟩

/-- Images under a renaming are injective. -/
theorem image_inj (σ : Renaming n) {s t : VSet n} (h : s.image σ = t.image σ) : s = t := by
  refine ext fun v => ?_
  rcases Nat.lt_or_ge v n with hv | hv
  · rw [← mem_image_apply σ s hv, ← mem_image_apply σ t hv, h]
  · rw [mem_of_ge hv, mem_of_ge hv]

theorem image_eq_empty_iff (σ : Renaming n) {s : VSet n} : s.image σ = empty ↔ s = empty :=
  ⟨fun h => image_inj σ (by rw [h, image_empty]), fun h => by rw [h, image_empty]⟩

/-- Emptiness of an intersection is preserved by a renaming. -/
theorem interIsEmpty_image (σ : Renaming n) (s t : VSet n) :
    (s.image σ).interIsEmpty (t.image σ) = s.interIsEmpty t := by
  rw [interIsEmpty_eq, interIsEmpty_eq, ← image_inter, Bool.eq_iff_iff, isEmpty_iff,
    isEmpty_iff, image_eq_empty_iff]

/-- Containment is preserved by a renaming. -/
theorem subset_image (σ : Renaming n) (s t : VSet n) :
    (s.image σ).subset (t.image σ) = s.subset t := by
  rw [Bool.eq_iff_iff, subset_iff_inter, subset_iff_inter, ← image_inter]
  exact ⟨fun h => image_inj σ h, fun h => by rw [h]⟩

/-- The member count is preserved by a renaming. -/
theorem card_image (σ : Renaming n) (s : VSet n) : (s.image σ).card = s.card := by
  rw [card_eq_countBelow, card_eq_countBelow, countBelow, countBelow,
    List.countP_eq_length_filter, List.countP_eq_length_filter]
  have hperm : List.Perm ((List.range n).filter (s.image σ).mem)
      (((List.range n).filter s.mem).map σ) := by
    refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
    · exact List.filter_sublist.nodup List.nodup_range
    · refine List.pairwise_map.mpr ?_
      refine (List.filter_sublist.nodup List.nodup_range).imp ?_
      intro a b hne heq
      exact hne (σ.inj a b heq)
    · intro w
      rw [List.mem_filter, List.mem_range, List.mem_map]
      constructor
      · rintro ⟨hw, hbit⟩
        rw [mem_image, List.any_eq_true] at hbit
        rcases hbit with ⟨v, hv, hb⟩
        rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
        refine ⟨v, ?_, hb.1.2⟩
        rw [List.mem_filter, List.mem_range]
        exact ⟨List.mem_range.mp hv, hb.1.1⟩
      · rintro ⟨v, hv, rfl⟩
        rw [List.mem_filter, List.mem_range] at hv
        exact ⟨(σ.maps v).mp hv.1, by rw [mem_image_apply σ s hv.1]; exact hv.2⟩
  rw [hperm.length_eq, List.length_map]

/-! # Identities of the empty set -/

@[simp] theorem inter_empty (s : VSet n) : s.inter empty = empty :=
  ext fun w => by rw [mem_inter, mem_empty, Bool.and_false]

@[simp] theorem empty_inter (s : VSet n) : (empty : VSet n).inter s = empty :=
  ext fun w => by rw [mem_inter, mem_empty, Bool.false_and]

@[simp] theorem union_empty (s : VSet n) : s.union empty = s :=
  ext fun w => by rw [mem_union, mem_empty, Bool.or_false]

@[simp] theorem empty_union (s : VSet n) : (empty : VSet n).union s = s :=
  ext fun w => by rw [mem_union, mem_empty, Bool.false_or]

theorem inter_self (s : VSet n) : s.inter s = s :=
  ext fun w => by rw [mem_inter, Bool.and_self]

/-! # Counts over disjoint unions -/

private theorem countP_or_disjoint {p q : Nat → Bool} :
    ∀ l : List Nat, (∀ i ∈ l, ¬(p i = true ∧ q i = true)) →
      l.countP (fun i => p i || q i) = l.countP p + l.countP q
  | [], _ => rfl
  | x :: l, h => by
    rw [List.countP_cons, List.countP_cons, List.countP_cons,
      countP_or_disjoint l fun i hi => h i (List.mem_cons_of_mem x hi)]
    rcases hp : p x with _ | _ <;> rcases hq : q x with _ | _
    · simp
    · simp; omega
    · simp; omega
    · exact absurd ⟨hp, hq⟩ (h x (List.mem_cons_self ..))

/-- Member counts add over a disjoint union. -/
theorem card_union_disjoint {a b : VSet n} (hd : a.inter b = empty) :
    (a.union b).card = a.card + b.card := by
  rw [card_eq_countBelow, card_eq_countBelow, card_eq_countBelow, countBelow, countBelow,
    countBelow]
  have hf : (a.union b).mem = fun i => a.mem i || b.mem i := funext fun i => mem_union a b i
  rw [hf]
  refine countP_or_disjoint _ fun i _ hpq => ?_
  have := congrArg (fun s => s.mem i) hd
  simp only [mem_inter, mem_empty, hpq.1, hpq.2] at this
  cases this

theorem inter_union_distrib (a b x : VSet n) :
    (a.union b).inter x = (a.inter x).union (b.inter x) :=
  ext fun w => by
    rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
    cases a.mem w <;> cases b.mem w <;> cases x.mem w <;> rfl

/-- Counts into a set add over a disjoint union. -/
theorem cardInter_union_disjoint {a b : VSet n} (hd : a.inter b = empty) (x : VSet n) :
    (a.union b).cardInter x = a.cardInter x + b.cardInter x := by
  rw [cardInter_eq, cardInter_eq, cardInter_eq, inter_union_distrib]
  refine card_union_disjoint (ext fun w => ?_)
  have := congrArg (fun s => s.mem w) hd
  simp only [mem_inter, mem_empty] at this ⊢
  cases ha : a.mem w <;> cases hb : b.mem w <;> simp_all

/-! # Singletons -/

theorem mem_singleton (u v : Nat) :
    ((empty : VSet n).insert u).mem v = (u == v && decide (u < n)) := by
  rw [mem_insert, mem_empty, Bool.false_or]

theorem inter_comm (s t : VSet n) : s.inter t = t.inter s :=
  ext fun w => by rw [mem_inter, mem_inter, Bool.and_comm]

theorem union_comm (s t : VSet n) : s.union t = t.union s :=
  ext fun w => by rw [mem_union, mem_union, Bool.or_comm]

theorem union_assoc (s t u : VSet n) : (s.union t).union u = s.union (t.union u) :=
  ext fun w => by rw [mem_union, mem_union, mem_union, mem_union, Bool.or_assoc]

theorem cardInter_comm (s t : VSet n) : s.cardInter t = t.cardInter s := by
  rw [cardInter_eq, cardInter_eq, inter_comm]

/-- The count into a singleton is the membership bit. -/
theorem cardInter_singleton (u : Nat) (x : VSet n) :
    ((empty : VSet n).insert u).cardInter x = if x.mem u then 1 else 0 := by
  rw [cardInter_eq, card_eq_countBelow, countBelow]
  rcases hb : x.mem u with _ | _
  · have hz : (List.range n).countP
        (fun v => (((empty : VSet n).insert u).inter x).mem v) = 0 := by
      rw [List.countP_eq_zero]
      intro v _
      rw [mem_inter, mem_singleton]
      rcases Decidable.em (u = v) with rfl | hne
      · simp [hb]
      · simp [hne]
    rw [hz]
    simp
  · have hu : u < n := mem_lt hb
    rw [List.countP_eq_length_filter]
    have hsplit : List.range n = List.range u ++ u :: List.range' (u + 1) (n - (u + 1)) := by
      have h1 := @List.range'_append 0 u (n - u) 1
      rw [Nat.zero_add, Nat.one_mul, show u + (n - u) = n by omega] at h1
      rw [List.range_eq_range', ← h1, ← List.range_eq_range',
        show n - u = (n - (u + 1)) + 1 by omega, List.range'_succ]
    have hfilter : (List.range n).filter
        (fun v => (((empty : VSet n).insert u).inter x).mem v) = [u] := by
      rw [hsplit, List.filter_append, List.filter_cons_of_pos (by
        rw [mem_inter, mem_singleton, beq_self_eq_true, decide_eq_true hu, hb]
        rfl)]
      have hl : (List.range u).filter
          (fun v => (((empty : VSet n).insert u).inter x).mem v) = [] := by
        rw [List.filter_eq_nil_iff]
        intro v hv
        rw [List.mem_range] at hv
        rw [mem_inter, mem_singleton, show (u == v) = false by
          simp only [beq_eq_false_iff_ne, ne_eq]; omega]
        simp
      have hr : (List.range' (u + 1) (n - (u + 1))).filter
          (fun v => (((empty : VSet n).insert u).inter x).mem v) = [] := by
        rw [List.filter_eq_nil_iff]
        intro v hv
        rw [List.mem_range'] at hv
        rw [mem_inter, mem_singleton, show (u == v) = false by
          simp only [beq_eq_false_iff_ne, ne_eq]; omega]
        simp
      rw [hl, hr]
      rfl
    rw [hfilter]
    rfl

/-! # Cardinality comparisons -/

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
have the same length. -/
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

/-- A subset has no more members. -/
theorem card_le_of_subset {s t : VSet n} (h : s.subset t = true) : s.card ≤ t.card := by
  rw [card_eq_countBelow, card_eq_countBelow, countBelow, countBelow]
  exact countP_le_of_imp fun v _ hv => subset_iff.mp h v hv

/-- A set with no members is empty. -/
theorem eq_empty_of_card_eq_zero {s : VSet n} (h : s.card = 0) : s = empty := by
  rw [eq_empty_iff]
  intro v
  rcases Nat.lt_or_ge v n with hv | hv
  · rw [card_eq_countBelow, countBelow, List.countP_eq_zero] at h
    simpa using h v (List.mem_range.mpr hv)
  · exact mem_of_ge hv

/-- A subset with the same member count is the whole set. -/
theorem eq_of_subset_of_card_eq {s t : VSet n} (h : s.subset t = true)
    (hcard : s.card = t.card) : s = t := by
  have hlen : ((List.range n).filter s.mem).length = ((List.range n).filter t.mem).length := by
    have := hcard
    rw [card_eq_countBelow, card_eq_countBelow, countBelow, countBelow,
      List.countP_eq_length_filter, List.countP_eq_length_filter] at this
    exact this
  have hfilter : (List.range n).filter s.mem = (List.range n).filter t.mem :=
    filter_eq_of_imp_of_length_eq (fun v _ hv => subset_iff.mp h v hv) hlen
  refine ext fun v => ?_
  rcases Nat.lt_or_ge v n with hv | hv
  · have hiff := congrArg (fun l => v ∈ l) hfilter
    simp only [List.mem_filter, List.mem_range, hv, true_and, eq_iff_iff] at hiff
    rcases hs : s.mem v with _ | _
    · rcases ht : t.mem v with _ | _
      · rfl
      · exact absurd (hiff.mpr ht) (by simp [hs])
    · exact (subset_iff.mp h v hs).symm
  · rw [mem_of_ge hv, mem_of_ge hv]

/-! # The `Nat` bitset view

The certificate checker and the kernel work with adjacency rows as
natural numbers (bit `v` for vertex `v`), where the kernel's bignum
arithmetic is fast and arrays are not. `toNat` is the boundary. -/

/-- The bitset with bit `v` set exactly for the members `v`. -/
@[expose] def toNat (s : VSet n) : Nat :=
  s.limbs.foldr (fun limb acc => (acc <<< 63) ||| limb) 0

private theorem testBit_foldr_limbs :
    ∀ (L : List Nat), (∀ x ∈ L, x < 2 ^ 63) → ∀ v : Nat,
      (L.foldr (fun limb acc => (acc <<< 63) ||| limb) 0).testBit v =
        (L.getD (v / 63) 0).testBit (v % 63)
  | [], _, v => by simp [List.getD]
  | l :: ls, hb, v => by
    rw [List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases Nat.lt_or_ge v 63 with hlt | hge
    · rw [decide_eq_false (by omega), Bool.false_and, Bool.false_or, Nat.div_eq_of_lt hlt,
        Nat.mod_eq_of_lt hlt]
      simp [List.getD]
    · rw [decide_eq_true hge, Bool.true_and,
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hb l List.mem_cons_self)
          (Nat.pow_le_pow_right (by omega) hge)), Bool.or_false,
        testBit_foldr_limbs ls (fun x hx => hb x (List.mem_cons_of_mem _ hx)),
        show (v - 63) / 63 = v / 63 - 1 by omega, show (v - 63) % 63 = v % 63 by omega]
      obtain ⟨q, hq⟩ : ∃ q, v / 63 = q + 1 := ⟨v / 63 - 1, by omega⟩
      rw [hq]
      simp [List.getD]

theorem testBit_toNat (s : VSet n) (v : Nat) : s.toNat.testBit v = s.mem v := by
  rw [toNat, ← Array.foldr_toList, testBit_foldr_limbs _ (fun x hx => by
    rw [List.mem_iff_getElem] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Array.getElem_toList, ← getElem!_pos]
    exact s.bounded i), mem_eq, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge (v / 63) s.limbs.size with h | h
  · rw [List.getElem?_eq_getElem (by simpa using h), Option.getD_some, Array.getElem_toList,
      ← getElem!_pos]
  · rw [List.getElem?_eq_none (by simpa using h), Option.getD_none,
      getElem!_neg _ _ (by omega)]
    rfl

theorem toNat_lt (s : VSet n) : s.toNat < 2 ^ n := by
  refine lt_two_pow_of_bits fun v hv => ?_
  rw [testBit_toNat]
  exact mem_of_ge hv

theorem toNat_inj {s t : VSet n} (h : s.toNat = t.toNat) : s = t :=
  ext fun v => by rw [← testBit_toNat, ← testBit_toNat, h]

/-! # Cardinality under insert and erase -/

theorem countBelow_succ (s : VSet n) (k : Nat) :
    s.countBelow (k + 1) = s.countBelow k + (if s.mem k then 1 else 0) := by
  rw [countBelow, countBelow, List.range_succ, List.countP_append, List.countP_cons,
    List.countP_nil]
  rcases h : s.mem k with _ | _ <;> simp

theorem countBelow_congr {s t : VSet n} {k : Nat}
    (h : ∀ i, i < k → s.mem i = t.mem i) : s.countBelow k = t.countBelow k := by
  induction k with
  | zero => rfl
  | succ m ih =>
    rw [countBelow_succ, countBelow_succ, ih fun i hi => h i (by omega), h m (by omega)]

theorem countBelow_le (s : VSet n) (k : Nat) : s.countBelow k ≤ k := by
  rw [countBelow]
  exact Nat.le_trans List.countP_le_length (Nat.le_of_eq List.length_range)

/-- A set has at most `n` members. -/
theorem card_le (s : VSet n) : s.card ≤ n := by
  rw [card_eq_countBelow]
  exact countBelow_le s n

theorem countBelow_insert_le (s : VSet n) (v k : Nat) :
    (s.insert v).countBelow k ≤ s.countBelow k + 1 := by
  induction k with
  | zero => simp [countBelow]
  | succ m ih =>
    rw [countBelow_succ, countBelow_succ, mem_insert]
    rcases hv : (v == m) with _ | _
    · rcases h : s.mem m with _ | _ <;> simp <;> omega
    · have hvm : v = m := by simpa using hv
      rw [countBelow_congr (t := s) fun i hi => by
        rw [mem_insert, show (v == i) = false from by simp [show v ≠ i from by omega],
          Bool.false_and, Bool.or_false]]
      rcases h : s.mem m with _ | _ <;> rcases hd : decide (v < n) with _ | _ <;> simp <;>
        omega

/-- Inserting adds at most one member. -/
theorem card_insert_le (s : VSet n) (v : Nat) : (s.insert v).card ≤ s.card + 1 := by
  rw [card_eq_countBelow, card_eq_countBelow]
  exact countBelow_insert_le s v n

theorem countBelow_erase_of_mem {s : VSet n} {v : Nat} (h : s.mem v = true) :
    ∀ k, v < k → (s.erase v).countBelow k + 1 = s.countBelow k
  | 0, hv => absurd hv (by omega)
  | m + 1, hv => by
    rcases Decidable.em (v = m) with heq | hne
    · rw [countBelow_succ, countBelow_succ, mem_erase,
        show (v == m) = true from by simp [heq], Bool.not_true, Bool.and_false,
        countBelow_congr (t := s) fun i hi => by
          rw [mem_erase, show (v == i) = false from by simp [show v ≠ i from by omega],
            Bool.not_false, Bool.and_true],
        show s.mem m = true from heq ▸ h]
      simp
    · rw [countBelow_succ, countBelow_succ, mem_erase,
        show (v == m) = false from by simp [hne], Bool.not_false, Bool.and_true]
      have := countBelow_erase_of_mem h m (by omega)
      omega

/-- Erasing a member removes exactly one. -/
theorem card_erase_of_mem {s : VSet n} {v : Nat} (h : s.mem v = true) :
    (s.erase v).card + 1 = s.card := by
  rw [card_eq_countBelow, card_eq_countBelow]
  exact countBelow_erase_of_mem h n (mem_lt h)

/-- Erasing never adds members. -/
theorem card_erase_le (s : VSet n) (v : Nat) : (s.erase v).card ≤ s.card :=
  card_le_of_subset (subset_iff.mpr fun w hw => by
    rw [mem_erase] at hw
    exact ((Bool.and_eq_true _ _).mp hw).1)

/-- Inserting a member changes nothing. -/
theorem insert_of_mem {s : VSet n} {v : Nat} (h : s.mem v = true) : s.insert v = s :=
  ext fun w => by
    rw [mem_insert]
    rcases Decidable.em (v = w) with rfl | hne
    · rw [h, Bool.true_or]
    · rw [show (v == w) = false from by simp [hne], Bool.false_and, Bool.or_false]

instance : Repr (VSet n) := ⟨fun s _ => repr s.toNat⟩

end VSet

end Hex.GraphIso.Nauty
