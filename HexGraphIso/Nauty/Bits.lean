/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

This file contains code translated from the nauty 2.9.3 sources
(https://users.cecs.anu.edu.au/~bdm/nauty/), copyright Brendan McKay and Adolfo
Piperno, released under the Apache 2.0 license.
-/

module

public import HexBasic.Conditional
public import Std

public section

/-!
Vertex-set primitives for the nauty-compatible search.

nauty stores a vertex set as packed setwords with vertex `0` at the most
significant bit, so unsigned setword comparison is lexicographic in vertex
order and `FIRSTBITNZ` returns the least vertex. This module models a
vertex set as a `Nat` bitset with bit `v` for vertex `v` and provides the
same observable operations: least-element extraction, ascending iteration
(`nextElem`), population count, and the vertex-order row comparison used
by `testcanlab`. The packed-word representation may replace this one later
only with a proof that no observable result changes.
-/

namespace Hex.GraphIso.Nauty

/-- The index of the least set bit. Returns `0` for the empty set; callers
guard on nonemptiness. Structurally recursive on an always-sufficient
fuel so the kernel can replay it. -/
@[expose] def lowBit (s : Nat) : Nat :=
  go (s + 1) s
where
  go : Nat → Nat → Nat
    | 0, _ => 0
    | fuel + 1, s =>
      if s == 0 then 0
      else if s % 2 == 1 then 0
      else 1 + go fuel (s / 2)

theorem lowBit_go_congr :
    ∀ (f₁ : Nat) {f₂ s : Nat}, s < f₁ → s < f₂ →
      lowBit.go f₁ s = lowBit.go f₂ s
  | f₁ + 1, f₂ + 1, s, h₁, h₂ => by
    rw [lowBit.go, lowBit.go]
    rcases Decidable.em (s = 0) with rfl | hs
    · simp
    · rcases Decidable.em (s % 2 = 1) with ho | ho
      · simp [hs, ho]
      · have hlt : s / 2 < f₁ ∧ s / 2 < f₂ := by omega
        simp only [beq_iff_eq, hs, ho, ite_false]
        rw [lowBit_go_congr f₁ (f₂ := f₂) hlt.1 hlt.2]

/-- The unconditional unfolding of `lowBit`. -/
theorem lowBit_eq (s : Nat) :
    lowBit s = if s = 0 then 0 else if s % 2 = 1 then 0
      else 1 + lowBit (s / 2) := by
  rw [lowBit, lowBit, lowBit.go]
  rcases Decidable.em (s = 0) with rfl | hs
  · simp
  · rcases Decidable.em (s % 2 = 1) with ho | ho
    · simp [hs, ho]
    · simp only [beq_iff_eq, hs, ho, ite_false]
      rw [lowBit_go_congr s (f₂ := s / 2 + 1) (by omega) (by omega)]

/-- `lowBit` of every nonzero byte, by the specification itself. -/
def lbByte : Array Nat :=
  ((List.range 256).map lowBit).toArray

def lowBitGo (s shift : Nat) : Nat :=
  if s = 0 then 0
  else if s % 256 = 0 then lowBitGo (s >>> 8) (shift + 8)
  else shift + lbByte[s % 256]!
termination_by s
decreasing_by
  simp only [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_self (by omega) (by omega)

def lowBitFast (s : Nat) : Nat :=
  lowBitGo s 0

theorem lbByte_get {b : Nat} (h : b < 256) : lbByte[b]! = lowBit b := by
  rw [lbByte, getElem!_pos _ _ (by simpa using h)]
  simp

@[simp] theorem lowBit_zero : lowBit 0 = 0 := by
  rw [lowBit_eq]
  simp

/-- `lowBit` looks only at the low bits while they are not all
zero. -/
theorem lowBit_mod_pow :
    ∀ (k : Nat) {s : Nat}, s % 2 ^ k ≠ 0 → lowBit s = lowBit (s % 2 ^ k)
  | 0, s, h => absurd (Nat.mod_one s) h
  | k + 1, s, h => by
    have hs : s ≠ 0 := fun hz => h (by simp [hz])
    have h2 : s % 2 ^ (k + 1) % 2 = s % 2 :=
      Nat.mod_mod_of_dvd s ⟨2 ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have hdiv : s % 2 ^ (k + 1) / 2 = s / 2 % 2 ^ k := by
      rw [hp]
      exact Nat.mod_mul_right_div_self s 2 (2 ^ k)
    rcases Decidable.em (s % 2 = 1) with ho | ho
    · rw [lowBit_eq s, lowBit_eq (s % 2 ^ (k + 1))]
      simp [hs, h, ho, h2]
    · have he : s % 2 = 0 := by omega
      have hm : s / 2 % 2 ^ k ≠ 0 := by
        intro hz
        rw [← hdiv] at hz
        have : s % 2 ^ (k + 1) < 2 := by omega
        omega
      rw [lowBit_eq s, lowBit_eq (s % 2 ^ (k + 1))]
      simp only [hs, h, he, h2, ite_false, ite_eq_right (by omega : ¬(0 = 1))]
      rw [hdiv, lowBit_mod_pow k hm]

/-- `lowBit` steps over all-zero low bits. -/
theorem lowBit_shift_pow :
    ∀ (k : Nat) {s : Nat}, s ≠ 0 → s % 2 ^ k = 0 →
      lowBit s = k + lowBit (s / 2 ^ k)
  | 0, s, _, _ => by simp
  | k + 1, s, hs, h => by
    have h2 : s % 2 = 0 := by
      have := Nat.mod_mod_of_dvd s
        (⟨2 ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩ : 2 ∣ 2 ^ (k + 1))
      omega
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have h' : s % (2 * 2 ^ k) = 0 := by rw [← hp]; exact h
    have hdvd : s / 2 % 2 ^ k = 0 := by
      rw [← Nat.mod_mul_right_div_self s 2 (2 ^ k), h', Nat.zero_div]
    have hhalf : s / 2 ≠ 0 := by omega
    rw [lowBit_eq s]
    simp only [hs, h2, ite_false, ite_eq_right (by omega : ¬(0 = 1))]
    rw [lowBit_shift_pow k hhalf hdvd, Nat.div_div_eq_div_mul, ← hp]
    omega

theorem lowBitGo_eq (s shift : Nat) :
    lowBitGo s shift = if s = 0 then 0 else shift + lowBit s := by
  induction s, shift using lowBitGo.induct with
  | case1 shift => rw [lowBitGo]; simp
  | case2 s shift hs hb ih =>
    have h256 : (2 : Nat) ^ 8 = 256 := by rfl
    have hge : s / 256 ≠ 0 := by
      have : 256 ∣ s := Nat.dvd_of_mod_eq_zero hb
      rcases this with ⟨c, rfl⟩
      simp only [Nat.mul_div_cancel_left _ (by omega : 0 < 256)]
      omega
    have h8 : s >>> 8 = s / 256 := by
      rw [Nat.shiftRight_eq_div_pow, h256]
    have hsplit : lowBit s = 8 + lowBit (s / 256) := by
      rw [lowBit_shift_pow 8 hs (by rw [h256]; exact hb), h256]
    rw [lowBitGo, ite_eq_right hs, ite_eq_left hb, ih, h8, ite_eq_right hge, ite_eq_right hs,
      hsplit]
    omega
  | case3 s shift hs hb =>
    have h256 : (2 : Nat) ^ 8 = 256 := by rfl
    rw [lowBitGo, ite_eq_right hs, ite_eq_right hb, ite_eq_right hs,
      lbByte_get (Nat.mod_lt s (by omega))]
    have := lowBit_mod_pow 8 (s := s) (by rw [h256]; exact hb)
    rw [h256] at this
    rw [← this]

@[csimp] theorem lowBit_eq_lowBitFast : @lowBit = @lowBitFast := by
  funext s
  rw [lowBitFast, lowBitGo_eq]
  rcases Decidable.em (s = 0) with rfl | hs
  · simp
  · simp [hs]

/-- The number of set bits. Structurally recursive on an
always-sufficient fuel so the kernel can replay it. -/
@[expose] def popCount (s : Nat) : Nat :=
  go (s + 1) s
where
  go : Nat → Nat → Nat
    | 0, _ => 0
    | fuel + 1, s =>
      if s == 0 then 0
      else s % 2 + go fuel (s / 2)

theorem popCount_go_congr :
    ∀ (f₁ : Nat) {f₂ s : Nat}, s < f₁ → s < f₂ →
      popCount.go f₁ s = popCount.go f₂ s
  | f₁ + 1, f₂ + 1, s, h₁, h₂ => by
    rw [popCount.go, popCount.go]
    rcases Decidable.em (s = 0) with rfl | hs
    · simp
    · have hlt : s / 2 < f₁ ∧ s / 2 < f₂ := by omega
      simp only [beq_iff_eq, hs, ite_false]
      rw [popCount_go_congr f₁ (f₂ := f₂) hlt.1 hlt.2]

/-- The unconditional unfolding of `popCount`: also valid at zero. -/
theorem popCount_eq (s : Nat) :
    popCount s = s % 2 + popCount (s / 2) := by
  rw [popCount, popCount, popCount.go]
  rcases Decidable.em (s = 0) with rfl | hs
  · simp [popCount.go]
  · simp only [beq_iff_eq, hs, ite_false]
    rw [popCount_go_congr s (f₂ := s / 2 + 1) (by omega) (by omega)]

@[simp] theorem popCount_zero : popCount 0 = 0 := by
  rw [popCount, popCount.go]
  simp

/-! # Byte-chunked runtime implementations

The per-bit recursions above are the proof- and kernel-facing
definitions. The compiled code runs the byte-chunked versions below,
attached by `csimp` equalities: one big-number operation per byte
instead of per bit, with the per-byte answers read from tables that
are definitionally maps of the specification. -/

/-- `popCount` of every byte, by the specification itself. -/
def pcByte : Array Nat :=
  ((List.range 256).map popCount).toArray

def popCountGo (s acc : Nat) : Nat :=
  if s = 0 then acc
  else popCountGo (s >>> 8) (acc + pcByte[s % 256]!)
termination_by s
decreasing_by
  simp only [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_self (by omega) (by omega)

def popCountFast (s : Nat) : Nat :=
  popCountGo s 0

theorem pcByte_get {b : Nat} (h : b < 256) : pcByte[b]! = popCount b := by
  rw [pcByte, getElem!_pos _ _ (by simpa using h)]
  simp

/-- `popCount` splits at any power-of-two boundary. -/
theorem popCount_split_pow :
    ∀ (k s : Nat), popCount s = popCount (s % 2 ^ k) + popCount (s / 2 ^ k)
  | 0, s => by simp [Nat.mod_one]
  | k + 1, s => by
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have h1 : s % 2 ^ (k + 1) % 2 = s % 2 :=
      Nat.mod_mod_of_dvd s ⟨2 ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    have h2 : s % 2 ^ (k + 1) / 2 = s / 2 % 2 ^ k := by
      rw [hp]
      exact Nat.mod_mul_right_div_self s 2 (2 ^ k)
    have h3 : s / 2 / 2 ^ k = s / 2 ^ (k + 1) := by
      rw [Nat.div_div_eq_div_mul, ← hp]
    rw [popCount_eq s, popCount_split_pow k (s / 2),
      popCount_eq (s % 2 ^ (k + 1)), h1, h2, h3]
    omega

/-- `popCount` splits at the byte boundary. -/
theorem popCount_split (s : Nat) :
    popCount s = popCount (s % 256) + popCount (s >>> 8) := by
  rw [Nat.shiftRight_eq_div_pow]
  exact popCount_split_pow 8 s

theorem popCountGo_eq (s acc : Nat) :
    popCountGo s acc = acc + popCount s := by
  induction s, acc using popCountGo.induct with
  | case1 acc => rw [popCountGo]; simp
  | case2 s acc hs ih =>
    rw [popCountGo, ite_eq_right hs, ih, pcByte_get (Nat.mod_lt s (by omega))]
    have := popCount_split s
    omega

@[csimp] theorem popCount_eq_popCountFast :
    @popCount = @popCountFast := by
  funext s
  rw [popCountFast, popCountGo_eq, Nat.zero_add]

/-- Membership test. -/
@[expose, inline] def elem (s v : Nat) : Bool :=
  s.testBit v

/-- Insertion. -/
@[expose, inline] def insert (s v : Nat) : Nat :=
  s ||| (1 <<< v)

/-- Deletion. -/
@[expose, inline] def erase (s v : Nat) : Nat :=
  if s.testBit v then s ^^^ (1 <<< v) else s

/-- The least element of `s` greater than `pos`, or `none`: nauty's
`nextelement`, which iterates a set in ascending vertex order. `pos = none`
starts from the least element. -/
@[expose] def nextElem (s : Nat) (pos : Option Nat) : Option Nat :=
  let s' :=
    match pos with
    | none => s
    | some p => (s >>> (p + 1)) <<< (p + 1)
  if s' = 0 then none else some (lowBit s')

/-- All elements of `s` below `n` in ascending order. -/
@[expose] def toList (s n : Nat) : List Nat :=
  (List.range n).filter s.testBit

/-- One byte of `toList`: prepend the set positions `base + k`,
`k < min 8 cnt`, in ascending order (so the whole accumulator is
descending and one final reverse restores order). -/
def toListByteGo (b base cnt k : Nat) (acc : List Nat) : List Nat :=
  if k ≥ 8 ∨ k ≥ cnt then acc
  else toListByteGo b base cnt (k + 1)
    (if b.testBit k then (base + k) :: acc else acc)
termination_by 8 - k
decreasing_by omega

def toListByte (b base cnt : Nat) (acc : List Nat) : List Nat :=
  toListByteGo b base cnt 0 acc

/-- The byte-chunked `toList` walk: one big-number shift per byte,
early exit once the remainder is empty. Accumulates reversed; one
final reverse restores ascending order. -/
def toListGo (base cnt s : Nat) (acc : List Nat) : List Nat :=
  if cnt = 0 ∨ s = 0 then acc
  else toListGo (base + 8) (cnt - 8) (s >>> 8)
    (toListByte (s % 256) base cnt acc)
termination_by cnt
decreasing_by omega

def toListFast (s n : Nat) : List Nat :=
  (toListGo 0 n s []).reverse

theorem toListByteGo_eq (b base cnt : Nat) :
    ∀ (k : Nat) (acc : List Nat),
      toListByteGo b base cnt k acc =
        (((List.range' k (min 8 cnt - k)).filter b.testBit).map
          (base + ·)).reverse ++ acc := by
  refine toListByteGo.induct b base cnt
    (fun k acc => toListByteGo b base cnt k acc =
      (((List.range' k (min 8 cnt - k)).filter b.testBit).map
        (base + ·)).reverse ++ acc) ?_ ?_
  · intro k acc h
    rw [toListByteGo, ite_eq_left h, (by omega : min 8 cnt - k = 0)]
    simp [List.range']
  · intro k acc h ih
    rw [toListByteGo, ite_eq_right h,
      (by omega : min 8 cnt - k = (min 8 cnt - (k + 1)) + 1),
      List.range'_succ]
    rcases htb : b.testBit k with _ | _
    · simp only [htb] at ih ⊢
      rw [dite_eq_right (by simp : ¬(false = true))] at ih
      rw [ite_eq_right (by simp : ¬(false = true)), ih]
      simp [htb]
    · simp only [htb, reduceDIte, reduceIte] at ih ⊢
      rw [ih]
      simp [htb, List.append_assoc]

theorem toListGo_eq (base cnt s : Nat) (acc : List Nat) :
    toListGo base cnt s acc =
      (((List.range cnt).filter s.testBit).map
        (base + ·)).reverse ++ acc := by
  induction base, cnt, s, acc using toListGo.induct with
  | case1 base cnt s acc h =>
    rw [toListGo, ite_eq_left h]
    rcases h with rfl | rfl
    · simp
    · simp [Nat.zero_testBit]
  | case2 base cnt s acc h ih =>
    have hc : cnt ≠ 0 := fun hz => h (Or.inl hz)
    rw [toListGo, ite_eq_right h, ih, toListByte, toListByteGo_eq,
      Nat.sub_zero]
    rcases Decidable.em (cnt ≤ 8) with h8 | h8
    · have hz : cnt - 8 = 0 := by omega
      have hmin : min 8 cnt = cnt := by omega
      have hbyte : List.filter (s % 256).testBit (List.range cnt) =
          List.filter s.testBit (List.range cnt) :=
        List.filter_congr fun x hx => by
          have hx8 : x < 8 := by
            have := List.mem_range.mp hx
            omega
          rw [(by rfl : (256 : Nat) = 2 ^ 8), Nat.testBit_mod_two_pow]
          simp [hx8]
      rw [hz, hmin]
      simp only [List.range_zero, List.filter_nil, List.map_nil,
        List.reverse_nil, List.nil_append, ← List.range_eq_range']
      rw [hbyte]
    · have hmin : min 8 cnt = 8 := by omega
      have hr : List.range cnt =
          List.range 8 ++ (List.range (cnt - 8)).map (fun j => 8 + j) := by
        rw [← List.range_add]
        congr 1
        omega
      have hmap : ((fun x => base + x) ∘ fun j => 8 + j) =
          fun j => base + 8 + j := by
        funext j
        simp only [Function.comp]
        omega
      have hpred : (s.testBit ∘ fun j => 8 + j) = (s >>> 8).testBit := by
        funext j
        simp [Function.comp, Nat.testBit_shiftRight]
      have hbyte : List.filter (s % 256).testBit (List.range 8) =
          List.filter s.testBit (List.range 8) :=
        List.filter_congr fun x hx => by
          have hx8 : x < 8 := List.mem_range.mp hx
          rw [(by rfl : (256 : Nat) = 2 ^ 8), Nat.testBit_mod_two_pow]
          simp [hx8]
      rw [hmin, hr, List.filter_append, List.filter_map,
        List.map_append, List.map_map, List.reverse_append,
        List.append_assoc, ← List.range_eq_range', hmap, hpred, hbyte]

@[csimp] theorem toList_eq_toListFast : @toList = @toListFast := by
  funext s n
  rw [toListFast, toListGo_eq, List.append_nil, List.reverse_reverse,
    toList]
  have hid : ∀ l : List Nat, l.map (0 + ·) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih => simp [Nat.zero_add]
  rw [hid]

/-- nauty's row order: rows are compared as packed setwords with vertex `0`
most significant, so the least differing vertex decides and the row
containing it is greater. -/
@[expose] def rowCmp (a b : Nat) : Ordering :=
  if a = b then
    .eq
  else if a.testBit (lowBit (a ^^^ b)) then
    .gt
  else
    .lt

/-- The image of a vertex set under a vertex map: nauty's `permset`. -/
@[expose] def permset (s : Nat) (perm : Array Nat) (n : Nat) : Nat :=
  (List.range n).foldl
    (fun acc v => if s.testBit v then insert acc perm[v]! else acc) 0

end Hex.GraphIso.Nauty
