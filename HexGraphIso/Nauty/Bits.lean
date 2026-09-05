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

The word layer under the packed vertex sets of `VSet`: the least set
bit (`lowBit`, nauty's `FIRSTBITNZ`), the population count
(`popCount`, nauty's `POPCOUNT`), and the byte-chunked walk that lists
the set bits of a word, each with a per-bit specification the kernel can
replay, a byte-table implementation the compiled code runs, and the
`csimp` equality between them. A word here is a natural number; the
implementations are only ever applied to 63-bit limbs, where every
operation is a scalar one.
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
      simp only [hs, h, he, h2, ite_false, if_neg (by omega : ¬(0 = 1))]
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
    simp only [hs, h2, ite_false, if_neg (by omega : ¬(0 = 1))]
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
    rw [lowBitGo, if_neg hs, if_pos hb, ih, h8, if_neg hge, if_neg hs,
      hsplit]
    omega
  | case3 s shift hs hb =>
    have h256 : (2 : Nat) ^ 8 = 256 := by rfl
    rw [lowBitGo, if_neg hs, if_neg hb, if_neg hs,
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
    rw [popCountGo, if_neg hs, ih, pcByte_get (Nat.mod_lt s (by omega))]
    have := popCount_split s
    omega

@[csimp] theorem popCount_eq_popCountFast :
    @popCount = @popCountFast := by
  funext s
  rw [popCountFast, popCountGo_eq, Nat.zero_add]

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
    rw [toListByteGo, if_pos h, (by omega : min 8 cnt - k = 0)]
    simp [List.range']
  · intro k acc h ih
    rw [toListByteGo, if_neg h,
      (by omega : min 8 cnt - k = (min 8 cnt - (k + 1)) + 1),
      List.range'_succ]
    rcases htb : b.testBit k with _ | _
    · simp only [htb] at ih ⊢
      rw [dif_neg (by simp : ¬(false = true))] at ih
      rw [if_neg (by simp : ¬(false = true)), ih]
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
    rw [toListGo, if_pos h]
    rcases h with rfl | rfl
    · simp
    · simp [Nat.zero_testBit]
  | case2 base cnt s acc h ih =>
    have hc : cnt ≠ 0 := fun hz => h (Or.inl hz)
    rw [toListGo, if_neg h, ih, toListByte, toListByteGo_eq,
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

/-! # Word-level lemmas

Bit facts about a single word that the packed vertex-set layer
(`VSet`) builds its membership lemmas from. -/

/-- The number of set bits below `n`. -/
@[expose] def bitCount (n s : Nat) : Nat :=
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

/-- The least set bit is a member. -/
theorem testBit_lowBit : ∀ (s : Nat), s ≠ 0 → s.testBit (lowBit s) = true
  | s, hs => by
    rw [lowBit_eq, ite_eq_right hs]
    rcases Decidable.em (s % 2 = 1) with ho | ho
    · rw [ite_eq_left ho]
      simp [Nat.testBit_zero, ho]
    · rw [ite_eq_right ho]
      have hs2 : s / 2 ≠ 0 := by omega
      rw [Nat.add_comm 1 (lowBit (s / 2)), Nat.testBit_add_one]
      exact testBit_lowBit (s / 2) hs2
  termination_by s => s
  decreasing_by omega

/-- A set whose bits all lie below `n` is bounded by `2 ^ n`. -/
theorem lt_two_pow_of_bits {s n : Nat}
    (h : ∀ i, n ≤ i → s.testBit i = false) : s < 2 ^ n := by
  rcases Nat.lt_or_ge s (2 ^ n) with hlt | hge
  · exact hlt
  · rcases Nat.exists_ge_and_testBit_of_ge_two_pow hge with ⟨i, hi, hb⟩
    rw [h i hi] at hb
    exact absurd hb (by simp)

/-- Entry bound after an insertion. -/
theorem or_shift_lt {x : Nat} (hx : x < 2 ^ 63) {j : Nat}
    (hj : j < 63) : x ||| (1 <<< j) < 2 ^ 63 := by
  refine lt_two_pow_of_bits fun i hi => ?_
  rw [Nat.testBit_or, testBit_one_shift,
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx
      (Nat.pow_le_pow_right (by omega) hi))]
  simp
  omega

theorem testBit_lt_lowBit :
    ∀ (s i : Nat), i < lowBit s → s.testBit i = false
  | s, i, hi => by
    rw [lowBit_eq] at hi
    rcases Decidable.em (s = 0) with rfl | hs
    · rw [ite_eq_left rfl] at hi
      omega
    · rw [ite_eq_right hs] at hi
      rcases Decidable.em (s % 2 = 1) with ho | ho
      · rw [ite_eq_left ho] at hi
        omega
      · rw [ite_eq_right ho] at hi
        rcases i with _ | j
        · simp only [Nat.testBit_zero]
          simp
          omega
        · rw [Nat.testBit_add_one]
          exact testBit_lt_lowBit (s / 2) j (by omega)
  termination_by s => s
  decreasing_by omega

theorem lowBit_eq_of {s d : Nat} (hd : s.testBit d = true)
    (hlow : ∀ i, i < d → s.testBit i = false) : lowBit s = d := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hd
    simp at hd
  rcases Nat.lt_trichotomy (lowBit s) d with h | h | h
  · exact absurd (testBit_lowBit s hs0) (by rw [hlow _ h]; simp)
  · exact h
  · exact absurd hd (by rw [testBit_lt_lowBit s d h]; simp)

theorem xor_ne_zero_of_ne {a b : Nat} (hab : a ≠ b) : a ^^^ b ≠ 0 := by
  intro h
  refine hab (Nat.eq_of_testBit_eq fun i => ?_)
  have hx := congrArg (fun s => Nat.testBit s i) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at hx
  rcases ha : a.testBit i with _ | _ <;>
    rcases hb : b.testBit i with _ | _ <;> simp_all

theorem testBit_eq_of_lt_lowBit_xor {a b i : Nat}
    (hi : i < lowBit (a ^^^ b)) : a.testBit i = b.testBit i := by
  have hx := testBit_lt_lowBit (a ^^^ b) i hi
  rw [Nat.testBit_xor] at hx
  rcases ha : a.testBit i with _ | _ <;>
    rcases hb : b.testBit i with _ | _ <;> simp_all

theorem testBit_ne_at_lowBit_xor {a b : Nat} (hab : a ≠ b) :
    a.testBit (lowBit (a ^^^ b)) ≠ b.testBit (lowBit (a ^^^ b)) := by
  have hx := testBit_lowBit _ (xor_ne_zero_of_ne hab)
  rw [Nat.testBit_xor] at hx
  intro he
  rw [he] at hx
  simp at hx

/-! # Bitset operations on a single `Nat`

The kernel-facing literal replay (`HexGraphIso.NodeLit`) keeps every
vertex set as one `Nat`, because the kernel's GMP-backed `Nat`
arithmetic is its cheapest reduction path. These are that layer's set
operations; `VSet.toNat` relates each to its packed runtime
counterpart. Insertion and deletion are guarded by the vertex bound
exactly as the packed operations are, so the correspondences are
unconditional. -/

/-- Insertion, a no-op outside the vertex range. -/
@[expose] def insertL (n s v : Nat) : Nat :=
  if v < n then s ||| (1 <<< v) else s

/-- Deletion, a no-op outside the vertex range. -/
@[expose] def eraseL (n s v : Nat) : Nat :=
  if v < n ∧ s.testBit v = true then s ^^^ (1 <<< v) else s

/-- The least element strictly after the cursor (`none` starts from the
least element): nauty's `nextelement`. -/
@[expose] def nextElemL (s : Nat) (pos : Option Nat) : Option Nat :=
  let s' :=
    match pos with
    | none => s
    | some p => (s >>> (p + 1)) <<< (p + 1)
  if s' = 0 then none else some (lowBit s')

/-- nauty's row order: the least differing vertex decides, and the row
holding it is the greater. -/
@[expose] def rowCmpL (a b : Nat) : Ordering :=
  if a = b then .eq
  else if a.testBit (lowBit (a ^^^ b)) then .gt
  else .lt

/-- The image of a bitset under a vertex map. -/
@[expose] def imageL (n : Nat) (σ : Nat → Nat) (s : Nat) : Nat :=
  (List.range n).foldl (fun t v => if s.testBit v then insertL n t (σ v) else t) 0

theorem testBit_shiftUp (x a w : Nat) :
    ((x >>> a) <<< a).testBit w = (decide (a ≤ w) && x.testBit w) := by
  rw [Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  rcases Decidable.em (a ≤ w) with h | h
  · rw [show a + (w - a) = w by omega, decide_eq_true h]
  · rw [decide_eq_false h]
    simp only [Bool.false_and]

end Hex.GraphIso.Nauty
