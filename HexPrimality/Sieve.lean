/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.Nat.Prime

public section

/-!
The kernel-reducible bitset sieve over the residues coprime to `6`.

The sieve state is a single `Nat` whose bit `t` names the number
`numOfIndex t` (`0 ↦ 1, 1 ↦ 5, 2 ↦ 7, 3 ↦ 11, …`). Marking a candidate
`p = numOfIndex s` clears the union of two arithmetic progressions of
index step `2p` (the multiples of `p` coprime to `6` step by `6p` in
value), with each progression's mask built by 32 doubling rounds, so a
single mask covers `2^32` progression terms and the recursion depth stays
fixed. Every definition is `@[expose]` and structurally recursive:
generating and verifying the committed prime table is a kernel
computation, which is the point of this module (see the SPEC's "Initial
segments"); `sqrtBound` is data because core `Nat.sqrt` is defined by
well-founded recursion and does not kernel-reduce.

`sieve_testBit_iff` is the correctness theorem, with the four hypotheses
the SPEC calls load-bearing: the mask-coverage bound, the square bound
that makes marking complete, `0 < t` (bit `0` names the non-prime `1`),
and the representation range.
-/

namespace Hex

namespace Nat

/-- The number named by sieve index `t`: the `t`-th member of
`1, 5, 7, 11, 13, 17, …`, the residues coprime to `6`. -/
@[expose]
def numOfIndex (t : Nat) : Nat := 3 * t + 1 + t % 2

/-- The sieve index of a residue coprime to `6`
(`numOfIndex_indexOfNum` is the round trip). -/
@[expose]
def indexOfNum (n : Nat) : Nat := n / 3

/-- The number of sieve indices representing values below `bound`. -/
@[expose]
def indexWidth (bound : Nat) : Nat :=
  2 * (bound / 6) + if bound % 6 ≥ 2 then 1 else 0

/-! Index arithmetic. -/

theorem numOfIndex_lt_iff {t bound : Nat} :
    numOfIndex t < bound ↔ t < indexWidth bound := by
  unfold numOfIndex indexWidth
  split <;> omega

private theorem numOfIndex_lt_numOfIndex {s t : Nat} :
    numOfIndex s < numOfIndex t ↔ s < t := by
  unfold numOfIndex
  omega

private theorem numOfIndex_mod6 (t : Nat) :
    numOfIndex t % 6 = 1 ∨ numOfIndex t % 6 = 5 := by
  unfold numOfIndex
  omega

theorem numOfIndex_indexOfNum {n : Nat}
    (h : n % 6 = 1 ∨ n % 6 = 5) : numOfIndex (indexOfNum n) = n := by
  unfold numOfIndex indexOfNum
  omega

theorem indexOfNum_numOfIndex (t : Nat) :
    indexOfNum (numOfIndex t) = t := by
  unfold numOfIndex indexOfNum
  omega

private theorem numOfIndex_add_two (t : Nat) :
    numOfIndex (t + 2) = numOfIndex t + 6 := by
  unfold numOfIndex
  omega

/-- Residues coprime to `6` are closed under multiplication. -/
private theorem mod6_mul {a b : Nat} (ha : a % 6 = 1 ∨ a % 6 = 5)
    (hb : b % 6 = 1 ∨ b % 6 = 5) : a * b % 6 = 1 ∨ a * b % 6 = 5 := by
  rw [Nat.mul_mod]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rw [ha, hb] <;> decide

/-- A divisor of a residue coprime to `6` is coprime to `6`. -/
private theorem mod6_of_dvd {d n : Nat} (hdvd : d ∣ n)
    (hn : n % 6 = 1 ∨ n % 6 = 5) : d % 6 = 1 ∨ d % 6 = 5 := by
  obtain ⟨e, rfl⟩ := hdvd
  -- d odd: an even d makes the product even.
  have hodd : d % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one d with h | h
    · exfalso
      obtain ⟨k, hk⟩ : ∃ k, d = 2 * k := ⟨d / 2, by omega⟩
      have : d * e = 2 * (k * e) := by
        rw [hk, Nat.mul_assoc]
      omega
    · exact h
  -- 3 ∤ d: a multiple of three makes the product a multiple of three.
  have h3 : d % 3 ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ : ∃ k, d = 3 * k := ⟨d / 3, by omega⟩
    have : d * e = 3 * (k * e) := by
      rw [hk, Nat.mul_assoc]
    omega
  omega

/-! The doubling-round mask. -/

/-- Union a mask with its own shifts by `step · 2^i` for `i < r`, truncating
to `width` bits every round: after `r` rounds the mask covers `2^r`
progression terms per seed bit within the width. Truncating (and skipping
shifts that alone exceed the width) keeps every intermediate below
`2^width`; an untruncated round at the 32-round budget would materialise
numbers of `step · 2^31` bits. -/
@[expose]
def doubleRounds (step width : Nat) : Nat → Nat → Nat
  | 0, m => m
  | r + 1, m =>
      doubleRounds step width r
        (if step * 2 ^ r < width then
          (m ||| (m <<< (step * 2 ^ r))) % 2 ^ width
        else m)

/-- The marking mask: progression start `start`, index step `step`,
truncated to `width` bits, with `2^32` in-range terms covered. -/
@[expose]
def markMask (start step width : Nat) : Nat :=
  doubleRounds step width 32 ((1 <<< start) % 2 ^ width)

private theorem testBit_doubleRounds {step width : Nat} :
    ∀ (r m i : Nat), m < 2 ^ width →
      ((doubleRounds step width r m).testBit i = true ↔
        i < width ∧
          ∃ k, k < 2 ^ r ∧ ∃ j, m.testBit j = true ∧ i = j + step * k) := by
  intro r
  induction r with
  | zero =>
      intro m i hm
      constructor
      · intro h
        replace h : m.testBit i = true := h
        have hi : i < width := by
          rcases Nat.lt_or_ge i width with h' | h'
          · exact h'
          · exfalso
            have : m < 2 ^ i := by
              have := Nat.pow_le_pow_right (show 0 < 2 by decide) h'
              omega
            rw [Nat.testBit_lt_two_pow this] at h
            cases h
        exact ⟨hi, 0, by omega, i, h, by omega⟩
      · rintro ⟨_, k, hk, j, hj, rfl⟩
        have hk0 : k = 0 := by omega
        subst hk0
        have e : j + step * 0 = j := by omega
        rw [e]
        exact hj
  | succ r ih =>
      intro m i hm
      have hm' : (if step * 2 ^ r < width then
          (m ||| (m <<< (step * 2 ^ r))) % 2 ^ width
        else m) < 2 ^ width := by
        split
        · exact Nat.mod_lt _ (Nat.two_pow_pos width)
        · exact hm
      show ((doubleRounds step width r _).testBit i = true ↔ _)
      rw [ih _ i hm']
      have hp2 : (2 : Nat) ^ (r + 1) = 2 ^ r + 2 ^ r := by
        rw [Nat.pow_succ]
        omega
      constructor
      · rintro ⟨hi, k, hk, j, hj, rfl⟩
        refine ⟨hi, ?_⟩
        split at hj
        · rw [Nat.testBit_mod_two_pow, Bool.and_eq_true, Nat.testBit_or,
            Bool.or_eq_true] at hj
          obtain ⟨_, hj | hj⟩ := hj
          · exact ⟨k, by omega, j, hj, rfl⟩
          · rw [Nat.testBit_shiftLeft, Bool.and_eq_true,
              decide_eq_true_iff] at hj
            obtain ⟨hge, hj'⟩ := hj
            have hd : step * (k + 2 ^ r) = step * k + step * 2 ^ r :=
              Nat.mul_add step k (2 ^ r)
            exact ⟨k + 2 ^ r, by omega, j - step * 2 ^ r, hj', by omega⟩
        · exact ⟨k, by omega, j, hj, rfl⟩
      · rintro ⟨hi, k, hk, j, hj, rfl⟩
        have hjw : j < width := by
          rcases Nat.lt_or_ge j width with h' | h'
          · exact h'
          · exfalso
            have : m < 2 ^ j := by
              have := Nat.pow_le_pow_right (show 0 < 2 by decide) h'
              omega
            rw [Nat.testBit_lt_two_pow this] at hj
            cases hj
        refine ⟨hi, ?_⟩
        by_cases hsmall : k < 2 ^ r
        · refine ⟨k, hsmall, j, ?_, rfl⟩
          split
          · rw [Nat.testBit_mod_two_pow, Bool.and_eq_true, Nat.testBit_or,
              Bool.or_eq_true]
            exact ⟨decide_eq_true hjw ▸ rfl, Or.inl hj⟩
          · exact hj
        · have hd : step * k = step * (k - 2 ^ r) + step * 2 ^ r := by
            rw [← Nat.mul_add]
            congr 1
            omega
          refine ⟨k - 2 ^ r, by omega, j + step * 2 ^ r, ?_, by omega⟩
          have hjd : j + step * 2 ^ r < width := by
            have hkpos : 1 ≤ k - 2 ^ r + 1 := by omega
            omega
          split
          · rw [Nat.testBit_mod_two_pow, Bool.and_eq_true, Nat.testBit_or,
              Bool.or_eq_true]
            refine ⟨decide_eq_true hjd ▸ rfl, Or.inr ?_⟩
            rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_iff]
            refine ⟨by omega, ?_⟩
            have e : j + step * 2 ^ r - step * 2 ^ r = j := by omega
            rw [e]
            exact hj
          · -- The shift alone exceeds the width, but the target bit sits
            -- below it: impossible.
            rename_i hbig
            exfalso
            omega

private theorem testBit_one_shiftLeft {start j : Nat} :
    (1 <<< start).testBit j = true ↔ j = start := by
  have h : (1 : Nat) <<< start = 2 ^ start := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [h, Nat.testBit_two_pow, decide_eq_true_iff]
  omega

/-- The mask covers exactly the in-range progression indices, provided
the truncation width fits under the `2^32` covered terms. -/
private theorem testBit_markMask {start step width i : Nat}
    (hstep : 0 < step) (hwidth : width ≤ 2 ^ 32) :
    (markMask start step width).testBit i = true ↔
      i < width ∧ ∃ k, i = start + step * k := by
  unfold markMask
  rw [testBit_doubleRounds 32 _ i (Nat.mod_lt _ (Nat.two_pow_pos width))]
  constructor
  · rintro ⟨hi, k, hk, j, hj, rfl⟩
    rw [Nat.testBit_mod_two_pow, Bool.and_eq_true] at hj
    obtain ⟨_, hj⟩ := hj
    rw [testBit_one_shiftLeft] at hj
    subst hj
    exact ⟨hi, k, rfl⟩
  · rintro ⟨hlt, k, rfl⟩
    refine ⟨hlt, k, ?_, start, ?_, rfl⟩
    · -- step · k ≤ i < width ≤ 2^32 pins k under the covered range.
      have hk : step * k < 2 ^ 32 := by omega
      have : k ≤ step * k := Nat.le_mul_of_pos_left k hstep
      omega
    · rw [Nat.testBit_mod_two_pow, Bool.and_eq_true]
      exact ⟨decide_eq_true (show start < width by omega) ▸ rfl,
        testBit_one_shiftLeft.mpr rfl⟩

/-! Marking one candidate. -/

/-- Clear the multiples of `p = numOfIndex s` at or above `p²`: the union
of the two progressions of index step `2p` starting at the indices of
`p · numOfIndex s` and `p · numOfIndex (s + 1)` (the two residue classes
of the cofactor). `Nat` has no complement, so clearing is and-with-xor
against the all-ones width mask. -/
@[expose]
def markCandidate (width state s : Nat) : Nat :=
  state &&&
    ((2 ^ width - 1) ^^^
      (markMask (indexOfNum (numOfIndex s * numOfIndex s))
          (2 * numOfIndex s) width |||
        markMask (indexOfNum (numOfIndex s * numOfIndex (s + 1)))
          (2 * numOfIndex s) width))

private theorem testBit_clear {width state mask t : Nat} (ht : t < width) :
    (state &&& ((2 ^ width - 1) ^^^ mask)).testBit t =
      (state.testBit t && !(mask.testBit t)) := by
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    decide_eq_true ht]
  cases state.testBit t <;> cases mask.testBit t <;> rfl

/-- One progression pair marks exactly the represented multiples of
`p = numOfIndex s` at or above `p²`: the bridging lemma between mask
membership and divisibility. -/
private theorem mem_markPair_iff {width s t : Nat} (hw : width ≤ 2 ^ 32)
    (ht : t < width) :
    ((markMask (indexOfNum (numOfIndex s * numOfIndex s))
          (2 * numOfIndex s) width |||
        markMask (indexOfNum (numOfIndex s * numOfIndex (s + 1)))
          (2 * numOfIndex s) width).testBit t = true) ↔
      numOfIndex s ∣ numOfIndex t ∧
        numOfIndex s * numOfIndex s ≤ numOfIndex t := by
  have hp0 : 0 < numOfIndex s := by
    unfold numOfIndex
    omega
  have hstep : 0 < 2 * numOfIndex s := by omega
  rw [Nat.testBit_or, Bool.or_eq_true, testBit_markMask hstep hw,
    testBit_markMask hstep hw]
  -- The generic direction: index of `p · numOfIndex u` for `u = base + 2k`.
  have index_eq : ∀ (base k : Nat),
      indexOfNum (numOfIndex s * numOfIndex base) + 2 * numOfIndex s * k =
        indexOfNum (numOfIndex s * numOfIndex (base + 2 * k)) := by
    intro base k
    have e0 : numOfIndex (base + 2 * k) = numOfIndex base + 6 * k := by
      unfold numOfIndex
      omega
    rw [e0, Nat.mul_add]
    have e1 : numOfIndex s * (6 * k) = 6 * (numOfIndex s * k) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have e2 : 2 * numOfIndex s * k = 2 * (numOfIndex s * k) := by
      simp [Nat.mul_assoc]
    rw [e1]
    unfold indexOfNum
    omega
  have value_of_index : ∀ (base k : Nat),
      numOfIndex (indexOfNum (numOfIndex s * numOfIndex base) +
          2 * numOfIndex s * k) =
        numOfIndex s * numOfIndex (base + 2 * k) := by
    intro base k
    rw [index_eq base k]
    exact numOfIndex_indexOfNum
      (mod6_mul (numOfIndex_mod6 s) (numOfIndex_mod6 (base + 2 * k)))
  constructor
  · rintro (⟨_, k, rfl⟩ | ⟨_, k, rfl⟩)
    · rw [value_of_index s k]
      refine ⟨⟨numOfIndex (s + 2 * k), rfl⟩, ?_⟩
      have hmono : numOfIndex s ≤ numOfIndex (s + 2 * k) := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · have e : s + 2 * 0 = s := by omega
          rw [e]
          exact Nat.le_refl _
        · exact Nat.le_of_lt (numOfIndex_lt_numOfIndex.mpr (by omega))
      exact Nat.mul_le_mul_left _ hmono
    · rw [value_of_index (s + 1) k]
      refine ⟨⟨numOfIndex (s + 1 + 2 * k), rfl⟩, ?_⟩
      have hmono : numOfIndex s ≤ numOfIndex (s + 1 + 2 * k) :=
        Nat.le_of_lt (numOfIndex_lt_numOfIndex.mpr (by omega))
      exact Nat.mul_le_mul_left _ hmono
  · rintro ⟨⟨m, hm⟩, hsq⟩
    -- The cofactor is coprime to 6 and at least p, so it is
    -- `numOfIndex (s + j)`; the parity of `j` selects the progression.
    have hmmod : m % 6 = 1 ∨ m % 6 = 5 :=
      mod6_of_dvd ⟨numOfIndex s, by rw [hm, Nat.mul_comm]⟩
        (numOfIndex_mod6 t)
    have hmval : numOfIndex (indexOfNum m) = m := numOfIndex_indexOfNum hmmod
    have hmge : numOfIndex s ≤ m := by
      rcases Nat.le_total (numOfIndex s) m with h | h
      · exact h
      · have h2 := Nat.mul_le_mul_left (numOfIndex s) h
        have heq : numOfIndex s * m = numOfIndex s * numOfIndex s := by omega
        have := Nat.eq_of_mul_eq_mul_left hp0 heq
        omega
    have hu : s ≤ indexOfNum m := by
      rcases Nat.lt_or_ge (indexOfNum m) s with h | h
      · exfalso
        have := numOfIndex_lt_numOfIndex.mpr h
        omega
      · exact h
    have hteq : t = indexOfNum (numOfIndex s * m) := by
      rw [← hm, indexOfNum_numOfIndex]
    obtain ⟨j, hj⟩ : ∃ j, indexOfNum m = s + j := ⟨indexOfNum m - s, by omega⟩
    rcases Nat.mod_two_eq_zero_or_one j with hpar | hpar
    · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
      left
      refine ⟨ht, k, ?_⟩
      have hmeq : m = numOfIndex (s + 2 * k) := by
        rw [← hmval, hj]
      rw [hteq, hmeq, ← index_eq s k]
    · obtain ⟨k, hk⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by omega⟩
      right
      refine ⟨ht, k, ?_⟩
      have hmeq : m = numOfIndex (s + 1 + 2 * k) := by
        rw [← hmval, hj, hk]
        congr 1
        omega
      rw [hteq, hmeq, ← index_eq (s + 1) k]

/-! The fold. -/

/-- Mark the candidates `s, s + 1, …` for `count` steps, unconditionally:
marking multiples at or above the square of any coprime-to-6 value only
ever clears composites, and the unguarded fold removes an entire
invariant from the proof (restricting to unmarked candidates is a later,
separately provable optimization). -/
@[expose]
def sieveGoRange (width : Nat) : Nat → Nat → Nat → Nat
  | _, 0, state => state
  | s, count + 1, state =>
      sieveGoRange width (s + 1) count (markCandidate width state s)

/-- All candidate bits except index `0`, which names the non-prime `1`. -/
@[expose]
def sieveInit (width : Nat) : Nat := 2 ^ width - 2

/-- The sieve over values below `bound`, marking candidates up to
`sqrtBound`. `sqrtBound` is data (rather than `Nat.sqrt bound`) because
core `Nat.sqrt` does not kernel-reduce; correctness only needs
`bound ≤ sqrtBound²`. -/
@[expose]
def sieve (bound sqrtBound : Nat) : Nat :=
  sieveGoRange (indexWidth bound) 1 (indexWidth (sqrtBound + 1) - 1)
    (sieveInit (indexWidth bound))

/-- The fold-splitting lemma the batched replay elaborator stands on. -/
theorem sieveGoRange_add (width s a b state : Nat) :
    sieveGoRange width s (a + b) state =
      sieveGoRange width (s + a) b (sieveGoRange width s a state) := by
  induction a generalizing s state with
  | zero =>
      rw [Nat.zero_add, Nat.add_zero]
      rfl
  | succ a ih =>
      have e1 : a + 1 + b = (a + b) + 1 := by omega
      have e2 : s + (a + 1) = (s + 1) + a := by omega
      rw [e1, e2]
      show sieveGoRange width (s + 1) (a + b) (markCandidate width state s) = _
      rw [ih]
      rfl

private theorem sieveGoRange_testBit {width : Nat} (hw : width ≤ 2 ^ 32) :
    ∀ (count s0 state t : Nat), t < width →
      ((sieveGoRange width s0 count state).testBit t = true ↔
        state.testBit t = true ∧
          ∀ s, s0 ≤ s → s < s0 + count →
            ¬ (numOfIndex s ∣ numOfIndex t ∧
                numOfIndex s * numOfIndex s ≤ numOfIndex t)) := by
  intro count
  induction count with
  | zero =>
      intro s0 state t ht
      constructor
      · intro h
        exact ⟨h, fun s h1 h2 => by omega⟩
      · intro h
        exact h.1
  | succ count ih =>
      intro s0 state t ht
      show ((sieveGoRange width (s0 + 1) count
          (markCandidate width state s0)).testBit t = true ↔ _)
      rw [ih (s0 + 1) (markCandidate width state s0) t ht]
      constructor
      · rintro ⟨hstate', hrest⟩
        unfold markCandidate at hstate'
        rw [testBit_clear ht, Bool.and_eq_true, Bool.not_eq_true'] at hstate'
        obtain ⟨hstate, hmark⟩ := hstate'
        refine ⟨hstate, ?_⟩
        intro s h1 h2
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
        · intro hcontra
          have hbit := (mem_markPair_iff hw ht).mpr hcontra
          rw [hbit] at hmark
          cases hmark
        · exact hrest s h1' (by omega)
      · rintro ⟨hstate, hall⟩
        refine ⟨?_, ?_⟩
        · unfold markCandidate
          rw [testBit_clear ht, Bool.and_eq_true, Bool.not_eq_true']
          refine ⟨hstate, ?_⟩
          rcases hbit : (markMask (indexOfNum (numOfIndex s0 * numOfIndex s0))
              (2 * numOfIndex s0) width |||
            markMask (indexOfNum (numOfIndex s0 * numOfIndex (s0 + 1)))
              (2 * numOfIndex s0) width).testBit t with _ | _
          · rfl
          · exfalso
            exact hall s0 (Nat.le_refl _) (by omega)
              ((mem_markPair_iff hw ht).mp hbit)
        · intro s h1 h2
          exact hall s (by omega) (by omega)

private theorem testBit_sieveInit {w t : Nat} (hw : 1 ≤ w) :
    (sieveInit w).testBit t = (decide (0 < t) && decide (t < w)) := by
  unfold sieveInit
  have h2 : (2 : Nat) ^ w = 2 * 2 ^ (w - 1) := by
    have e : (w - 1) + 1 = w := by omega
    calc (2 : Nat) ^ w = 2 ^ ((w - 1) + 1) := by rw [e]
      _ = 2 ^ (w - 1) * 2 := Nat.pow_succ ..
      _ = 2 * 2 ^ (w - 1) := Nat.mul_comm ..
  match t with
  | 0 =>
      rw [Nat.testBit_zero]
      have hmod : (2 ^ w - 2) % 2 = 0 := by omega
      rw [hmod]
      simp
  | t + 1 =>
      rw [Nat.testBit_succ]
      have hdiv : (2 ^ w - 2) / 2 = 2 ^ (w - 1) - 1 := by omega
      rw [hdiv, Nat.testBit_two_pow_sub_one]
      by_cases hlt : t < w - 1
      · rw [decide_eq_true hlt, decide_eq_true (show 0 < t + 1 by omega),
          decide_eq_true (show t + 1 < w by omega)]
        rfl
      · rw [decide_eq_false hlt, decide_eq_false (show ¬ t + 1 < w by omega)]
        cases decide (0 < t + 1) <;> rfl

/-- Correctness of the sieve: within the represented range and above
index `0`, a set bit is exactly a prime. All four hypotheses are
load-bearing: `hmask` is the range the fixed 32 doubling rounds promise,
`hsqrt` makes the marking loop complete, `ht` excludes the non-prime `1`
at index `0`, and `hrange` keeps `t` inside the representation. -/
theorem sieve_testBit_iff {bound sqrtBound t : Nat}
    (hmask : indexWidth bound ≤ 2 ^ 32)
    (hsqrt : bound ≤ sqrtBound * sqrtBound) (ht : 0 < t)
    (hrange : numOfIndex t < bound) :
    (sieve bound sqrtBound).testBit t = true ↔ Prime (numOfIndex t) := by
  have htw : t < indexWidth bound := numOfIndex_lt_iff.mp hrange
  have hw1 : 1 ≤ indexWidth bound := by omega
  have hnt5 : 5 ≤ numOfIndex t := by
    unfold numOfIndex
    omega
  unfold sieve
  rw [sieveGoRange_testBit hmask _ 1 _ t htw, testBit_sieveInit hw1,
    decide_eq_true ht, decide_eq_true htw]
  simp only [Bool.true_and, true_and]
  constructor
  · intro hall
    -- No represented candidate divides below its square; a composite
    -- would have a prime divisor at most the square root.
    by_cases hp : Prime (numOfIndex t)
    · exact hp
    exfalso
    obtain ⟨q, hq, hqdvd, hqsq⟩ :=
      exists_prime_le_sqrt (by omega) hp
    have hq6 : q % 6 = 1 ∨ q % 6 = 5 :=
      mod6_of_dvd hqdvd (numOfIndex_mod6 t)
    have hq5 : 5 ≤ q := by
      have h2 := hq.two_le
      omega
    have hqval : numOfIndex (indexOfNum q) = q := numOfIndex_indexOfNum hq6
    have hs1 : 1 ≤ indexOfNum q := by
      rcases Nat.eq_zero_or_pos (indexOfNum q) with h0 | h
      · exfalso
        rw [h0] at hqval
        unfold numOfIndex at hqval
        omega
      · exact h
    have hsrange : indexOfNum q < 1 + (indexWidth (sqrtBound + 1) - 1) := by
      -- q ≤ sqrtBound from q² ≤ n_t < bound ≤ sqrtBound².
      have hqle : q ≤ sqrtBound := by
        rcases Nat.le_total q sqrtBound with h | h
        · exact h
        · have := Nat.mul_le_mul h h
          omega
      have : numOfIndex (indexOfNum q) < sqrtBound + 1 := by omega
      have hlt := numOfIndex_lt_iff.mp this
      have hwidth1 : 1 ≤ indexWidth (sqrtBound + 1) := by omega
      omega
    exact hall (indexOfNum q) hs1 hsrange (by rw [hqval]; exact ⟨hqdvd, by omega⟩)
  · intro hp s hs1 hs2 ⟨hdvd, hsq⟩
    have hps := hp.2 (numOfIndex s) hdvd
    have hp5 : 5 ≤ numOfIndex s := by
      unfold numOfIndex
      omega
    rcases hps with h1 | h1
    · omega
    · rw [h1] at hsq
      have := Nat.mul_le_mul_left (numOfIndex t) hnt5
      have h5 : numOfIndex t * 5 ≤ numOfIndex t * numOfIndex t := by
        exact Nat.mul_le_mul_left _ (by omega)
      omega

/-! Reading the final state back into a value list. -/

/-- Collect the represented values with set bits over `fuel` indices
starting at `t0`, ascending. -/
@[expose]
def bitsToListGo (state : Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | t, fuel + 1 =>
      if state.testBit t then
        numOfIndex t :: bitsToListGo state (t + 1) fuel
      else bitsToListGo state (t + 1) fuel

/-- The represented values with set bits below `bound`, ascending,
starting from index `1` (index `0` names the non-prime `1`). -/
@[expose]
def bitsToList (state bound : Nat) : List Nat :=
  bitsToListGo state 1 (indexWidth bound - 1)

private theorem mem_bitsToListGo {state : Nat} :
    ∀ (fuel t0 n : Nat),
      n ∈ bitsToListGo state t0 fuel ↔
        ∃ t, t0 ≤ t ∧ t < t0 + fuel ∧ state.testBit t = true ∧
          numOfIndex t = n := by
  intro fuel
  induction fuel with
  | zero =>
      intro t0 n
      constructor
      · intro h
        cases h
      · rintro ⟨t, h1, h2, _, _⟩
        omega
  | succ fuel ih =>
      intro t0 n
      unfold bitsToListGo
      by_cases hbit : state.testBit t0 = true
      · rw [ite_eq_left hbit]
        constructor
        · intro h
          rcases List.mem_cons.mp h with rfl | h'
          · exact ⟨t0, Nat.le_refl _, by omega, hbit, rfl⟩
          · obtain ⟨t, h1, h2, h3, h4⟩ := (ih (t0 + 1) n).mp h'
            exact ⟨t, by omega, by omega, h3, h4⟩
        · rintro ⟨t, h1, h2, h3, h4⟩
          rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
          · subst h4
            exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _
              ((ih (t0 + 1) n).mpr ⟨t, by omega, by omega, h3, h4⟩)
      · rw [ite_eq_right hbit]
        rw [ih (t0 + 1) n]
        constructor
        · rintro ⟨t, h1, h2, h3, h4⟩
          exact ⟨t, by omega, by omega, h3, h4⟩
        · rintro ⟨t, h1, h2, h3, h4⟩
          rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
          · exact absurd h3 hbit
          · exact ⟨t, by omega, by omega, h3, h4⟩

/-- Membership in the read-back list is a set bit on a represented index
above `0`. -/
theorem mem_bitsToList {state bound n : Nat} (hw : 1 ≤ indexWidth bound) :
    n ∈ bitsToList state bound ↔
      ∃ t, 1 ≤ t ∧ t < indexWidth bound ∧ state.testBit t = true ∧
        numOfIndex t = n := by
  unfold bitsToList
  rw [mem_bitsToListGo]
  constructor
  · rintro ⟨t, h1, h2, h3, h4⟩
    exact ⟨t, h1, by omega, h3, h4⟩
  · rintro ⟨t, h1, h2, h3, h4⟩
    exact ⟨t, h1, by omega, h3, h4⟩

private theorem bitsToListGo_pairwise {state : Nat} :
    ∀ (fuel t0 : Nat), (bitsToListGo state t0 fuel).Pairwise (· < ·) := by
  intro fuel
  induction fuel with
  | zero =>
      intro t0
      exact List.Pairwise.nil
  | succ fuel ih =>
      intro t0
      unfold bitsToListGo
      by_cases hbit : state.testBit t0 = true
      · rw [ite_eq_left hbit]
        rw [List.pairwise_cons]
        refine ⟨?_, ih (t0 + 1)⟩
        intro x hx
        obtain ⟨t, h1, _, _, rfl⟩ := (mem_bitsToListGo fuel (t0 + 1) x).mp hx
        exact numOfIndex_lt_numOfIndex.mpr (by omega)
      · rw [ite_eq_right hbit]
        exact ih (t0 + 1)

/-- The read-back list is strictly ascending. -/
theorem bitsToList_pairwise_lt (state bound : Nat) :
    (bitsToList state bound).Pairwise (· < ·) :=
  bitsToListGo_pairwise _ _

/-- A prime of at least `5` is coprime to `6`: the residue fact that puts
primes onto sieve indices. -/
theorem prime_mod_six {n : Nat} (hp : Prime n) (h5 : 5 ≤ n) :
    n % 6 = 1 ∨ n % 6 = 5 := by
  have h2 : n % 2 ≠ 0 := by
    intro h
    rcases hp.2 2 (Nat.dvd_of_mod_eq_zero h) with h' | h' <;> omega
  have h3 : n % 3 ≠ 0 := by
    intro h
    rcases hp.2 3 (Nat.dvd_of_mod_eq_zero h) with h' | h' <;> omega
  omega

end Nat

end Hex
