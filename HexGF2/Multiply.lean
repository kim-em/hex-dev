/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGF2.Basic
public import HexGF2.Clmul
public import HexGF2.Multiply.Assoc
import all HexGF2.Multiply.WordBits
import all HexGF2.Multiply.MulWords
import all HexGF2.Multiply.Coeff
import all HexGF2.Multiply.Assoc

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
Packed `GF2Poly` multiplication. The word-level machinery lives in the
`HexGF2.Multiply.*` submodules imported above; this module defines `mul`,
the `Mul` instance, and the public carry-less convolution coefficient and
ring-structure theorems.
-/
namespace Hex
namespace GF2Poly
/-- Multiplication in `F_2[x]` via carry-less word products and XOR
accumulation. -/
@[expose]
def mul (p q : GF2Poly) : GF2Poly :=
  ofWords (mulWords p.words q.words)

instance : Mul GF2Poly where
  mul := mul

/-- Zero is a left annihilator for packed `GF(2)` polynomial multiplication. -/
@[simp, grind =] theorem zero_mul (p : GF2Poly) : (0 : GF2Poly) * p = 0 := by
  apply ext_words
  change (mul 0 p).words = #[]
  simp [mul, mulWords]

/-- Zero is a right annihilator for packed `GF(2)` polynomial multiplication. -/
@[simp, grind =] theorem mul_zero (p : GF2Poly) : p * (0 : GF2Poly) = 0 := by
  apply ext_words
  change (mul p 0).words = #[]
  simp [mul, mulWords]

/-- The normalized product stores no more than the raw convolution capacity. -/
theorem wordCount_mul_le (p q : GF2Poly) : (p * q).wordCount ≤ p.wordCount + q.wordCount := by
  have hnorm := normalizeWords_size_le (mulWords p.words q.words)
  have hraw : (mulWords p.words q.words).size ≤ p.wordCount + q.wordCount := by
    unfold mulWords GF2Poly.wordCount
    by_cases hxs : p.words.isEmpty <;> by_cases hys : q.words.isEmpty
    · simp [hxs, hys]
    · simp [hxs, hys]
    · simp [hxs, hys]
    · simp [hxs, hys, foldl_mulWords_size]
  calc
    (p * q).wordCount = (ofWords (mulWords p.words q.words)).words.size := by
      rfl
    _ ≤ (mulWords p.words q.words).size := hnorm
    _ ≤ p.wordCount + q.wordCount := hraw

/-- Multiplication by a monomial has the expected packed-word capacity bound. -/
theorem wordCount_mul_monomial_le (p : GF2Poly) (k : Nat) :
    (p * monomial k).wordCount ≤ p.wordCount + (k / 64 + 1) := by
  exact Nat.le_trans (wordCount_mul_le p (monomial k))
    (Nat.add_le_add_left (wordCount_monomial_le k) p.wordCount)

/-- Multiplication coefficients reduce to the raw carry-less word product. -/
@[simp, grind =]
theorem coeff_mul (p q : GF2Poly) (n : Nat) :
    (p * q).coeff n = coeffWords (mulWords p.words q.words) n := by
  change (ofWords (mulWords p.words q.words)).coeff n =
    coeffWords (mulWords p.words q.words) n
  simp

example (p q : GF2Poly) (n : Nat) :
    (p * q).coeff n = coeffWords (mulWords p.words q.words) n := by
  simp

/-! ### Public carryless-convolution coefficient lemma

`coeff_mul_diagonal` (below) expresses bit `n` of a packed product as the
XOR-parity of the diagonal `p.coeff i && q.coeff (n - i)` over `i ∈ range (n+1)`.
This is the public coefficient-level convolution the Mathlib bridge
`HexGF2Mathlib` needs to relate the carryless `clmul` product to the schoolbook
`mulCoeffSum` over `ZMod64 2`. The proof reindexes the `(word, bit)` double
decomposition `64 * I + A` / `64 * J + B` of the internal source-pair sum into
the flat coefficient indices `s + t = n`. -/

/-- Split `range (m + k)` into a low block and a shifted high block. -/
private theorem range_eq_append_map_add (m k : Nat) :
    List.range (m + k) = List.range m ++ (List.range k).map (· + m) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, List.range_succ, ih, List.range_succ, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc, Nat.add_comm m k]

/-- Flattening a shifted index map commutes with `flatMap`. -/
private theorem flatMap_map_add_shift (l : List Nat) (c : Nat) (G : Nat → List Bool) :
    (l.map (· + c)).flatMap G = l.flatMap (fun a => G (a + c)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, ih]

/-- Range-product reindexing for `map`: iterating `i < W` then `a < d` over the
combined index `d * i + a` enumerates `range (d * W)` exactly. -/
private theorem flatMap_range_map_range (d W : Nat) (g : Nat → Bool) :
    (List.range W).flatMap (fun i => (List.range d).map (fun a => g (d * i + a))) =
      (List.range (d * W)).map g := by
  induction W with
  | zero => simp
  | succ W ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, ih, Nat.mul_succ, range_eq_append_map_add (d * W) d,
        List.map_append, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _ha
      simp [Function.comp, Nat.add_comm (d * W) a]

/-- Range-product reindexing for `flatMap`: iterating `i < W` then `a < d` over
the combined index `d * i + a` enumerates `range (d * W)` exactly. -/
private theorem flatMap_range_flatMap_range (d W : Nat) (G : Nat → List Bool) :
    (List.range W).flatMap (fun i => (List.range d).flatMap (fun a => G (d * i + a))) =
      (List.range (d * W)).flatMap G := by
  induction W with
  | zero => simp
  | succ W ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, ih, Nat.mul_succ, range_eq_append_map_add (d * W) d,
        List.flatMap_append, flatMap_map_add_shift]
      congr 1
      apply List.flatMap_congr_left
      intro a _ha
      rw [Nat.add_comm (d * W) a]

/-- Singleton parity. -/
private theorem xorBoolList_singleton (x : Bool) : xorBoolList [x] = x := by
  cases x <;> rfl

/-- Selecting a single index by decidable equality collapses the parity to that
entry, or `false` when the index is out of range. -/
private theorem xorBoolList_map_decide_eq (M T : Nat) (g : Nat → Bool) :
    xorBoolList ((List.range M).map (fun t => g t && decide (t = T))) =
      if T < M then g T else false := by
  by_cases hT : T < M
  · rw [if_pos hT]
    have hmap : (List.range M).map (fun t => g t && decide (t = T)) =
        (List.range M).map (fun t => g T && decide (t = T)) := by
      apply List.map_congr_left
      intro t _ht
      by_cases htT : t = T
      · subst htT; rfl
      · simp [htT]
    rw [hmap, xorBoolList_range_single_decide (g T) hT]
  · rw [if_neg hT]
    have hmap : (List.range M).map (fun t => g t && decide (t = T)) =
        (List.range M).map (fun _ => false) := by
      apply List.map_congr_left
      intro t ht
      have htlt : t < M := List.mem_range.mp ht
      have htne : t ≠ T := by omega
      simp [htne]
    rw [hmap, xorBoolList_range_false]

/-- Extending the mapped range past a point where `f` is identically `false`
does not change the parity. -/
private theorem xorBoolList_map_range_reduce (f : Nat → Bool) (m : Nat)
    (hzero : ∀ s, m ≤ s → f s = false) :
    ∀ d, xorBoolList ((List.range (m + d)).map f) =
      xorBoolList ((List.range m).map f)
  | 0 => by simp
  | d + 1 => by
      rw [Nat.add_succ, List.range_succ, List.map_append, xorBoolList_append,
        xorBoolList_map_range_reduce f m hzero d]
      have hf : f (m + d) = false := hzero (m + d) (by omega)
      simp only [List.map_cons, List.map_nil, hf, xorBoolList_singleton]
      cases xorBoolList ((List.range m).map f) <;> rfl

/-- Two mapped ranges with the same `false`-from-`m` tail have equal parity. -/
private theorem xorBoolList_map_range_eq_of_ge (f : Nat → Bool) (A B m : Nat)
    (hzero : ∀ s, m ≤ s → f s = false) (hA : m ≤ A) (hB : m ≤ B) :
    xorBoolList ((List.range A).map f) = xorBoolList ((List.range B).map f) := by
  obtain ⟨a, rfl⟩ : ∃ a, A = m + a := ⟨A - m, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, B = m + b := ⟨B - m, by omega⟩
  rw [xorBoolList_map_range_reduce f m hzero a, xorBoolList_map_range_reduce f m hzero b]

/-- Factor a constant left `AND` out of a mapped parity. -/
private theorem xorBoolList_map_and_left' (value : Bool) (l : List Nat) (X : Nat → Bool) :
    xorBoolList (l.map (fun t => value && X t)) = (value && xorBoolList (l.map X)) := by
  have h := xorBoolList_map_and_left value (l.map X)
  rw [List.map_map] at h
  exact h

/-- Selecting the diagonal index `t = n - s` collapses the parity to that entry,
or `false` outside the range. -/
private theorem xorBoolList_map_decide_add (M s n : Nat) (g : Nat → Bool) :
    xorBoolList ((List.range M).map (fun t => g t && decide (s + t = n))) =
      if s ≤ n then (if n - s < M then g (n - s) else false) else false := by
  by_cases hsn : s ≤ n
  · rw [if_pos hsn]
    have hmap : (List.range M).map (fun t => g t && decide (s + t = n)) =
        (List.range M).map (fun t => g t && decide (t = n - s)) := by
      apply List.map_congr_left
      intro t _ht
      by_cases h : t = n - s
      · subst h
        simp [show s + (n - s) = n from by omega]
      · have hne : ¬ (s + t = n) := by omega
        simp [h, hne]
    rw [hmap, xorBoolList_map_decide_eq M (n - s) g]
  · rw [if_neg hsn]
    have hmap : (List.range M).map (fun t => g t && decide (s + t = n)) =
        (List.range M).map (fun _ => false) := by
      apply List.map_congr_left
      intro t _ht
      have hne : ¬ (s + t = n) := by omega
      simp [hne]
    rw [hmap, xorBoolList_range_false]

/-- Per-word-pair source decomposition with a unified guard: bit `n` of the
carryless product of two words at combined slot `c` is the XOR-parity over all
source bit pairs `(a, b)` whose product `64 * c + a + b` lands at `n`. -/
private theorem clmulCoeffAt_diag (c : Nat) (x y : UInt64) (n : Nat) :
    clmulCoeffAt c x y n =
      xorBoolList ((List.range 64).flatMap (fun a =>
        (List.range 64).map (fun b =>
          (wordBitAt x a && wordBitAt y b) && decide (64 * c + a + b = n)))) := by
  have hswap :
      xorBoolList ((List.range 64).flatMap (fun a =>
        (List.range 64).map (fun b =>
          (wordBitAt x a && wordBitAt y b) && decide (64 * c + a + b = n)))) =
      xorBoolList ((List.range 64).flatMap (fun b =>
        (List.range 64).map (fun a =>
          (wordBitAt x a && wordBitAt y b) && decide (64 * c + a + b = n)))) :=
    xorBoolList_wordPairs_swap 64 64
      (fun a b => (wordBitAt x a && wordBitAt y b) && decide (64 * c + a + b = n))
  rw [hswap, clmulCoeffAt_sourcePairCoeff]
  by_cases hlow : n / 64 = c
  · rw [if_pos hlow]
    unfold clmulSourcePairCoeff
    apply congrArg xorBoolList
    apply List.flatMap_congr_left
    intro b hb
    apply List.map_congr_left
    intro a ha
    have ha' : a < 64 := List.mem_range.mp ha
    have hb' : b < 64 := List.mem_range.mp hb
    by_cases h : 64 * c + a + b = n
    · have h2 : a + b = n % 64 := by omega
      simp [h, h2]
    · have h2 : ¬ (a + b = n % 64) := by omega
      simp [h, h2]
  · by_cases hhigh : n / 64 = c + 1
    · rw [if_neg hlow, if_pos hhigh]
      unfold clmulSourcePairCoeff
      apply congrArg xorBoolList
      apply List.flatMap_congr_left
      intro b hb
      apply List.map_congr_left
      intro a ha
      have ha' : a < 64 := List.mem_range.mp ha
      have hb' : b < 64 := List.mem_range.mp hb
      by_cases h : 64 * c + a + b = n
      · have h2 : a + b = n % 64 + 64 := by omega
        simp [h, h2]
      · have h2 : ¬ (a + b = n % 64 + 64) := by omega
        simp [h, h2]
    · rw [if_neg hlow, if_neg hhigh]
      have hguard :
          (List.range 64).flatMap (fun b =>
            (List.range 64).map (fun a =>
              (wordBitAt x a && wordBitAt y b) && decide (64 * c + a + b = n))) =
          (List.range 64).flatMap (fun b =>
            (List.range 64).map (fun _ : Nat => (false : Bool))) := by
        apply List.flatMap_congr_left
        intro b hb
        apply List.map_congr_left
        intro a ha
        have ha' : a < 64 := List.mem_range.mp ha
        have hb' : b < 64 := List.mem_range.mp hb
        have hne : 64 * c + a + b ≠ n := by omega
        simp [hne]
      rw [hguard, ← xorBoolList_map_xorBoolList]
      simp [xorBoolList_range_false]

/-- Carryless-convolution coefficient law: bit `n` of a packed `GF(2)` product
is the XOR-parity of the diagonal `p.coeff i && q.coeff (n - i)` for
`i ∈ range (n + 1)`. This is the public coefficient-level convolution that the
`HexGF2Mathlib` bridge uses to relate the carryless `clmul` product to the
schoolbook `mulCoeffSum` over `ZMod64 2`. -/
theorem coeff_mul_diagonal (p q : GF2Poly) (n : Nat) :
    (p * q).coeff n =
      xorBoolList ((List.range (n + 1)).map (fun s => p.coeff s && q.coeff (n - s))) := by
  rw [coeff_mul, coeffWords_mulWords_contrib]
  calc
    xorBoolList ((List.range p.words.size).flatMap (fun i =>
        (List.range q.words.size).map (fun j =>
          clmulCoeffAt (i + j) p.words[i]! q.words[j]! n)))
      = xorBoolList ((List.range p.words.size).flatMap (fun i =>
          (List.range q.words.size).flatMap (fun j =>
            (List.range 64).flatMap (fun a => (List.range 64).map (fun b =>
              (wordBitAt p.words[i]! a && wordBitAt q.words[j]! b) &&
                decide (64 * (i + j) + a + b = n)))))) := by
        apply xorBoolList_flatMap_congr_xor
        intro i _hi
        have hmap : (List.range q.words.size).map (fun j =>
              clmulCoeffAt (i + j) p.words[i]! q.words[j]! n)
            = (List.range q.words.size).map (fun j =>
              xorBoolList ((List.range 64).flatMap (fun a => (List.range 64).map (fun b =>
                (wordBitAt p.words[i]! a && wordBitAt q.words[j]! b) &&
                  decide (64 * (i + j) + a + b = n))))) := by
          apply List.map_congr_left
          intro j _hj
          exact clmulCoeffAt_diag (i + j) p.words[i]! q.words[j]! n
        rw [hmap, xorBoolList_map_xorBoolList]
    _ = xorBoolList ((List.range p.words.size).flatMap (fun i =>
          (List.range q.words.size).flatMap (fun j =>
            (List.range 64).flatMap (fun a => (List.range 64).map (fun b =>
              (p.coeff (64 * i + a) && q.coeff (64 * j + b)) &&
                decide (64 * i + a + (64 * j + b) = n)))))) := by
        apply congrArg xorBoolList
        apply List.flatMap_congr_left; intro i _hi
        apply List.flatMap_congr_left; intro j _hj
        apply List.flatMap_congr_left; intro a ha
        apply List.map_congr_left; intro b hb
        have ha' : a < 64 := List.mem_range.mp ha
        have hb' : b < 64 := List.mem_range.mp hb
        rw [wordBitAt_getElem!_eq_coeff p ha', wordBitAt_getElem!_eq_coeff q hb',
          show 64 * (i + j) + a + b = 64 * i + a + (64 * j + b) from by omega]
    _ = xorBoolList ((List.range p.words.size).flatMap (fun i =>
          (List.range 64).flatMap (fun a => (List.range q.words.size).flatMap (fun j =>
            (List.range 64).map (fun b =>
              (p.coeff (64 * i + a) && q.coeff (64 * j + b)) &&
                decide (64 * i + a + (64 * j + b) = n)))))) := by
        apply xorBoolList_flatMap_congr_xor
        intro i _hi
        exact xorBoolList_flatMap_ranges_swap_list q.words.size 64
          (fun j a => (List.range 64).map (fun b =>
            (p.coeff (64 * i + a) && q.coeff (64 * j + b)) &&
              decide (64 * i + a + (64 * j + b) = n)))
    _ = xorBoolList ((List.range (64 * p.words.size)).flatMap (fun s =>
          (List.range q.words.size).flatMap (fun j => (List.range 64).map (fun b =>
            (p.coeff s && q.coeff (64 * j + b)) && decide (s + (64 * j + b) = n))))) := by
        apply congrArg xorBoolList
        exact flatMap_range_flatMap_range 64 p.words.size (fun s =>
          (List.range q.words.size).flatMap (fun j => (List.range 64).map (fun b =>
            (p.coeff s && q.coeff (64 * j + b)) && decide (s + (64 * j + b) = n))))
    _ = xorBoolList ((List.range (64 * p.words.size)).flatMap (fun s =>
          (List.range (64 * q.words.size)).map (fun t =>
            (p.coeff s && q.coeff t) && decide (s + t = n)))) := by
        apply congrArg xorBoolList
        apply List.flatMap_congr_left
        intro s _hs
        exact flatMap_range_map_range 64 q.words.size (fun t =>
          (p.coeff s && q.coeff t) && decide (s + t = n))
    _ = xorBoolList ((List.range (64 * p.words.size)).map (fun s =>
          xorBoolList ((List.range (64 * q.words.size)).map (fun t =>
            (p.coeff s && q.coeff t) && decide (s + t = n))))) := by
        rw [← xorBoolList_map_xorBoolList]
    _ = xorBoolList ((List.range (64 * p.words.size)).map (fun s =>
          p.coeff s && (if s ≤ n then q.coeff (n - s) else false))) := by
        apply congrArg xorBoolList
        apply List.map_congr_left
        intro s _hs
        have hbody : (List.range (64 * q.words.size)).map (fun t =>
              (p.coeff s && q.coeff t) && decide (s + t = n))
            = (List.range (64 * q.words.size)).map (fun t =>
              p.coeff s && (q.coeff t && decide (s + t = n))) := by
          apply List.map_congr_left; intro t _ht; rw [Bool.and_assoc]
        rw [hbody, xorBoolList_map_and_left' (p.coeff s) (List.range (64 * q.words.size))
              (fun t => q.coeff t && decide (s + t = n)),
          xorBoolList_map_decide_add (64 * q.words.size) s n (fun t => q.coeff t)]
        congr 1
        by_cases hsn : s ≤ n
        · rw [if_pos hsn, if_pos hsn]
          by_cases hlt : n - s < 64 * q.words.size
          · rw [if_pos hlt]
          · rw [if_neg hlt]
            symm
            apply coeff_eq_false_of_wordCount_le
            simp only [wordCount]
            omega
        · rw [if_neg hsn, if_neg hsn]
    _ = xorBoolList ((List.range (n + 1)).map (fun s => p.coeff s && q.coeff (n - s))) := by
        have hzero : ∀ s, min (64 * p.words.size) (n + 1) ≤ s →
            (p.coeff s && (if s ≤ n then q.coeff (n - s) else false)) = false := by
          intro s hs
          have hcase : 64 * p.words.size ≤ s ∨ n + 1 ≤ s := by omega
          rcases hcase with h | h
          · have hp : p.coeff s = false := by
              apply coeff_eq_false_of_wordCount_le
              simp only [wordCount]
              omega
            simp [hp]
          · have hsn : ¬ (s ≤ n) := by omega
            simp [hsn]
        rw [xorBoolList_map_range_eq_of_ge
              (fun s => p.coeff s && (if s ≤ n then q.coeff (n - s) else false))
              (64 * p.words.size) (n + 1) (min (64 * p.words.size) (n + 1))
              hzero (Nat.min_le_left _ _) (Nat.min_le_right _ _)]
        apply congrArg xorBoolList
        apply List.map_congr_left
        intro s hs
        have hsn : s ≤ n := by have := List.mem_range.mp hs; omega
        simp [hsn]

/-- The unit polynomial is the degree-zero monomial. -/
theorem one_eq_monomial_zero : (1 : GF2Poly) = monomial 0 := by
  change one = monomial 0
  simp [one, monomial]

private theorem replicate_two_set_zero_one (lo hi : UInt64) :
    ((Array.replicate 2 (0 : UInt64)).set 0 lo (by simp)).set 1 hi (by simp) =
      #[lo, hi] := by
  rfl

/-- Multiplying two single packed words is the two-word carry-less product. -/
theorem ofUInt64_mul_ofUInt64 (a b : UInt64) :
    ofUInt64 a * ofUInt64 b = ofWords #[(clmul a b).2, (clmul a b).1] := by
  by_cases ha : a = 0
  · subst ha
    rw [clmul_zero_left]
    apply ext_words
    change (mul (ofWords #[(0 : UInt64)]) (ofUInt64 b)).words = (ofWords #[0, 0]).words
    simp [ofUInt64, mul, mulWords]
  by_cases hb : b = 0
  · subst hb
    rw [clmul_zero_right]
    apply ext_words
    change (mul (ofUInt64 a) (ofWords #[(0 : UInt64)])).words = (ofWords #[0, 0]).words
    simp [ofUInt64, mul, mulWords]
  apply ext_coeff
  intro n
  rw [coeff_mul]
  simp [ofUInt64, mulWords, xorClmulAt, Array.setIfInBounds, ha, hb,
    replicate_two_set_zero_one]

private theorem wordBitAt_getElem!_eq_false_of_degree?_lt
    {p : GF2Poly} {d i bit : Nat}
    (hp : p.degree? = some d) (hbit : bit < 64) (hlt : d < 64 * i + bit) :
    wordBitAt p.words[i]! bit = false := by
  rw [wordBitAt_getElem!_eq_coeff p hbit]
  exact coeff_eq_false_of_degree?_lt hp hlt

private theorem degree?_eq_some_word_lt {p : GF2Poly} {d : Nat}
    (hp : p.degree? = some d) :
    d / 64 < p.words.size := by
  have hcoeff := coeff_eq_true_of_degree?_eq_some hp
  by_cases hlt : d / 64 < p.words.size
  · exact hlt
  · have hfalse : p.coeff d = false := by
      simp [coeff, coeffWords, hlt]
    rw [hfalse] at hcoeff
    contradiction

private theorem wordBitAt_getElem!_eq_true_of_degree?_eq_some
    {p : GF2Poly} {d : Nat} (hp : p.degree? = some d) :
    wordBitAt p.words[d / 64]! (d % 64) = true := by
  have hbit : d % 64 < 64 := Nat.mod_lt d (by decide : 0 < 64)
  rw [wordBitAt_getElem!_eq_coeff p hbit]
  have hd : 64 * (d / 64) + d % 64 = d := by
    exact Nat.div_add_mod d 64
  rw [hd]
  exact coeff_eq_true_of_degree?_eq_some hp

private theorem clmulSourcePairCoeff_eq_false_of_forall
    (x y : UInt64) {total : Nat}
    (hzero :
      ∀ a b, a < 64 → b < 64 → a + b = total →
        (wordBitAt x a && wordBitAt y b) = false) :
    clmulSourcePairCoeff x y total = false := by
  unfold clmulSourcePairCoeff
  rw [← xorBoolList_map_xorBoolList]
  have houter :
      (List.range 64).map
          (fun b =>
            xorBoolList
              ((List.range 64).map
                (fun a => (wordBitAt x a && wordBitAt y b) &&
                  decide (a + b = total)))) =
        (List.range 64).map (fun _ => false) := by
    apply List.map_congr_left
    intro b hbMem
    have hb : b < 64 := List.mem_range.mp hbMem
    have hinner :
        (List.range 64).map
            (fun a => (wordBitAt x a && wordBitAt y b) &&
              decide (a + b = total)) =
          (List.range 64).map (fun _ => false) := by
      apply List.map_congr_left
      intro a haMem
      have ha : a < 64 := List.mem_range.mp haMem
      by_cases hsum : a + b = total
      · rw [hzero a b ha hb hsum]
        simp [hsum]
      · simp [hsum]
    rw [hinner, xorBoolList_range_false]
  rw [houter, xorBoolList_range_false]

private theorem source_pair_and_eq_false_of_not_leading
    {p q : GF2Poly} {dp dq i j a b : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq)
    (ha : a < 64) (hb : b < 64)
    (hsum : 64 * i + a + (64 * j + b) = dp + dq)
    (hnot : i ≠ dp / 64 ∨ j ≠ dq / 64 ∨ a ≠ dp % 64 ∨ b ≠ dq % 64) :
    (wordBitAt p.words[i]! a && wordBitAt q.words[j]! b) = false := by
  by_cases hpi : i = dp / 64
  · by_cases hpa : a = dp % 64
    · have hpidx : 64 * i + a = dp := by
        subst hpi
        subst hpa
        exact Nat.div_add_mod dp 64
      have hqidx : 64 * j + b = dq := by omega
      have hj : j = dq / 64 := by
        have hdiv := congrArg (fun n => n / 64) hqidx
        simpa [Nat.mul_add_div (by decide : 0 < 64), Nat.div_eq_of_lt hb] using hdiv
      have hbq : b = dq % 64 := by
        have hmod := congrArg (fun n => n % 64) hqidx
        simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt hb] using hmod
      cases hnot with
      | inl hi => contradiction
      | inr hrest =>
          cases hrest with
          | inl hjne => contradiction
          | inr hrest2 =>
              cases hrest2 with
              | inl hane => contradiction
              | inr hbne => contradiction
    · have hqgt_or_hpgt : dq < 64 * j + b ∨ dp < 64 * i + a := by
        by_cases halt : a < dp % 64
        · left
          subst hpi
          have hdp := Nat.div_add_mod dp 64
          omega
        · right
          subst hpi
          have hdp := Nat.div_add_mod dp 64
          have hdpbit : dp % 64 < 64 := Nat.mod_lt dp (by decide : 0 < 64)
          omega
      cases hqgt_or_hpgt with
      | inl hqgt =>
          have hqfalse := wordBitAt_getElem!_eq_false_of_degree?_lt hq hb hqgt
          simp [hqfalse]
      | inr hpgt =>
          have hpfalse := wordBitAt_getElem!_eq_false_of_degree?_lt hp ha hpgt
          simp [hpfalse]
  · by_cases hilt : i < dp / 64
    · have hqgt : dq < 64 * j + b := by
        have hdp := Nat.div_add_mod dp 64
        have hdpbit : dp % 64 < 64 := Nat.mod_lt dp (by decide : 0 < 64)
        omega
      have hqfalse := wordBitAt_getElem!_eq_false_of_degree?_lt hq hb hqgt
      simp [hqfalse]
    · have higt : dp < 64 * i + a := by
        have hdp := Nat.div_add_mod dp 64
        have hdpbit : dp % 64 < 64 := Nat.mod_lt dp (by decide : 0 < 64)
        omega
      have hpfalse := wordBitAt_getElem!_eq_false_of_degree?_lt hp ha higt
      simp [hpfalse]

private theorem clmulCoeffAt_degree_add_eq_false_of_not_leading_word
    {p q : GF2Poly} {dp dq i j : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq)
    (hnot : i ≠ dp / 64 ∨ j ≠ dq / 64) :
    clmulCoeffAt (i + j) p.words[i]! q.words[j]! (dp + dq) = false := by
  rw [clmulCoeffAt_sourcePairCoeff]
  by_cases hlow : (dp + dq) / 64 = i + j
  · simp only [if_pos hlow]
    apply clmulSourcePairCoeff_eq_false_of_forall
    intro a b ha hb hsum
    apply source_pair_and_eq_false_of_not_leading hp hq ha hb
    · have htarget := Nat.div_add_mod (dp + dq) 64
      omega
    · cases hnot with
      | inl hi => exact Or.inl hi
      | inr hj => exact Or.inr (Or.inl hj)
  · by_cases hhigh : (dp + dq) / 64 = i + j + 1
    · simp only [if_neg hlow, if_pos hhigh]
      apply clmulSourcePairCoeff_eq_false_of_forall
      intro a b ha hb hsum
      apply source_pair_and_eq_false_of_not_leading hp hq ha hb
      · have htarget := Nat.div_add_mod (dp + dq) 64
        omega
      · cases hnot with
        | inl hi => exact Or.inl hi
        | inr hj => exact Or.inr (Or.inl hj)
    · simp only [if_neg hlow, if_neg hhigh]

private theorem clmulCoeffAt_degree_add_leading_word
    {p q : GF2Poly} {dp dq : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq) :
    clmulCoeffAt (dp / 64 + dq / 64)
      p.words[dp / 64]! q.words[dq / 64]! (dp + dq) = true := by
  rw [clmulCoeffAt_sourcePairCoeff]
  by_cases hcarry : dp % 64 + dq % 64 < 64
  · have hlow : (dp + dq) / 64 = dp / 64 + dq / 64 := by
      have hdp := Nat.div_add_mod dp 64
      have hdq := Nat.div_add_mod dq 64
      omega
    have hmod : (dp + dq) % 64 = dp % 64 + dq % 64 := by
      have hdp := Nat.div_add_mod dp 64
      have hdq := Nat.div_add_mod dq 64
      omega
    simp only [if_pos hlow]
    rw [hmod]
    apply clmulSourcePairCoeff_single_active
      (a₀ := dp % 64) (b₀ := dq % 64)
    · exact Nat.mod_lt dp (by decide : 0 < 64)
    · exact Nat.mod_lt dq (by decide : 0 < 64)
    · exact wordBitAt_getElem!_eq_true_of_degree?_eq_some hp
    · exact wordBitAt_getElem!_eq_true_of_degree?_eq_some hq
    · rfl
    · intro a b ha hb hsum hnot
      apply source_pair_and_eq_false_of_not_leading hp hq ha hb
      · have hdp := Nat.div_add_mod dp 64
        have hdq := Nat.div_add_mod dq 64
        omega
      · exact Or.inr (Or.inr hnot)
  · have hhigh : (dp + dq) / 64 = dp / 64 + dq / 64 + 1 := by
      have hdp := Nat.div_add_mod dp 64
      have hdq := Nat.div_add_mod dq 64
      have hdpbit : dp % 64 < 64 := Nat.mod_lt dp (by decide : 0 < 64)
      have hdqbit : dq % 64 < 64 := Nat.mod_lt dq (by decide : 0 < 64)
      omega
    have hlow : (dp + dq) / 64 ≠ dp / 64 + dq / 64 := by omega
    have hmod : (dp + dq) % 64 + 64 = dp % 64 + dq % 64 := by
      have hdp := Nat.div_add_mod dp 64
      have hdq := Nat.div_add_mod dq 64
      have htarget := Nat.div_add_mod (dp + dq) 64
      have hdpbit : dp % 64 < 64 := Nat.mod_lt dp (by decide : 0 < 64)
      have hdqbit : dq % 64 < 64 := Nat.mod_lt dq (by decide : 0 < 64)
      omega
    simp only [if_neg hlow, if_pos hhigh]
    rw [hmod]
    apply clmulSourcePairCoeff_single_active
      (a₀ := dp % 64) (b₀ := dq % 64)
    · exact Nat.mod_lt dp (by decide : 0 < 64)
    · exact Nat.mod_lt dq (by decide : 0 < 64)
    · exact wordBitAt_getElem!_eq_true_of_degree?_eq_some hp
    · exact wordBitAt_getElem!_eq_true_of_degree?_eq_some hq
    · rfl
    · intro a b ha hb hsum hnot
      apply source_pair_and_eq_false_of_not_leading hp hq ha hb
      · have hdp := Nat.div_add_mod dp 64
        have hdq := Nat.div_add_mod dq 64
        omega
      · exact Or.inr (Or.inr hnot)

private theorem coeffWords_mulWords_degree_add_of_degree?_eq_some
    {p q : GF2Poly} {dp dq : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq) :
    coeffWords (mulWords p.words q.words) (dp + dq) = true := by
  rw [coeffWords_mulWords_contrib]
  rw [← xorBoolList_map_xorBoolList (List.range p.words.size)
    (fun i =>
      (List.range q.words.size).map
        (fun j => clmulCoeffAt (i + j) p.words[i]! q.words[j]! (dp + dq)))]
  rw [xorBoolList_range_single_active
    (fun i =>
      xorBoolList
        ((List.range q.words.size).map
          (fun j => clmulCoeffAt (i + j) p.words[i]! q.words[j]! (dp + dq))))
    (degree?_eq_some_word_lt hp)]
  · rw [xorBoolList_range_single_active
      (fun j =>
        clmulCoeffAt (dp / 64 + j) p.words[dp / 64]! q.words[j]! (dp + dq))
      (degree?_eq_some_word_lt hq)]
    · exact clmulCoeffAt_degree_add_leading_word hp hq
    · intro j hj hineq
      exact clmulCoeffAt_degree_add_eq_false_of_not_leading_word hp hq (Or.inr hineq)
  · intro i hi hineq
    have hinner :
        (List.range q.words.size).map
            (fun j => clmulCoeffAt (i + j) p.words[i]! q.words[j]! (dp + dq)) =
          (List.range q.words.size).map (fun _ => false) := by
      apply List.map_congr_left
      intro j _hj
      exact clmulCoeffAt_degree_add_eq_false_of_not_leading_word hp hq (Or.inl hineq)
    rw [hinner, xorBoolList_range_false]

private theorem clmulCoeffAt_above_degree_add_eq_false
    {p q : GF2Poly} {dp dq i j n : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq)
    (hn : dp + dq < n) :
    clmulCoeffAt (i + j) p.words[i]! q.words[j]! n = false := by
  rw [clmulCoeffAt_sourcePairCoeff]
  by_cases hlow : n / 64 = i + j
  · simp only [if_pos hlow]
    apply clmulSourcePairCoeff_eq_false_of_forall
    intro a b ha hb hsum
    have htotal : 64 * i + a + (64 * j + b) = n := by
      have hndecomp := Nat.div_add_mod n 64
      omega
    by_cases hpgt : dp < 64 * i + a
    · have hpfalse := wordBitAt_getElem!_eq_false_of_degree?_lt hp ha hpgt
      simp [hpfalse]
    · have hqgt : dq < 64 * j + b := by omega
      have hqfalse := wordBitAt_getElem!_eq_false_of_degree?_lt hq hb hqgt
      simp [hqfalse]
  · by_cases hhigh : n / 64 = i + j + 1
    · simp only [if_neg hlow, if_pos hhigh]
      apply clmulSourcePairCoeff_eq_false_of_forall
      intro a b ha hb hsum
      have htotal : 64 * i + a + (64 * j + b) = n := by
        have hndecomp := Nat.div_add_mod n 64
        omega
      by_cases hpgt : dp < 64 * i + a
      · have hpfalse := wordBitAt_getElem!_eq_false_of_degree?_lt hp ha hpgt
        simp [hpfalse]
      · have hqgt : dq < 64 * j + b := by omega
        have hqfalse := wordBitAt_getElem!_eq_false_of_degree?_lt hq hb hqgt
        simp [hqfalse]
    · simp only [if_neg hlow, if_neg hhigh]

private theorem coeffWords_mulWords_above_degree_add_eq_false
    {p q : GF2Poly} {dp dq n : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq)
    (hn : dp + dq < n) :
    coeffWords (mulWords p.words q.words) n = false := by
  rw [coeffWords_mulWords_contrib]
  rw [← xorBoolList_map_xorBoolList (List.range p.words.size)
    (fun i =>
      (List.range q.words.size).map
        (fun j => clmulCoeffAt (i + j) p.words[i]! q.words[j]! n))]
  have hrows :
      (List.range p.words.size).map
          (fun i =>
            xorBoolList
              ((List.range q.words.size).map
                (fun j => clmulCoeffAt (i + j) p.words[i]! q.words[j]! n))) =
        (List.range p.words.size).map (fun _ => false) := by
    apply List.map_congr_left
    intro i _hi
    have hinner :
        (List.range q.words.size).map
            (fun j => clmulCoeffAt (i + j) p.words[i]! q.words[j]! n) =
          (List.range q.words.size).map (fun _ => false) := by
      apply List.map_congr_left
      intro j _hj
      exact clmulCoeffAt_above_degree_add_eq_false hp hq hn
    rw [hinner, xorBoolList_range_false]
  rw [hrows, xorBoolList_range_false]

/-- The top coefficient of a product is the product of the two top
coefficients, hence set for nonzero `GF(2)` polynomials. -/
theorem coeff_mul_degree_add_of_degree?_eq_some {p q : GF2Poly} {dp dq : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq) :
    (p * q).coeff (dp + dq) = true := by
  rw [coeff_mul]
  exact coeffWords_mulWords_degree_add_of_degree?_eq_some hp hq

/-- Coefficients of a packed `GF(2)` product strictly above the sum of the
factor degrees vanish. -/
theorem coeff_mul_eq_false_of_degree_add_lt {p q : GF2Poly} {dp dq n : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq)
    (hn : dp + dq < n) :
    (p * q).coeff n = false := by
  rw [coeff_mul]
  exact coeffWords_mulWords_above_degree_add_eq_false hp hq hn

/-- The packed `GF(2)` product of two nonzero polynomials has degree exactly the
sum of the two factor degrees. -/
@[grind →]
theorem degree?_mul_of_degree?_eq_some {p q : GF2Poly} {dp dq : Nat}
    (hp : p.degree? = some dp) (hq : q.degree? = some dq) :
    (p * q).degree? = some (dp + dq) := by
  apply degree?_eq_some_of_coeff_eq_true_of_forall_gt_false
  · exact coeff_mul_degree_add_of_degree?_eq_some hp hq
  · intro m hm
    exact coeff_mul_eq_false_of_degree_add_lt hp hq hm

/-- Left distributivity of packed `GF(2)` polynomial multiplication over
addition. -/
theorem left_distrib (p r q : GF2Poly) :
    (p + r) * q = p * q + r * q := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_add_eq_bne, coeff_mul, coeff_mul]
  change
    coeffWords (mulWords (normalizeWords (xorWords p.words r.words)) q.words) n =
      (coeffWords (mulWords p.words q.words) n !=
        coeffWords (mulWords r.words q.words) n)
  let raw := xorWords p.words r.words
  let m := raw.size
  have hraw := coeffWords_mulWords_xor_left p.words r.words q.words n
  rw [← coeffWords_mulWords_common_left raw q.words n m (by simp [m])] at hraw
  rw [← coeffWords_mulWords_common_left (normalizeWords raw) q.words n m
    (by
      dsimp [m, raw]
      exact normalizeWords_size_le _)]
  simpa [raw, normalizeWords_getElem!] using hraw

/-- Packed `GF(2)` polynomial multiplication is commutative. -/
theorem mul_comm (p q : GF2Poly) :
    p * q = q * p := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_mul]
  exact coeffWords_mulWords_comm p.words q.words n

/-- Right distributivity of packed `GF(2)` polynomial multiplication over
addition. -/
theorem right_distrib (p q r : GF2Poly) :
    p * (q + r) = p * q + p * r := by
  rw [mul_comm p (q + r), left_distrib, mul_comm q p, mul_comm r p]

/-- Packed `GF(2)` polynomial multiplication is associative. -/
theorem mul_assoc (p q r : GF2Poly) :
    (p * q) * r = p * (q * r) := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_mul]
  change
    coeffWords (mulWords (ofWords (mulWords p.words q.words)).words r.words) n =
      coeffWords (mulWords p.words (ofWords (mulWords q.words r.words)).words) n
  rw [coeffWords_mulWords_ofWords_left, coeffWords_mulWords_ofWords_right]
  exact coeffWords_mulWords_assoc p.words q.words r.words n

private theorem coeff_shiftLeft_lt (p : GF2Poly) {k n : Nat} (hn : n < k) :
    (p.shiftLeft k).coeff n = false := by
  rw [coeff_shiftLeft]
  by_cases hbitShift : k % 64 = 0
  · simp [hbitShift]
    have hword : n / 64 < k / 64 := by
      have hnSplit := Nat.div_add_mod n 64
      have hkSplit := Nat.div_add_mod k 64
      have hnBit := Nat.mod_lt n (by decide : 0 < 64)
      omega
    rw [coeffWords]
    have hget :
        (((Array.replicate (k / 64) (0 : UInt64)) ++ p.words)[n / 64]?).getD 0 = 0 := by
      rw [Array.getElem?_append_left]
      · simp [hword]
      · simp [hword]
    rw [hget, UInt64.bne_zero_eq_toNat_bne_zero]
    simp
  · simp [hbitShift, coeffWords_replicate_append_shiftLeftBitsList_lt p.words hbitShift hn]

private theorem coeff_shiftLeft_add_source_oob
    (p : GF2Poly) {k source : Nat} (hsource : p.words.size ≤ source / 64) :
    (p.shiftLeft k).coeff (source + k) = false := by
  rw [coeff_shiftLeft]
  by_cases hbitShift : k % 64 = 0
  · have hcoeff : p.coeff source = false := by
      simp [coeff, coeffWords, hsource]
    simp [hbitShift, coeffWords_replicate_append_add_of_mod_eq_zero, coeff] at hcoeff ⊢
    exact hcoeff
  · simp [hbitShift,
      coeffWords_replicate_append_shiftLeftBitsList_add_of_not_word
        p.words hbitShift (Nat.not_lt.mpr hsource)]

/-- Right multiplication by the monomial `x^k` shifts packed GF(2)
polynomials left by `k` coefficients. -/
@[simp, grind =]
theorem mul_monomial (q : GF2Poly) (k : Nat) :
    q * monomial k = q.mulXk k := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_mulXk]
  by_cases hn : n < k
  · rw [coeffWords_mulWords_monomial_lt q.words hn]
    exact (coeff_shiftLeft_lt q hn).symm
  · let source := n - k
    have hn_eq : n = source + k := by
      dsimp [source]
      omega
    rw [hn_eq]
    by_cases hsource : source / 64 < q.words.size
    · rw [coeffWords_mulWords_monomial_source q.words hsource]
      exact (coeff_shiftLeft_add_of_word_lt (p := q) (k := k) (n := source) hsource).symm
    · have hsource_le : q.words.size ≤ source / 64 := Nat.le_of_not_gt hsource
      rw [coeffWords_mulWords_monomial_source_oob q.words hsource_le]
      exact (coeff_shiftLeft_add_source_oob q hsource_le).symm

/-- Left multiplication by the monomial `x^k` shifts packed GF(2)
polynomials left by `k` coefficients. -/
@[simp, grind =]
theorem monomial_mul (k : Nat) (q : GF2Poly) :
    monomial k * q = q.mulXk k := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_mulXk]
  by_cases hn : n < k
  · rw [coeffWords_monomial_mulWords_lt q.words hn]
    exact (coeff_shiftLeft_lt q hn).symm
  · let source := n - k
    have hn_eq : n = source + k := by
      dsimp [source]
      omega
    rw [hn_eq]
    by_cases hsource : source / 64 < q.words.size
    · rw [coeffWords_monomial_mulWords_source q.words hsource]
      exact (coeff_shiftLeft_add_of_word_lt (p := q) (k := k) (n := source) hsource).symm
    · have hsource_le : q.words.size ≤ source / 64 := Nat.le_of_not_gt hsource
      rw [coeffWords_monomial_mulWords_source_oob q.words hsource_le]
      exact (coeff_shiftLeft_add_source_oob q hsource_le).symm

example (q : GF2Poly) (k : Nat) :
    (monomial k * q).degree? = (q.mulXk k).degree? := by
  simp

/-- Multiplication by `x^0` leaves a packed `GF(2)` polynomial unchanged. -/
@[simp, grind =] theorem mulXk_zero (p : GF2Poly) :
    p.mulXk 0 = p := by
  apply ext_coeff
  intro n
  rw [coeff_mulXk, coeff_shiftLeft]
  simp [coeff]

/-- One is a left identity for packed `GF(2)` polynomial multiplication. -/
@[simp, grind =] theorem one_mul (p : GF2Poly) :
    (1 : GF2Poly) * p = p := by
  rw [one_eq_monomial_zero, monomial_mul, mulXk_zero]

/-- One is a right identity for packed `GF(2)` polynomial multiplication. -/
@[simp, grind =] theorem mul_one (p : GF2Poly) :
    p * (1 : GF2Poly) = p := by
  rw [one_eq_monomial_zero, mul_monomial, mulXk_zero]

/-- Expanding a quotient update by an added monomial gives the product update
used by long division. -/
theorem add_monomial_mul (quot q : GF2Poly) (k : Nat) :
    (quot + monomial k) * q = quot * q + q.mulXk k := by
  rw [left_distrib, monomial_mul]

/-- The product of two monomials is the monomial whose exponent is the sum. -/
theorem monomial_mul_monomial (a b : Nat) :
    monomial a * monomial b = monomial (a + b) := by
  rw [monomial_mul]
  apply ext_coeff
  intro n
  by_cases hn_eq : n = a + b
  · subst hn_eq
    have hdeg : ((monomial b).mulXk a).degree? = some (b + a) :=
      degree?_mulXk_of_degree?_eq_some (degree?_monomial b)
    rw [coeff_monomial_self,
      show a + b = b + a from Nat.add_comm a b]
    exact coeff_eq_true_of_degree?_eq_some hdeg
  · rw [coeff_monomial_ne hn_eq]
    by_cases h_gt : a + b < n
    · have hdeg : ((monomial b).mulXk a).degree? = some (b + a) :=
        degree?_mulXk_of_degree?_eq_some (degree?_monomial b)
      exact coeff_eq_false_of_degree?_lt hdeg (by omega)
    · rw [coeff_mulXk]
      by_cases hn_lt_a : n < a
      · exact coeff_shiftLeft_lt (monomial b) hn_lt_a
      · have hn_ge_a : a ≤ n := Nat.le_of_not_gt hn_lt_a
        have hlt : n < a + b := by omega
        have hsource_lt_b : n - a < b := by omega
        have hsource_ne_b : n - a ≠ b := Nat.ne_of_lt hsource_lt_b
        have hword : (n - a) / 64 < (monomial b).words.size := by
          rw [words_monomial_size]
          have : (n - a) / 64 ≤ b / 64 :=
            Nat.div_le_div_right (Nat.le_of_lt hsource_lt_b)
          omega
        have hn_eq_source : n = (n - a) + a := by omega
        rw [hn_eq_source, coeff_shiftLeft_add_of_word_lt (monomial b) hword]
        exact coeff_monomial_ne hsource_ne_b


end GF2Poly
end Hex
