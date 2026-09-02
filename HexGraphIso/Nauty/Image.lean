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
  · simp only [Bool.false_eq_true, ite_false]
    rcases Decidable.em (v = w) with rfl | hne
    · simp [hb]
    · simp [show (v == w) = false by simp [hne]]
  · simp only [ite_true]
    rw [Nat.testBit_xor, testBit_one_shift]
    rcases Decidable.em (v = w) with rfl | hne
    · simp [hb]
    · simp [show (v == w) = false by simp [hne]]

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

/-! # The limb-kernel runtime implementation of `image`

`image`'s fold recomputes `testBit` (a whole-number shift) per bit and
allocates a fresh `1 <<< v` per insertion, which turns into GMP work
for every bit once rows cross the small-`Nat` boundary. The runtime
implementation peels `s` into 63-bit small-`Nat` limbs once, walks the
same vertex order as the fold with every bit test and insertion a
small-`Nat` register operation against an in-place limb-array
accumulator, and recombines once; insertions at positions the
accumulator does not cover (which the checked callers never produce,
but the signature permits) go to a spill set through plain `insert`.
`image_eq_imageFast` transfers equality, so the kernel and every
proof keep the fold. -/

/-- The 63-bit limb mask. -/
def limbMask : Nat := 0x7FFFFFFFFFFFFFFF

/-- The `i`-th 63-bit limb of `s`. -/
def limbOf (s i : Nat) : Nat := (s >>> (63 * i)) &&& limbMask

/-- The first `count` limbs of `s`. -/
def limbsOf (s : Nat) : Nat → Array Nat
  | 0 => #[]
  | count + 1 => (limbsOf s count).push (limbOf s count)

/-- Recombine 63-bit limbs, least significant first. A zero
accumulator skips the shift, so single-limb results (every call with
`n ≤ 63`) never touch big-number arithmetic. -/
def limbsToNat (arr : Array Nat) : Nat :=
  arr.foldr (fun limb acc => if acc == 0 then limb else (acc <<< 63) ||| limb) 0

/-- The insertion sweep, mirroring `image`'s fold vertex for vertex:
the bit test reads the precomputed limbs of `s`, the insertion writes
the limb-array accumulator in place. -/
@[specialize] def imageGo (σ : Nat → Nat) (cap : Nat)
    (limbs : Array Nat) : Nat → Nat → Array Nat → Nat →
      Array Nat × Nat
  | 0, _, arr, spill => (arr, spill)
  | fuel + 1, v, arr, spill =>
    if (limbs[v / 63]!).testBit (v % 63) then
      let d := σ v
      if d < cap then
        imageGo σ cap limbs fuel (v + 1)
          (arr.set! (d / 63) (arr[d / 63]! ||| (1 <<< (d % 63)))) spill
      else
        imageGo σ cap limbs fuel (v + 1) arr (insert spill d)
    else
      imageGo σ cap limbs fuel (v + 1) arr spill

/-- `image` through the limb kernel. -/
@[specialize] def imageFast (σ : Nat → Nat) (n s : Nat) : Nat :=
  let limbCount := (n + 62) / 63
  let (arr, spill) := imageGo σ (limbCount * 63) (limbsOf s limbCount)
    n 0 (Array.replicate limbCount 0) 0
  limbsToNat arr ||| spill

/-! Equality of the kernel with the fold, by `testBit` extensionality
through the limb representation. `limbsVal` is the list view of the
accumulator's value. -/

/-- The value of a limb list, least significant first. -/
def limbsVal : List Nat → Nat
  | [] => 0
  | l :: ls => (limbsVal ls <<< 63) ||| l

theorem limbMask_eq : limbMask = 2 ^ 63 - 1 := by decide

theorem limbsToNat_eq_limbsVal (arr : Array Nat) :
    limbsToNat arr = limbsVal arr.toList := by
  rw [limbsToNat, ← Array.foldr_toList]
  induction arr.toList with
  | nil => rfl
  | cons l ls ih =>
    rw [List.foldr_cons, ih, limbsVal]
    rcases hz : limbsVal ls == 0 with _ | _
    · simp only [hz, Bool.false_eq_true, ite_false]
    · simp only [hz, ite_true]
      rw [show limbsVal ls = 0 from by simpa using hz,
        Nat.zero_shiftLeft]
      simp

/-- The limb count of `limbsOf`. -/
theorem limbsOf_size {s : Nat} : ∀ c, (limbsOf s c).size = c
  | 0 => rfl
  | c + 1 => by rw [limbsOf, Array.size_push, limbsOf_size c]

/-- Bits of a limb-list value, entrywise. -/
theorem testBit_limbsVal : ∀ (L : List Nat), (∀ x ∈ L, x < 2 ^ 63) →
    ∀ w, (limbsVal L).testBit w = (L.getD (w / 63) 0).testBit (w % 63)
  | [], _, w => by
    rw [limbsVal]
    simp [List.getD]
  | l :: ls, hb, w => by
    rw [limbsVal, Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases Nat.lt_or_ge w 63 with hlt | hge
    · rw [show decide (63 ≤ w) = false by simp [Nat.not_le.mpr hlt]]
      rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
      simp [List.getD]
    · rw [show decide (63 ≤ w) = true by simp [hge]]
      have hl : l.testBit w = false := by
        refine Nat.testBit_lt_two_pow ?_
        exact Nat.lt_of_lt_of_le (hb l List.mem_cons_self)
          (Nat.pow_le_pow_right (by omega) hge)
      rw [hl, Bool.or_false, Bool.true_and]
      rw [testBit_limbsVal ls
        (fun x hx => hb x (List.mem_cons.mpr (Or.inr hx)))]
      have hdiv : (w - 63) / 63 = w / 63 - 1 := by omega
      have hmod : (w - 63) % 63 = w % 63 := by omega
      rw [hdiv, hmod]
      have hpos : 1 ≤ w / 63 := by
        rcases Nat.lt_or_ge (w / 63) 1 with h1 | h1
        · exfalso
          have := (Nat.div_lt_iff_lt_mul (show 0 < 63 by omega)).mp h1
          omega
        · exact h1
      obtain ⟨q, hq⟩ : ∃ q, w / 63 = q + 1 := ⟨w / 63 - 1, by omega⟩
      rw [hq]
      simp [List.getD]

/-- Bits of the precomputed limbs of `s`. -/
theorem testBit_limbsOf {s : Nat} : ∀ (c i : Nat), i < c →
    ∀ j, j < 63 →
      ((limbsOf s c).toList.getD i 0).testBit j = s.testBit (63 * i + j)
  | 0, i, hi, _, _ => by omega
  | c + 1, i, hi, j, hj => by
    rw [limbsOf, Array.toList_push]
    rcases Nat.lt_or_ge i c with hlt | hge
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by
        simp [limbsOf_size, hlt]), ← List.getD_eq_getElem?_getD]
      exact testBit_limbsOf c i hlt j hj
    · have hieq : i = c := by omega
      subst hieq
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by
        simp [limbsOf_size])]
      simp only [Array.length_toList, limbsOf_size, Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
      rw [limbOf, Nat.testBit_and, Nat.testBit_shiftRight, limbMask_eq]
      rw [Nat.testBit_two_pow_sub_one]
      simp only [hj, decide_true, Bool.and_true]

/-- Entry bound after an insertion. -/
theorem or_shift_lt {x : Nat} (hx : x < 2 ^ 63) {j : Nat}
    (hj : j < 63) : x ||| (1 <<< j) < 2 ^ 63 := by
  refine lt_two_pow_of_bits fun i hi => ?_
  rw [Nat.testBit_or, testBit_one_shift,
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx
      (Nat.pow_le_pow_right (by omega) hi))]
  simp
  omega

/-- Inserting through the limb array is inserting into its value. -/
theorem limbsVal_set_insert {arr : Array Nat}
    (hb : ∀ x ∈ arr.toList, x < 2 ^ 63) {d : Nat}
    (hd : d < 63 * arr.size) :
    limbsVal (arr.set! (d / 63)
        (arr[d / 63]! ||| (1 <<< (d % 63)))).toList =
      insert (limbsVal arr.toList) d := by
  have hidx : d / 63 < arr.size :=
    (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  have hentry : arr[d / 63]! ||| (1 <<< (d % 63)) < 2 ^ 63 := by
    refine or_shift_lt ?_ (Nat.mod_lt _ (by omega))
    rw [getElem!_pos arr (d / 63) hidx]
    exact hb _ (Array.getElem_mem_toList ..)
  have hb' : ∀ x ∈ (arr.set! (d / 63)
      (arr[d / 63]! ||| (1 <<< (d % 63)))).toList, x < 2 ^ 63 := by
    intro x hx
    rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds] at hx
    rcases List.mem_or_eq_of_mem_set hx with hmem | rfl
    · exact hb x hmem
    · exact hentry
  refine Nat.eq_of_testBit_eq fun w => ?_
  rw [testBit_limbsVal _ hb', testBit_insert, testBit_limbsVal _ hb]
  rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  rcases Decidable.em (w / 63 = d / 63) with heq | hne
  · rw [List.getD_eq_getElem?_getD, heq, List.getElem?_set_self (by
      simpa [Array.length_toList] using hidx), Option.getD_some,
      Nat.testBit_or, testBit_one_shift,
      getElem!_pos arr (d / 63) hidx, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by
        simpa [Array.length_toList] using hidx), Option.getD_some,
      Array.getElem_toList]
    congr 1
    rcases Decidable.em (d % 63 = w % 63) with hmeq | hmne
    · rw [hmeq]
      have hdw : d = w := by omega
      simp [hdw]
    · rw [show (d % 63 == w % 63) = false by simp [hmne],
        show (d == w) = false by
          simp only [beq_eq_false_iff_ne, ne_eq]
          omega]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
      ← List.getD_eq_getElem?_getD,
      show (d == w) = false by
        simp only [beq_eq_false_iff_ne, ne_eq]
        omega]
    simp

/-- The value of the zero accumulator. -/
theorem limbsVal_replicate : ∀ c, limbsVal (List.replicate c 0) = 0
  | 0 => rfl
  | c + 1 => by
    rw [List.replicate, limbsVal, limbsVal_replicate c]
    simp [Nat.zero_shiftLeft]

/-- The kernel's sweep computes the fold over the remaining range. -/
theorem imageGo_spec (σ : Nat → Nat) {s limbCount : Nat}
    (fuel : Nat) :
    ∀ (v : Nat) (arr : Array Nat) (spill : Nat),
      v + fuel ≤ 63 * limbCount →
      arr.size = limbCount →
      (∀ x ∈ arr.toList, x < 2 ^ 63) →
      limbsVal (imageGo σ (limbCount * 63) (limbsOf s limbCount)
          fuel v arr spill).1.toList |||
        (imageGo σ (limbCount * 63) (limbsOf s limbCount)
          fuel v arr spill).2 =
      (List.range' v fuel).foldl
        (fun t u => if s.testBit u then insert t (σ u) else t)
        (limbsVal arr.toList ||| spill) := by
  induction fuel with
  | zero =>
    intro v arr spill _ _ _
    rw [imageGo]
    rfl
  | succ fuel ih =>
    intro v arr spill hrange hsize hb
    have hvdiv : v / 63 < limbCount :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    have hbit : ((limbsOf s limbCount)[v / 63]!).testBit (v % 63) =
        s.testBit v := by
      rw [getElem!_pos _ _ (by simpa [limbsOf_size] using hvdiv)]
      have h := testBit_limbsOf (s := s) limbCount (v / 63) hvdiv
        (v % 63) (Nat.mod_lt _ (by omega))
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
        simpa [Array.length_toList, limbsOf_size] using hvdiv),
        Option.getD_some, Array.getElem_toList] at h
      rw [h, show 63 * (v / 63) + v % 63 = v from by omega]
    rw [imageGo]
    simp only [hbit]
    rw [show List.range' v (fuel + 1) =
      v :: List.range' (v + 1) fuel from rfl, List.foldl_cons]
    rcases hsb : s.testBit v with _ | _
    · simp only [hsb, Bool.false_eq_true, ite_false]
      exact ih (v + 1) arr spill (by omega) hsize hb
    · simp only [hsb, ite_true]
      rcases Decidable.em (σ v < limbCount * 63) with hlt | hge
      · rw [if_pos hlt]
        have hsize' : (arr.set! (σ v / 63) (arr[σ v / 63]! |||
            (1 <<< (σ v % 63)))).size = limbCount := by
          rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
            hsize]
        have hb' : ∀ x ∈ (arr.set! (σ v / 63) (arr[σ v / 63]! |||
            (1 <<< (σ v % 63)))).toList, x < 2 ^ 63 := by
          intro x hx
          rw [Array.set!_eq_setIfInBounds,
            Array.toList_setIfInBounds] at hx
          rcases List.mem_or_eq_of_mem_set hx with hmem | rfl
          · exact hb x hmem
          · refine or_shift_lt ?_ (Nat.mod_lt _ (by omega))
            rw [getElem!_pos arr (σ v / 63) (by
              rw [hsize]
              exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega))]
            exact hb _ (Array.getElem_mem_toList ..)
        rw [ih (v + 1) _ spill (by omega) hsize' hb']
        rw [limbsVal_set_insert hb (by omega)]
        rw [insert, insert, Nat.or_assoc, Nat.or_comm (1 <<< (σ v)) spill,
          ← Nat.or_assoc]
      · rw [if_neg hge]
        rw [ih (v + 1) arr (insert spill (σ v)) (by omega) hsize hb]
        rw [insert, insert, Nat.or_assoc]

@[csimp] theorem image_eq_imageFast : @image = @imageFast := by
  funext σ n s
  rw [image, imageFast]
  have hspec := imageGo_spec (s := s) (limbCount := (n + 62) / 63) σ n 0
    (Array.replicate ((n + 62) / 63) 0) 0
    (by omega) (by rw [Array.size_replicate]) (by
      intro x hx
      rw [Array.toList_replicate] at hx
      rw [List.eq_of_mem_replicate hx]
      exact Nat.two_pow_pos 63)
  rw [Array.toList_replicate, limbsVal_replicate] at hspec
  rw [List.range_eq_range']
  have hfinal : (match imageGo σ ((n + 62) / 63 * 63)
      (limbsOf s ((n + 62) / 63)) n 0
      (Array.replicate ((n + 62) / 63) 0) 0 with
    | (arr, spill) => limbsToNat arr ||| spill) =
      limbsVal (imageGo σ ((n + 62) / 63 * 63)
        (limbsOf s ((n + 62) / 63)) n 0
        (Array.replicate ((n + 62) / 63) 0) 0).1.toList |||
      (imageGo σ ((n + 62) / 63 * 63)
        (limbsOf s ((n + 62) / 63)) n 0
        (Array.replicate ((n + 62) / 63) 0) 0).2 := by
    rcases imageGo σ ((n + 62) / 63 * 63) (limbsOf s ((n + 62) / 63))
      n 0 (Array.replicate ((n + 62) / 63) 0) 0 with ⟨a, sp⟩
    show limbsToNat a ||| sp = limbsVal a.toList ||| sp
    rw [limbsToNat_eq_limbsVal]
  rw [hfinal, hspec, Nat.zero_or]

/-- `permset` is `image` over array indexing, so it shares the limb
kernel. -/
def permsetFast (s : Nat) (perm : Array Nat) (n : Nat) : Nat :=
  imageFast (fun v => perm[v]!) n s

@[csimp] theorem permset_eq_permsetFast : @permset = @permsetFast := by
  funext s perm n
  show image (fun v => perm[v]!) n s = imageFast (fun v => perm[v]!) n s
  rw [image_eq_imageFast]

theorem testBit_image_foldl (σ : Nat → Nat) (s w : Nat) :
    ∀ (l : List Nat) (t : Nat),
      ((l.foldl (fun t v => if s.testBit v then insert t (σ v) else t)
        t).testBit w) =
        (t.testBit w || l.any fun v => s.testBit v && σ v == w)
  | [], t => by simp
  | v :: l, t => by
    rw [List.foldl_cons, List.any_cons]
    rcases hb : s.testBit v with _ | _
    · rw [ite_eq_right (by simp), testBit_image_foldl σ s w l t]
      simp
    · rw [ite_eq_left (by simp),
        testBit_image_foldl σ s w l (insert t (σ v)), testBit_insert]
      simp [Bool.or_assoc]

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
