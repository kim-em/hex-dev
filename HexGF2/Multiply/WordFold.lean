/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGF2.Basic
public import HexGF2.Clmul
public import HexGF2.Multiply.WordBits
import all HexGF2.Multiply.WordBits

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
The `foldl_xorClmulAt` / `foldl_mulWords` monomial fold lemmas over word
arrays.
-/
namespace Hex
namespace GF2Poly
/-- `foldl_mulWords_congr_coeff` lifts coefficient-level accumulator congruence across the full `mulWords` double fold. -/
private theorem foldl_mulWords_congr_coeff
    (is : List Nat) (accA accB : Array UInt64) {n : Nat}
    (xs ys : Array UInt64)
    (hidxA : ∀ i ∈ is, ∀ j, j < ys.size → i + j + 1 < accA.size)
    (hidxB : ∀ i ∈ is, ∀ j, j < ys.size → i + j + 1 < accB.size)
    (hacc : coeffWords accA n = coeffWords accB n) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          accA)
        n =
      coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          accB)
        n := by
  induction is generalizing accA accB with
  | nil =>
      simpa using hacc
  | cons i is ih =>
      simp only [List.foldl_cons]
      have hinner :=
        foldl_xorClmulAt_congr_coeff (List.range ys.size)
          accA accB (idx := i) (n := n) xs[i]! ys
          (by
            intro j hj
            exact hidxA i (by simp) j (List.mem_range.mp hj))
          (by
            intro j hj
            exact hidxB i (by simp) j (List.mem_range.mp hj))
          hacc
      have htailA : ∀ i' ∈ is, ∀ j, j < ys.size →
          i' + j + 1 <
            ((List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) xs[i]! ys[j]!)
              accA).size := by
        intro i' hi' j hj
        rw [foldl_xorClmulAt_size]
        exact hidxA i' (by simp [hi']) j hj
      have htailB : ∀ i' ∈ is, ∀ j, j < ys.size →
          i' + j + 1 <
            ((List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) xs[i]! ys[j]!)
              accB).size := by
        intro i' hi' j hj
        rw [foldl_xorClmulAt_size]
        exact hidxB i' (by simp [hi']) j hj
      exact ih
        (accA :=
          (List.range ys.size).foldl
            (fun acc j => xorClmulAt acc (i + j) xs[i]! ys[j]!)
            accA)
        (accB :=
          (List.range ys.size).foldl
            (fun acc j => xorClmulAt acc (i + j) xs[i]! ys[j]!)
            accB)
        htailA htailB hinner

/-- `foldl_xorClmulAt_zero_left` says an inner fold of `xorClmulAt` steps with a zero left factor returns the accumulator unchanged. -/
private theorem foldl_xorClmulAt_zero_left (js : List Nat) (acc : Array UInt64)
    (idx : Nat) (ys : Array UInt64) :
    js.foldl (fun acc j => xorClmulAt acc (idx + j) 0 ys[j]!) acc = acc := by
  induction js generalizing acc with
  | nil =>
      simp
  | cons j js ih =>
      simp only [List.foldl_cons]
      rw [xorClmulAt_zero_left, ih]

/-- `foldl_xorClmulAt_zero_left_coeff` says that same zero-left-factor inner fold leaves every output coefficient unchanged. -/
private theorem foldl_xorClmulAt_zero_left_coeff (js : List Nat) (acc : Array UInt64)
    (idx n : Nat) (ys : Array UInt64) :
    coeffWords
        (js.foldl (fun acc j => xorClmulAt acc (idx + j) 0 ys[j]!) acc)
        n =
      coeffWords acc n := by
  induction js generalizing acc with
  | nil =>
      simp
  | cons j js ih =>
      simp only [List.foldl_cons]
      rw [ih, coeffWords_xorClmulAt_zero_left]

/-- `getElem!_eq_zero_of_size_le` says an out-of-bounds `getElem!` into a `UInt64` array returns the `0` default. -/
private theorem getElem!_eq_zero_of_size_le (xs : Array UInt64) {i : Nat}
    (hi : xs.size ≤ i) :
    xs[i]! = 0 := by
  rw [getElem!_def, Array.getElem?_eq_none]
  · rfl
  · exact hi

/-- `foldl_mulWords_range_add_zero_left_coeff` says extending the outer `mulWords` fold by `k` indices past `xs.size` adds only zero left factors and so leaves coefficients unchanged. -/
private theorem foldl_mulWords_range_add_zero_left_coeff
    (xs ys acc : Array UInt64) (n k : Nat) :
    coeffWords
        ((List.range (xs.size + k)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          acc)
        n =
      coeffWords
        ((List.range xs.size).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          acc)
        n := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [show xs.size + Nat.succ k = xs.size + k + 1 by omega, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [getElem!_eq_zero_of_size_le xs (by omega), foldl_xorClmulAt_zero_left_coeff]
      exact ih

/-- `foldl_mulWords_range_extend_left_coeff` says running the outer `mulWords` fold over any range bound `m ≥ xs.size` gives the same coefficients as the exact `xs.size` range. -/
private theorem foldl_mulWords_range_extend_left_coeff
    (xs ys acc : Array UInt64) (n m : Nat) (hsize : xs.size ≤ m) :
    coeffWords
        ((List.range m).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          acc)
        n =
      coeffWords
        ((List.range xs.size).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          acc)
        n := by
  have hm : m = xs.size + (m - xs.size) := by omega
  rw [hm]
  exact foldl_mulWords_range_add_zero_left_coeff xs ys acc n (m - xs.size)

/-- `foldl_mulWords_left_monomial_zero_prefix_coeff_aux` is the list-generalized step showing outer indices below `k / 64` read zero `monomial k` words and so leave coefficients unchanged. -/
private theorem foldl_mulWords_left_monomial_zero_prefix_coeff_aux
    (is : List Nat) (acc xs : Array UInt64) (k n : Nat)
    (hmem : ∀ i ∈ is, i < k / 64) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := (monomial k).words[i]!
            (List.range xs.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x xs[j]!)
              acc)
          acc)
        n =
      coeffWords acc n := by
  induction is generalizing acc with
  | nil =>
      simp
  | cons i is ih =>
      have hi : i < k / 64 := hmem i (by simp)
      have htail : ∀ i' ∈ is, i' < k / 64 := by
        intro i' hi'
        exact hmem i' (by simp [hi'])
      simp only [List.foldl_cons]
      have hzero : (monomial k).words[i]! = 0 :=
        words_monomial_getElem!_zero_lt (k := k) hi
      rw [hzero]
      rw [ih (acc :=
        (List.range xs.size).foldl (fun acc j => xorClmulAt acc (i + j) 0 xs[j]!) acc)
        htail]
      exact foldl_xorClmulAt_zero_left_coeff (List.range xs.size) acc i n xs

/-- `foldl_mulWords_left_monomial_zero_prefix_coeff` specializes the prefix law to `List.range (k / 64)`: the zero low words of `monomial k` leave coefficients unchanged. -/
private theorem foldl_mulWords_left_monomial_zero_prefix_coeff
    (acc xs : Array UInt64) (k n : Nat) :
    coeffWords
        ((List.range (k / 64)).foldl
          (fun acc i =>
            let x := (monomial k).words[i]!
            (List.range xs.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x xs[j]!)
              acc)
          acc)
        n =
      coeffWords acc n := by
  exact foldl_mulWords_left_monomial_zero_prefix_coeff_aux
    (List.range (k / 64)) acc xs k n (by
      intro i hi
      exact List.mem_range.mp hi)

/-- `foldl_mulWords_left_monomial_zero_prefix_aux` is the array-level list-generalized step showing the zero low words of `monomial k` return the accumulator unchanged. -/
private theorem foldl_mulWords_left_monomial_zero_prefix_aux
    (is : List Nat) (acc xs : Array UInt64) (k : Nat)
    (hmem : ∀ i ∈ is, i < k / 64) :
    is.foldl
        (fun acc i =>
          let x := (monomial k).words[i]!
          (List.range xs.size).foldl
            (fun acc j => xorClmulAt acc (i + j) x xs[j]!)
            acc)
        acc =
      acc := by
  induction is generalizing acc with
  | nil =>
      simp
  | cons i is ih =>
      have hi : i < k / 64 := hmem i (by simp)
      have htail : ∀ i' ∈ is, i' < k / 64 := by
        intro i' hi'
        exact hmem i' (by simp [hi'])
      simp only [List.foldl_cons]
      have hzero : (monomial k).words[i]! = 0 :=
        words_monomial_getElem!_zero_lt (k := k) hi
      rw [hzero, foldl_xorClmulAt_zero_left, ih (hmem := htail)]

/-- `foldl_mulWords_left_monomial_zero_prefix` says the `List.range (k / 64)` prefix fold over `monomial k`'s zero low words returns the accumulator unchanged. -/
private theorem foldl_mulWords_left_monomial_zero_prefix
    (acc xs : Array UInt64) (k : Nat) :
    (List.range (k / 64)).foldl
        (fun acc i =>
          let x := (monomial k).words[i]!
          (List.range xs.size).foldl
            (fun acc j => xorClmulAt acc (i + j) x xs[j]!)
            acc)
        acc =
      acc := by
  exact foldl_mulWords_left_monomial_zero_prefix_aux
    (List.range (k / 64)) acc xs k (by
      intro i hi
      exact List.mem_range.mp hi)

/-- `coeffWords_xorClmulAt_monomial_left_active_low` says that for the active source word, a shifted bit staying within the same output word toggles output bit `n + k` by the `n`-th bit of `x`. -/
private theorem coeffWords_xorClmulAt_monomial_left_active_low
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : k / 64 + i < acc.size) (hn : n / 64 = i)
    (hbitShift : k % 64 ≠ 0) (hbit : n % 64 + k % 64 < 64) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! x)
        (n + k) =
      (coeffWords acc (n + k) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have hshiftPos : 0 < k % 64 := Nat.pos_of_ne_zero hbitShift
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  have htarget : n + k = (n + k / 64 * 64) + k % 64 := by
    have hk := Nat.div_add_mod k 64
    omega
  have hsourceMod : (n + k / 64 * 64) % 64 = n % 64 := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  rw [words_monomial_getElem!_active k, htarget]
  simpa [hsourceMod, Nat.add_comm] using
    coeffWords_xorClmulAt_oneHot_left_low_same_word
      (acc := acc) (idx := k / 64 + i) (n := n + k / 64 * 64)
      (shift := k % 64) x hidx hshiftPos hshift
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)

/-- `coeffWords_xorClmulAt_monomial_left_active_zero` says that when the monomial shift is word-aligned (`k % 64 = 0`), output bit `n + k` toggles by the `n`-th bit of `x` with no carry into the next word. -/
private theorem coeffWords_xorClmulAt_monomial_left_active_zero
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : k / 64 + i < acc.size) (hn : n / 64 = i)
    (hbitShift : k % 64 = 0) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! x)
        (n + k) =
      (coeffWords acc (n + k) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have htargetDiv : (n + k) / 64 = k / 64 + i := by
    have hnSplit := Nat.div_add_mod n 64
    have hkSplit := Nat.div_add_mod k 64
    omega
  have htargetMod : (n + k) % 64 = n % 64 := by
    have hnSplit := Nat.div_add_mod n 64
    have hkSplit := Nat.div_add_mod k 64
    omega
  rw [words_monomial_getElem!_active k]
  rw [coeffWords_xorClmulAt_low acc ((1 : UInt64) <<< (k % 64).toUInt64) x hidx
    htargetDiv]
  rw [clmul_oneHot_left_snd x (Nat.mod_lt k (by decide : 0 < 64))]
  simp [hbitShift, htargetMod]

/-- `coeffWords_xorClmulAt_monomial_left_active_low_before_shift` says that target positions in the active word below the shift amount (`target % 64 < k % 64`) receive no contribution, so `coeffWords` is unchanged there. -/
private theorem coeffWords_xorClmulAt_monomial_left_active_low_before_shift
    (acc : Array UInt64) {i k target : Nat} (x : UInt64)
    (hidx : k / 64 + i < acc.size) (hword : target / 64 = k / 64 + i)
    (hbitShift : k % 64 ≠ 0) (hbit : target % 64 < k % 64) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! x)
        target =
      coeffWords acc target := by
  have hshiftPos : 0 < k % 64 := Nat.pos_of_ne_zero hbitShift
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  rw [words_monomial_getElem!_active k]
  exact coeffWords_xorClmulAt_oneHot_left_low_before_shift
    (acc := acc) (idx := k / 64 + i) (target := target)
    (shift := k % 64) x hidx hshiftPos hshift hword hbit

/-- `coeffWords_xorClmulAt_monomial_left_active_high` says that for the active source word, a shifted bit carrying into the next word (`64 ≤ n % 64 + k % 64`) toggles the carry-word output bit `n + k` by the `n`-th bit of `x`. -/
private theorem coeffWords_xorClmulAt_monomial_left_active_high
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : k / 64 + i < acc.size) (hidxNext : k / 64 + i + 1 < acc.size)
    (hn : n / 64 = i) (hbit : 64 ≤ n % 64 + k % 64) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! x)
        (n + k) =
      (coeffWords acc (n + k) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have hshiftPos : 0 < k % 64 := by
    have hnbit : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
    omega
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  have htarget : n + k = (n + k / 64 * 64) + k % 64 := by
    have hk := Nat.div_add_mod k 64
    omega
  have hsourceMod : (n + k / 64 * 64) % 64 = n % 64 := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  rw [words_monomial_getElem!_active k, htarget]
  simpa [hsourceMod, Nat.add_comm] using
    coeffWords_xorClmulAt_oneHot_left_high_carry_word
      (acc := acc) (idx := k / 64 + i) (n := n + k / 64 * 64)
      (shift := k % 64) x hidx hidxNext hshiftPos hshift
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)

/-- `coeffWords_xorClmulAt_monomial_left_active_high_after_carry` says that target positions in the carry word at or above the shift amount (`k % 64 ≤ target % 64`) lie beyond the carried bits, so `coeffWords` is unchanged there. -/
private theorem coeffWords_xorClmulAt_monomial_left_active_high_after_carry
    (acc : Array UInt64) {i k target : Nat} (x : UInt64)
    (hidx : k / 64 + i < acc.size) (hidxNext : k / 64 + i + 1 < acc.size)
    (hword : target / 64 = k / 64 + i + 1) (hbit : k % 64 ≤ target % 64) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! x)
        target =
      coeffWords acc target := by
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  rw [words_monomial_getElem!_active k]
  exact coeffWords_xorClmulAt_oneHot_left_high_after_carry
    (acc := acc) (idx := k / 64 + i) (target := target)
    (shift := k % 64) x hidx hidxNext hshift hword hbit

/-- `foldl_xorClmulAt_monomial_left_ne` says that a single monomial-left `xorClmulAt` step leaves `coeffWords` at `target` unchanged when `target` lies in neither the source-aligned word nor its carry word. -/
private theorem foldl_xorClmulAt_monomial_left_ne
    (acc xs : Array UInt64) {k i target : Nat}
    (hLow : target / 64 ≠ k / 64 + i)
    (hHigh : target / 64 ≠ k / 64 + i + 1) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! xs[i]!)
        target =
      coeffWords acc target := by
  exact coeffWords_xorClmulAt_ne
    (acc := acc) (idx := k / 64 + i) (n := target)
    ((monomial k).words[k / 64]!) xs[i]! hLow hHigh

/-- `foldl_xorClmulAt_monomial_left_target_lt` says that folding the monomial-left `xorClmulAt` steps over `js` leaves `coeffWords` unchanged at any `target < k`, since output positions below the monomial degree receive no contribution. -/
private theorem foldl_xorClmulAt_monomial_left_target_lt
    (js : List Nat) (acc xs : Array UInt64) {k target : Nat}
    (hmem : ∀ j ∈ js, j < xs.size) (hacc : k / 64 + xs.size + 1 ≤ acc.size)
    (htarget : target < k) :
    coeffWords
        (js.foldl
          (fun acc j => xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
          acc)
        target =
      coeffWords acc target := by
  induction js generalizing acc with
  | nil =>
      simp
  | cons j js ih =>
      have hj : j < xs.size := hmem j (by simp)
      have htail : ∀ j' ∈ js, j' < xs.size := by
        intro j' hj'
        exact hmem j' (by simp [hj'])
      simp only [List.foldl_cons]
      rw [ih
        (acc := xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
        htail]
      · by_cases hLow : target / 64 = k / 64 + j
        · have hbitShift : k % 64 ≠ 0 := by
            intro hzero
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            omega
          have hbit : target % 64 < k % 64 := by
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            omega
          exact coeffWords_xorClmulAt_monomial_left_active_low_before_shift
            (acc := acc) (i := j) (k := k) (target := target) (x := xs[j]!)
            (hidx := by omega) hLow hbitShift hbit
        · have hHigh : target / 64 ≠ k / 64 + j + 1 := by
            intro hHigh
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            omega
          exact foldl_xorClmulAt_monomial_left_ne
            (acc := acc) (xs := xs) (k := k) (i := j) (target := target)
            hLow hHigh
      · simpa [xorClmulAt_size] using hacc

/-- `foldl_xorClmulAt_monomial_left_source_oob` says that folding the monomial-left `xorClmulAt` steps over `js` leaves `coeffWords` at `source + k` unchanged when the source word index is at or beyond `xs.size`, since out-of-range source words contribute nothing. -/
private theorem foldl_xorClmulAt_monomial_left_source_oob
    (js : List Nat) (acc xs : Array UInt64) {k source : Nat}
    (hmem : ∀ j ∈ js, j < xs.size) (hacc : k / 64 + xs.size + 1 ≤ acc.size)
    (hsource : xs.size ≤ source / 64) :
    coeffWords
        (js.foldl
          (fun acc j => xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
          acc)
        (source + k) =
      coeffWords acc (source + k) := by
  induction js generalizing acc with
  | nil =>
      simp
  | cons j js ih =>
      have hj : j < xs.size := hmem j (by simp)
      have htail : ∀ j' ∈ js, j' < xs.size := by
        intro j' hj'
        exact hmem j' (by simp [hj'])
      simp only [List.foldl_cons]
      rw [ih
        (acc := xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
        htail]
      · by_cases hLow : (source + k) / 64 = k / 64 + j
        · by_cases hbit : (source + k) % 64 < k % 64
          · have hbitShift : k % 64 ≠ 0 := by omega
            exact coeffWords_xorClmulAt_monomial_left_active_low_before_shift
              (acc := acc) (i := j) (k := k) (target := source + k)
              (x := xs[j]!) (hidx := by omega) hLow hbitShift hbit
          · have hsourceWord : source / 64 = j := by
              have hsourceSplit := Nat.div_add_mod source 64
              have hkSplit := Nat.div_add_mod k 64
              have htargetSplit := Nat.div_add_mod (source + k) 64
              have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
              have hkBit := Nat.mod_lt k (by decide : 0 < 64)
              have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
              omega
            omega
        · by_cases hHigh : (source + k) / 64 = k / 64 + j + 1
          · by_cases hbit : k % 64 ≤ (source + k) % 64
            · exact coeffWords_xorClmulAt_monomial_left_active_high_after_carry
                (acc := acc) (i := j) (k := k) (target := source + k)
                (x := xs[j]!) (hidx := by omega) (hidxNext := by omega)
                hHigh hbit
            · have hsourceWord : source / 64 = j := by
                have hsourceSplit := Nat.div_add_mod source 64
                have hkSplit := Nat.div_add_mod k 64
                have htargetSplit := Nat.div_add_mod (source + k) 64
                have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
                have hkBit := Nat.mod_lt k (by decide : 0 < 64)
                have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
                omega
              omega
          · exact foldl_xorClmulAt_monomial_left_ne
              (acc := acc) (xs := xs) (k := k) (i := j) (target := source + k)
              hLow hHigh
      · simpa [xorClmulAt_size] using hacc

/-- `foldl_xorClmulAt_monomial_left_prefix_before_source` says that folding the first `m` words (`m ≤ source / 64`) into the zero accumulator leaves output bit `source + k` `false`, since words before the source word contribute nothing there. -/
private theorem foldl_xorClmulAt_monomial_left_prefix_before_source
    (xs : Array UInt64) {k source m : Nat} (hm : m ≤ source / 64)
    (hsource : source / 64 < xs.size) :
    coeffWords
        ((List.range m).foldl
          (fun acc j => xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
          (Array.replicate ((monomial k).words.size + xs.size) (0 : UInt64)))
        (source + k) =
      false := by
  induction m with
  | zero =>
      simp only [List.range_zero, List.foldl_nil]
      rw [coeffWords]
      have hword :
          ((Array.replicate ((monomial k).words.size + xs.size) (0 : UInt64))[
              (source + k) / 64]?).getD 0 = 0 := by
        by_cases h : (source + k) / 64 <
            (Array.replicate ((monomial k).words.size + xs.size) (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword, UInt64.bne_zero_eq_toNat_bne_zero]
      simp
  | succ m ih =>
      have hm_le : m ≤ source / 64 := by omega
      have hm_lt : m < source / 64 := by omega
      rw [show m + 1 = m.succ by omega, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [words_monomial_size]
      by_cases hLow : (source + k) / 64 = k / 64 + m
      · by_cases hbit : (source + k) % 64 < k % 64
        · have hbitShift : k % 64 ≠ 0 := by omega
          rw [coeffWords_xorClmulAt_monomial_left_active_low_before_shift
            (acc :=
              (List.range m).foldl
                (fun acc j => xorClmulAt acc (k / 64 + j)
                  (monomial k).words[k / 64]! xs[j]!)
                (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
            (i := m) (k := k) (target := source + k) (x := xs[m]!)
            (hidx := by
              have hsize := foldl_xorClmulAt_size (List.range m)
                (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                (k / 64) (monomial k).words[k / 64]! xs
              have hcap : k / 64 + m <
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                simp
                omega
              simpa [hsize] using hcap)
            hLow hbitShift hbit]
          simpa [words_monomial_size] using ih hm_le
        · have hsourceWord : source / 64 = m := by
            have hsourceSplit := Nat.div_add_mod source 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetSplit := Nat.div_add_mod (source + k) 64
            have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
            omega
          omega
      · by_cases hHigh : (source + k) / 64 = k / 64 + m + 1
        · by_cases hbit : k % 64 ≤ (source + k) % 64
          · rw [coeffWords_xorClmulAt_monomial_left_active_high_after_carry
              (acc :=
                (List.range m).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
              (i := m) (k := k) (target := source + k) (x := xs[m]!)
              (hidx := by
                have hsize := foldl_xorClmulAt_size (List.range m)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + m <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              (hidxNext := by
                have hsize := foldl_xorClmulAt_size (List.range m)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + m + 1 <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              hHigh hbit]
            simpa [words_monomial_size] using ih hm_le
          · have hsourceWord : source / 64 = m := by
              have hsourceSplit := Nat.div_add_mod source 64
              have hkSplit := Nat.div_add_mod k 64
              have htargetSplit := Nat.div_add_mod (source + k) 64
              have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
              have hkBit := Nat.mod_lt k (by decide : 0 < 64)
              have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
              omega
            omega
        · rw [foldl_xorClmulAt_monomial_left_ne
            (acc :=
              (List.range m).foldl
                (fun acc j => xorClmulAt acc (k / 64 + j)
                  (monomial k).words[k / 64]! xs[j]!)
                (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
            (xs := xs) (k := k) (i := m) (target := source + k) hLow hHigh]
          simpa [words_monomial_size] using ih hm_le

/-- `foldl_xorClmulAt_monomial_left_prefix_after_source` says that once the fold has passed the source word (`source / 64 + 1 ≤ m`), output bit `source + k` equals `coeffWords xs source`, the `source`-th bit of the input. -/
private theorem foldl_xorClmulAt_monomial_left_prefix_after_source
    (xs : Array UInt64) {k source m : Nat} (hm : source / 64 + 1 ≤ m)
    (hmSize : m ≤ xs.size) (hsource : source / 64 < xs.size) :
    coeffWords
        ((List.range m).foldl
          (fun acc j => xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
          (Array.replicate ((monomial k).words.size + xs.size) (0 : UInt64)))
        (source + k) =
      coeffWords xs source := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      by_cases hm_active : m = source / 64
      · subst hm_active
        rw [show source / 64 + 1 = (source / 64).succ by omega, List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [words_monomial_size]
        have hprefix := foldl_xorClmulAt_monomial_left_prefix_before_source xs
          (m := source / 64) (k := k) (source := source) (by omega) hsource
        have hprefix' :
            coeffWords
                ((List.range (source / 64)).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
                (source + k) =
              false := by
          simpa [words_monomial_size] using hprefix
        by_cases hbitShift : k % 64 = 0
        · rw [coeffWords_xorClmulAt_monomial_left_active_zero
            (acc :=
              (List.range (source / 64)).foldl
                (fun acc j => xorClmulAt acc (k / 64 + j)
                  (monomial k).words[k / 64]! xs[j]!)
                (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
            (i := source / 64) (k := k) (n := source) (x := xs[source / 64]!)
            (hidx := by
              have hsize := foldl_xorClmulAt_size (List.range (source / 64))
                (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                (k / 64) (monomial k).words[k / 64]! xs
              have hcap : k / 64 + source / 64 <
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                simp
                omega
              simpa [hsize] using hcap) (hn := rfl) hbitShift]
          rw [hprefix']
          have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
            exact (getElem!_def xs (source / 64)).symm
          simp [coeffWords, hget]
        · by_cases hbit : source % 64 + k % 64 < 64
          · rw [coeffWords_xorClmulAt_monomial_left_active_low
              (acc :=
                (List.range (source / 64)).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
              (i := source / 64) (k := k) (n := source) (x := xs[source / 64]!)
              (hidx := by
                have hsize := foldl_xorClmulAt_size (List.range (source / 64))
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + source / 64 <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap) (hn := rfl)
              hbitShift hbit]
            rw [hprefix']
            have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
              exact (getElem!_def xs (source / 64)).symm
            simp [coeffWords, hget]
          · rw [coeffWords_xorClmulAt_monomial_left_active_high
              (acc :=
                (List.range (source / 64)).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
              (i := source / 64) (k := k) (n := source) (x := xs[source / 64]!)
              (hidx := by
                have hsize := foldl_xorClmulAt_size (List.range (source / 64))
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + source / 64 <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              (hidxNext := by
                have hsize := foldl_xorClmulAt_size (List.range (source / 64))
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + source / 64 + 1 <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              (hn := rfl) (hbit := by omega)]
            rw [hprefix']
            have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
              exact (getElem!_def xs (source / 64)).symm
            simp [coeffWords, hget]
      · have hm_tail : source / 64 + 1 ≤ m := by omega
        have hm_gt : source / 64 < m := by omega
        rw [show m + 1 = m.succ by omega, List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [words_monomial_size]
        by_cases hLow : (source + k) / 64 = k / 64 + m
        · by_cases hbit : (source + k) % 64 < k % 64
          · have hbitShift : k % 64 ≠ 0 := by omega
            rw [coeffWords_xorClmulAt_monomial_left_active_low_before_shift
              (acc :=
                (List.range m).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
              (i := m) (k := k) (target := source + k) (x := xs[m]!)
              (hidx := by
                have hsize := foldl_xorClmulAt_size (List.range m)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + m <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              hLow hbitShift hbit]
            simpa [words_monomial_size] using ih hm_tail (by omega)
          · have hsourceWord : source / 64 = m := by
              have hsourceSplit := Nat.div_add_mod source 64
              have hkSplit := Nat.div_add_mod k 64
              have htargetSplit := Nat.div_add_mod (source + k) 64
              have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
              have hkBit := Nat.mod_lt k (by decide : 0 < 64)
              have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
              omega
            omega
        · by_cases hHigh : (source + k) / 64 = k / 64 + m + 1
          · by_cases hbit : k % 64 ≤ (source + k) % 64
            · rw [coeffWords_xorClmulAt_monomial_left_active_high_after_carry
                (acc :=
                  (List.range m).foldl
                    (fun acc j => xorClmulAt acc (k / 64 + j)
                      (monomial k).words[k / 64]! xs[j]!)
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
                (i := m) (k := k) (target := source + k) (x := xs[m]!)
                (hidx := by
                  have hsize := foldl_xorClmulAt_size (List.range m)
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                    (k / 64) (monomial k).words[k / 64]! xs
                  have hcap : k / 64 + m <
                      (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                    simp
                    omega
                  simpa [hsize] using hcap)
                (hidxNext := by
                  have hsize := foldl_xorClmulAt_size (List.range m)
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                    (k / 64) (monomial k).words[k / 64]! xs
                  have hcap : k / 64 + m + 1 <
                      (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                    simp
                    omega
                  simpa [hsize] using hcap)
                hHigh hbit]
              simpa [words_monomial_size] using ih hm_tail (by omega)
            · have hsourceWord : source / 64 = m := by
                have hsourceSplit := Nat.div_add_mod source 64
                have hkSplit := Nat.div_add_mod k 64
                have htargetSplit := Nat.div_add_mod (source + k) 64
                have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
                have hkBit := Nat.mod_lt k (by decide : 0 < 64)
                have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
                omega
              omega
          · rw [foldl_xorClmulAt_monomial_left_ne
              (acc :=
                (List.range m).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
              (xs := xs) (k := k) (i := m) (target := source + k) hLow hHigh]
            simpa [words_monomial_size] using ih hm_tail (by omega)

/-- `k % 64 = 0` case: a monomial shifted by a whole number of words lands
exactly at word `n / 64 + k / 64`, so coefficient `n + k` toggles by the
source bit at position `n`. -/
private theorem foldl_mulWords_monomial_active_zero
    (acc xs : Array UInt64) {k n : Nat}
    (hidx : n / 64 + k / 64 < acc.size) (hbitShift : k % 64 = 0) :
    coeffWords
        ((List.range (n / 64 + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        (n + k) =
      (coeffWords
          ((List.range (n / 64)).foldl
            (fun acc i =>
              let x := xs[i]!
              (List.range (monomial k).words.size).foldl
                (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
                acc)
            acc)
          (n + k) !=
        (((xs[n / 64]! >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [show n / 64 + 1 = (n / 64).succ by omega, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_active_zero
    (acc :=
      (List.range (n / 64)).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[n / 64]!)
    (hidx := by
      have hsize := foldl_mulWords_size (List.range (n / 64)) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidx)
    (hn := rfl) (hbitShift := hbitShift)

/-- `n % 64 + k % 64 < 64` case (nonzero bit shift): the shifted bit stays
within the low target word `n / 64 + k / 64`, so coefficient `n + k` toggles
by the source bit at position `n` with no carry into the next word. -/
private theorem foldl_mulWords_monomial_active_low
    (acc xs : Array UInt64) {k n : Nat}
    (hidx : n / 64 + k / 64 < acc.size)
    (hbitShift : k % 64 ≠ 0) (hbit : n % 64 + k % 64 < 64) :
    coeffWords
        ((List.range (n / 64 + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        (n + k) =
      (coeffWords
          ((List.range (n / 64)).foldl
            (fun acc i =>
              let x := xs[i]!
              (List.range (monomial k).words.size).foldl
                (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
                acc)
            acc)
          (n + k) !=
        (((xs[n / 64]! >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [show n / 64 + 1 = (n / 64).succ by omega, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_active_low
    (acc :=
      (List.range (n / 64)).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[n / 64]!)
    (hidx := by
      have hsize := foldl_mulWords_size (List.range (n / 64)) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidx)
    (hn := rfl) (hbitShift := hbitShift) (hbit := hbit)

/-- `64 ≤ n % 64 + k % 64` case: the shifted bit carries into word
`n / 64 + k / 64 + 1`, so coefficient `n + k` toggles by the source bit at
position `n`. -/
private theorem foldl_mulWords_monomial_active_high
    (acc xs : Array UInt64) {k n : Nat}
    (hidx : n / 64 + k / 64 < acc.size)
    (hidxNext : n / 64 + k / 64 + 1 < acc.size)
    (hbit : 64 ≤ n % 64 + k % 64) :
    coeffWords
        ((List.range (n / 64 + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        (n + k) =
      (coeffWords
          ((List.range (n / 64)).foldl
            (fun acc i =>
              let x := xs[i]!
              (List.range (monomial k).words.size).foldl
                (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
                acc)
            acc)
          (n + k) !=
        (((xs[n / 64]! >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [show n / 64 + 1 = (n / 64).succ by omega, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_active_high
    (acc :=
      (List.range (n / 64)).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[n / 64]!)
    (hidx := by
      have hsize := foldl_mulWords_size (List.range (n / 64)) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidx)
    (hidxNext := by
      have hsize := foldl_mulWords_size (List.range (n / 64)) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidxNext)
    (hn := rfl) (hbit := hbit)

/-- Target word equals the active word `i + k / 64` but its bit index lies
below the shift `k % 64`, so source `i` leaves `target` unchanged. -/
private theorem foldl_mulWords_monomial_active_low_before_shift
    (acc xs : Array UInt64) {i k target : Nat}
    (hidx : i + k / 64 < acc.size) (hword : target / 64 = i + k / 64)
    (hbitShift : k % 64 ≠ 0) (hbit : target % 64 < k % 64) :
    coeffWords
        ((List.range (i + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target =
      coeffWords
        ((List.range i).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target := by
  rw [show i + 1 = i.succ by omega, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_active_low_before_shift
    (acc :=
      (List.range i).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[i]!)
    (hidx := by
      have hsize := foldl_mulWords_size (List.range i) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidx)
    (hword := hword) (hbitShift := hbitShift) (hbit := hbit)

/-- Target word equals the carry word `i + k / 64 + 1` but its bit index is at
or above the shift `k % 64`, so source `i` leaves `target` unchanged. -/
private theorem foldl_mulWords_monomial_active_high_after_carry
    (acc xs : Array UInt64) {i k target : Nat}
    (hidx : i + k / 64 < acc.size) (hidxNext : i + k / 64 + 1 < acc.size)
    (hword : target / 64 = i + k / 64 + 1) (hbit : k % 64 ≤ target % 64) :
    coeffWords
        ((List.range (i + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target =
      coeffWords
        ((List.range i).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target := by
  rw [show i + 1 = i.succ by omega, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_active_high_after_carry
    (acc :=
      (List.range i).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[i]!)
    (hidx := by
      have hsize := foldl_mulWords_size (List.range i) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidx)
    (hidxNext := by
      have hsize := foldl_mulWords_size (List.range i) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidxNext)
    (hword := hword) (hbit := hbit)

/-- Target word is neither the active word `i + k / 64` nor its carry word
`i + k / 64 + 1`, so source `i`'s monomial contributes nothing at `target`. -/
private theorem foldl_mulWords_monomial_ne
    (acc xs : Array UInt64) {i k target : Nat}
    (hLow : target / 64 ≠ i + k / 64)
    (hHigh : target / 64 ≠ i + k / 64 + 1) :
    coeffWords
        ((List.range (i + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target =
      coeffWords
        ((List.range i).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target := by
  rw [show i + 1 = i.succ by omega, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_ne
    (acc :=
      (List.range i).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[i]!) (hLow := hLow) (hHigh := hHigh)

/-- Folding the monomial product over a list of in-range sources leaves every
target bit below the shift `k` unchanged (each source contributes only at or
above `k`). -/
private theorem foldl_mulWords_monomial_target_lt
    (is : List Nat) (acc xs : Array UInt64) {k target : Nat}
    (hmem : ∀ i ∈ is, i < xs.size)
    (hacc : xs.size + (k / 64 + 1) ≤ acc.size) (htarget : target < k) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target =
      coeffWords acc target := by
  induction is generalizing acc with
  | nil =>
      simp
  | cons i is ih =>
      have hi : i < xs.size := hmem i (by simp)
      have htail : ∀ i' ∈ is, i' < xs.size := by
        intro i' hi'
        exact hmem i' (by simp [hi'])
      simp only [List.foldl_cons]
      rw [ih
        (acc :=
          (List.range (monomial k).words.size).foldl
            (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
            acc)
        htail]
      · rw [words_monomial_size]
        by_cases hLow : target / 64 = i + k / 64
        · have hbitShift : k % 64 ≠ 0 := by
            intro hzero
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            omega
          have hbit : target % 64 < k % 64 := by
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            omega
          exact foldl_xorClmulAt_monomial_active_low_before_shift
            (acc := acc) (i := i) (k := k) (target := target) (x := xs[i]!)
            (hidx := by omega) hLow hbitShift hbit
        · have hHigh : target / 64 ≠ i + k / 64 + 1 := by
            intro hHigh
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            omega
          exact foldl_xorClmulAt_monomial_ne
            (acc := acc) (i := i) (k := k) (target := target) (x := xs[i]!)
            hLow hHigh
      · simpa [foldl_xorClmulAt_size] using hacc

/-- A target offset `source` whose word index `source / 64` lies beyond
`xs.size` receives nothing from the monomial fold, so coefficient `source + k`
keeps its starting value. -/
private theorem foldl_mulWords_monomial_source_oob
    (is : List Nat) (acc xs : Array UInt64) {k source : Nat}
    (hmem : ∀ i ∈ is, i < xs.size)
    (hacc : xs.size + (k / 64 + 1) ≤ acc.size)
    (hsource : xs.size ≤ source / 64) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        (source + k) =
      coeffWords acc (source + k) := by
  induction is generalizing acc with
  | nil =>
      simp
  | cons i is ih =>
      have hi : i < xs.size := hmem i (by simp)
      have htail : ∀ i' ∈ is, i' < xs.size := by
        intro i' hi'
        exact hmem i' (by simp [hi'])
      simp only [List.foldl_cons]
      rw [ih
        (acc :=
          (List.range (monomial k).words.size).foldl
            (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
            acc)
        htail]
      · rw [words_monomial_size]
        by_cases hLow : (source + k) / 64 = i + k / 64
        · by_cases hbit : (source + k) % 64 < k % 64
          · have hbitShift : k % 64 ≠ 0 := by omega
            exact foldl_xorClmulAt_monomial_active_low_before_shift
              (acc := acc) (i := i) (k := k) (target := source + k) (x := xs[i]!)
              (hidx := by omega) hLow hbitShift hbit
          · have hsourceWord : source / 64 = i := by
              have hsourceSplit := Nat.div_add_mod source 64
              have hkSplit := Nat.div_add_mod k 64
              have htargetSplit := Nat.div_add_mod (source + k) 64
              have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
              have hkBit := Nat.mod_lt k (by decide : 0 < 64)
              have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
              omega
            omega
        · by_cases hHigh : (source + k) / 64 = i + k / 64 + 1
          · by_cases hbit : k % 64 ≤ (source + k) % 64
            · exact foldl_xorClmulAt_monomial_active_high_after_carry
                (acc := acc) (i := i) (k := k) (target := source + k)
                (x := xs[i]!) (hidx := by omega) (hidxNext := by omega)
                hHigh hbit
            · have hsourceWord : source / 64 = i := by
                have hsourceSplit := Nat.div_add_mod source 64
                have hkSplit := Nat.div_add_mod k 64
                have htargetSplit := Nat.div_add_mod (source + k) 64
                have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
                have hkBit := Nat.mod_lt k (by decide : 0 < 64)
                have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
                omega
              omega
          · exact foldl_xorClmulAt_monomial_ne
              (acc := acc) (i := i) (k := k) (target := source + k) (x := xs[i]!)
              hLow hHigh
      · simpa [foldl_xorClmulAt_size] using hacc


end GF2Poly
end Hex
