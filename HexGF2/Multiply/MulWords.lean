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
Raw packed-word multiplication `mulWords` and its
`coeffWords_mulWords` coefficient lemmas.
-/
namespace Hex
namespace GF2Poly
/-- Raw packed-word multiplication before trailing zero normalization. -/
@[expose]
def mulWords (xs ys : Array UInt64) : Array UInt64 :=
  if xs.isEmpty || ys.isEmpty then
    #[]
  else
    (List.range xs.size).foldl
      (fun acc i =>
        let x := xs[i]!
        (List.range ys.size).foldl
          (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
          acc)
      (Array.replicate (xs.size + ys.size) (0 : UInt64))

private theorem coeffWords_replicate_zero (size n : Nat) :
    coeffWords (Array.replicate size (0 : UInt64)) n = false := by
  rw [coeffWords]
  by_cases h : n / 64 < (Array.replicate size (0 : UInt64)).size
  · rw [Array.getElem?_eq_getElem h]
    simp
  · rw [Array.getElem?_eq_none]
    · simp
    · exact Nat.le_of_not_gt h

private theorem coeffWords_empty (n : Nat) :
    coeffWords #[] n = false := by
  rw [coeffWords]
  simp

private theorem coeffWords_mulWords_common_left
    (xs zs : Array UInt64) (n m : Nat) (hm : xs.size ≤ m) :
    coeffWords
        ((List.range m).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range zs.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x zs[j]!)
              acc)
          (Array.replicate (m + zs.size) (0 : UInt64)))
        n =
      coeffWords (mulWords xs zs) n := by
  unfold mulWords
  by_cases hzs : zs.isEmpty
  · have hcommon :=
      foldl_mulWords_range_extend_left_coeff xs zs
        (Array.replicate (m + zs.size) (0 : UInt64)) n m hm
    rw [hcommon]
    have hzsize : zs.size = 0 := by
      simpa [Array.isEmpty] using hzs
    simp only [hzs, hzsize, List.range_zero, List.foldl_nil, Bool.or_true, ↓reduceIte]
    rw [List.foldl_const_step, coeffWords_replicate_zero, coeffWords_empty]
  · by_cases hxs : xs.isEmpty
    · have hcommon :=
        foldl_mulWords_range_extend_left_coeff xs zs
          (Array.replicate (m + zs.size) (0 : UInt64)) n m hm
      rw [hcommon]
      have hxsize : xs.size = 0 := by
        simpa [Array.isEmpty] using hxs
      simp [hxs, hzs, hxsize, coeffWords_replicate_zero, coeffWords_empty]
    · have hcommon :=
        foldl_mulWords_range_extend_left_coeff xs zs
          (Array.replicate (m + zs.size) (0 : UInt64)) n m hm
      rw [hcommon]
      have hcongr :=
        foldl_mulWords_congr_coeff (List.range xs.size)
          (Array.replicate (m + zs.size) (0 : UInt64))
          (Array.replicate (xs.size + zs.size) (0 : UInt64))
          (n := n) xs zs
          (by
            intro i hi j hj
            have hi' : i < xs.size := List.mem_range.mp hi
            simpa using (by omega : i + j + 1 < m + zs.size))
          (by
            intro i hi j hj
            have hi' : i < xs.size := List.mem_range.mp hi
            simpa using (by omega : i + j + 1 < xs.size + zs.size))
          (by
            rw [coeffWords_replicate_zero, coeffWords_replicate_zero])
      rw [hcongr]
      simp [hxs, hzs]

private theorem coeffWords_mulWords_xor_left_same_size
    (xs ys zs : Array UInt64) (n : Nat) (hsize : xs.size = ys.size) :
    coeffWords (mulWords (xorWords xs ys) zs) n =
      (coeffWords (mulWords xs zs) n != coeffWords (mulWords ys zs) n) := by
  unfold mulWords
  by_cases hzs : zs.isEmpty
  · simp [hzs]
    exact coeffWords_empty n
  · by_cases hxs : xs.isEmpty
    · have hxempty : xs = #[] := by
        apply Array.eq_empty_of_size_eq_zero
        simpa [Array.isEmpty] using hxs
      have hyempty : ys = #[] := by
        apply Array.eq_empty_of_size_eq_zero
        have hxsize : xs.size = 0 := by
          simp [hxempty]
        omega
      simp [hxempty, hyempty, xorWords, coeffWords_empty]
    · have hys : ys.isEmpty = false := by
        have hxsize : xs.size ≠ 0 := by
          intro hz
          apply hxs
          simpa [Array.isEmpty] using hz
        have hysize : ys.size ≠ 0 := by omega
        rw [Array.isEmpty]
        simp [hysize]
      have hxor : (xorWords xs ys).isEmpty = false := by
        rw [Array.isEmpty]
        have hxsize : xs.size ≠ 0 := by
          intro hz
          apply hxs
          simpa [Array.isEmpty] using hz
        have hmax : max xs.size ys.size ≠ 0 := by omega
        simp [xorWords_size, hmax]
      have hzarr : zs ≠ #[] := by
        intro hz
        apply hzs
        simp [hz]
      simp [hxs, hys, hxor, xorWords_size, hsize, xorWords_getElem!, hzarr]
      exact foldl_mulWords_xor_left_coeff (List.range ys.size)
        (Array.replicate (ys.size + zs.size) (0 : UInt64))
        (Array.replicate (ys.size + zs.size) (0 : UInt64))
        (Array.replicate (ys.size + zs.size) (0 : UInt64))
        (n := n) xs ys zs rfl rfl
        (by
          intro i hi j hj
          have hi' : i < ys.size := List.mem_range.mp hi
          simp
          omega)
        (by
          rw [coeffWords_replicate_zero]
          rfl)

private theorem coeffWords_mulWords_xor_left
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords (xorWords xs ys) zs) n =
      (coeffWords (mulWords xs zs) n != coeffWords (mulWords ys zs) n) := by
  let m := max xs.size ys.size
  rw [← coeffWords_mulWords_common_left (xorWords xs ys) zs n m (by simp [m])]
  rw [← coeffWords_mulWords_common_left xs zs n m
    (by simpa [m] using Nat.le_max_left xs.size ys.size)]
  rw [← coeffWords_mulWords_common_left ys zs n m
    (by simpa [m] using Nat.le_max_right xs.size ys.size)]
  simp only [xorWords_getElem!]
  exact foldl_mulWords_xor_left_coeff (List.range m)
    (Array.replicate (m + zs.size) (0 : UInt64))
    (Array.replicate (m + zs.size) (0 : UInt64))
    (Array.replicate (m + zs.size) (0 : UInt64))
    (n := n) xs ys zs rfl rfl
    (by
      intro i hi j hj
      have hi' : i < m := List.mem_range.mp hi
      simpa using (by omega : i + j + 1 < m + zs.size))
    (by
      rw [coeffWords_replicate_zero]
      rfl)

private theorem coeffWords_mulWords_monomial_lt
    (xs : Array UInt64) {k target : Nat} (htarget : target < k) :
    coeffWords (mulWords xs (monomial k).words) target = false := by
  unfold mulWords
  by_cases hxs : xs.isEmpty
  · simp [hxs, coeffWords]
  · have hys : ¬ (monomial k).words.isEmpty := by
      rw [words_monomial]
      simp
    simp [hxs, hys]
    rw [foldl_mulWords_monomial_target_lt]
    · rw [coeffWords]
      have hword :
          ((Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))[target / 64]?).getD
              0 = 0 := by
        by_cases h : target / 64 < (Array.replicate (xs.size + (monomial k).words.size)
            (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword, UInt64.bne_zero_eq_toNat_bne_zero]
      simp
    · intro i hi
      exact List.mem_range.mp hi
    · simp [words_monomial_size]
    · exact htarget

private theorem coeffWords_mulWords_monomial_source_oob
    (xs : Array UInt64) {k source : Nat} (hsource : xs.size ≤ source / 64) :
    coeffWords (mulWords xs (monomial k).words) (source + k) = false := by
  unfold mulWords
  by_cases hxs : xs.isEmpty
  · simp [hxs, coeffWords]
  · have hys : ¬ (monomial k).words.isEmpty := by
      rw [words_monomial]
      simp
    simp [hxs, hys]
    rw [foldl_mulWords_monomial_source_oob]
    · rw [coeffWords]
      have hword :
          ((Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))[(source + k) / 64]?).getD
              0 = 0 := by
        by_cases h : (source + k) / 64 <
            (Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword, UInt64.bne_zero_eq_toNat_bne_zero]
      simp
    · intro i hi
      exact List.mem_range.mp hi
    · simp [words_monomial_size]
    · exact hsource

private theorem foldl_mulWords_monomial_prefix_before_source
    (xs : Array UInt64) {k source m : Nat} (hm : m ≤ source / 64)
    (hsource : source / 64 < xs.size) :
    coeffWords
        ((List.range m).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          (Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64)))
        (source + k) =
      false := by
  induction m with
  | zero =>
      simp only [List.range_zero, List.foldl_nil]
      rw [coeffWords]
      have hword :
          ((Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))[
              (source + k) / 64]?).getD 0 = 0 := by
        by_cases h : (source + k) / 64 <
            (Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64)).size
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
      by_cases hLow : (source + k) / 64 = m + k / 64
      · by_cases hbit : (source + k) % 64 < k % 64
        · have hbitShift : k % 64 ≠ 0 := by omega
          rw [foldl_xorClmulAt_monomial_active_low_before_shift
            (acc :=
              (List.range m).foldl
                (fun acc i =>
                  let x := xs[i]!
                  (List.range (k / 64 + 1)).foldl
                    (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                    acc)
                (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
            (i := m) (k := k) (target := source + k) (x := xs[m]!)
            (hidx := by
              have hsize := foldl_mulWords_size (List.range m)
                (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                xs (monomial k).words
              rw [words_monomial_size] at hsize
              have hcap : m + k / 64 <
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
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
      · by_cases hHigh : (source + k) / 64 = m + k / 64 + 1
        · by_cases hbit : k % 64 ≤ (source + k) % 64
          · rw [foldl_xorClmulAt_monomial_active_high_after_carry
              (acc :=
                (List.range m).foldl
                  (fun acc i =>
                    let x := xs[i]!
                    (List.range (k / 64 + 1)).foldl
                      (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                      acc)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
              (i := m) (k := k) (target := source + k) (x := xs[m]!)
              (hidx := by
                have hsize := foldl_mulWords_size (List.range m)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                  xs (monomial k).words
                rw [words_monomial_size] at hsize
                have hcap : m + k / 64 <
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              (hidxNext := by
                have hsize := foldl_mulWords_size (List.range m)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                  xs (monomial k).words
                rw [words_monomial_size] at hsize
                have hcap : m + k / 64 + 1 <
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
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
        · rw [foldl_xorClmulAt_monomial_ne
            (acc :=
              (List.range m).foldl
                (fun acc i =>
                  let x := xs[i]!
                  (List.range (k / 64 + 1)).foldl
                    (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                    acc)
                (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
            (i := m) (k := k) (target := source + k) (x := xs[m]!) hLow hHigh]
          simpa [words_monomial_size] using ih hm_le

private theorem foldl_mulWords_monomial_prefix_after_source
    (xs : Array UInt64) {k source m : Nat} (hm : source / 64 + 1 ≤ m)
    (hmSize : m ≤ xs.size)
    (hsource : source / 64 < xs.size) :
    coeffWords
        ((List.range m).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          (Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64)))
        (source + k) =
      coeffWords xs source := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      by_cases hm_active : m = source / 64
      · subst hm_active
        by_cases hbitShift : k % 64 = 0
        · rw [foldl_mulWords_monomial_active_zero
            (acc := Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))
            (xs := xs) (k := k) (n := source)
            (hidx := by simp [words_monomial_size]; omega) hbitShift]
          have hprefix := foldl_mulWords_monomial_prefix_before_source xs
            (m := source / 64) (k := k) (source := source) (by omega) hsource
          rw [hprefix]
          have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
            exact (getElem!_def xs (source / 64)).symm
          simp [coeffWords, hget]
        · by_cases hbit : source % 64 + k % 64 < 64
          · rw [foldl_mulWords_monomial_active_low
              (acc := Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))
              (xs := xs) (k := k) (n := source)
              (hidx := by simp [words_monomial_size]; omega) hbitShift hbit]
            have hprefix := foldl_mulWords_monomial_prefix_before_source xs
              (m := source / 64) (k := k) (source := source) (by omega) hsource
            rw [hprefix]
            have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
              exact (getElem!_def xs (source / 64)).symm
            simp [coeffWords, hget]
          · rw [foldl_mulWords_monomial_active_high
              (acc := Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))
              (xs := xs) (k := k) (n := source)
              (hidx := by simp [words_monomial_size]; omega)
              (hidxNext := by simp [words_monomial_size]; omega)
              (hbit := by omega)]
            have hprefix := foldl_mulWords_monomial_prefix_before_source xs
              (m := source / 64) (k := k) (source := source) (by omega) hsource
            rw [hprefix]
            have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
              exact (getElem!_def xs (source / 64)).symm
            simp [coeffWords, hget]
      · have hm_tail : source / 64 + 1 ≤ m := by omega
        have hm_gt : source / 64 < m := by omega
        rw [show m + 1 = m.succ by omega, List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [words_monomial_size]
        by_cases hLow : (source + k) / 64 = m + k / 64
        · by_cases hbit : (source + k) % 64 < k % 64
          · have hbitShift : k % 64 ≠ 0 := by omega
            rw [foldl_xorClmulAt_monomial_active_low_before_shift
              (acc :=
                (List.range m).foldl
                  (fun acc i =>
                    let x := xs[i]!
                    (List.range (k / 64 + 1)).foldl
                      (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                      acc)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
              (i := m) (k := k) (target := source + k) (x := xs[m]!)
              (hidx := by
                have hsize := foldl_mulWords_size (List.range m)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                  xs (monomial k).words
                rw [words_monomial_size] at hsize
                have hcap : m + k / 64 <
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
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
        · by_cases hHigh : (source + k) / 64 = m + k / 64 + 1
          · by_cases hbit : k % 64 ≤ (source + k) % 64
            · rw [foldl_xorClmulAt_monomial_active_high_after_carry
                (acc :=
                  (List.range m).foldl
                    (fun acc i =>
                      let x := xs[i]!
                      (List.range (k / 64 + 1)).foldl
                        (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                        acc)
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
                (i := m) (k := k) (target := source + k) (x := xs[m]!)
                (hidx := by
                  have hsize := foldl_mulWords_size (List.range m)
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                    xs (monomial k).words
                  rw [words_monomial_size] at hsize
                  have hcap : m + k / 64 <
                      (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
                    simp
                    omega
                  simpa [hsize] using hcap)
                (hidxNext := by
                  have hsize := foldl_mulWords_size (List.range m)
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                    xs (monomial k).words
                  rw [words_monomial_size] at hsize
                  have hcap : m + k / 64 + 1 <
                      (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
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
          · rw [foldl_xorClmulAt_monomial_ne
              (acc :=
                (List.range m).foldl
                  (fun acc i =>
                    let x := xs[i]!
                    (List.range (k / 64 + 1)).foldl
                      (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                      acc)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
              (i := m) (k := k) (target := source + k) (x := xs[m]!) hLow hHigh]
            simpa [words_monomial_size] using ih hm_tail (by omega)

private theorem coeffWords_mulWords_monomial_source
    (xs : Array UInt64) {k source : Nat} (hsource : source / 64 < xs.size) :
    coeffWords (mulWords xs (monomial k).words) (source + k) =
      coeffWords xs source := by
  unfold mulWords
  have hxs : ¬xs.isEmpty := by
    intro hempty
    have hsize : xs.size = 0 := by
      simpa [Array.isEmpty] using hempty
    omega
  have hys : ¬ (monomial k).words.isEmpty := by
    rw [words_monomial]
    simp
  simp [hxs, hys]
  exact foldl_mulWords_monomial_prefix_after_source xs
    (m := xs.size) (k := k) (source := source) (by omega) (by omega) hsource

private theorem coeffWords_monomial_mulWords_lt
    (xs : Array UInt64) {k target : Nat} (htarget : target < k) :
    coeffWords (mulWords (monomial k).words xs) target = false := by
  unfold mulWords
  have hmon : ¬ (monomial k).words.isEmpty := by
    rw [words_monomial]
    simp
  by_cases hxs : xs.isEmpty
  · simp [hmon, hxs, coeffWords]
  · simp [hmon, hxs]
    rw [words_monomial_size, show k / 64 + 1 = (k / 64).succ by omega,
      List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [foldl_mulWords_left_monomial_zero_prefix, foldl_xorClmulAt_monomial_left_target_lt]
    · rw [coeffWords]
      have hword :
          ((Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))[target / 64]?).getD
              0 = 0 := by
        by_cases h : target / 64 <
            (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword, UInt64.bne_zero_eq_toNat_bne_zero]
      simp
    · intro j hj
      exact List.mem_range.mp hj
    · simp
      omega
    · exact htarget

private theorem coeffWords_monomial_mulWords_source_oob
    (xs : Array UInt64) {k source : Nat} (hsource : xs.size ≤ source / 64) :
    coeffWords (mulWords (monomial k).words xs) (source + k) = false := by
  unfold mulWords
  have hmon : ¬ (monomial k).words.isEmpty := by
    rw [words_monomial]
    simp
  by_cases hxs : xs.isEmpty
  · simp [hmon, hxs, coeffWords]
  · simp [hmon, hxs]
    rw [words_monomial_size, show k / 64 + 1 = (k / 64).succ by omega,
      List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [foldl_mulWords_left_monomial_zero_prefix, foldl_xorClmulAt_monomial_left_source_oob]
    · rw [coeffWords]
      have hword :
          ((Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))[(source + k) / 64]?).getD
              0 = 0 := by
        by_cases h : (source + k) / 64 <
            (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword, UInt64.bne_zero_eq_toNat_bne_zero]
      simp
    · intro j hj
      exact List.mem_range.mp hj
    · simp
      omega
    · exact hsource

private theorem coeffWords_monomial_mulWords_source
    (xs : Array UInt64) {k source : Nat} (hsource : source / 64 < xs.size) :
    coeffWords (mulWords (monomial k).words xs) (source + k) =
      coeffWords xs source := by
  unfold mulWords
  have hmon : ¬ (monomial k).words.isEmpty := by
    rw [words_monomial]
    simp
  have hxs : ¬ xs.isEmpty := by
    intro hempty
    have hsize : xs.size = 0 := by
      simpa [Array.isEmpty] using hempty
    omega
  simp [hmon, hxs]
  rw [words_monomial_size, show k / 64 + 1 = (k / 64).succ by omega,
    List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [foldl_mulWords_left_monomial_zero_prefix]
  simpa [words_monomial_size] using
    foldl_xorClmulAt_monomial_left_prefix_after_source xs
      (m := xs.size) (k := k) (source := source) (by omega) (by omega) hsource


end GF2Poly
end Hex
