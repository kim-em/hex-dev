import HexGF2.Basic
import Std.Tactic.BVDecide

/-!
Carry-less `UInt64` multiplication for `hex-gf2`.

`pureClmul` is the logical reference implementation used in proofs and by the
fallback runtime path. The `@[extern]` boundary lets compiled code swap in a C
shim that may dispatch to architecture intrinsics, but the trusted contract is
still exactly the `(hi, lo)` product returned by `pureClmul`.
-/
namespace Hex

/-- XOR the carry-less partial product `a * x^bitIdx` into the `(hi, lo)`
accumulator. The caller must supply `bitIdx < 64`. -/
private def clmulAccumulateBit (acc : UInt64 × UInt64) (a : UInt64) (bitIdx : Nat) :
    UInt64 × UInt64 :=
  let (hi, lo) := acc
  if bitIdx = 0 then
    (hi, lo ^^^ a)
  else
    let loPart := a <<< bitIdx.toUInt64
    let hiPart := a >>> (64 - bitIdx).toUInt64
    (hi ^^^ hiPart, lo ^^^ loPart)

/-- Pure Lean carry-less multiplication of two 64-bit words, returned as
`(hi, lo)` for the 128-bit product. -/
def pureClmul (a b : UInt64) : UInt64 × UInt64 :=
  (List.range 64).foldl
    (fun acc bitIdx =>
      if ((b >>> bitIdx.toUInt64) &&& 1) != 0 then
        clmulAccumulateBit acc a bitIdx
      else
        acc)
    (0, 0)

/-- Accumulating the partial product of a zero left word leaves the
`(hi, lo)` accumulator unchanged. -/
private theorem clmulAccumulateBit_zero_left (acc : UInt64 × UInt64) (bitIdx : Nat) :
    clmulAccumulateBit acc 0 bitIdx = acc := by
  by_cases h : bitIdx = 0 <;> simp [clmulAccumulateBit, h]

/-- `clmulAccumulateBit` is linear over bitwise XOR in the accumulator and
left word jointly: accumulating `x ^^^ y` into componentwise-XORed accumulators
equals the XOR of the two separate accumulations. -/
private theorem clmulAccumulateBit_xor_left
    (accX accY : UInt64 × UInt64) (x y : UInt64) (bitIdx : Nat) :
    clmulAccumulateBit (accX.1 ^^^ accY.1, accX.2 ^^^ accY.2) (x ^^^ y) bitIdx =
      ((clmulAccumulateBit accX x bitIdx).1 ^^^ (clmulAccumulateBit accY y bitIdx).1,
        (clmulAccumulateBit accX x bitIdx).2 ^^^ (clmulAccumulateBit accY y bitIdx).2) := by
  by_cases h : bitIdx = 0 <;> simp [clmulAccumulateBit, h] <;> bv_decide

/-- The partial-product fold is linear over bitwise XOR in the left word:
folding `x ^^^ y` from componentwise-XORed seed accumulators equals the XOR of
the two separate folds of `x` and `y`. -/
private theorem foldl_clmul_xor_left (bits : List Nat)
    (accX accY : UInt64 × UInt64) (x y z : UInt64) :
    bits.foldl
        (fun acc bitIdx =>
          if ((z >>> bitIdx.toUInt64) &&& 1) != 0 then
            clmulAccumulateBit acc (x ^^^ y) bitIdx
          else
            acc)
        (accX.1 ^^^ accY.1, accX.2 ^^^ accY.2) =
      let outX := bits.foldl
        (fun acc bitIdx =>
          if ((z >>> bitIdx.toUInt64) &&& 1) != 0 then
            clmulAccumulateBit acc x bitIdx
          else
            acc)
        accX
      let outY := bits.foldl
        (fun acc bitIdx =>
          if ((z >>> bitIdx.toUInt64) &&& 1) != 0 then
            clmulAccumulateBit acc y bitIdx
          else
            acc)
        accY
      (outX.1 ^^^ outY.1, outX.2 ^^^ outY.2) := by
  induction bits generalizing accX accY with
  | nil =>
      simp
  | cons bitIdx bits ih =>
      simp only [List.foldl_cons]
      by_cases hbit : ((z >>> bitIdx.toUInt64) &&& 1) != 0
      · simp [hbit]
        rw [clmulAccumulateBit_xor_left]
        simpa using ih (clmulAccumulateBit accX x bitIdx) (clmulAccumulateBit accY y bitIdx)
      · simp [hbit]
        simpa using ih accX accY

/-- The pure carry-less multiplier is linear in its left word argument over
bitwise XOR. -/
theorem pureClmul_xor_left (x y z : UInt64) :
    pureClmul (x ^^^ y) z =
      ((pureClmul x z).1 ^^^ (pureClmul y z).1,
        (pureClmul x z).2 ^^^ (pureClmul y z).2) := by
  unfold pureClmul
  simpa using foldl_clmul_xor_left (List.range 64) (0, 0) (0, 0) x y z

/-- Folding with a step that discards the list element and returns the
accumulator unchanged yields the initial accumulator. -/
private theorem foldl_keep {α β : Type} (xs : List β) (acc : α) :
    xs.foldl (fun acc _ => acc) acc = acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons _ xs ih => simp [ih]

/-- The pure carry-less multiplier returns zero when the left word is zero. -/
@[simp]
theorem pureClmul_zero_left (x : UInt64) : pureClmul 0 x = (0, 0) := by
  simp [pureClmul, clmulAccumulateBit_zero_left, foldl_keep]

/-- The pure carry-less multiplier returns zero when the right word is zero. -/
@[simp]
theorem pureClmul_zero_right (x : UInt64) : pureClmul x 0 = (0, 0) := by
  simp [pureClmul, foldl_keep]

/-- Bit `bit` of the one-hot word `1 <<< hot` is set exactly when `hot = bit`. -/
private theorem oneHotWord_bit {hot bit : Nat} (hhot : hot < 64) (hbit : bit < 64) :
    (((((1 : UInt64) <<< hot.toUInt64) >>> bit.toUInt64) &&& 1) != 0) = (hot == bit) := by
  by_cases h : hot = bit
  · subst h
    simp [GF2Poly.oneHotWord_bit_self hbit]
  · rw [GF2Poly.oneHotWord_bit_ne hhot hbit h]
    simp [h]

/-- Accumulating the partial product `a * x^bit` into the zero accumulator gives
`(0, a)` at `bit = 0` and otherwise the shifted split `(a >>> (64 - bit), a <<< bit)`. -/
private theorem clmulAccumulateBit_zero (a : UInt64) (bit : Nat) :
    clmulAccumulateBit (0, 0) a bit =
      if bit = 0 then (0, a) else (a >>> (64 - bit).toUInt64, a <<< bit.toUInt64) := by
  by_cases h : bit = 0 <;> simp [clmulAccumulateBit, h]

/-- Left-shifting the one-hot word `1 <<< hot` by `bitIdx`, when `hot + bitIdx < 64`,
yields the one-hot word `1 <<< (hot + bitIdx)`. -/
private theorem oneHot_shiftLeft_of_sum_lt {hot bitIdx : Nat}
    (hhot : hot < 64) (hbitIdx : bitIdx < 64) (hsum : hot + bitIdx < 64) :
    (((1 : UInt64) <<< hot.toUInt64) <<< bitIdx.toUInt64) =
      ((1 : UInt64) <<< (hot + bitIdx).toUInt64) := by
  apply UInt64.toNat_inj.mp
  have hpowHot : 2 ^ hot < 2 ^ 64 := Nat.pow_lt_pow_of_lt (by decide : 1 < 2) hhot
  have hpowSum : 2 ^ (hot + bitIdx) < 2 ^ 64 :=
    Nat.pow_lt_pow_of_lt (by decide : 1 < 2) hsum
  simp [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hhot,
    Nat.mod_eq_of_lt hbitIdx, Nat.mod_eq_of_lt hsum, Nat.mod_eq_of_lt hpowHot,
    Nat.mod_eq_of_lt hpowSum, Nat.shiftLeft_eq]
  rw [← Nat.pow_add]
  exact Nat.mod_eq_of_lt hpowSum

/-- Left-shifting the one-hot word `1 <<< hot` by `bitIdx`, when `64 ≤ hot + bitIdx`,
overflows out of the word to `0`. -/
private theorem oneHot_shiftLeft_of_sum_ge {hot bitIdx : Nat}
    (hhot : hot < 64) (hbitIdx : bitIdx < 64) (hsum : 64 ≤ hot + bitIdx) :
    (((1 : UInt64) <<< hot.toUInt64) <<< bitIdx.toUInt64) = 0 := by
  apply UInt64.toNat_inj.mp
  have hpowHot : 2 ^ hot < 2 ^ 64 := Nat.pow_lt_pow_of_lt (by decide : 1 < 2) hhot
  simp [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hhot,
    Nat.mod_eq_of_lt hbitIdx, Nat.mod_eq_of_lt hpowHot, Nat.shiftLeft_eq]
  have hdiv : 2 ^ 64 ∣ 2 ^ hot * 2 ^ bitIdx := by
    rw [← Nat.pow_add]
    exact Nat.pow_dvd_pow 2 hsum
  exact Nat.mod_eq_zero_of_dvd hdiv

/-- Right-shifting the one-hot word `1 <<< hot` by `64 - bitIdx`, when
`hot + bitIdx < 64`, yields `0` (the partial product produces no high carry-out). -/
private theorem oneHot_shiftRight_of_sum_lt {hot bitIdx : Nat}
    (hhot : hot < 64) (hbitIdx : bitIdx < 64) (hbitIdxPos : 0 < bitIdx)
    (hsum : hot + bitIdx < 64) :
    (((1 : UInt64) <<< hot.toUInt64) >>> (64 - bitIdx).toUInt64) = 0 := by
  apply UInt64.toNat_inj.mp
  have hpowHot : 2 ^ hot < 2 ^ 64 := Nat.pow_lt_pow_of_lt (by decide : 1 < 2) hhot
  have hshift : 64 - bitIdx < 64 := by omega
  simp [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight,
    Nat.mod_eq_of_lt hhot, Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt hpowHot,
    Nat.shiftLeft_eq]
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt
    (Nat.pow_lt_pow_of_lt (by decide : 1 < 2) (by omega))

/-- Right-shifting the one-hot word `1 <<< hot` by `64 - bitIdx`, when
`64 ≤ hot + bitIdx`, yields the carried-out one-hot word `1 <<< (hot + bitIdx - 64)`. -/
private theorem oneHot_shiftRight_of_sum_ge {hot bitIdx : Nat}
    (hhot : hot < 64) (hbitIdx : bitIdx < 64) (hsum : 64 ≤ hot + bitIdx) :
    (((1 : UInt64) <<< hot.toUInt64) >>> (64 - bitIdx).toUInt64) =
      ((1 : UInt64) <<< (hot + bitIdx - 64).toUInt64) := by
  apply UInt64.toNat_inj.mp
  have hpowHot : 2 ^ hot < 2 ^ 64 := Nat.pow_lt_pow_of_lt (by decide : 1 < 2) hhot
  have hshift : 64 - bitIdx < 64 := by omega
  have htarget : hot + bitIdx - 64 < 64 := by omega
  have hpowTarget : 2 ^ (hot + bitIdx - 64) < 2 ^ 64 :=
    Nat.pow_lt_pow_of_lt (by decide : 1 < 2) htarget
  have hexp : hot = (64 - bitIdx) + (hot + bitIdx - 64) := by omega
  simp [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight,
    Nat.mod_eq_of_lt hhot, Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt htarget,
    Nat.mod_eq_of_lt hpowHot, Nat.mod_eq_of_lt hpowTarget, Nat.shiftLeft_eq]
  rw [hexp, Nat.pow_add]
  rw [Nat.shiftRight_eq_div_pow]
  have hrhs : 64 - bitIdx + (hot + bitIdx - 64) + bitIdx - 64 =
      hot + bitIdx - 64 := by
    omega
  rw [hrhs]
  have hpos : 0 < 2 ^ (64 - bitIdx) := Nat.pow_pos (by decide : 0 < 2)
  exact Nat.mul_div_right _ hpos

/-- Accumulating the one-hot left word `1 <<< hot` at shift `bitIdx`, when
`hot + bitIdx < 64`, XORs `1 <<< (hot + bitIdx)` into the low word and leaves the
high word unchanged. -/
private theorem clmulAccumulateBit_oneHot_low {hot bitIdx : Nat}
    (acc : UInt64 × UInt64) (hhot : hot < 64) (hbitIdx : bitIdx < 64)
    (hsum : hot + bitIdx < 64) :
    clmulAccumulateBit acc ((1 : UInt64) <<< hot.toUInt64) bitIdx =
      (acc.1, acc.2 ^^^ ((1 : UInt64) <<< (hot + bitIdx).toUInt64)) := by
  by_cases hzero : bitIdx = 0
  · subst bitIdx
    simp [clmulAccumulateBit]
  · have hbitIdxPos : 0 < bitIdx := Nat.pos_of_ne_zero hzero
    simp [clmulAccumulateBit, hzero,
      oneHot_shiftLeft_of_sum_lt hhot hbitIdx hsum,
      oneHot_shiftRight_of_sum_lt hhot hbitIdx hbitIdxPos hsum]

/-- Accumulating the one-hot left word `1 <<< hot` at shift `bitIdx`, when
`64 ≤ hot + bitIdx`, XORs `1 <<< (hot + bitIdx - 64)` into the high word and leaves
the low word unchanged. -/
private theorem clmulAccumulateBit_oneHot_high {hot bitIdx : Nat}
    (acc : UInt64 × UInt64) (hhot : hot < 64) (hbitIdx : bitIdx < 64)
    (hsum : 64 ≤ hot + bitIdx) :
    clmulAccumulateBit acc ((1 : UInt64) <<< hot.toUInt64) bitIdx =
      (acc.1 ^^^ ((1 : UInt64) <<< (hot + bitIdx - 64).toUInt64), acc.2) := by
  have hzero : bitIdx ≠ 0 := by omega
  simp [clmulAccumulateBit, hzero, oneHot_shiftLeft_of_sum_ge hhot hbitIdx hsum,
    oneHot_shiftRight_of_sum_ge hhot hbitIdx hsum]

/-- One fold step for multiplying by the one-hot right word `1 <<< hot`:
accumulate `a`'s partial product at `bitIdx` only when `bitIdx` is the hot bit. -/
private def clmulOneHotStep (a : UInt64) (hot : Nat) (acc : UInt64 × UInt64)
    (bitIdx : Nat) : UInt64 × UInt64 :=
  if (((((1 : UInt64) <<< hot.toUInt64) >>> bitIdx.toUInt64) &&& 1) != 0) then
    clmulAccumulateBit acc a bitIdx
  else
    acc

/-- A one-hot fold step at a non-hot index `bitIdx ≠ hot` leaves the accumulator
unchanged. -/
private theorem clmulOneHotStep_of_ne (a : UInt64) {hot bitIdx : Nat}
    (hhot : hot < 64) (hbitIdx : bitIdx < 64) (hne : hot ≠ bitIdx)
    (acc : UInt64 × UInt64) :
    clmulOneHotStep a hot acc bitIdx = acc := by
  have hclear :
      (((((1 : UInt64) <<< hot.toUInt64) >>> bitIdx.toUInt64) &&& 1) != 0) = false := by
    rw [oneHotWord_bit hhot hbitIdx]
    simp [hne]
  simp [clmulOneHotStep, hclear]

/-- A one-hot fold step at the hot index reduces to the plain
`clmulAccumulateBit` of `a` at `hot`. -/
private theorem clmulOneHotStep_self (a : UInt64) {hot : Nat} (hhot : hot < 64)
    (acc : UInt64 × UInt64) :
    clmulOneHotStep a hot acc hot = clmulAccumulateBit acc a hot := by
  simp [clmulOneHotStep, GF2Poly.oneHotWord_bit_self hhot]

/-- Folding the one-hot step over a bit list that does not contain `hot` leaves
the accumulator unchanged. -/
private theorem foldl_oneHot_absent (a : UInt64) {hot : Nat} (hhot : hot < 64)
    (acc : UInt64 × UInt64) :
    ∀ (xs : List Nat),
      hot ∉ xs →
      (∀ bitIdx ∈ xs, bitIdx < 64) →
      xs.foldl (clmulOneHotStep a hot) acc = acc := by
  intro xs
  induction xs generalizing acc with
  | nil =>
      intro _ _
      simp
  | cons bitIdx xs ih =>
      intro hnot hlt
      have hne : hot ≠ bitIdx := by
        intro h
        exact hnot (by simp [h])
      have hbitIdx : bitIdx < 64 := hlt bitIdx (by simp)
      have hnotTail : hot ∉ xs := by
        intro hmem
        exact hnot (by simp [hmem])
      have hltTail : ∀ idx ∈ xs, idx < 64 := by
        intro idx hmem
        exact hlt idx (by simp [hmem])
      rw [List.foldl_cons, clmulOneHotStep_of_ne a hhot hbitIdx hne acc]
      exact ih acc hnotTail hltTail

/-- Folding the one-hot step over a duplicate-free bit list from `(0, 0)` yields a
single `clmulAccumulateBit` at `hot` when `hot` is present, and `(0, 0)` otherwise. -/
private theorem foldl_oneHot_list (a : UInt64) {hot : Nat} (hhot : hot < 64) :
    ∀ (xs : List Nat),
      xs.Nodup →
      (∀ bitIdx ∈ xs, bitIdx < 64) →
      xs.foldl (clmulOneHotStep a hot) (0, 0) =
        if hot ∈ xs then clmulAccumulateBit (0, 0) a hot else (0, 0) := by
  intro xs
  induction xs with
  | nil =>
      intro _ _
      simp
  | cons bitIdx xs ih =>
      intro hnodup hlt
      have hbitIdx : bitIdx < 64 := hlt bitIdx (by simp)
      have hltTail : ∀ idx ∈ xs, idx < 64 := by
        intro idx hmem
        exact hlt idx (by simp [hmem])
      by_cases hhit : bitIdx = hot
      · subst bitIdx
        have hnotTail : hot ∉ xs := by
          exact (List.nodup_cons.mp hnodup).1
        rw [List.foldl_cons, clmulOneHotStep_self a hhot]
        rw [foldl_oneHot_absent a hhot _ xs hnotTail hltTail]
        simp
      · have hstep :
            clmulOneHotStep a hot (0, 0) bitIdx = (0, 0) :=
          clmulOneHotStep_of_ne a hhot hbitIdx (Ne.symm hhit) (0, 0)
        rw [List.foldl_cons, hstep]
        have hnodupTail : xs.Nodup := (List.nodup_cons.mp hnodup).2
        rw [ih hnodupTail hltTail]
        have hhot_ne : hot ≠ bitIdx := Ne.symm hhit
        simp [hhot_ne]

/-- The full 64-bit `pureClmul` fold against the one-hot right word `1 <<< hot`
collapses to a single `clmulAccumulateBit (0, 0) a hot`. -/
private theorem foldl_oneHot (a : UInt64) {hot : Nat} (hhot : hot < 64) :
    (List.range 64).foldl
        (fun acc bitIdx =>
          if (((((1 : UInt64) <<< hot.toUInt64) >>> bitIdx.toUInt64) &&& 1) != 0) then
            clmulAccumulateBit acc a bitIdx
          else
            acc)
        (0, 0) =
      clmulAccumulateBit (0, 0) a hot := by
  change (List.range 64).foldl (clmulOneHotStep a hot) (0, 0) =
    clmulAccumulateBit (0, 0) a hot
  have hfold := foldl_oneHot_list (a := a) hhot (List.range 64)
    (List.nodup_range : (List.range 64).Nodup)
    (by
      intro bitIdx hmem
      exact List.mem_range.mp hmem)
  simpa [hhot] using hfold

/-- Carry-less multiplication by an in-word monomial has one contributing
partial product in the pure fold. -/
theorem pureClmul_oneHot (a : UInt64) {bit : Nat} (hbit : bit < 64) :
    pureClmul a ((1 : UInt64) <<< bit.toUInt64) =
      if bit = 0 then (0, a) else (a >>> (64 - bit).toUInt64, a <<< bit.toUInt64) := by
  rw [pureClmul, foldl_oneHot a hbit, clmulAccumulateBit_zero]

/-- Low-word fold step for the one-hot left word `1 <<< hot`: XOR
`1 <<< (hot + bitIdx)` into the low word when bit `bitIdx` of `a` is set and
`hot + bitIdx < 64`, otherwise leave it unchanged. -/
private def clmulOneHotLeftLowStep (hot : Nat) (a lo : UInt64) (bitIdx : Nat) : UInt64 :=
  if (((a >>> bitIdx.toUInt64) &&& 1) != 0) then
    if hot + bitIdx < 64 then
      lo ^^^ ((1 : UInt64) <<< (hot + bitIdx).toUInt64)
    else
      lo
  else
    lo

/-- The low word (`.2`) of the one-hot-left accumulation fold equals folding
`clmulOneHotLeftLowStep` over the low word alone. -/
private theorem foldl_oneHot_left_snd_eq_lowStep (a : UInt64) {hot : Nat}
    (hhot : hot < 64) :
    ∀ (xs : List Nat) (acc : UInt64 × UInt64),
      (∀ bitIdx ∈ xs, bitIdx < 64) →
      (xs.foldl
          (fun acc bitIdx =>
            if (((a >>> bitIdx.toUInt64) &&& 1) != 0) then
              clmulAccumulateBit acc ((1 : UInt64) <<< hot.toUInt64) bitIdx
            else
              acc)
          acc).2 =
        xs.foldl (clmulOneHotLeftLowStep hot a) acc.2 := by
  intro xs
  induction xs with
  | nil =>
      intro acc _
      simp
  | cons bitIdx xs ih =>
      intro acc hlt
      have hbitIdx : bitIdx < 64 := hlt bitIdx (by simp)
      have hltTail : ∀ idx ∈ xs, idx < 64 := by
        intro idx hmem
        exact hlt idx (by simp [hmem])
      rw [List.foldl_cons, List.foldl_cons]
      by_cases hset : (((a >>> bitIdx.toUInt64) &&& 1) != 0) = true
      · by_cases hsum : hot + bitIdx < 64
        · rw [if_pos hset]
          have hlowStep :
              clmulOneHotLeftLowStep hot a acc.2 bitIdx =
                acc.2 ^^^ ((1 : UInt64) <<< (hot + bitIdx).toUInt64) := by
            simp [clmulOneHotLeftLowStep, hset, hsum]
          rw [clmulAccumulateBit_oneHot_low acc hhot hbitIdx hsum]
          simpa [hlowStep] using
            ih (acc.1, acc.2 ^^^ ((1 : UInt64) <<< (hot + bitIdx).toUInt64)) hltTail
        · have hsumGe : 64 ≤ hot + bitIdx := Nat.le_of_not_gt hsum
          rw [if_pos hset]
          have hlowStep : clmulOneHotLeftLowStep hot a acc.2 bitIdx = acc.2 := by
            simp [clmulOneHotLeftLowStep, hset, hsum]
          rw [clmulAccumulateBit_oneHot_high acc hhot hbitIdx hsumGe]
          simpa [hlowStep] using
            ih (acc.1 ^^^ ((1 : UInt64) <<< (hot + bitIdx - 64).toUInt64), acc.2) hltTail
      · rw [if_neg hset]
        have hlowStep : clmulOneHotLeftLowStep hot a acc.2 bitIdx = acc.2 := by
          simp [clmulOneHotLeftLowStep, hset]
        simpa [hlowStep] using ih acc hltTail

set_option maxHeartbeats 2000000 in
/-- Low word of pure carry-less multiplication with an in-word monomial on the
left. -/
theorem pureClmul_oneHot_left_snd (a : UInt64) {bit : Nat} (hbit : bit < 64) :
    (pureClmul ((1 : UInt64) <<< bit.toUInt64) a).2 =
      if bit = 0 then a else a <<< bit.toUInt64 := by
  rw [pureClmul]
  rw [foldl_oneHot_left_snd_eq_lowStep a hbit (List.range 64) (0, 0)
    (by
      intro bitIdx hmem
      exact List.mem_range.mp hmem)]
  have hcases : bit = 0 ∨ bit = 1 ∨ bit = 2 ∨ bit = 3 ∨ bit = 4 ∨ bit = 5 ∨
      bit = 6 ∨ bit = 7 ∨ bit = 8 ∨ bit = 9 ∨ bit = 10 ∨ bit = 11 ∨
      bit = 12 ∨ bit = 13 ∨ bit = 14 ∨ bit = 15 ∨ bit = 16 ∨ bit = 17 ∨
      bit = 18 ∨ bit = 19 ∨ bit = 20 ∨ bit = 21 ∨ bit = 22 ∨ bit = 23 ∨
      bit = 24 ∨ bit = 25 ∨ bit = 26 ∨ bit = 27 ∨ bit = 28 ∨ bit = 29 ∨
      bit = 30 ∨ bit = 31 ∨ bit = 32 ∨ bit = 33 ∨ bit = 34 ∨ bit = 35 ∨
      bit = 36 ∨ bit = 37 ∨ bit = 38 ∨ bit = 39 ∨ bit = 40 ∨ bit = 41 ∨
      bit = 42 ∨ bit = 43 ∨ bit = 44 ∨ bit = 45 ∨ bit = 46 ∨ bit = 47 ∨
      bit = 48 ∨ bit = 49 ∨ bit = 50 ∨ bit = 51 ∨ bit = 52 ∨ bit = 53 ∨
      bit = 54 ∨ bit = 55 ∨ bit = 56 ∨ bit = 57 ∨ bit = 58 ∨ bit = 59 ∨
      bit = 60 ∨ bit = 61 ∨ bit = 62 ∨ bit = 63 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [List.range, List.range.loop, List.foldl, clmulOneHotLeftLowStep] <;>
    bv_decide

/-- High-word fold step for the one-hot left word `1 <<< hot`: XOR
`1 <<< (hot + bitIdx - 64)` into the high word when bit `bitIdx` of `a` is set and
`64 ≤ hot + bitIdx`, otherwise leave it unchanged. -/
private def clmulOneHotLeftHighStep (hot : Nat) (a hi : UInt64) (bitIdx : Nat) : UInt64 :=
  if (((a >>> bitIdx.toUInt64) &&& 1) != 0) then
    if hot + bitIdx < 64 then
      hi
    else
      hi ^^^ ((1 : UInt64) <<< (hot + bitIdx - 64).toUInt64)
  else
    hi

/-- The high word (`.1`) of the one-hot-left accumulation fold equals folding
`clmulOneHotLeftHighStep` over the high word alone. -/
private theorem foldl_oneHot_left_fst_eq_highStep (a : UInt64) {hot : Nat}
    (hhot : hot < 64) :
    ∀ (xs : List Nat) (acc : UInt64 × UInt64),
      (∀ bitIdx ∈ xs, bitIdx < 64) →
      (xs.foldl
          (fun acc bitIdx =>
            if (((a >>> bitIdx.toUInt64) &&& 1) != 0) then
              clmulAccumulateBit acc ((1 : UInt64) <<< hot.toUInt64) bitIdx
            else
              acc)
          acc).1 =
        xs.foldl (clmulOneHotLeftHighStep hot a) acc.1 := by
  intro xs
  induction xs with
  | nil =>
      intro acc _
      simp
  | cons bitIdx xs ih =>
      intro acc hlt
      have hbitIdx : bitIdx < 64 := hlt bitIdx (by simp)
      have hltTail : ∀ idx ∈ xs, idx < 64 := by
        intro idx hmem
        exact hlt idx (by simp [hmem])
      rw [List.foldl_cons, List.foldl_cons]
      by_cases hset : (((a >>> bitIdx.toUInt64) &&& 1) != 0) = true
      · by_cases hsum : hot + bitIdx < 64
        · rw [if_pos hset]
          have hhighStep : clmulOneHotLeftHighStep hot a acc.1 bitIdx = acc.1 := by
            simp [clmulOneHotLeftHighStep, hset, hsum]
          rw [clmulAccumulateBit_oneHot_low acc hhot hbitIdx hsum]
          simpa [hhighStep] using
            ih (acc.1, acc.2 ^^^ ((1 : UInt64) <<< (hot + bitIdx).toUInt64)) hltTail
        · have hsumGe : 64 ≤ hot + bitIdx := Nat.le_of_not_gt hsum
          rw [if_pos hset]
          have hhighStep :
              clmulOneHotLeftHighStep hot a acc.1 bitIdx =
                acc.1 ^^^ ((1 : UInt64) <<< (hot + bitIdx - 64).toUInt64) := by
            simp [clmulOneHotLeftHighStep, hset, hsum]
          rw [clmulAccumulateBit_oneHot_high acc hhot hbitIdx hsumGe]
          simpa [hhighStep] using
            ih (acc.1 ^^^ ((1 : UInt64) <<< (hot + bitIdx - 64).toUInt64), acc.2)
              hltTail
      · rw [if_neg hset]
        have hhighStep : clmulOneHotLeftHighStep hot a acc.1 bitIdx = acc.1 := by
          simp [clmulOneHotLeftHighStep, hset]
        simpa [hhighStep] using ih acc hltTail

set_option maxHeartbeats 2000000 in
/-- High word of pure carry-less multiplication with an in-word monomial on the
left. -/
theorem pureClmul_oneHot_left_fst (a : UInt64) {bit : Nat} (hbit : bit < 64) :
    (pureClmul ((1 : UInt64) <<< bit.toUInt64) a).1 =
      if bit = 0 then 0 else a >>> (64 - bit).toUInt64 := by
  rw [pureClmul]
  rw [foldl_oneHot_left_fst_eq_highStep a hbit (List.range 64) (0, 0)
    (by
      intro bitIdx hmem
      exact List.mem_range.mp hmem)]
  have hcases : bit = 0 ∨ bit = 1 ∨ bit = 2 ∨ bit = 3 ∨ bit = 4 ∨ bit = 5 ∨
      bit = 6 ∨ bit = 7 ∨ bit = 8 ∨ bit = 9 ∨ bit = 10 ∨ bit = 11 ∨
      bit = 12 ∨ bit = 13 ∨ bit = 14 ∨ bit = 15 ∨ bit = 16 ∨ bit = 17 ∨
      bit = 18 ∨ bit = 19 ∨ bit = 20 ∨ bit = 21 ∨ bit = 22 ∨ bit = 23 ∨
      bit = 24 ∨ bit = 25 ∨ bit = 26 ∨ bit = 27 ∨ bit = 28 ∨ bit = 29 ∨
      bit = 30 ∨ bit = 31 ∨ bit = 32 ∨ bit = 33 ∨ bit = 34 ∨ bit = 35 ∨
      bit = 36 ∨ bit = 37 ∨ bit = 38 ∨ bit = 39 ∨ bit = 40 ∨ bit = 41 ∨
      bit = 42 ∨ bit = 43 ∨ bit = 44 ∨ bit = 45 ∨ bit = 46 ∨ bit = 47 ∨
      bit = 48 ∨ bit = 49 ∨ bit = 50 ∨ bit = 51 ∨ bit = 52 ∨ bit = 53 ∨
      bit = 54 ∨ bit = 55 ∨ bit = 56 ∨ bit = 57 ∨ bit = 58 ∨ bit = 59 ∨
      bit = 60 ∨ bit = 61 ∨ bit = 62 ∨ bit = 63 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [List.range, List.range.loop, List.foldl, clmulOneHotLeftHighStep] <;>
    bv_decide

/-- Pure carry-less multiplication with an in-word monomial on the left. -/
theorem pureClmul_oneHot_left (a : UInt64) {bit : Nat} (hbit : bit < 64) :
    pureClmul ((1 : UInt64) <<< bit.toUInt64) a =
      if bit = 0 then (0, a) else (a >>> (64 - bit).toUInt64, a <<< bit.toUInt64) := by
  ext
  · rw [pureClmul_oneHot_left_fst a hbit]
    by_cases h : bit = 0 <;> simp [h]
  · rw [pureClmul_oneHot_left_snd a hbit]
    by_cases h : bit = 0 <;> simp [h]

/-- Trusted runtime hook for carry-less multiplication.

The compiled C shim must return the same `(hi, lo)` pair as `pureClmul`; the
intrinsic-backed implementations are an optimization only. -/
@[extern "lean_hex_clmul_u64"]
def clmul (a b : @& UInt64) : UInt64 × UInt64 :=
  pureClmul a b

/-- The trusted extern-backed multiplier has `pureClmul` as its logical
reference semantics. -/
theorem clmul_eq_pureClmul (a b : UInt64) : clmul a b = pureClmul a b := by
  rw [clmul]

/-- The high word of the extern-backed multiplier has `pureClmul` as its
logical reference semantics. -/
theorem clmul_eq_pureClmul_fst (a b : UInt64) : (clmul a b).1 = (pureClmul a b).1 := by
  rw [clmul_eq_pureClmul]

/-- The low word of the extern-backed multiplier has `pureClmul` as its logical
reference semantics. -/
theorem clmul_eq_pureClmul_snd (a b : UInt64) : (clmul a b).2 = (pureClmul a b).2 := by
  rw [clmul_eq_pureClmul]

/-- Carry-less multiplication by zero on the left returns the zero product. -/
@[simp]
theorem clmul_zero_left (x : UInt64) : clmul 0 x = (0, 0) := by
  rw [clmul_eq_pureClmul, pureClmul_zero_left]

/-- Carry-less multiplication by zero on the right returns the zero product. -/
@[simp]
theorem clmul_zero_right (x : UInt64) : clmul x 0 = (0, 0) := by
  rw [clmul_eq_pureClmul, pureClmul_zero_right]

/-- Runtime `clmul`, under its trusted reference contract, agrees with the
one-hot pure carry-less multiplication split. -/
theorem clmul_oneHot (a : UInt64) {bit : Nat} (hbit : bit < 64) :
    clmul a ((1 : UInt64) <<< bit.toUInt64) =
      if bit = 0 then (0, a) else (a >>> (64 - bit).toUInt64, a <<< bit.toUInt64) := by
  rw [clmul, pureClmul_oneHot a hbit]

/-- Runtime `clmul`, under its trusted reference contract, is linear in its
left word argument over bitwise XOR. -/
@[grind =]
theorem clmul_xor_left (x y z : UInt64) :
    clmul (x ^^^ y) z =
      ((clmul x z).1 ^^^ (clmul y z).1, (clmul x z).2 ^^^ (clmul y z).2) := by
  rw [clmul, clmul, clmul, pureClmul_xor_left]

/-- High word of carry-less multiplication by an in-word monomial. -/
theorem clmul_oneHot_fst (a : UInt64) {bit : Nat} (hbit : bit < 64) :
    (clmul a ((1 : UInt64) <<< bit.toUInt64)).1 =
      if bit = 0 then 0 else a >>> (64 - bit).toUInt64 := by
  rw [clmul_oneHot a hbit]
  by_cases h : bit = 0 <;> simp [h]

/-- Low word of carry-less multiplication by an in-word monomial. -/
theorem clmul_oneHot_snd (a : UInt64) {bit : Nat} (hbit : bit < 64) :
    (clmul a ((1 : UInt64) <<< bit.toUInt64)).2 =
      if bit = 0 then a else a <<< bit.toUInt64 := by
  rw [clmul_oneHot a hbit]
  by_cases h : bit = 0 <;> simp [h]

/-- Runtime `clmul`, under its trusted reference contract, with an in-word
monomial on the left. -/
theorem clmul_oneHot_left (a : UInt64) {bit : Nat} (hbit : bit < 64) :
    clmul ((1 : UInt64) <<< bit.toUInt64) a =
      if bit = 0 then (0, a) else (a >>> (64 - bit).toUInt64, a <<< bit.toUInt64) := by
  rw [clmul, pureClmul_oneHot_left a hbit]

/-- High word of carry-less multiplication with an in-word monomial on the left. -/
theorem clmul_oneHot_left_fst (a : UInt64) {bit : Nat} (hbit : bit < 64) :
    (clmul ((1 : UInt64) <<< bit.toUInt64) a).1 =
      if bit = 0 then 0 else a >>> (64 - bit).toUInt64 := by
  rw [clmul_oneHot_left a hbit]
  by_cases h : bit = 0 <;> simp [h]

/-- Low word of carry-less multiplication with an in-word monomial on the left. -/
theorem clmul_oneHot_left_snd (a : UInt64) {bit : Nat} (hbit : bit < 64) :
    (clmul ((1 : UInt64) <<< bit.toUInt64) a).2 =
      if bit = 0 then a else a <<< bit.toUInt64 := by
  rw [clmul_oneHot_left a hbit]
  by_cases h : bit = 0 <;> simp [h]

private def xorPair (x y : UInt64 × UInt64) : UInt64 × UInt64 :=
  (x.1 ^^^ y.1, x.2 ^^^ y.2)

private theorem xorPair_zero_left (x : UInt64 × UInt64) :
    xorPair (0, 0) x = x := by
  cases x
  simp [xorPair]

private theorem xorPair_zero_right (x : UInt64 × UInt64) :
    xorPair x (0, 0) = x := by
  cases x
  simp [xorPair]

private theorem xorPair_assoc (x y z : UInt64 × UInt64) :
    xorPair (xorPair x y) z = xorPair x (xorPair y z) := by
  cases x
  cases y
  cases z
  simp [xorPair]
  constructor <;> bv_decide

private def wordBitXorStep (w acc : UInt64) (bit : Nat) : UInt64 :=
  if (((w >>> bit.toUInt64) &&& 1) != 0) then
    acc ^^^ ((1 : UInt64) <<< bit.toUInt64)
  else
    acc

private def wordBitFold (w : UInt64) : UInt64 :=
  (List.range 64).foldl (wordBitXorStep w) 0

private theorem wordBitFold_eq (w : UInt64) : wordBitFold w = w := by
  unfold wordBitFold wordBitXorStep
  simp [List.range, List.range.loop, List.foldl]
  bv_decide

private def clmulLeftBitFoldStep (w y : UInt64) (acc : UInt64 × UInt64) (bit : Nat) :
    UInt64 × UInt64 :=
  if (((w >>> bit.toUInt64) &&& 1) != 0) then
    xorPair acc (clmul ((1 : UInt64) <<< bit.toUInt64) y)
  else
    acc

private def clmulRightBitFoldStep (w y : UInt64) (acc : UInt64 × UInt64) (bit : Nat) :
    UInt64 × UInt64 :=
  if (((w >>> bit.toUInt64) &&& 1) != 0) then
    xorPair acc (clmul y ((1 : UInt64) <<< bit.toUInt64))
  else
    acc

private theorem clmulLeftBitFoldStep_eq_right (w y : UInt64) {bit : Nat}
    (hbit : bit < 64) (acc : UInt64 × UInt64) :
    clmulLeftBitFoldStep w y acc bit = clmulRightBitFoldStep w y acc bit := by
  by_cases hset : (((w >>> bit.toUInt64) &&& 1) != 0)
  · simp [clmulLeftBitFoldStep, clmulRightBitFoldStep, hset]
    rw [clmul_oneHot_left (a := y) hbit, clmul_oneHot (a := y) hbit]
  · simp [clmulLeftBitFoldStep, clmulRightBitFoldStep, hset]

private theorem foldl_clmulLeftBitFoldStep_eq_right (bits : List Nat) (w y : UInt64)
    (hlt : ∀ bit ∈ bits, bit < 64) (acc : UInt64 × UInt64) :
    bits.foldl (clmulLeftBitFoldStep w y) acc =
      bits.foldl (clmulRightBitFoldStep w y) acc := by
  induction bits generalizing acc with
  | nil =>
      simp
  | cons bit bits ih =>
      have hbit : bit < 64 := hlt bit (by simp)
      have htail : ∀ bit ∈ bits, bit < 64 := by
        intro bit hmem
        exact hlt bit (by simp [hmem])
      rw [List.foldl_cons, List.foldl_cons]
      rw [clmulLeftBitFoldStep_eq_right w y hbit acc]
      exact ih htail _

private theorem foldl_clmulLeftBitFoldStep_acc (bits : List Nat) (w y : UInt64)
    (acc : UInt64 × UInt64) :
    bits.foldl (clmulLeftBitFoldStep w y) acc =
      xorPair acc (bits.foldl (clmulLeftBitFoldStep w y) (0, 0)) := by
  induction bits generalizing acc with
  | nil =>
      simp [xorPair]
  | cons bit bits ih =>
      simp only [List.foldl_cons]
      by_cases hbit : (((w >>> bit.toUInt64) &&& 1) != 0)
      · simp [clmulLeftBitFoldStep, hbit]
        rw [ih (xorPair acc (clmul ((1 : UInt64) <<< bit.toUInt64) y))]
        rw [ih (xorPair (0, 0) (clmul ((1 : UInt64) <<< bit.toUInt64) y))]
        rw [xorPair_zero_left, xorPair_assoc]
      · simp [clmulLeftBitFoldStep, hbit]
        exact ih acc

private theorem clmul_wordBitFold_left_eq_bits_acc (bits : List Nat) (w y seed : UInt64)
    (hlt : ∀ bit ∈ bits, bit < 64) :
    clmul (bits.foldl (wordBitXorStep w) seed) y =
      xorPair (clmul seed y) (bits.foldl (clmulLeftBitFoldStep w y) (0, 0)) := by
  induction bits generalizing seed with
  | nil =>
      simp [xorPair_zero_right]
  | cons bit bits ih =>
      have hbitLt : bit < 64 := hlt bit (by simp)
      have htail : ∀ bit ∈ bits, bit < 64 := by
        intro bit hmem
        exact hlt bit (by simp [hmem])
      simp only [List.foldl_cons]
      by_cases hset : (((w >>> bit.toUInt64) &&& 1) != 0)
      · simp [wordBitXorStep, clmulLeftBitFoldStep, hset]
        rw [ih (seed ^^^ ((1 : UInt64) <<< bit.toUInt64)) htail]
        rw [foldl_clmulLeftBitFoldStep_acc bits w y
          (xorPair (0, 0) (clmul ((1 : UInt64) <<< bit.toUInt64) y))]
        rw [clmul_xor_left]
        rw [xorPair_zero_left]
        simpa [xorPair] using
          xorPair_assoc (clmul seed y) (clmul ((1 : UInt64) <<< bit.toUInt64) y)
            (bits.foldl (clmulLeftBitFoldStep w y) (0, 0))
      · simp [wordBitXorStep, clmulLeftBitFoldStep, hset]
        exact ih seed htail

private theorem clmul_wordBitFold_left_eq_bits (bits : List Nat) (w y : UInt64)
    (hlt : ∀ bit ∈ bits, bit < 64) :
    clmul (bits.foldl (wordBitXorStep w) 0) y =
      bits.foldl (clmulLeftBitFoldStep w y) (0, 0) := by
  rw [clmul_wordBitFold_left_eq_bits_acc bits w y 0 hlt, clmul_zero_left, xorPair_zero_left]

private theorem clmulAccumulateBit_eq_xorPair_oneHot (acc : UInt64 × UInt64)
    (y : UInt64) {bit : Nat} (hbit : bit < 64) :
    clmulAccumulateBit acc y bit =
      xorPair acc (clmul y ((1 : UInt64) <<< bit.toUInt64)) := by
  rw [clmul_oneHot (a := y) hbit]
  by_cases hzero : bit = 0 <;> simp [clmulAccumulateBit, xorPair, hzero]

private def clmulPureRightStep (w y : UInt64) (acc : UInt64 × UInt64) (bit : Nat) :
    UInt64 × UInt64 :=
  if (((w >>> bit.toUInt64) &&& 1) != 0) then
    clmulAccumulateBit acc y bit
  else
    acc

private theorem foldl_pureClmul_eq_right_bits (bits : List Nat) (w y : UInt64)
    (hlt : ∀ bit ∈ bits, bit < 64) (acc : UInt64 × UInt64) :
    bits.foldl (clmulPureRightStep w y) acc =
      bits.foldl (clmulRightBitFoldStep w y) acc := by
  induction bits generalizing acc with
  | nil =>
      simp
  | cons bit bits ih =>
      have hbit : bit < 64 := hlt bit (by simp)
      have htail : ∀ bit ∈ bits, bit < 64 := by
        intro bit hmem
        exact hlt bit (by simp [hmem])
      rw [List.foldl_cons, List.foldl_cons]
      by_cases hset : (((w >>> bit.toUInt64) &&& 1) != 0)
      · simp [clmulPureRightStep, clmulRightBitFoldStep, hset]
        rw [clmulAccumulateBit_eq_xorPair_oneHot acc y hbit]
        exact ih htail _
      · simp [clmulPureRightStep, clmulRightBitFoldStep, hset]
        exact ih htail acc

private theorem clmul_eq_right_bits (w y : UInt64) :
    clmul y w =
      (List.range 64).foldl (clmulRightBitFoldStep w y) (0, 0) := by
  rw [clmul, pureClmul]
  change (List.range 64).foldl (clmulPureRightStep w y) (0, 0) =
    (List.range 64).foldl (clmulRightBitFoldStep w y) (0, 0)
  exact foldl_pureClmul_eq_right_bits (List.range 64) w y (by
    intro bit hmem
    exact List.mem_range.mp hmem) (0, 0)

/-- Carry-less word multiplication is commutative. This is the reusable
word-level symmetry needed by packed polynomial multiplication proofs. -/
theorem clmul_comm (x y : UInt64) :
    clmul x y = clmul y x := by
  calc
    clmul x y = clmul (wordBitFold x) y := by rw [wordBitFold_eq]
    _ = (List.range 64).foldl (clmulLeftBitFoldStep x y) (0, 0) := by
      rw [wordBitFold]
      rw [clmul_wordBitFold_left_eq_bits (List.range 64) x y (by
        intro bit hmem
        exact List.mem_range.mp hmem)]
    _ = (List.range 64).foldl (clmulRightBitFoldStep x y) (0, 0) := by
      rw [foldl_clmulLeftBitFoldStep_eq_right (List.range 64) x y (by
        intro bit hmem
        exact List.mem_range.mp hmem)]
    _ = clmul y x := by
      rw [← clmul_eq_right_bits x y]

/-- Runtime `clmul`, under its trusted reference contract, is linear in its
right word argument over bitwise XOR. -/
@[grind =]
theorem clmul_xor_right (x y z : UInt64) :
    clmul x (y ^^^ z) =
      ((clmul x y).1 ^^^ (clmul x z).1, (clmul x y).2 ^^^ (clmul x z).2) := by
  calc
    clmul x (y ^^^ z) = clmul (y ^^^ z) x := clmul_comm x (y ^^^ z)
    _ = ((clmul y x).1 ^^^ (clmul z x).1, (clmul y x).2 ^^^ (clmul z x).2) := by
      rw [clmul_xor_left]
    _ = ((clmul x y).1 ^^^ (clmul x z).1, (clmul x y).2 ^^^ (clmul x z).2) := by
      rw [clmul_comm y x, clmul_comm z x]

/-- Pure carry-less word multiplication is commutative. -/
theorem pureClmul_comm (x y : UInt64) :
    pureClmul x y = pureClmul y x := by
  rw [← clmul_eq_pureClmul, ← clmul_eq_pureClmul, clmul_comm]

/-- The pure carry-less multiplier is linear in its right word argument over
bitwise XOR. -/
theorem pureClmul_xor_right (x y z : UInt64) :
    pureClmul x (y ^^^ z) =
      ((pureClmul x y).1 ^^^ (pureClmul x z).1,
        (pureClmul x y).2 ^^^ (pureClmul x z).2) := by
  rw [← clmul_eq_pureClmul, clmul_xor_right]
  rw [clmul_eq_pureClmul, clmul_eq_pureClmul]

end Hex
