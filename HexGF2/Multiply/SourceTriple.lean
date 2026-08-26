/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGF2.Basic
public import HexGF2.Clmul
public import HexGF2.Multiply.Coeff
import all HexGF2.Multiply.WordBits
import all HexGF2.Multiply.WordFold
import all HexGF2.Multiply.MulWords
import all HexGF2.Multiply.Coeff

public section
set_option backward.proofsInPublic true

/-!
Source-pair and source-triple coefficient definitions and the low-word
collapse lemmas.
-/
namespace Hex
namespace GF2Poly
/-- Source bit-pair contribution for the coefficient of total bit index
`total` in one word-word carry-less product. -/
@[expose]
def clmulSourcePairCoeff (x y : UInt64) (total : Nat) : Bool :=
  xorBoolList
    (List.flatMap
      (fun b =>
        (List.range 64).map
          (fun a => (wordBitAt x a && wordBitAt y b) && decide (a + b = total)))
      (List.range 64))

private theorem clmulSourcePairCoeff_low
    (x y : UInt64) {bit : Nat} (hbit : bit < 64) :
    wordBitAt (clmul x y).2 bit = clmulSourcePairCoeff x y bit := by
  rw [clmul_rightBitFold_low x y hbit]
  unfold clmulSourcePairCoeff
  calc
    xorBoolList
        ((List.range 64).map
          (fun b =>
            wordBitAt y b &&
              wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).2 bit))
        = xorBoolList
            ((List.range 64).map
              (fun b =>
                wordBitAt y b &&
                  xorBoolList
                    ((List.range 64).map
                      (fun a => wordBitAt x a && decide (a + b = bit))))) := by
            apply congrArg xorBoolList
            apply List.map_congr_left
            intro b hb
            rw [clmul_oneHot_source_low x (List.mem_range.mp hb) hbit]
    _ = xorBoolList
            ((List.range 64).map
              (fun b =>
                xorBoolList
                  ((List.range 64).map
                    (fun a => (wordBitAt x a && wordBitAt y b) &&
                      decide (a + b = bit))))) := by
            apply congrArg xorBoolList
            apply List.map_congr_left
            intro b _hb
            rw [← xorBoolList_map_and_left (wordBitAt y b)
              ((List.range 64).map
                (fun a => wordBitAt x a && decide (a + b = bit)))]
            apply congrArg xorBoolList
            rw [List.map_map]
            apply List.map_congr_left
            intro a _ha
            exact Bool.and_swap_middle (wordBitAt x a) (wordBitAt y b)
              (decide (a + b = bit))
    _ = xorBoolList
            (List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun a => (wordBitAt x a && wordBitAt y b) &&
                    decide (a + b = bit)))
              (List.range 64)) := by
            rw [xorBoolList_map_xorBoolList]

private theorem clmulSourcePairCoeff_high
    (x y : UInt64) {bit : Nat} (hbit : bit < 64) :
    wordBitAt (clmul x y).1 bit = clmulSourcePairCoeff x y (bit + 64) := by
  rw [clmul_rightBitFold_high x y hbit]
  unfold clmulSourcePairCoeff
  calc
    xorBoolList
        ((List.range 64).map
          (fun b =>
            wordBitAt y b &&
              wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).1 bit))
        = xorBoolList
            ((List.range 64).map
              (fun b =>
                wordBitAt y b &&
                  xorBoolList
                    ((List.range 64).map
                      (fun a => wordBitAt x a && decide (a + b = bit + 64))))) := by
            apply congrArg xorBoolList
            apply List.map_congr_left
            intro b hb
            rw [clmul_oneHot_source_high x (List.mem_range.mp hb) hbit]
    _ = xorBoolList
            ((List.range 64).map
              (fun b =>
                xorBoolList
                  ((List.range 64).map
                    (fun a => (wordBitAt x a && wordBitAt y b) &&
                      decide (a + b = bit + 64))))) := by
            apply congrArg xorBoolList
            apply List.map_congr_left
            intro b _hb
            rw [← xorBoolList_map_and_left (wordBitAt y b)
              ((List.range 64).map
                (fun a => wordBitAt x a && decide (a + b = bit + 64)))]
            apply congrArg xorBoolList
            rw [List.map_map]
            apply List.map_congr_left
            intro a _ha
            exact Bool.and_swap_middle (wordBitAt x a) (wordBitAt y b)
              (decide (a + b = bit + 64))
    _ = xorBoolList
            (List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun a => (wordBitAt x a && wordBitAt y b) &&
                    decide (a + b = bit + 64)))
              (List.range 64)) := by
            rw [xorBoolList_map_xorBoolList]

private theorem clmulCoeffAt_sourcePairCoeff
    (idx : Nat) (x y : UInt64) (n : Nat) :
    clmulCoeffAt idx x y n =
      if n / 64 = idx then
        clmulSourcePairCoeff x y (n % 64)
      else if n / 64 = idx + 1 then
        clmulSourcePairCoeff x y (n % 64 + 64)
      else
        false := by
  unfold clmulCoeffAt
  by_cases hlow : n / 64 = idx
  · simp only [if_pos hlow]
    have hbit : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
    change wordBitAt (clmul x y).2 (n % 64) =
      clmulSourcePairCoeff x y (n % 64)
    exact clmulSourcePairCoeff_low x y hbit
  · by_cases hhigh : n / 64 = idx + 1
    · simp only [if_neg hlow, if_pos hhigh]
      have hbit : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
      change wordBitAt (clmul x y).1 (n % 64) =
        clmulSourcePairCoeff x y (n % 64 + 64)
      exact clmulSourcePairCoeff_high x y hbit
    · simp only [if_neg hlow, if_neg hhigh]

/-- Source bit-triple contribution for the coefficient of total bit index
`total` in a three-word carry-less product. -/
@[expose]
def clmulSourceTripleCoeff (x y z : UInt64) (total : Nat) : Bool :=
  xorBoolList
    (List.flatMap
      (fun a =>
        List.flatMap
          (fun b =>
            (List.range 64).map
              (fun c =>
                (wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                  decide (a + b + c = total)))
          (List.range 64))
      (List.range 64))

private theorem xorBoolList_map_and_right_two (bits : List Bool) (left right : Bool) :
    xorBoolList (bits.map (fun bit => (bit && left) && right)) =
      ((xorBoolList bits && left) && right) := by
  cases left <;> cases right
  · induction bits with
    | nil =>
        simp [xorBoolList]
    | cons bit bits ih =>
        rw [List.map_cons, xorBoolList_cons, ih]
        cases bit <;> simp
  · induction bits with
    | nil =>
        simp [xorBoolList]
    | cons bit bits ih =>
        rw [List.map_cons, xorBoolList_cons, ih]
        cases bit <;> simp
  · induction bits with
    | nil =>
        simp [xorBoolList]
    | cons bit bits ih =>
        rw [List.map_cons, xorBoolList_cons, ih]
        cases bit <;> simp
  · induction bits with
    | nil =>
        simp [xorBoolList]
    | cons bit bits ih =>
        rw [List.map_cons, xorBoolList_cons, xorBoolList_cons, ih]
        cases bit <;> simp

private theorem xorBoolList_sourcePair_index_collapse_low
    (xy zc : Bool) {a b c bit : Nat} (hbit : bit < 64) :
    xorBoolList
        ((List.range 64).map
          (fun p => (((xy && decide (a + b = p)) && zc) && decide (p + c = bit)))) =
      ((xy && zc) && decide (a + b + c = bit)) := by
  cases xy <;> cases zc
  · simp [xorBoolList_range_false]
  · simp [xorBoolList_range_false]
  · simp [xorBoolList_range_false]
  · by_cases hsum : a + b + c = bit
    · have hsource : a + b < 64 := by omega
      rw [show
          (List.range 64).map
              (fun p => (((true && decide (a + b = p)) && true) &&
                decide (p + c = bit))) =
            (List.range 64).map (fun p => true && decide (p = a + b)) by
        apply List.map_congr_left
        intro p hp
        have hpLt : p < 64 := List.mem_range.mp hp
        by_cases hpab : p = a + b
        · subst hpab
          simp [hsum]
        · have hleft : ¬ a + b = p := by omega
          have hright : p + c ≠ bit := by omega
          simp [hpab, hleft, hright]]
      simpa [hsum] using xorBoolList_range_single_decide true hsource
    · rw [show
          (List.range 64).map
              (fun p => (((true && decide (a + b = p)) && true) &&
                decide (p + c = bit))) =
            (List.range 64).map (fun _ => false) by
        apply List.map_congr_left
        intro p _hp
        by_cases hpab : a + b = p
        · subst hpab
          simp [hsum]
        · simp [hpab]]
      simp [xorBoolList_range_false, hsum]

private theorem xorBoolList_sourcePair_index_collapse_high
    (xy zc : Bool) {a b c bit : Nat}
    (ha : a < 64) (hb : b < 64) (hc : c < 64) (hbit : bit < 64) :
    xorBoolList
        ((List.range 64).map
          (fun p => (((xy && decide (a + b = p + 64)) && zc) &&
            decide (p + c = bit + 64)))) =
      ((xy && zc) && decide (a + b + c = bit + 128)) := by
  cases xy <;> cases zc
  · simp [xorBoolList_range_false]
  · simp [xorBoolList_range_false]
  · simp [xorBoolList_range_false]
  · by_cases hsum : a + b + c = bit + 128
    · have hsourceGe : 64 ≤ a + b := by omega
      have hsource : a + b - 64 < 64 := by omega
      have hsourceEq : a + b - 64 + 64 = a + b := by omega
      rw [show
          (List.range 64).map
              (fun p => (((true && decide (a + b = p + 64)) && true) &&
                decide (p + c = bit + 64))) =
            (List.range 64).map (fun p => true && decide (p = a + b - 64)) by
        apply List.map_congr_left
        intro p hp
        have hpLt : p < 64 := List.mem_range.mp hp
        by_cases hpab : p = a + b - 64
        · subst hpab
          simp [hsourceEq]
          have hpc : a + b - 64 + c = bit + 64 := by omega
          simp [hpc]
        · have hleft : ¬ a + b = p + 64 := by omega
          have hright : p + c ≠ bit + 64 := by omega
          simp [hpab, hleft, hright]]
      simpa [hsum] using xorBoolList_range_single_decide true hsource
    · rw [show
          (List.range 64).map
              (fun p => (((true && decide (a + b = p + 64)) && true) &&
                decide (p + c = bit + 64))) =
            (List.range 64).map (fun _ => false) by
        apply List.map_congr_left
        intro p _hp
        by_cases hpab : a + b = p + 64
        · have hright : p + c ≠ bit + 64 := by
            intro hpc
            omega
          simp [hpab, hright]
        · simp [hpab]]
      simp [xorBoolList_range_false, hsum]

private theorem xorBoolList_sourcePair_index_collapse_middle_low
    (xy zc : Bool) {a b c bit : Nat} :
    xorBoolList
        ((List.range 64).map
          (fun p => (((xy && decide (a + b = p)) && zc) &&
            decide (p + c = bit + 64)))) =
      (((xy && zc) && decide (a + b + c = bit + 64)) &&
        decide (a + b < 64)) := by
  cases xy <;> cases zc
  · simp [xorBoolList_range_false]
  · simp [xorBoolList_range_false]
  · simp [xorBoolList_range_false]
  · by_cases hsum : a + b + c = bit + 64
    · by_cases hsource : a + b < 64
      · rw [show
            (List.range 64).map
                (fun p => (((true && decide (a + b = p)) && true) &&
                  decide (p + c = bit + 64))) =
              (List.range 64).map (fun p => true && decide (p = a + b)) by
          apply List.map_congr_left
          intro p hp
          have hpLt : p < 64 := List.mem_range.mp hp
          by_cases hpab : p = a + b
          · subst hpab
            simp [hsum]
          · have hleft : ¬ a + b = p := by omega
            have hright : p + c ≠ bit + 64 := by omega
            simp [hpab, hleft, hright]]
        simpa [hsum, hsource] using xorBoolList_range_single_decide true hsource
      · rw [show
            (List.range 64).map
                (fun p => (((true && decide (a + b = p)) && true) &&
                  decide (p + c = bit + 64))) =
              (List.range 64).map (fun _ => false) by
          apply List.map_congr_left
          intro p hp
          have hpLt : p < 64 := List.mem_range.mp hp
          have hpne : ¬ a + b = p := by omega
          simp [hpne]]
        simp [xorBoolList_range_false, hsum, hsource]
    · rw [show
          (List.range 64).map
              (fun p => (((true && decide (a + b = p)) && true) &&
                decide (p + c = bit + 64))) =
            (List.range 64).map (fun _ => false) by
        apply List.map_congr_left
        intro p _hp
        by_cases hpab : a + b = p
        · subst hpab
          simp [hsum]
        · simp [hpab]]
      simp [xorBoolList_range_false, hsum]

private theorem xorBoolList_sourcePair_index_collapse_middle_high
    (xy zc : Bool) {a b c bit : Nat}
    (ha : a < 64) (hb : b < 64) :
    xorBoolList
        ((List.range 64).map
          (fun p => (((xy && decide (a + b = p + 64)) && zc) &&
            decide (p + c = bit)))) =
      (((xy && zc) && decide (a + b + c = bit + 64)) &&
        decide (64 ≤ a + b)) := by
  cases xy <;> cases zc
  · simp [xorBoolList_range_false]
  · simp [xorBoolList_range_false]
  · simp [xorBoolList_range_false]
  · by_cases hsum : a + b + c = bit + 64
    · by_cases hsourceGe : 64 ≤ a + b
      · have hsource : a + b - 64 < 64 := by omega
        have hsourceEq : a + b - 64 + 64 = a + b := by omega
        rw [show
            (List.range 64).map
                (fun p => (((true && decide (a + b = p + 64)) && true) &&
                  decide (p + c = bit))) =
              (List.range 64).map (fun p => true && decide (p = a + b - 64)) by
          apply List.map_congr_left
          intro p hp
          have hpLt : p < 64 := List.mem_range.mp hp
          by_cases hpab : p = a + b - 64
          · subst hpab
            simp [hsourceEq]
            have hpc : a + b - 64 + c = bit := by omega
            simp [hpc]
          · have hleft : ¬ a + b = p + 64 := by omega
            have hright : p + c ≠ bit := by omega
            simp [hpab, hleft, hright]]
        simpa [hsum, hsourceGe] using xorBoolList_range_single_decide true hsource
      · rw [show
            (List.range 64).map
                (fun p => (((true && decide (a + b = p + 64)) && true) &&
                  decide (p + c = bit))) =
              (List.range 64).map (fun _ => false) by
          apply List.map_congr_left
          intro p _hp
          have hpne : ¬ a + b = p + 64 := by omega
          simp [hpne]]
        simp [xorBoolList_range_false, hsum, hsourceGe]
    · rw [show
          (List.range 64).map
              (fun p => (((true && decide (a + b = p + 64)) && true) &&
                decide (p + c = bit))) =
            (List.range 64).map (fun _ => false) by
        apply List.map_congr_left
        intro p _hp
        by_cases hpab : a + b = p + 64
        · have hright : p + c ≠ bit := by
            intro hpc
            omega
          simp [hpab, hright]
        · simp [hpab]]
      simp [xorBoolList_range_false, hsum]

private theorem clmulSourcePairCoeff_and_bit_low
    (x y : UInt64) {p : Nat} (hp : p < 64) (zc gate : Bool) :
    ((wordBitAt (clmul x y).2 p && zc) && gate) =
      xorBoolList
        ((List.range 64).flatMap
          (fun b =>
            (List.range 64).map
              (fun a =>
                ((((wordBitAt x a && wordBitAt y b) &&
                    decide (a + b = p)) && zc) && gate)))) := by
  rw [clmulSourcePairCoeff_low x y hp]
  unfold clmulSourcePairCoeff
  rw [← xorBoolList_map_and_right_two
    (List.flatMap
      (fun b =>
        (List.range 64).map
          (fun a => (wordBitAt x a && wordBitAt y b) && decide (a + b = p)))
      (List.range 64)) zc gate]
  rw [List.map_flatMap]
  simp only [List.map_map]
  rfl

private theorem clmulSourcePairCoeff_and_bit_high
    (x y : UInt64) {p : Nat} (hp : p < 64) (zc gate : Bool) :
    ((wordBitAt (clmul x y).1 p && zc) && gate) =
      xorBoolList
        ((List.range 64).flatMap
          (fun b =>
            (List.range 64).map
              (fun a =>
                ((((wordBitAt x a && wordBitAt y b) &&
                    decide (a + b = p + 64)) && zc) && gate)))) := by
  rw [clmulSourcePairCoeff_high x y hp]
  unfold clmulSourcePairCoeff
  rw [← xorBoolList_map_and_right_two
    (List.flatMap
      (fun b =>
        (List.range 64).map
          (fun a => (wordBitAt x a && wordBitAt y b) && decide (a + b = p + 64)))
      (List.range 64)) zc gate]
  rw [List.map_flatMap]
  simp only [List.map_map]
  rfl

private theorem xorBoolList_left_middle_low_sourceTriple_mask_collapse
    (x y z : UInt64) {bit : Nat} :
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) =
      xorBoolList
        (List.flatMap
          (fun a =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun c =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (a + b < 64))))
              (List.range 64))
          (List.range 64)) := by
  calc
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64))
        =
      xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun b =>
                List.flatMap
                  (fun a =>
                    List.map
                      (fun p =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          calc
            xorBoolList
                (List.flatMap
                  (fun p =>
                    List.flatMap
                      (fun b =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p)) && wordBitAt z c) &&
                              decide (p + c = bit + 64)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64))
                =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.flatMap
                      (fun p =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p)) && wordBitAt z c) &&
                              decide (p + c = bit + 64)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun p b =>
                      (List.range 64).map
                        (fun a =>
                          ((((wordBitAt x a && wordBitAt y b) &&
                              decide (a + b = p)) && wordBitAt z c) &&
                            decide (p + c = bit + 64))))
            _ =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.flatMap
                      (fun a =>
                        List.map
                          (fun p =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p)) && wordBitAt z c) &&
                              decide (p + c = bit + 64)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  apply xorBoolList_flatMap_congr_xor
                  intro b _hb
                  simpa [List.flatMap_singleton] using
                    xorBoolList_flatMap_ranges_swap_list 64 64
                      (fun p a =>
                        [((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit + 64))])
    _ =
      xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).flatMap
              (fun b =>
                (List.range 64).map
                  (fun a =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (a + b < 64)))))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          apply xorBoolList_flatMap_congr_xor
          intro b _hb
          calc
            xorBoolList
                ((List.range 64).flatMap
                  (fun a =>
                    (List.range 64).map
                      (fun p =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))))
                =
              xorBoolList
                ((List.range 64).map
                  (fun a =>
                    xorBoolList
                      ((List.range 64).map
                        (fun p =>
                          ((((wordBitAt x a && wordBitAt y b) &&
                              decide (a + b = p)) && wordBitAt z c) &&
                            decide (p + c = bit + 64)))))) := by
                  rw [xorBoolList_map_xorBoolList]
            _ =
              xorBoolList
                ((List.range 64).map
                  (fun a =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (a + b < 64)))) := by
                  apply congrArg xorBoolList
                  apply List.map_congr_left
                  intro a _ha
                  simpa [Bool.and_assoc] using
                    xorBoolList_sourcePair_index_collapse_middle_low
                      (wordBitAt x a && wordBitAt y b) (wordBitAt z c)
                      (a := a) (b := b) (c := c) (bit := bit)
    _ =
      xorBoolList
        (List.flatMap
          (fun a =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun c =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (a + b < 64))))
              (List.range 64))
          (List.range 64)) := by
          calc
            xorBoolList
                (List.flatMap
                  (fun c =>
                    (List.range 64).flatMap
                      (fun b =>
                        (List.range 64).map
                          (fun a =>
                            (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 64)) &&
                              decide (a + b < 64)))))
                  (List.range 64))
                =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    (List.range 64).flatMap
                      (fun c =>
                        (List.range 64).map
                          (fun a =>
                            (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 64)) &&
                              decide (a + b < 64)))))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun c b =>
                      (List.range 64).map
                        (fun a =>
                          (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                            decide (a + b + c = bit + 64)) && decide (a + b < 64))))
            _ =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    (List.range 64).flatMap
                      (fun a =>
                        (List.range 64).map
                          (fun c =>
                            (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 64)) &&
                              decide (a + b < 64)))))
                  (List.range 64)) := by
                  apply xorBoolList_flatMap_congr_xor
                  intro b _hb
                  simpa [List.flatMap_singleton] using
                    xorBoolList_flatMap_ranges_swap_list 64 64
                      (fun c a =>
                        [(((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                          decide (a + b + c = bit + 64)) && decide (a + b < 64))])
            _ =
              xorBoolList
                (List.flatMap
                  (fun a =>
                    (List.range 64).flatMap
                      (fun b =>
                        (List.range 64).map
                          (fun c =>
                            (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 64)) &&
                              decide (a + b < 64)))))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun b a =>
                      (List.range 64).map
                        (fun c =>
                          (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                            decide (a + b + c = bit + 64)) && decide (a + b < 64))))

private theorem xorBoolList_left_middle_high_sourceTriple_mask_collapse
    (x y z : UInt64) {bit : Nat} :
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) =
      xorBoolList
        (List.flatMap
          (fun a =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun c =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (64 ≤ a + b))))
              (List.range 64))
          (List.range 64)) := by
  calc
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64))
        =
      xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun b =>
                List.flatMap
                  (fun a =>
                    List.map
                      (fun p =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          calc
            xorBoolList
                (List.flatMap
                  (fun p =>
                    List.flatMap
                      (fun b =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p + 64)) && wordBitAt z c) &&
                              decide (p + c = bit)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64))
                =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.flatMap
                      (fun p =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p + 64)) && wordBitAt z c) &&
                              decide (p + c = bit)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun p b =>
                      (List.range 64).map
                        (fun a =>
                          ((((wordBitAt x a && wordBitAt y b) &&
                              decide (a + b = p + 64)) && wordBitAt z c) &&
                            decide (p + c = bit))))
            _ =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.flatMap
                      (fun a =>
                        List.map
                          (fun p =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p + 64)) && wordBitAt z c) &&
                              decide (p + c = bit)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  apply xorBoolList_flatMap_congr_xor
                  intro b _hb
                  simpa [List.flatMap_singleton] using
                    xorBoolList_flatMap_ranges_swap_list 64 64
                      (fun p a =>
                        [((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit))])
    _ =
      xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).flatMap
              (fun b =>
                (List.range 64).map
                  (fun a =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (64 ≤ a + b)))))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          apply xorBoolList_flatMap_congr_xor
          intro b hb
          calc
            xorBoolList
                ((List.range 64).flatMap
                  (fun a =>
                    (List.range 64).map
                      (fun p =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit)))))
                =
              xorBoolList
                ((List.range 64).map
                  (fun a =>
                    xorBoolList
                      ((List.range 64).map
                        (fun p =>
                          ((((wordBitAt x a && wordBitAt y b) &&
                              decide (a + b = p + 64)) && wordBitAt z c) &&
                            decide (p + c = bit)))))) := by
                  rw [xorBoolList_map_xorBoolList]
            _ =
              xorBoolList
                ((List.range 64).map
                  (fun a =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (64 ≤ a + b)))) := by
                  apply congrArg xorBoolList
                  apply List.map_congr_left
                  intro a ha
                  simpa [Bool.and_assoc] using
                    xorBoolList_sourcePair_index_collapse_middle_high
                      (wordBitAt x a && wordBitAt y b) (wordBitAt z c)
                      (a := a) (b := b) (c := c) (bit := bit)
                      (List.mem_range.mp ha) (List.mem_range.mp hb)
    _ =
      xorBoolList
        (List.flatMap
          (fun a =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun c =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (64 ≤ a + b))))
              (List.range 64))
          (List.range 64)) := by
          calc
            xorBoolList
                (List.flatMap
                  (fun c =>
                    (List.range 64).flatMap
                      (fun b =>
                        (List.range 64).map
                          (fun a =>
                            (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 64)) &&
                              decide (64 ≤ a + b)))))
                  (List.range 64))
                =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    (List.range 64).flatMap
                      (fun c =>
                        (List.range 64).map
                          (fun a =>
                            (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 64)) &&
                              decide (64 ≤ a + b)))))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun c b =>
                      (List.range 64).map
                        (fun a =>
                          (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                            decide (a + b + c = bit + 64)) && decide (64 ≤ a + b))))
            _ =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    (List.range 64).flatMap
                      (fun a =>
                        (List.range 64).map
                          (fun c =>
                            (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 64)) &&
                              decide (64 ≤ a + b)))))
                  (List.range 64)) := by
                  apply xorBoolList_flatMap_congr_xor
                  intro b _hb
                  simpa [List.flatMap_singleton] using
                    xorBoolList_flatMap_ranges_swap_list 64 64
                      (fun c a =>
                        [(((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                          decide (a + b + c = bit + 64)) && decide (64 ≤ a + b))])
            _ =
              xorBoolList
                (List.flatMap
                  (fun a =>
                    (List.range 64).flatMap
                      (fun b =>
                        (List.range 64).map
                          (fun c =>
                            (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 64)) &&
                              decide (64 ≤ a + b)))))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun b a =>
                      (List.range 64).map
                        (fun c =>
                          (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                            decide (a + b + c = bit + 64)) && decide (64 ≤ a + b))))

private theorem xorBoolList_left_low_sourceTriple_collapse
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) =
      clmulSourceTripleCoeff x y z bit := by
  unfold clmulSourceTripleCoeff
  calc
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun p =>
                List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64))
        =
      xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun b =>
                List.flatMap
                  (fun a =>
                    List.map
                      (fun p =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          calc
            xorBoolList
                (List.flatMap
                  (fun p =>
                    List.flatMap
                      (fun b =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p)) && wordBitAt z c) &&
                              decide (p + c = bit)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64))
                =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.flatMap
                      (fun p =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p)) && wordBitAt z c) &&
                              decide (p + c = bit)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun p b =>
                      (List.range 64).map
                        (fun a =>
                          ((((wordBitAt x a && wordBitAt y b) &&
                              decide (a + b = p)) && wordBitAt z c) &&
                            decide (p + c = bit))))
            _ =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.flatMap
                      (fun a =>
                        List.map
                          (fun p =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p)) && wordBitAt z c) &&
                              decide (p + c = bit)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  apply xorBoolList_flatMap_congr_xor
                  intro b _hb
                  simpa [List.flatMap_singleton] using
                    xorBoolList_flatMap_ranges_swap_list 64 64
                      (fun p a =>
                        [((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit))])
    _ =
      xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).flatMap
              (fun b =>
                (List.range 64).map
                  (fun a =>
                    ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit)))))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          apply xorBoolList_flatMap_congr_xor
          intro b _hb
          calc
            xorBoolList
                ((List.range 64).flatMap
                  (fun a =>
                    (List.range 64).map
                      (fun p =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit)))))
                =
              xorBoolList
                ((List.range 64).map
                  (fun a =>
                    xorBoolList
                      ((List.range 64).map
                        (fun p =>
                          ((((wordBitAt x a && wordBitAt y b) &&
                              decide (a + b = p)) && wordBitAt z c) &&
                            decide (p + c = bit)))))) := by
                  rw [xorBoolList_map_xorBoolList]
            _ =
              xorBoolList
                ((List.range 64).map
                  (fun a =>
                    ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit)))) := by
                  apply congrArg xorBoolList
                  apply List.map_congr_left
                  intro a _ha
                  simpa [Bool.and_assoc] using
                    xorBoolList_sourcePair_index_collapse_low
                      (wordBitAt x a && wordBitAt y b) (wordBitAt z c)
                      (a := a) (b := b) (c := c) hbit
    _ =
      xorBoolList
        (List.flatMap
          (fun a =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun c =>
                    ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit))))
              (List.range 64))
          (List.range 64)) := by
          calc
            xorBoolList
                (List.flatMap
                  (fun c =>
                    (List.range 64).flatMap
                      (fun b =>
                        (List.range 64).map
                          (fun a =>
                            ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit)))))
                  (List.range 64))
                =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    (List.range 64).flatMap
                      (fun c =>
                        (List.range 64).map
                          (fun a =>
                            ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit)))))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun c b =>
                      (List.range 64).map
                        (fun a =>
                          ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                            decide (a + b + c = bit))))
            _ =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    (List.range 64).flatMap
                      (fun a =>
                        (List.range 64).map
                          (fun c =>
                            ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit)))))
                  (List.range 64)) := by
                  apply xorBoolList_flatMap_congr_xor
                  intro b _hb
                  simpa [List.flatMap_singleton] using
                    xorBoolList_flatMap_ranges_swap_list 64 64
                      (fun c a =>
                        [((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                          decide (a + b + c = bit))])
            _ =
              xorBoolList
                (List.flatMap
                  (fun a =>
                    (List.range 64).flatMap
                      (fun b =>
                        (List.range 64).map
                          (fun c =>
                            ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit)))))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun b a =>
                      (List.range 64).map
                        (fun c =>
                          ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                            decide (a + b + c = bit))))


end GF2Poly
end Hex
