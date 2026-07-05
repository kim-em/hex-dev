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
import all HexGF2.Multiply.MulWords
import all HexGF2.Multiply.Coeff

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
Source-pair/source-triple coefficient definitions and the
associativity/commutativity collapse lemmas for `coeffWords_mulWords`.
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

private theorem clmulAssoc_left_low_sourceTriple
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    wordBitAt (clmul (clmul x y).2 z).2 bit =
      clmulSourceTripleCoeff x y z bit := by
  rw [clmulSourcePairCoeff_low (clmul x y).2 z hbit]
  unfold clmulSourcePairCoeff
  calc
    xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).map
              (fun p =>
                ((wordBitAt (clmul x y).2 p && wordBitAt z c) &&
                  decide (p + c = bit))))
          (List.range 64))
        =
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
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          calc
            xorBoolList
                ((List.range 64).map
                  (fun p =>
                    ((wordBitAt (clmul x y).2 p && wordBitAt z c) &&
                      decide (p + c = bit))))
                =
              xorBoolList
                ((List.range 64).map
                  (fun p =>
                    xorBoolList
                      (List.flatMap
                        (fun b =>
                          List.map
                            (fun a =>
                              ((((wordBitAt x a && wordBitAt y b) &&
                                  decide (a + b = p)) && wordBitAt z c) &&
                                decide (p + c = bit)))
                            (List.range 64))
                        (List.range 64)))) := by
                  apply congrArg xorBoolList
                  apply List.map_congr_left
                  intro p hp
                  exact clmulSourcePairCoeff_and_bit_low x y (List.mem_range.mp hp)
                    (wordBitAt z c) (decide (p + c = bit))
            _ =
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
                  (List.range 64)) := by
                  rw [xorBoolList_map_xorBoolList]
    _ = clmulSourceTripleCoeff x y z bit := by
          exact xorBoolList_left_low_sourceTriple_collapse x y z hbit

private theorem clmulSourceTripleCoeff_reverse_outer
    (x y z : UInt64) (total : Nat) :
    clmulSourceTripleCoeff z y x total =
      clmulSourceTripleCoeff x y z total := by
  unfold clmulSourceTripleCoeff
  calc
    xorBoolList
        (List.flatMap
          (fun c =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun a =>
                    ((wordBitAt z c && wordBitAt y b && wordBitAt x a) &&
                      decide (c + b + a = total))))
              (List.range 64))
          (List.range 64))
        =
      xorBoolList
        (List.flatMap
          (fun b =>
            List.flatMap
              (fun c =>
                (List.range 64).map
                  (fun a =>
                    ((wordBitAt z c && wordBitAt y b && wordBitAt x a) &&
                      decide (c + b + a = total))))
              (List.range 64))
          (List.range 64)) := by
          exact xorBoolList_flatMap_ranges_swap_list 64 64
            (fun c b =>
              (List.range 64).map
                (fun a =>
                  ((wordBitAt z c && wordBitAt y b && wordBitAt x a) &&
                    decide (c + b + a = total))))
    _ =
      xorBoolList
        (List.flatMap
          (fun b =>
            List.flatMap
              (fun a =>
                (List.range 64).map
                  (fun c =>
                    ((wordBitAt z c && wordBitAt y b && wordBitAt x a) &&
                      decide (c + b + a = total))))
              (List.range 64))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro b _hb
          simpa [List.flatMap_singleton] using
            xorBoolList_flatMap_ranges_swap_list 64 64
              (fun c a =>
                [((wordBitAt z c && wordBitAt y b && wordBitAt x a) &&
                  decide (c + b + a = total))])
    _ =
      xorBoolList
        (List.flatMap
          (fun a =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun c =>
                    ((wordBitAt z c && wordBitAt y b && wordBitAt x a) &&
                      decide (c + b + a = total))))
              (List.range 64))
          (List.range 64)) := by
          exact xorBoolList_flatMap_ranges_swap_list 64 64
            (fun b a =>
              (List.range 64).map
                (fun c =>
                  ((wordBitAt z c && wordBitAt y b && wordBitAt x a) &&
                    decide (c + b + a = total))))
    _ =
      xorBoolList
        (List.flatMap
          (fun a =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun c =>
                    ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = total))))
              (List.range 64))
          (List.range 64)) := by
          apply congrArg xorBoolList
          apply List.flatMap_congr_left
          intro a _ha
          apply List.flatMap_congr_left
          intro b _hb
          apply List.map_congr_left
          intro c _hc
          cases wordBitAt x a <;> cases wordBitAt y b <;> cases wordBitAt z c <;>
            simp [show (c + b + a = total) ↔ (a + b + c = total) by omega]

private theorem clmulAssoc_right_low_sourceTriple
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    wordBitAt (clmul x (clmul y z).2).2 bit =
      clmulSourceTripleCoeff x y z bit := by
  calc
    wordBitAt (clmul x (clmul y z).2).2 bit
        = wordBitAt (clmul (clmul z y).2 x).2 bit := by
          rw [clmul_comm x (clmul y z).2, clmul_comm y z]
    _ = clmulSourceTripleCoeff z y x bit := by
          exact clmulAssoc_left_low_sourceTriple z y x hbit
    _ = clmulSourceTripleCoeff x y z bit := by
          exact clmulSourceTripleCoeff_reverse_outer x y z bit

private theorem xorBoolList_left_middle_sourceTriple_collapse
    (x y z : UInt64) {bit : Nat} (_hbit : bit < 64) :
    (xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).map
              (fun p =>
                ((wordBitAt (clmul x y).2 p && wordBitAt z c) &&
                  decide (p + c = bit + 64))))
          (List.range 64)) !=
      xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).map
              (fun p =>
                ((wordBitAt (clmul x y).1 p && wordBitAt z c) &&
                  decide (p + c = bit))))
          (List.range 64))) =
      clmulSourceTripleCoeff x y z (bit + 64) := by
  unfold clmulSourceTripleCoeff
  have hlow :
      xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).map
              (fun p =>
                ((wordBitAt (clmul x y).2 p && wordBitAt z c) &&
                  decide (p + c = bit + 64))))
          (List.range 64)) =
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
          (List.range 64)) := by
    apply xorBoolList_flatMap_congr_xor
    intro c _hc
    calc
      xorBoolList
          ((List.range 64).map
            (fun p =>
              ((wordBitAt (clmul x y).2 p && wordBitAt z c) &&
                decide (p + c = bit + 64))))
          =
        xorBoolList
          ((List.range 64).map
            (fun p =>
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))
                      (List.range 64))
                  (List.range 64)))) := by
            apply congrArg xorBoolList
            apply List.map_congr_left
            intro p hp
            exact clmulSourcePairCoeff_and_bit_low x y (List.mem_range.mp hp)
              (wordBitAt z c) (decide (p + c = bit + 64))
      _ =
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
            (List.range 64)) := by
            rw [xorBoolList_map_xorBoolList]
  have hhigh :
      xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).map
              (fun p =>
                ((wordBitAt (clmul x y).1 p && wordBitAt z c) &&
                  decide (p + c = bit))))
          (List.range 64)) =
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
          (List.range 64)) := by
    apply xorBoolList_flatMap_congr_xor
    intro c _hc
    calc
      xorBoolList
          ((List.range 64).map
            (fun p =>
              ((wordBitAt (clmul x y).1 p && wordBitAt z c) &&
                decide (p + c = bit))))
          =
        xorBoolList
          ((List.range 64).map
            (fun p =>
              xorBoolList
                (List.flatMap
                  (fun b =>
                    List.map
                      (fun a =>
                        ((((wordBitAt x a && wordBitAt y b) &&
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit)))
                      (List.range 64))
                  (List.range 64)))) := by
            apply congrArg xorBoolList
            apply List.map_congr_left
            intro p hp
            exact clmulSourcePairCoeff_and_bit_high x y (List.mem_range.mp hp)
              (wordBitAt z c) (decide (p + c = bit))
      _ =
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
            (List.range 64)) := by
            rw [xorBoolList_map_xorBoolList]
  rw [hlow, hhigh]
  rw [xorBoolList_left_middle_low_sourceTriple_mask_collapse x y z,
    xorBoolList_left_middle_high_sourceTriple_mask_collapse x y z]
  exact
    xorBoolList_flatMap_bne_congr
      (xs := List.range 64)
      (left := fun a =>
        List.flatMap
          (fun b =>
            (List.range 64).map
              (fun c =>
                (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                  decide (a + b + c = bit + 64)) && decide (a + b < 64))))
          (List.range 64))
      (right := fun a =>
        List.flatMap
          (fun b =>
            (List.range 64).map
              (fun c =>
                (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                  decide (a + b + c = bit + 64)) && decide (64 ≤ a + b))))
          (List.range 64))
      (both := fun a =>
        List.flatMap
          (fun b =>
            (List.range 64).map
              (fun c =>
                ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                  decide (a + b + c = bit + 64))))
          (List.range 64))
      (by
        intro a _ha
        exact
          xorBoolList_flatMap_bne_congr
            (xs := List.range 64)
            (left := fun b =>
              (List.range 64).map
                (fun c =>
                  (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                    decide (a + b + c = bit + 64)) && decide (a + b < 64))))
            (right := fun b =>
              (List.range 64).map
                (fun c =>
                  (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                    decide (a + b + c = bit + 64)) && decide (64 ≤ a + b))))
            (both := fun b =>
              (List.range 64).map
                (fun c =>
                  ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                    decide (a + b + c = bit + 64))))
            (by
              intro b _hb
              exact
                xorBoolList_map_bne_congr
                  (xs := List.range 64)
                  (left := fun c =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (a + b < 64)))
                  (right := fun c =>
                    (((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)) && decide (64 ≤ a + b)))
                  (both := fun c =>
                    ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 64)))
                  (by
                    intro c _hc
                    generalize
                      ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                        decide (a + b + c = bit + 64)) = term
                    by_cases hlt : a + b < 64
                    · have hge : ¬ 64 ≤ a + b := by omega
                      cases term <;> simp [hlt, hge]
                    · have hge : 64 ≤ a + b := by omega
                      cases term <;> simp [hlt, hge])))

private theorem clmulAssoc_left_middle_sourceTriple
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    (wordBitAt (clmul (clmul x y).2 z).1 bit !=
        wordBitAt (clmul (clmul x y).1 z).2 bit) =
      clmulSourceTripleCoeff x y z (bit + 64) := by
  rw [clmulSourcePairCoeff_high (clmul x y).2 z hbit, clmulSourcePairCoeff_low (clmul x y).1 z hbit]
  unfold clmulSourcePairCoeff
  exact xorBoolList_left_middle_sourceTriple_collapse x y z hbit

private theorem clmulAssoc_right_middle_sourceTriple
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    (wordBitAt (clmul x (clmul y z).2).1 bit !=
        wordBitAt (clmul x (clmul y z).1).2 bit) =
      clmulSourceTripleCoeff x y z (bit + 64) := by
  calc
    (wordBitAt (clmul x (clmul y z).2).1 bit !=
        wordBitAt (clmul x (clmul y z).1).2 bit)
        =
      (wordBitAt (clmul (clmul z y).2 x).1 bit !=
        wordBitAt (clmul (clmul z y).1 x).2 bit) := by
          rw [clmul_comm x (clmul y z).2, clmul_comm x (clmul y z).1,
            clmul_comm y z]
    _ = clmulSourceTripleCoeff z y x (bit + 64) := by
          exact clmulAssoc_left_middle_sourceTriple z y x hbit
    _ = clmulSourceTripleCoeff x y z (bit + 64) := by
          exact clmulSourceTripleCoeff_reverse_outer x y z (bit + 64)

private theorem xorBoolList_left_high_sourceTriple_collapse
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
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit + 64)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) =
      clmulSourceTripleCoeff x y z (bit + 128) := by
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
                            decide (a + b = p + 64)) && wordBitAt z c) &&
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
                            decide (a + b = p + 64)) && wordBitAt z c) &&
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
                                decide (a + b = p + 64)) && wordBitAt z c) &&
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
                                decide (a + b = p + 64)) && wordBitAt z c) &&
                              decide (p + c = bit + 64)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun p b =>
                      (List.range 64).map
                        (fun a =>
                          ((((wordBitAt x a && wordBitAt y b) &&
                              decide (a + b = p + 64)) && wordBitAt z c) &&
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
                                decide (a + b = p + 64)) && wordBitAt z c) &&
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
                            decide (a + b = p + 64)) && wordBitAt z c) &&
                          decide (p + c = bit + 64))])
    _ =
      xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).flatMap
              (fun b =>
                (List.range 64).map
                  (fun a =>
                    ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 128)))))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c hc
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
                          decide (p + c = bit + 64)))))
                =
              xorBoolList
                ((List.range 64).map
                  (fun a =>
                    xorBoolList
                      ((List.range 64).map
                        (fun p =>
                          ((((wordBitAt x a && wordBitAt y b) &&
                              decide (a + b = p + 64)) && wordBitAt z c) &&
                            decide (p + c = bit + 64)))))) := by
                  rw [xorBoolList_map_xorBoolList]
            _ =
              xorBoolList
                ((List.range 64).map
                  (fun a =>
                    ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 128)))) := by
                  apply congrArg xorBoolList
                  apply List.map_congr_left
                  intro a ha
                  simpa [Bool.and_assoc] using
                    xorBoolList_sourcePair_index_collapse_high
                      (wordBitAt x a && wordBitAt y b) (wordBitAt z c)
                      (a := a) (b := b) (c := c)
                      (List.mem_range.mp ha) (List.mem_range.mp hb)
                      (List.mem_range.mp hc) hbit
    _ =
      xorBoolList
        (List.flatMap
          (fun a =>
            List.flatMap
              (fun b =>
                (List.range 64).map
                  (fun c =>
                    ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                      decide (a + b + c = bit + 128))))
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
                              decide (a + b + c = bit + 128)))))
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
                              decide (a + b + c = bit + 128)))))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun c b =>
                      (List.range 64).map
                        (fun a =>
                          ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                            decide (a + b + c = bit + 128))))
            _ =
              xorBoolList
                (List.flatMap
                  (fun b =>
                    (List.range 64).flatMap
                      (fun a =>
                        (List.range 64).map
                          (fun c =>
                            ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 128)))))
                  (List.range 64)) := by
                  apply xorBoolList_flatMap_congr_xor
                  intro b _hb
                  simpa [List.flatMap_singleton] using
                    xorBoolList_flatMap_ranges_swap_list 64 64
                      (fun c a =>
                        [((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                          decide (a + b + c = bit + 128))])
            _ =
              xorBoolList
                (List.flatMap
                  (fun a =>
                    (List.range 64).flatMap
                      (fun b =>
                        (List.range 64).map
                          (fun c =>
                            ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                              decide (a + b + c = bit + 128)))))
                  (List.range 64)) := by
                  exact xorBoolList_flatMap_ranges_swap_list 64 64
                    (fun b a =>
                      (List.range 64).map
                        (fun c =>
                          ((wordBitAt x a && wordBitAt y b && wordBitAt z c) &&
                            decide (a + b + c = bit + 128))))

private theorem clmulAssoc_left_high_sourceTriple
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    wordBitAt (clmul (clmul x y).1 z).1 bit =
      clmulSourceTripleCoeff x y z (bit + 128) := by
  rw [clmulSourcePairCoeff_high (clmul x y).1 z hbit]
  unfold clmulSourcePairCoeff
  calc
    xorBoolList
        (List.flatMap
          (fun c =>
            (List.range 64).map
              (fun p =>
                ((wordBitAt (clmul x y).1 p && wordBitAt z c) &&
                  decide (p + c = bit + 64))))
          (List.range 64))
        =
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
                          decide (p + c = bit + 64)))
                      (List.range 64))
                  (List.range 64))
              (List.range 64))
          (List.range 64)) := by
          apply xorBoolList_flatMap_congr_xor
          intro c _hc
          calc
            xorBoolList
                ((List.range 64).map
                  (fun p =>
                    ((wordBitAt (clmul x y).1 p && wordBitAt z c) &&
                      decide (p + c = bit + 64))))
                =
              xorBoolList
                ((List.range 64).map
                  (fun p =>
                    xorBoolList
                      (List.flatMap
                        (fun b =>
                          List.map
                            (fun a =>
                              ((((wordBitAt x a && wordBitAt y b) &&
                                  decide (a + b = p + 64)) && wordBitAt z c) &&
                                decide (p + c = bit + 64)))
                            (List.range 64))
                        (List.range 64)))) := by
                  apply congrArg xorBoolList
                  apply List.map_congr_left
                  intro p hp
                  exact clmulSourcePairCoeff_and_bit_high x y (List.mem_range.mp hp)
                    (wordBitAt z c) (decide (p + c = bit + 64))
            _ =
              xorBoolList
                (List.flatMap
                  (fun p =>
                    List.flatMap
                      (fun b =>
                        List.map
                          (fun a =>
                            ((((wordBitAt x a && wordBitAt y b) &&
                                decide (a + b = p + 64)) && wordBitAt z c) &&
                              decide (p + c = bit + 64)))
                          (List.range 64))
                      (List.range 64))
                  (List.range 64)) := by
                  rw [xorBoolList_map_xorBoolList]
    _ = clmulSourceTripleCoeff x y z (bit + 128) := by
          exact xorBoolList_left_high_sourceTriple_collapse x y z hbit

private theorem clmulAssoc_right_high_sourceTriple
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    wordBitAt (clmul x (clmul y z).1).1 bit =
      clmulSourceTripleCoeff x y z (bit + 128) := by
  calc
    wordBitAt (clmul x (clmul y z).1).1 bit
        = wordBitAt (clmul (clmul z y).1 x).1 bit := by
          rw [clmul_comm x (clmul y z).1, clmul_comm y z]
    _ = clmulSourceTripleCoeff z y x (bit + 128) := by
          exact clmulAssoc_left_high_sourceTriple z y x hbit
    _ = clmulSourceTripleCoeff x y z (bit + 128) := by
          exact clmulSourceTripleCoeff_reverse_outer x y z (bit + 128)

private theorem clmulCoeffAt_assoc_twoWord_low
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    ((((clmul (clmul x y).2 z).2 >>> bit.toUInt64) &&& 1) != 0) =
      ((((clmul x (clmul y z).2).2 >>> bit.toUInt64) &&& 1) != 0) := by
  change wordBitAt (clmul (clmul x y).2 z).2 bit =
    wordBitAt (clmul x (clmul y z).2).2 bit
  rw [clmulAssoc_left_low_sourceTriple x y z hbit,
    clmulAssoc_right_low_sourceTriple x y z hbit]

private theorem clmulCoeffAt_assoc_twoWord_middle
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    (((((clmul (clmul x y).2 z).1 >>> bit.toUInt64) &&& 1) != 0) !=
        ((((clmul (clmul x y).1 z).2 >>> bit.toUInt64) &&& 1) != 0)) =
      (((((clmul x (clmul y z).2).1 >>> bit.toUInt64) &&& 1) != 0) !=
        ((((clmul x (clmul y z).1).2 >>> bit.toUInt64) &&& 1) != 0)) := by
  change (wordBitAt (clmul (clmul x y).2 z).1 bit !=
      wordBitAt (clmul (clmul x y).1 z).2 bit) =
    (wordBitAt (clmul x (clmul y z).2).1 bit !=
      wordBitAt (clmul x (clmul y z).1).2 bit)
  rw [clmulAssoc_left_middle_sourceTriple x y z hbit,
    clmulAssoc_right_middle_sourceTriple x y z hbit]

private theorem clmulCoeffAt_assoc_twoWord_high
    (x y z : UInt64) {bit : Nat} (hbit : bit < 64) :
    ((((clmul (clmul x y).1 z).1 >>> bit.toUInt64) &&& 1) != 0) =
      ((((clmul x (clmul y z).1).1 >>> bit.toUInt64) &&& 1) != 0) := by
  change wordBitAt (clmul (clmul x y).1 z).1 bit =
    wordBitAt (clmul x (clmul y z).1).1 bit
  rw [clmulAssoc_left_high_sourceTriple x y z hbit,
    clmulAssoc_right_high_sourceTriple x y z hbit]

private theorem clmulCoeffAt_assoc_twoWord
    (base n : Nat) (x y z : UInt64) :
    (clmulCoeffAt base (clmul x y).2 z n !=
      clmulCoeffAt (base + 1) (clmul x y).1 z n) =
    (clmulCoeffAt base x (clmul y z).2 n !=
      clmulCoeffAt (base + 1) x (clmul y z).1 n) := by
  unfold clmulCoeffAt
  by_cases h0 : n / 64 = base
  · have hbase02 : base ≠ base + 1 + 1 := by omega
    simp [h0, hbase02, clmulCoeffAt_assoc_twoWord_low x y z (Nat.mod_lt n (by decide : 0 < 64))]
  · by_cases h1 : n / 64 = base + 1
    · simp [h1, clmulCoeffAt_assoc_twoWord_middle x y z (Nat.mod_lt n (by decide : 0 < 64))]
    · by_cases h2 : n / 64 = base + 1 + 1
      · have hbase20 : base + 1 + 1 ≠ base := by omega
        simp [h2, hbase20,
          clmulCoeffAt_assoc_twoWord_high x y z (Nat.mod_lt n (by decide : 0 < 64))]
      · simp [h0, h1, h2]

/-- The raw product has enough intermediate slots to contain every source
word-pair contribution selected by the source ranges. -/
private theorem mulWords_size_source_pair
    {xs ys : Array UInt64} {i j : Nat}
    (hi : i ∈ List.range xs.size) (hj : j ∈ List.range ys.size) :
    i + j + 1 < (mulWords xs ys).size := by
  have hiLt : i < xs.size := List.mem_range.mp hi
  have hjLt : j < ys.size := List.mem_range.mp hj
  have hxs : ¬ xs.isEmpty := by
    intro h
    have hsize : xs.size = 0 := by
      simpa [Array.isEmpty] using h
    omega
  have hys : ¬ ys.isEmpty := by
    intro h
    have hsize : ys.size = 0 := by
      simpa [Array.isEmpty] using h
    omega
  unfold mulWords
  simp [hxs, hys, foldl_mulWords_size]
  omega

private theorem xorBoolList_range_single_active
    (f : Nat → Bool) {bound active : Nat}
    (hactive : active < bound)
    (hzero : ∀ slot, slot < bound → slot ≠ active → f slot = false) :
    xorBoolList ((List.range bound).map f) = f active := by
  induction bound with
  | zero =>
      omega
  | succ bound ih =>
      rw [List.range_succ, List.map_append, xorBoolList_append]
      by_cases hlast : active = bound
      · have hprefix :
            (List.range bound).map f = (List.range bound).map (fun _ => false) := by
          apply List.map_congr_left
          intro slot hslot
          have hslotLt : slot < bound := List.mem_range.mp hslot
          exact hzero slot (by omega) (by omega)
        rw [hprefix, xorBoolList_range_false]
        simp [xorBoolList, hlast]
      · have hactiveLt : active < bound := by omega
        rw [ih hactiveLt]
        · have htail : f bound = false := hzero bound (by omega) (by omega)
          simp [xorBoolList, htail]
        · intro slot hslot hslotNe
          exact hzero slot (by omega) hslotNe

private theorem clmulSourcePairCoeff_single_active
    (x y : UInt64) {a₀ b₀ total : Nat}
    (ha₀ : a₀ < 64) (hb₀ : b₀ < 64)
    (hx₀ : wordBitAt x a₀ = true) (hy₀ : wordBitAt y b₀ = true)
    (hsum : a₀ + b₀ = total)
    (hzero :
      ∀ a b, a < 64 → b < 64 → a + b = total → a ≠ a₀ ∨ b ≠ b₀ →
        (wordBitAt x a && wordBitAt y b) = false) :
    clmulSourcePairCoeff x y total = true := by
  unfold clmulSourcePairCoeff
  rw [← xorBoolList_map_xorBoolList]
  rw [xorBoolList_range_single_active
    (fun b =>
      xorBoolList
        ((List.range 64).map
          (fun a => (wordBitAt x a && wordBitAt y b) && decide (a + b = total))))
    hb₀]
  · rw [xorBoolList_range_single_active
      (fun a => (wordBitAt x a && wordBitAt y b₀) && decide (a + b₀ = total))
      ha₀]
    · simp [hx₀, hy₀, hsum]
    · intro a ha hne
      by_cases hsum' : a + b₀ = total
      · have hfalse := hzero a b₀ ha hb₀ hsum' (Or.inl hne)
        simp [hfalse, hsum']
      · simp [hsum']
  · intro b hb hne
    have hinner :
        (List.range 64).map
            (fun a => (wordBitAt x a && wordBitAt y b) && decide (a + b = total)) =
          (List.range 64).map (fun _ => false) := by
      apply List.map_congr_left
      intro a haMem
      have ha : a < 64 := List.mem_range.mp haMem
      by_cases hsum' : a + b = total
      · have hfalse := hzero a b ha hb hsum' (Or.inr hne)
        simp [hfalse, hsum']
      · simp [hsum']
    rw [hinner, xorBoolList_range_false]

private theorem xorBoolList_range_two_adjacent_active
    (f : Nat → Bool) {bound active : Nat}
    (hactive : active + 1 < bound)
    (hzero :
      ∀ slot, slot < bound → slot ≠ active → slot ≠ active + 1 → f slot = false) :
    xorBoolList ((List.range bound).map f) = (f active != f (active + 1)) := by
  induction bound with
  | zero =>
      omega
  | succ bound ih =>
      rw [List.range_succ, List.map_append, xorBoolList_append]
      by_cases hlast : active + 1 = bound
      · have hprefix :
            xorBoolList ((List.range bound).map f) = f active := by
          apply xorBoolList_range_single_active
          · omega
          · intro slot hslot hslotNe
            exact hzero slot (by omega) hslotNe (by omega)
        rw [hprefix]
        simp [xorBoolList, hlast]
      · have hactiveLt : active + 1 < bound := by omega
        rw [ih hactiveLt]
        · have htail : f bound = false := hzero bound (by omega) (by omega) (by omega)
          simp [xorBoolList, htail]
        · intro slot hslot hslotNe0 hslotNe1
          exact hzero slot (by omega) hslotNe0 hslotNe1

private theorem xorBoolList_leftAssocFixedTripleContribs_collapse
    (i j k : Nat) (x y z : UInt64) (n leftBound : Nat)
    (hleft : i + j + 1 < leftBound) :
    xorBoolList (leftAssocFixedTripleContribs i j k x y z n leftBound) =
      (clmulCoeffAt (i + j + k) (clmul x y).2 z n !=
        clmulCoeffAt (i + j + k + 1) (clmul x y).1 z n) := by
  unfold leftAssocFixedTripleContribs
  rw [xorBoolList_range_two_adjacent_active
    (fun slot => clmulCoeffAt (slot + k) (clmulWordAt (i + j) x y slot) z n)
    hleft]
  · simp [clmulWordAt]
    have hhigh : (i + j + 1) + k = i + j + k + 1 := by omega
    simp [hhigh]
  · intro slot _hslot hneLow hneHigh
    simp [clmulWordAt, hneLow, hneHigh, clmulCoeffAt_zero_left]

private theorem xorBoolList_rightAssocFixedTripleContribs_collapse
    (i j k : Nat) (x y z : UInt64) (n rightBound : Nat)
    (hright : j + k + 1 < rightBound) :
    xorBoolList (rightAssocFixedTripleContribs i j k x y z n rightBound) =
      (clmulCoeffAt (i + j + k) x (clmul y z).2 n !=
        clmulCoeffAt (i + j + k + 1) x (clmul y z).1 n) := by
  unfold rightAssocFixedTripleContribs
  rw [xorBoolList_range_two_adjacent_active
    (fun slot => clmulCoeffAt (i + slot) x (clmulWordAt (j + k) y z slot) n)
    hright]
  · simp [clmulWordAt]
    have hlow : i + (j + k) = i + j + k := by omega
    have hhigh : i + (j + k + 1) = i + j + k + 1 := by omega
    simp [hlow, hhigh]
  · intro slot _hslot hneLow hneHigh
    simp [clmulWordAt, hneLow, hneHigh, clmulCoeffAt_zero_right]

/-- Fixed source-word associativity for carry-less multiplication after
expanding only the intermediate packed-word slot. -/
private theorem xorBoolList_assoc_fixed_sourceTriple
    (i j k : Nat) (x y z : UInt64) (n leftBound rightBound : Nat)
    (hleft : i + j + 1 < leftBound) (hright : j + k + 1 < rightBound) :
    xorBoolList (leftAssocFixedTripleContribs i j k x y z n leftBound) =
      xorBoolList (rightAssocFixedTripleContribs i j k x y z n rightBound) := by
  rw [xorBoolList_leftAssocFixedTripleContribs_collapse i j k x y z n leftBound hleft,
    xorBoolList_rightAssocFixedTripleContribs_collapse i j k x y z n rightBound hright]
  exact clmulCoeffAt_assoc_twoWord (i + j + k) n x y z

/-- Regroup the left-associated source expansion by fixed source triples rather
than by intermediate product slot first. -/
private theorem leftAssocSourceTripleContribs_by_fixed
    (xs ys zs : Array UInt64) (n : Nat) :
    xorBoolList (leftAssocSourceTripleContribs xs ys zs n) =
      xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun j =>
                List.flatMap
                  (fun k =>
                    leftAssocFixedTripleContribs i j k xs[i]! ys[j]! zs[k]! n
                      (mulWords xs ys).size)
                  (List.range zs.size))
              (List.range ys.size))
          (List.range xs.size)) := by
  unfold leftAssocSourceTripleContribs leftAssocFixedTripleContribs
  simp only [List.map_flatMap, List.map_map]
  calc
    xorBoolList
        (List.flatMap
          (fun slot =>
            List.flatMap
              (fun k =>
                List.flatMap
                  (fun i =>
                    (List.range ys.size).map
                      (fun j =>
                        clmulCoeffAt (slot + k)
                          (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
                  (List.range xs.size))
              (List.range zs.size))
          (List.range (mulWords xs ys).size))
        =
      xorBoolList
        (List.flatMap
          (fun k =>
            List.flatMap
              (fun slot =>
                List.flatMap
                  (fun i =>
                    (List.range ys.size).map
                      (fun j =>
                        clmulCoeffAt (slot + k)
                          (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
                  (List.range xs.size))
              (List.range (mulWords xs ys).size))
          (List.range zs.size)) := by
          exact xorBoolList_flatMap_ranges_swap_list
            (mulWords xs ys).size zs.size
            (fun slot k =>
              List.flatMap
                (fun i =>
                  (List.range ys.size).map
                    (fun j =>
                      clmulCoeffAt (slot + k)
                        (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
                (List.range xs.size))
    _ =
      xorBoolList
        (List.flatMap
          (fun k =>
            List.flatMap
              (fun i =>
                List.flatMap
                  (fun slot =>
                    (List.range ys.size).map
                      (fun j =>
                        clmulCoeffAt (slot + k)
                          (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
                  (List.range (mulWords xs ys).size))
              (List.range xs.size))
          (List.range zs.size)) := by
          apply xorBoolList_flatMap_congr_xor
          intro k _hk
          exact xorBoolList_flatMap_ranges_swap_list
            (mulWords xs ys).size xs.size
            (fun slot i =>
              (List.range ys.size).map
                (fun j =>
                  clmulCoeffAt (slot + k)
                    (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
    _ =
      xorBoolList
        (List.flatMap
          (fun k =>
            List.flatMap
              (fun i =>
                List.flatMap
                  (fun j =>
                    (List.range (mulWords xs ys).size).map
                      (fun slot =>
                        clmulCoeffAt (slot + k)
                          (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
                  (List.range ys.size))
              (List.range xs.size))
          (List.range zs.size)) := by
          apply xorBoolList_flatMap_congr_xor
          intro k _hk
          apply xorBoolList_flatMap_congr_xor
          intro i _hi
          simpa [List.flatMap_singleton] using
            xorBoolList_flatMap_ranges_swap_list
              (mulWords xs ys).size ys.size
              (fun slot j =>
                [clmulCoeffAt (slot + k)
                  (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n])
    _ =
      xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun k =>
                List.flatMap
                  (fun j =>
                    (List.range (mulWords xs ys).size).map
                      (fun slot =>
                        clmulCoeffAt (slot + k)
                          (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
                  (List.range ys.size))
              (List.range zs.size))
          (List.range xs.size)) := by
          exact xorBoolList_flatMap_ranges_swap_list zs.size xs.size
            (fun k i =>
              List.flatMap
                (fun j =>
                  (List.range (mulWords xs ys).size).map
                    (fun slot =>
                      clmulCoeffAt (slot + k)
                        (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
                (List.range ys.size))
    _ =
      xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun j =>
                List.flatMap
                  (fun k =>
                    (List.range (mulWords xs ys).size).map
                      (fun slot =>
                        clmulCoeffAt (slot + k)
                          (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))
                  (List.range zs.size))
              (List.range ys.size))
          (List.range xs.size)) := by
          apply xorBoolList_flatMap_congr_xor
          intro i _hi
          exact xorBoolList_flatMap_ranges_swap_list zs.size ys.size
            (fun k j =>
              (List.range (mulWords xs ys).size).map
                (fun slot =>
                  clmulCoeffAt (slot + k)
                    (clmulWordAt (i + j) xs[i]! ys[j]! slot) zs[k]! n))

/-- Regroup the right-associated source expansion by fixed source triples rather
than by intermediate product slot first. -/
private theorem rightAssocSourceTripleContribs_by_fixed
    (xs ys zs : Array UInt64) (n : Nat) :
    xorBoolList (rightAssocSourceTripleContribs xs ys zs n) =
      xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun j =>
                List.flatMap
                  (fun k =>
                    rightAssocFixedTripleContribs i j k xs[i]! ys[j]! zs[k]! n
                      (mulWords ys zs).size)
                  (List.range zs.size))
              (List.range ys.size))
          (List.range xs.size)) := by
  unfold rightAssocSourceTripleContribs rightAssocFixedTripleContribs
  simp only [List.map_flatMap, List.map_map]
  apply xorBoolList_flatMap_congr_xor
  intro i _hi
  calc
    xorBoolList
        (List.flatMap
          (fun slot =>
            List.flatMap
              (fun j =>
                (List.range zs.size).map
                  (fun k =>
                    clmulCoeffAt (i + slot) xs[i]!
                      (clmulWordAt (j + k) ys[j]! zs[k]! slot) n))
              (List.range ys.size))
          (List.range (mulWords ys zs).size))
        =
      xorBoolList
        (List.flatMap
          (fun j =>
            List.flatMap
              (fun slot =>
                (List.range zs.size).map
                  (fun k =>
                    clmulCoeffAt (i + slot) xs[i]!
                      (clmulWordAt (j + k) ys[j]! zs[k]! slot) n))
              (List.range (mulWords ys zs).size))
          (List.range ys.size)) := by
          exact xorBoolList_flatMap_ranges_swap_list
            (mulWords ys zs).size ys.size
            (fun slot j =>
              (List.range zs.size).map
                (fun k =>
                  clmulCoeffAt (i + slot) xs[i]!
                    (clmulWordAt (j + k) ys[j]! zs[k]! slot) n))
    _ =
      xorBoolList
        (List.flatMap
          (fun j =>
            List.flatMap
              (fun k =>
                (List.range (mulWords ys zs).size).map
                  (fun slot =>
                    clmulCoeffAt (i + slot) xs[i]!
                      (clmulWordAt (j + k) ys[j]! zs[k]! slot) n))
              (List.range zs.size))
          (List.range ys.size)) := by
          apply xorBoolList_flatMap_congr_xor
          intro j _hj
          simpa [List.flatMap_singleton] using
            xorBoolList_flatMap_ranges_swap_list
              (mulWords ys zs).size zs.size
              (fun slot k =>
                [clmulCoeffAt (i + slot) xs[i]!
                  (clmulWordAt (j + k) ys[j]! zs[k]! slot) n])

private theorem leftAssocSourceTripleContribs_slot
    (xs ys zs : Array UInt64) (slot n : Nat) :
    xorBoolList
        ((List.range zs.size).map
          (fun k => clmulCoeffAt (slot + k) (mulWords xs ys)[slot]! zs[k]! n)) =
      xorBoolList
        (List.flatMap
          (fun k =>
            (List.flatMap
              (fun i =>
                (List.range ys.size).map
                  (fun j => clmulWordAt (i + j) xs[i]! ys[j]! slot))
              (List.range xs.size)).map
              (fun word => clmulCoeffAt (slot + k) word zs[k]! n))
          (List.range zs.size)) := by
  rw [← xorBoolList_map_xorBoolList]
  congr 1
  apply List.map_congr_left
  intro k _hk
  exact clmulCoeffAt_mulWords_left_contrib xs ys slot (slot + k) zs[k]! n

private theorem rightAssocSourceTripleContribs_slot
    (xs ys zs : Array UInt64) (i n : Nat) :
    xorBoolList
        ((List.range (mulWords ys zs).size).map
          (fun slot => clmulCoeffAt (i + slot) xs[i]! (mulWords ys zs)[slot]! n)) =
      xorBoolList
        (List.flatMap
          (fun slot =>
            (List.flatMap
              (fun j =>
                (List.range zs.size).map
                  (fun k => clmulWordAt (j + k) ys[j]! zs[k]! slot))
              (List.range ys.size)).map
              (fun word => clmulCoeffAt (i + slot) xs[i]! word n))
          (List.range (mulWords ys zs).size)) := by
  rw [← xorBoolList_map_xorBoolList]
  congr 1
  apply List.map_congr_left
  intro slot _hslot
  exact clmulCoeffAt_mulWords_right_contrib ys zs slot (i + slot) xs[i]! n

/-- Coefficients of the left-associated raw product expand to the finite XOR
of the source-word triples contributing to `(xs * ys) * zs`. -/
private theorem coeffWords_mulWords_left_assoc_sourceTriples
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords (mulWords xs ys) zs) n =
      xorBoolList (leftAssocSourceTripleContribs xs ys zs n) := by
  rw [coeffWords_mulWords_contrib]
  unfold leftAssocSourceTripleContribs
  exact xorBoolList_flatMap_congr_xor
    (fun slot _hslot => leftAssocSourceTripleContribs_slot xs ys zs slot n)

/-- Coefficients of the right-associated raw product expand to the finite XOR
of the source-word triples contributing to `xs * (ys * zs)`. -/
private theorem coeffWords_mulWords_right_assoc_sourceTriples
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords xs (mulWords ys zs)) n =
      xorBoolList (rightAssocSourceTripleContribs xs ys zs n) := by
  rw [coeffWords_mulWords_contrib]
  unfold rightAssocSourceTripleContribs
  exact xorBoolList_flatMap_congr_xor
    (fun i _hi => rightAssocSourceTripleContribs_slot xs ys zs i n)

/-- The source-triple XOR expansions of the two raw associated products
contribute the same coefficient.  Proving this requires the fixed source-word
triple identity: summing over the intermediate word slot in `(xs[i] * ys[j]) *
zs[k]` matches summing over the intermediate word slot in `xs[i] * (ys[j] *
zs[k])`. -/
private theorem xorBoolList_assoc_sourceTripleContribs
    (xs ys zs : Array UInt64) (n : Nat) :
    xorBoolList (leftAssocSourceTripleContribs xs ys zs n) =
      xorBoolList (rightAssocSourceTripleContribs xs ys zs n) := by
  rw [leftAssocSourceTripleContribs_by_fixed, rightAssocSourceTripleContribs_by_fixed]
  apply xorBoolList_flatMap_congr_xor
  intro i hi
  apply xorBoolList_flatMap_congr_xor
  intro j hj
  apply xorBoolList_flatMap_congr_xor
  intro k hk
  exact xorBoolList_assoc_fixed_sourceTriple i j k xs[i]! ys[j]! zs[k]! n
    (mulWords xs ys).size (mulWords ys zs).size
    (mulWords_size_source_pair hi hj)
    (mulWords_size_source_pair hj hk)

private theorem clmulCoeffAt_comm (i j : Nat) (x y : UInt64) (n : Nat) :
    clmulCoeffAt (i + j) x y n = clmulCoeffAt (j + i) y x n := by
  unfold clmulCoeffAt
  rw [Nat.add_comm i j, clmul_comm x y]

/-- Coefficients of the raw packed product are symmetric in the two input word
arrays. This is the local step from word-level `clmul_comm` to polynomial
multiplication commutativity. -/
private theorem coeffWords_mulWords_comm (xs ys : Array UInt64) (n : Nat) :
    coeffWords (mulWords xs ys) n = coeffWords (mulWords ys xs) n := by
  rw [coeffWords_mulWords_contrib xs ys n, coeffWords_mulWords_contrib ys xs n]
  rw [xorBoolList_wordPairs_swap xs.size ys.size
    (fun i j => clmulCoeffAt (i + j) xs[i]! ys[j]! n)]
  congr 1
  apply List.flatMap_congr_left
  intro j hj
  apply List.map_congr_left
  intro i hi
  exact clmulCoeffAt_comm i j xs[i]! ys[j]! n

private theorem coeffWords_mulWords_normalize_left
    (xs ys : Array UInt64) (n : Nat) :
    coeffWords (mulWords (normalizeWords xs) ys) n =
      coeffWords (mulWords xs ys) n := by
  rw [← coeffWords_mulWords_common_left (normalizeWords xs) ys n xs.size
    (normalizeWords_size_le xs)]
  rw [← coeffWords_mulWords_common_left xs ys n xs.size (Nat.le_refl xs.size)]
  simp [normalizeWords_getElem!]

private theorem coeffWords_mulWords_normalize_right
    (xs ys : Array UInt64) (n : Nat) :
    coeffWords (mulWords xs (normalizeWords ys)) n =
      coeffWords (mulWords xs ys) n := by
  rw [coeffWords_mulWords_comm xs (normalizeWords ys), coeffWords_mulWords_normalize_left ys xs,
    coeffWords_mulWords_comm ys xs]

private theorem coeffWords_mulWords_ofWords_left
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords (ofWords (mulWords xs ys)).words zs) n =
      coeffWords (mulWords (mulWords xs ys) zs) n := by
  change coeffWords (mulWords (normalizeWords (mulWords xs ys)) zs) n =
    coeffWords (mulWords (mulWords xs ys) zs) n
  exact coeffWords_mulWords_normalize_left (mulWords xs ys) zs n

private theorem coeffWords_mulWords_ofWords_right
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords xs (ofWords (mulWords ys zs)).words) n =
      coeffWords (mulWords xs (mulWords ys zs)) n := by
  change coeffWords (mulWords xs (normalizeWords (mulWords ys zs))) n =
    coeffWords (mulWords xs (mulWords ys zs)) n
  exact coeffWords_mulWords_normalize_right xs (mulWords ys zs) n

/-- Raw packed multiplication is coefficientwise associative.  This is the
source-triple frontier: the two source-triple expansions above reduce raw
associativity to a fixed-triple word contribution identity. -/
private theorem coeffWords_mulWords_assoc
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords (mulWords xs ys) zs) n =
      coeffWords (mulWords xs (mulWords ys zs)) n := by
  rw [coeffWords_mulWords_left_assoc_sourceTriples,
    coeffWords_mulWords_right_assoc_sourceTriples]
  exact xorBoolList_assoc_sourceTripleContribs xs ys zs n


end GF2Poly
end Hex
