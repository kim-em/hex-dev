/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

This file contains code translated from the nauty 2.9.3 sources
(https://users.cecs.anu.edu.au/~bdm/nauty/), copyright Brendan McKay and Adolfo
Piperno, released under the Apache 2.0 license.
-/

module
public import HexGraphIso.Nauty.VSet.Card

public section

/-!
The `Nat` bitset view of a packed vertex set: `toNat` reads the limbs
as one bitset, the representation the kernel-facing checker computes
with, and every packed operation corresponds to its `Nat` counterpart
under it.
-/

namespace Hex.GraphIso.Nauty

namespace VSet

variable {n : Nat}

/-! # The `Nat` bitset view

The certificate checker and the kernel work with adjacency rows as
natural numbers (bit `v` for vertex `v`), where the kernel's bignum
arithmetic is fast and arrays are not. `toNat` is the boundary. -/

/-- The bitset with bit `v` set exactly for the members `v`. -/
@[expose] def toNat (s : VSet n) : Nat :=
  s.limbs.foldr (fun limb acc => (acc <<< 63) ||| limb) 0

private theorem testBit_foldr_limbs :
    ∀ (L : List Nat), (∀ x ∈ L, x < 2 ^ 63) → ∀ v : Nat,
      (L.foldr (fun limb acc => (acc <<< 63) ||| limb) 0).testBit v =
        (L.getD (v / 63) 0).testBit (v % 63)
  | [], _, v => by simp [List.getD]
  | l :: ls, hb, v => by
    rw [List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases Nat.lt_or_ge v 63 with hlt | hge
    · rw [decide_eq_false (by omega), Bool.false_and, Bool.false_or, Nat.div_eq_of_lt hlt,
        Nat.mod_eq_of_lt hlt]
      simp [List.getD]
    · rw [decide_eq_true hge, Bool.true_and,
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hb l List.mem_cons_self)
          (Nat.pow_le_pow_right (by omega) hge)), Bool.or_false,
        testBit_foldr_limbs ls (fun x hx => hb x (List.mem_cons_of_mem _ hx)),
        show (v - 63) / 63 = v / 63 - 1 by omega, show (v - 63) % 63 = v % 63 by omega]
      obtain ⟨q, hq⟩ : ∃ q, v / 63 = q + 1 := ⟨v / 63 - 1, by omega⟩
      rw [hq]
      simp [List.getD]

theorem testBit_toNat (s : VSet n) (v : Nat) : s.toNat.testBit v = s.mem v := by
  rw [toNat, ← Array.foldr_toList, testBit_foldr_limbs _ (fun x hx => by
    rw [List.mem_iff_getElem] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Array.getElem_toList, ← getElem!_pos]
    exact s.bounded i), mem_eq, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge (v / 63) s.limbs.size with h | h
  · rw [List.getElem?_eq_getElem (by simpa using h), Option.getD_some, Array.getElem_toList,
      ← getElem!_pos]
  · rw [List.getElem?_eq_none (by simpa using h), Option.getD_none,
      getElem!_neg _ _ (by omega)]
    rfl

theorem toNat_lt (s : VSet n) : s.toNat < 2 ^ n := by
  refine lt_two_pow_of_bits fun v hv => ?_
  rw [testBit_toNat]
  exact mem_of_ge hv

theorem toNat_inj {s t : VSet n} (h : s.toNat = t.toNat) : s = t :=
  ext fun v => by rw [← testBit_toNat, ← testBit_toNat, h]

/-! # The single-`Nat` view

`toNat` reads the packed limbs as one bitset, the representation the
kernel-facing replay (`HexGraphIso.Kernel.CheckKey`) computes with.
Each packed operation corresponds to its `Nat` counterpart in
`HexGraphIso.Nauty.Bits`; `ofNat` reads a bitset back. -/

theorem toNat_empty : (empty : VSet n).toNat = 0 :=
  Nat.eq_of_testBit_eq fun v => by rw [testBit_toNat, mem_empty, Nat.zero_testBit]

theorem toNat_insert (s : VSet n) (v : Nat) : (s.insert v).toNat = insertL n s.toNat v :=
  Nat.eq_of_testBit_eq fun w => by
    rw [testBit_toNat, mem_insert, insertL]
    rcases Decidable.em (v < n) with hv | hv
    · rw [ite_eq_left hv, Nat.testBit_or, testBit_one_shift, testBit_toNat,
        decide_eq_true hv, Bool.and_true]
    · rw [ite_eq_right hv, testBit_toNat, decide_eq_false hv, Bool.and_false,
        Bool.or_false]

theorem toNat_erase (s : VSet n) (v : Nat) : (s.erase v).toNat = eraseL n s.toNat v :=
  Nat.eq_of_testBit_eq fun w => by
    rw [testBit_toNat, mem_erase, eraseL]
    rcases Decidable.em (v < n ∧ s.toNat.testBit v = true) with h | h
    · rw [ite_eq_left h, Nat.testBit_xor, testBit_one_shift, testBit_toNat]
      rcases Decidable.em (v = w) with rfl | hne
      · rw [testBit_toNat] at h
        rw [h.2]
        simp
      · rw [show (v == w) = false from by simp [hne]]
        cases s.mem w <;> rfl
    · rw [ite_eq_right h, testBit_toNat]
      rcases Decidable.em (v = w) with rfl | hne
      · have hm : s.mem v = false := by
          rcases Nat.lt_or_ge v n with hv | hv
          · rw [testBit_toNat] at h
            rcases hb : s.mem v with _ | _
            · rfl
            · exact absurd ⟨hv, hb⟩ h
          · exact mem_of_ge hv
        rw [hm]
        rfl
      · rw [show (v == w) = false from by simp [hne]]
        cases s.mem w <;> rfl

theorem toNat_inter (s t : VSet n) : (s.inter t).toNat = s.toNat &&& t.toNat :=
  Nat.eq_of_testBit_eq fun w => by
    rw [testBit_toNat, mem_inter, Nat.testBit_and, testBit_toNat, testBit_toNat]

theorem toNat_union (s t : VSet n) : (s.union t).toNat = s.toNat ||| t.toNat :=
  Nat.eq_of_testBit_eq fun w => by
    rw [testBit_toNat, mem_union, Nat.testBit_or, testBit_toNat, testBit_toNat]

theorem toNat_xor (s t : VSet n) : (s.xor t).toNat = s.toNat ^^^ t.toNat :=
  Nat.eq_of_testBit_eq fun w => by
    rw [testBit_toNat, mem_xor, Nat.testBit_xor, testBit_toNat, testBit_toNat]

theorem card_eq_popCount (s : VSet n) : s.card = popCount s.toNat := by
  rw [popCount_eq_bitCount n _ (toNat_lt s), bitCount, card_eq_countBelow, countBelow]
  congr 1
  funext v
  rw [testBit_toNat]

theorem cardInter_eq_popCount (s t : VSet n) :
    s.cardInter t = popCount (s.toNat &&& t.toNat) := by
  rw [cardInter_eq, card_eq_popCount, toNat_inter]

theorem interIsEmpty_eq_and (s t : VSet n) :
    s.interIsEmpty t = (s.toNat &&& t.toNat == 0) := by
  rw [Bool.eq_iff_iff, interIsEmpty_eq, isEmpty_iff, beq_iff_eq, ← toNat_inter]
  constructor
  · intro h
    rw [h, toNat_empty]
  · intro h
    exact toNat_inj (h.trans toNat_empty.symm)

theorem subset_eq_and (s t : VSet n) :
    s.subset t = (s.toNat &&& t.toNat == s.toNat) := by
  rw [Bool.eq_iff_iff, subset_iff_inter, beq_iff_eq, ← toNat_inter]
  constructor
  · intro h
    rw [h]
  · intro h
    exact toNat_inj h

theorem nextElem_eq_nextElemL (s : VSet n) (pos : Option Nat) :
    s.nextElem pos = nextElemL s.toNat pos := by
  -- the masked bitset the `Nat` side scans
  have key : ∀ (s' : Nat), (∀ w, s'.testBit w = (decide (scanStart pos ≤ w) && s.mem w)) →
      s.nextElem pos = (if s' = 0 then none else some (lowBit s')) := by
    intro s' hbit
    rcases h : s.nextElem pos with _ | v
    · have hnone := nextElem_eq_none_iff.mp h
      have hz : s' = 0 := Nat.eq_of_testBit_eq fun w => by
        rw [hbit, Nat.zero_testBit]
        rcases Decidable.em (scanStart pos ≤ w) with hw | hw
        · rw [hnone w hw, Bool.and_false]
        · rw [decide_eq_false hw, Bool.false_and]
      rw [ite_eq_left hz]
    · obtain ⟨hv, hstart, hlow⟩ := nextElem_eq_some_iff.mp h
      have hne : s' ≠ 0 := by
        intro hz
        have := congrArg (fun x => x.testBit v) hz
        simp only [hbit, Nat.zero_testBit, hv, decide_eq_true hstart, Bool.and_true] at this
        cases this
      have hlb : lowBit s' = v :=
        lowBit_eq_of (by rw [hbit, hv, decide_eq_true hstart]; rfl) fun i hi => by
          rw [hbit]
          rcases Decidable.em (scanStart pos ≤ i) with hw | hw
          · rw [hlow i hw hi, Bool.and_false]
          · rw [decide_eq_false hw, Bool.false_and]
      rw [ite_eq_right hne, hlb]
  rcases pos with _ | p
  · exact key s.toNat fun w => by
      rw [testBit_toNat]
      show s.mem w = (decide (0 ≤ w) && s.mem w)
      rw [decide_eq_true (Nat.zero_le w), Bool.true_and]
  · exact key ((s.toNat >>> (p + 1)) <<< (p + 1)) fun w => by
      rw [testBit_shiftUp, testBit_toNat]
      rfl

theorem rowCmp_eq_rowCmpL (s t : VSet n) : s.rowCmp t = rowCmpL s.toNat t.toNat := by
  have hne_of : ∀ d, s.mem d ≠ t.mem d → s.toNat ≠ t.toNat := fun d hd he =>
    hd (by rw [← testBit_toNat, ← testBit_toNat, he])
  rcases h : s.rowCmp t with _ | _ | _
  · obtain ⟨d, hs, ht, hlow⟩ := rowCmp_lt_iff.mp h
    have hne := hne_of d (by rw [hs, ht]; exact Bool.false_ne_true)
    rw [rowCmpL, ite_eq_right hne, lowBit_eq_of (s := s.toNat ^^^ t.toNat) (d := d)
      (by rw [Nat.testBit_xor, testBit_toNat, testBit_toNat, hs, ht]; rfl)
      (fun i hi => by rw [Nat.testBit_xor, testBit_toNat, testBit_toNat, hlow i hi]; simp),
      testBit_toNat, hs]
    rfl
  · rw [rowCmp_eq_iff] at h
    subst h
    rw [rowCmpL, ite_eq_left rfl]
  · obtain ⟨d, hs, ht, hlow⟩ := rowCmp_gt_iff.mp h
    have hne := hne_of d (by rw [hs, ht]; decide)
    rw [rowCmpL, ite_eq_right hne, lowBit_eq_of (s := s.toNat ^^^ t.toNat) (d := d)
      (by rw [Nat.testBit_xor, testBit_toNat, testBit_toNat, hs, ht]; rfl)
      (fun i hi => by rw [Nat.testBit_xor, testBit_toNat, testBit_toNat, hlow i hi]; simp),
      testBit_toNat, hs]
    rfl

private theorem toNat_foldl_image (σ : Nat → Nat) (s : VSet n) :
    ∀ (l : List Nat) (init : VSet n),
      (l.foldl (fun t v => if s.mem v then t.insert (σ v) else t) init).toNat =
        l.foldl (fun t v => if s.toNat.testBit v then insertL n t (σ v) else t) init.toNat
  | [], _ => rfl
  | v :: l, init => by
    rw [List.foldl_cons, List.foldl_cons, toNat_foldl_image σ s l, testBit_toNat]
    rcases hm : s.mem v with _ | _
    · simp only [Bool.false_eq_true, ite_false]
    · simp only [ite_true, toNat_insert]

theorem toNat_image (σ : Nat → Nat) (s : VSet n) :
    (s.image σ).toNat = imageL n σ s.toNat := by
  rw [image, imageL, toNat_foldl_image, toNat_empty]

theorem toNat_foldl_insert (g : Nat → Nat) :
    ∀ (l : List Nat) (init : VSet n),
      (l.foldl (fun w o => w.insert (g o)) init).toNat =
        l.foldl (fun w o => insertL n w (g o)) init.toNat
  | [], _ => rfl
  | o :: l, init => by
    rw [List.foldl_cons, List.foldl_cons, toNat_foldl_insert g l, toNat_insert]

theorem toNat_foldl_insert_if (f : Nat → Bool) :
    ∀ (l : List Nat) (init : VSet n),
      (l.foldl (fun s v => if f v then s.insert v else s) init).toNat =
        l.foldl (fun s v => if f v then insertL n s v else s) init.toNat
  | [], _ => rfl
  | v :: l, init => by
    rw [List.foldl_cons, List.foldl_cons, toNat_foldl_insert_if f l]
    rcases hf : f v with _ | _
    · simp only [Bool.false_eq_true, ite_false]
    · simp only [ite_true, toNat_insert]

theorem toNat_ofFn (f : Nat → Bool) :
    (ofFn f : VSet n).toNat =
      (List.range n).foldl (fun s v => if f v then insertL n s v else s) 0 := by
  rw [ofFn, toNat_foldl_insert_if, toNat_empty]

/-- The packed set of a bitset. -/
@[expose] def ofNat (x : Nat) : VSet n := ofFn fun v => x.testBit v

theorem mem_ofNat (x v : Nat) : (ofNat x : VSet n).mem v = (decide (v < n) && x.testBit v) :=
  mem_ofFn _ v

theorem toNat_ofNat {x : Nat} (h : x < 2 ^ n) : (ofNat x : VSet n).toNat = x :=
  Nat.eq_of_testBit_eq fun v => by
    rw [testBit_toNat, mem_ofNat]
    rcases Nat.lt_or_ge v n with hv | hv
    · rw [decide_eq_true hv, Bool.true_and]
    · rw [decide_eq_false (by omega), Bool.false_and,
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hv))]

theorem ofNat_toNat (s : VSet n) : ofNat s.toNat = s :=
  ext fun v => by
    rw [mem_ofNat, testBit_toNat]
    rcases Nat.lt_or_ge v n with hv | hv
    · rw [decide_eq_true hv, Bool.true_and]
    · rw [decide_eq_false (by omega), Bool.false_and, mem_of_ge hv]

instance : Repr (VSet n) := ⟨fun s _ => repr s.toNat⟩


end VSet

end Hex.GraphIso.Nauty
