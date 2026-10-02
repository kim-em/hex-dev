/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminant
public import HexArith.Nat.Prime

public section

/-!
The number of strictly increasing `r`-tuples in `Fin n` is the binomial
coefficient `n.choose r`. This counts the row and column selections that
`minors` enumerates, so `minors r A` has `n.choose r * m.choose r` members.
-/

namespace Hex
namespace Matrix

private theorem map_val_finRange (m : Nat) :
    (List.finRange m).map Fin.val = List.range m := by
  apply List.ext_getElem <;> simp

private theorem filter_range_lt : ∀ {b m : Nat}, b ≤ m →
    (List.range m).filter (fun i => decide (i < b)) = List.range b := by
  intro b m
  induction m with
  | zero =>
      intro h
      have hb : b = 0 := by omega
      subst hb
      simp
  | succ m ih =>
      intro h
      rw [List.range_succ, List.filter_append]
      rcases Nat.lt_or_ge m b with hm | hm
      · have hb : b = m + 1 := by omega
        subst hb
        rw [List.filter_eq_self.mpr (by intro a ha; simp at ha ⊢; omega)]
        simp [List.range_succ]
      · have hm' : ¬ m < b := by omega
        rw [ih hm]
        simp [hm']

private theorem map_val_filter_finRange {b m : Nat} (h : b ≤ m) :
    ((List.finRange m).filter (fun c : Fin m => decide (c.val < b))).map Fin.val
      = List.range b := by
  have key : ((List.finRange m).map Fin.val).filter (fun i => decide (i < b))
      = ((List.finRange m).filter (fun c : Fin m => decide (c.val < b))).map Fin.val :=
    List.filter_map
  rw [← key, map_val_finRange, filter_range_lt h]

private theorem sum_range_choose (k b : Nat) :
    ((List.range b).map (fun i => Nat.choose i k)).sum = Nat.choose b (k + 1) := by
  induction b with
  | zero => simp
  | succ b ih =>
      have hsplit : ((List.range (b + 1)).map (fun i => Nat.choose i k)).sum
          = ((List.range b).map (fun i => Nat.choose i k)).sum + Nat.choose b k := by
        rw [List.range_succ]
        simp
      rw [hsplit, ih, Nat.choose_succ_succ]
      omega

private theorem length_selectedColumnTuplesUpTo (k : Nat) : ∀ {m b : Nat}, b ≤ m →
    (selectedColumnTuplesUpTo m k b).length = Nat.choose b k := by
  induction k with
  | zero =>
      intro m b _
      simp [selectedColumnTuplesUpTo]
  | succ k ih =>
      intro m b hb
      have hfun : (fun c : Fin m => (selectedColumnTuplesUpTo m k c.val).length)
          = fun c : Fin m => Nat.choose c.val k := by
        funext c
        exact ih (Nat.le_of_lt c.isLt)
      have hmap : (((List.finRange m).filter (fun c : Fin m => decide (c.val < b))).map
            Fin.val).map (fun i => Nat.choose i k)
          = ((List.finRange m).filter (fun c : Fin m => decide (c.val < b))).map
            (fun c : Fin m => Nat.choose c.val k) := List.map_map
      rw [selectedColumnTuplesUpTo]
      simp only [List.length_flatMap, List.length_map, hfun]
      rw [← hmap, map_val_filter_finRange hb, sum_range_choose k b]

/-- `selectedColumnTuples r n` lists `n.choose r` tuples. -/
theorem length_selectedColumnTuples (r n : Nat) :
    (selectedColumnTuples r n).length = Nat.choose n r :=
  length_selectedColumnTuplesUpTo r (Nat.le_refl n)

end Matrix
end Hex
