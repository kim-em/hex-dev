/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Refine
public import HexGraphIso.Nauty.Image

public section

/-!
Refinement as a function of cell contents.

nauty's canonical form is well defined on a coloured graph because the
refinement machinery depends on an ordered partition only through the
multiset of vertices in each cell: two labellings whose cells hold the
same vertices in any order refine to the same positions and codes with
cell-wise permuted labellings. This file builds that invariance, cell
processor by cell processor, mirroring `Nauty.Equivariance`.

`segN lab lo len` reads the labelling segment of `len` positions from
`lo` as a list; cell contents are compared with `List.Perm`. The crux
is `splitCellLoop_spec`: the two-pointer partition's final pointers are
determined by the adjacency count of the cell's multiset, and its two
output segments are permutations of the adjacency filters.
-/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- The labelling segment of `len` positions from `lo`, as a list. -/
@[expose] def segN (lab : Array Nat) (lo len : Nat) : List Nat :=
  (List.range len).map fun o => lab[lo + o]!

theorem segN_length (lab : Array Nat) (lo len : Nat) :
    (segN lab lo len).length = len := by
  rw [segN, List.length_map, List.length_range]

theorem segN_zero (lab : Array Nat) (lo : Nat) : segN lab lo 0 = [] := rfl

/-- Split the first position off a segment. -/
theorem segN_cons (lab : Array Nat) (lo len : Nat) :
    segN lab lo (len + 1) = lab[lo]! :: segN lab (lo + 1) len := by
  rw [segN, segN, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.add_zero]
  exact congrArg _ (List.map_congr_left fun o _ => by
    show lab[lo + (o + 1)]! = lab[lo + 1 + o]!
    rw [show lo + (o + 1) = lo + 1 + o by omega])

/-- Split the last position off a segment. -/
theorem segN_concat (lab : Array Nat) (lo len : Nat) :
    segN lab lo (len + 1) = segN lab lo len ++ [lab[lo + len]!] := by
  rw [segN, segN, List.range_succ, List.map_append, List.map_cons,
    List.map_nil]

/-- Segments agree when the underlying positions agree. -/
theorem segN_congr {lab lab' : Array Nat} {lo len : Nat}
    (h : ∀ o, o < len → lab[lo + o]! = lab'[lo + o]!) :
    segN lab lo len = segN lab' lo len := by
  rw [segN, segN]
  exact List.map_congr_left fun o ho => h o (List.mem_range.mp ho)

/-- The two-pointer partition, characterized: the final pointers are the
adjacency count of the cell multiset, positions outside the cell are
untouched, and the two output segments are permutations of the
adjacency filters. -/
theorem splitCellLoop_spec {gRow : Nat} :
    ∀ (k fuel : Nat) (lab : Array Nat) (c1 c2 : Int),
      0 ≤ c1 → c2 < (lab.size : Int) → c2 + 1 - c1 = (k : Int) →
      k + 1 ≤ fuel →
      (splitCellLoop gRow fuel lab c1 c2).2.1 =
          c1 + ((segN lab c1.toNat k).countP (elem gRow ·) : Int) ∧
        (splitCellLoop gRow fuel lab c1 c2).2.2 =
          c1 + ((segN lab c1.toNat k).countP (elem gRow ·) : Int) - 1 ∧
        (splitCellLoop gRow fuel lab c1 c2).1.size = lab.size ∧
        (∀ j : Nat, ((j : Int) < c1 ∨ c2 < (j : Int)) →
          (splitCellLoop gRow fuel lab c1 c2).1[j]! = lab[j]!) ∧
        ((segN (splitCellLoop gRow fuel lab c1 c2).1 c1.toNat
            ((segN lab c1.toNat k).countP (elem gRow ·))).Perm
          ((segN lab c1.toNat k).filter (elem gRow ·))) ∧
        ((segN (splitCellLoop gRow fuel lab c1 c2).1
            (c1.toNat + (segN lab c1.toNat k).countP (elem gRow ·))
            (k - (segN lab c1.toNat k).countP (elem gRow ·))).Perm
          ((segN lab c1.toNat k).filter fun v => !(elem gRow v)))
  | 0, fuel, lab, c1, c2, h1, h2, hk, hf => by
    rcases fuel with _ | f
    · omega
    rw [splitCellLoop, if_neg (by omega)]
    refine ⟨by simp [segN_zero], by simp [segN_zero]; omega, rfl,
      fun j _ => rfl, by simp [segN_zero], by simp [segN_zero]⟩
  | k + 1, fuel, lab, c1, c2, h1, h2, hk, hf => by
    rcases fuel with _ | f
    · omega
    rw [splitCellLoop, if_pos (by omega)]
    have hc1s : c1.toNat < lab.size := by omega
    have hc2s : c2.toNat < lab.size := by omega
    have hS : segN lab c1.toNat (k + 1) =
        lab[c1.toNat]! :: segN lab (c1.toNat + 1) k := segN_cons lab _ k
    rcases hadj : elem gRow lab[c1.toNat]! with _ | _
    · -- non-adjacent head: swap the ends, recurse on `[c1, c2 - 1]`
      simp only [Bool.false_eq_true, if_false]
      obtain ⟨hp1, hp2, hsz, hout, hleft, hright⟩ :=
        splitCellLoop_spec (gRow := gRow) k f
        ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat lab[c1.toNat]!)
        c1 (c2 - 1) h1
        (by rw [Array.size_set!, Array.size_set!]; omega)
        (by omega) (by omega)
      -- the original segment is the swapped one plus its old head
      have hS2 : (segN lab c1.toNat (k + 1)).Perm
          (lab[c1.toNat]! ::
            segN ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat
              lab[c1.toNat]!) c1.toNat k) := by
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · rw [segN_zero, hS, segN_zero]
        · have hc12 : c1.toNat ≠ c2.toNat := by omega
          have hgot : ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat
              lab[c1.toNat]!)[c1.toNat]! = lab[c2.toNat]! := by
            rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hc12),
              Array.getElem!_set!_self _ _ _ hc1s]
          have hmid : segN ((lab.set! c1.toNat lab[c2.toNat]!).set!
              c2.toNat lab[c1.toNat]!) (c1.toNat + 1) (k - 1) =
              segN lab (c1.toNat + 1) (k - 1) := by
            refine segN_congr fun o ho => ?_
            rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
              Array.getElem!_set!_ne _ _ _ _ (by omega)]
          have hrhs : segN ((lab.set! c1.toNat lab[c2.toNat]!).set!
              c2.toNat lab[c1.toNat]!) c1.toNat k =
              lab[c2.toNat]! :: segN lab (c1.toNat + 1) (k - 1) := by
            rw [show k = (k - 1) + 1 by omega, segN_cons, hgot, hmid,
              Nat.add_sub_cancel]
          have hlhs : segN lab c1.toNat (k + 1) =
              lab[c1.toNat]! :: (segN lab (c1.toNat + 1) (k - 1) ++
                [lab[c2.toNat]!]) := by
            rw [hS, show k = (k - 1) + 1 by omega, segN_concat,
              show c1.toNat + 1 + (k - 1) = c2.toNat by omega,
              Nat.add_sub_cancel]
          rw [hlhs, hrhs]
          exact List.Perm.cons _ (List.perm_append_singleton _ _)
      have hcnt : (segN lab c1.toNat (k + 1)).countP (elem gRow ·) =
          (segN ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat
            lab[c1.toNat]!) c1.toNat k).countP (elem gRow ·) := by
        rw [hS2.countP_eq, List.countP_cons]
        simp [hadj]
      have hcle := List.countP_le_length (p := (elem gRow ·))
        (l := segN ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat
          lab[c1.toNat]!) c1.toNat k)
      rw [segN_length] at hcle
      have hto1 : (c1 + ((segN ((lab.set! c1.toNat lab[c2.toNat]!).set!
          c2.toNat lab[c1.toNat]!) c1.toNat k).countP (elem gRow ·) :
            Int)) = c1 + ((segN lab c1.toNat (k + 1)).countP
              (elem gRow ·) : Int) := by
        rw [hcnt]
      have hfe : ((segN lab c1.toNat (k + 1)).filter (elem gRow ·)).Perm
          ((segN ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat
            lab[c1.toNat]!) c1.toNat k).filter (elem gRow ·)) := by
        have h := hS2.filter (elem gRow ·)
        rw [List.filter_cons_of_neg (by simp [hadj])] at h
        exact h
      have hfn : ((segN lab c1.toNat (k + 1)).filter
          fun v => !(elem gRow v)).Perm
          (lab[c1.toNat]! :: ((segN ((lab.set! c1.toNat
            lab[c2.toNat]!).set! c2.toNat lab[c1.toNat]!) c1.toNat
              k).filter fun v => !(elem gRow v))) := by
        have h := hS2.filter (fun v => !(elem gRow v))
        rw [List.filter_cons_of_pos (by simp [hadj])] at h
        exact h
      refine ⟨by rw [hcnt]; exact hp1, by rw [hcnt]; exact hp2,
        by rw [hsz, Array.size_set!, Array.size_set!], ?_, ?_, ?_⟩
      · intro j hj
        rw [hout j (by omega),
          Array.getElem!_set!_ne _ _ _ _ (by omega),
          Array.getElem!_set!_ne _ _ _ _ (by omega)]
      · rw [hcnt]
        exact hleft.trans hfe.symm
      · rw [hcnt,
          show k + 1 - (segN ((lab.set! c1.toNat lab[c2.toNat]!).set!
            c2.toNat lab[c1.toNat]!) c1.toNat k).countP (elem gRow ·) =
            (k - (segN ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat
              lab[c1.toNat]!) c1.toNat k).countP (elem gRow ·)) + 1
            by omega,
          segN_concat,
          show c1.toNat + (segN ((lab.set! c1.toNat lab[c2.toNat]!).set!
            c2.toNat lab[c1.toNat]!) c1.toNat k).countP (elem gRow ·) +
            (k - (segN ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat
              lab[c1.toNat]!) c1.toNat k).countP (elem gRow ·)) =
            c2.toNat by omega]
        have hlast : (splitCellLoop gRow f
            ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat
              lab[c1.toNat]!) c1 (c2 - 1)).1[c2.toNat]! =
            lab[c1.toNat]! := by
          rw [hout c2.toNat (by omega),
            Array.getElem!_set!_self _ _ _
              (by rw [Array.size_set!]; omega)]
        rw [hlast]
        refine (List.perm_append_singleton _ _).trans ?_
        exact (List.Perm.cons _ hright).trans hfn.symm
    · -- adjacent head: advance the left pointer
      simp only [if_true]
      obtain ⟨hp1, hp2, hsz, hout, hleft, hright⟩ :=
        splitCellLoop_spec (gRow := gRow) k f lab (c1 + 1) c2 (by omega)
          h2 (by omega) (by omega)
      have hto : (c1 + 1).toNat = c1.toNat + 1 := by omega
      rw [hto] at hp1 hp2 hleft hright
      have hcnt : (segN lab c1.toNat (k + 1)).countP (elem gRow ·) =
          (segN lab (c1.toNat + 1) k).countP (elem gRow ·) + 1 := by
        rw [hS, List.countP_cons]
        simp [hadj]
      refine ⟨by rw [hcnt]; rw [hp1]; push_cast; omega,
        by rw [hcnt]; rw [hp2]; push_cast; omega, hsz, ?_, ?_, ?_⟩
      · intro j hj
        exact hout j (by omega)
      · rw [hcnt, segN_cons, hS,
          List.filter_cons_of_pos (by simp [hadj]),
          hout c1.toNat (by omega)]
        exact List.Perm.cons _ hleft
      · rw [hcnt, hS, List.filter_cons_of_neg (by simp [hadj]),
          show c1.toNat + ((segN lab (c1.toNat + 1) k).countP
            (elem gRow ·) + 1) = c1.toNat + 1 + (segN lab
              (c1.toNat + 1) k).countP (elem gRow ·) by omega,
          show k + 1 - ((segN lab (c1.toNat + 1) k).countP
            (elem gRow ·) + 1) = k - (segN lab (c1.toNat + 1) k).countP
              (elem gRow ·) by omega]
        exact hright

end Hex.GraphIso.Nauty
