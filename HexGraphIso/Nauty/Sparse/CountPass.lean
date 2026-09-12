/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountControl
public import HexGraphIso.Nauty.Sparse.CountOther
public import HexGraphIso.Nauty.Sparse.CountPerm

public section

namespace Hex.GraphIso.Nauty.Sparse.CountTrace

/-- A trace of executed count splits. The fixed key gives the semantic
count only on cells that are actually processed, leaving other scratch
entries unrestricted. The distance flag retains both production modes. -/
inductive Pass {n : Nat} (level : Nat) (distance : Bool) (key : Nat → Nat) :
    List Nat → RefineSt n → RefineSt n → Prop
  | nil : Pass level distance key [] s s
  | cons (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
      (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < n)
      (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
      (hv : ∀ v ∈ segN s.lab first (s.cellend[first]! + 1 - first), s.hits[v]! = key v)
      (ht : Pass level distance key rest (splitCounts level first distance s) u) :
      Pass level distance key (first :: rest) s u

/-- Consecutive portions of a count-split loop compose. -/
theorem Pass.append (h : Pass level distance key xs s t) :
    Pass level distance key ys t u → Pass level distance key (xs ++ ys) s u := by
  induction h with
  | nil => intro ht; exact ht
  | cons hc hf hb hk hv hrest ih =>
    intro ht
    exact .cons hc hf hb hk hv (ih ht)

/-- The structural facts needed at the next count split follow from the
actual splitter's permutation, frame and cache theorems. -/
theorem split_valid (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < n)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2) :
    let t := splitCounts level first distance s
    t.lab.toList.Perm (List.range n) ∧ t.ptn.size = n ∧
      Index.Valid n t.lab t.ptn level t.cellstart t.cellend := by
  have hl : s.lab.size = n := by simpa using hp.length_eq
  exact ⟨(splitCounts_perm level first distance s hf (by omega)).trans hp,
    (splitCounts_frame level first distance s).ptn_size.trans hs,
    splitCounts_index level first (s.cellend[first]! + 1 - first) distance s hp hs hi hc
      (by omega) (fun q hq he => hk q hq (by omega))⟩

/-- A completed trace preserves the labelling and valid partition index. -/
theorem Pass.valid {s t : RefineSt n} (h : Pass level distance key xs s t) :
    s.lab.toList.Perm (List.range n) → s.ptn.size = n →
    Index.Valid n s.lab s.ptn level s.cellstart s.cellend →
    t.lab.toList.Perm (List.range n) ∧ t.ptn.size = n ∧
      Index.Valid n t.lab t.ptn level t.cellstart t.cellend := by
  induction h with
  | nil => intro hp hs hi; exact ⟨hp, hs, hi⟩
  | cons hc hf hb hk hv hrest ih =>
    intro hp hs hi
    have hh := split_valid _ _ distance _ hp hs hi hc hf hb hk
    exact ih hh.1 hh.2.1 hh.2.2

end Hex.GraphIso.Nauty.Sparse.CountTrace
