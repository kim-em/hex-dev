/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.BinaryProps

public section

namespace Hex.GraphIso.Nauty.Sparse.Binary

/-- A trace of the executed singleton-cell loop. Each head is a proper
nontrivial cell at entry, and the cell contract describes its actual body.
The generation is fixed while the touched cells are processed. -/
inductive Pass {n : Nat} (level stamp : Nat) : List Nat → RefineSt n → RefineSt n → Prop
  | nil : Pass level stamp [] s s
  | cons (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
      (hf : first < s.cellend[first]!) (hb : s.cellend[first]! < n)
      (hstep : Cell level first (s.cellend[first]! + 1) (fun v => s.vmarks[v]! == stamp) s t)
      (ht : Pass level stamp rest t u) : Pass level stamp (first :: rest) s u

/-- Consecutive portions of the actual touched-cell loop compose. -/
theorem Pass.append (h : Pass level stamp xs s t) :
    Pass level stamp ys t u → Pass level stamp (xs ++ ys) s u := by
  induction h with
  | nil => intro ht; exact ht
  | cons hc hf hb hstep hrest ih =>
    intro ht
    exact .cons hc hf hb hstep (ih ht)

/-- Every completed trace carries a labelling permutation and valid cache
through all of its cells. -/
theorem Pass.valid {s t : RefineSt n} (h : Pass level stamp xs s t) :
    s.lab.toList.Perm (List.range n) → s.ptn.size = n →
    Index.Valid n s.lab s.ptn level s.cellstart s.cellend →
    t.lab.toList.Perm (List.range n) ∧ t.ptn.size = n ∧
      Index.Valid n t.lab t.ptn level t.cellstart t.cellend := by
  induction h with
  | nil => intro hp hs hi; exact ⟨hp, hs, hi⟩
  | cons hc hf hb hstep hrest ih =>
    intro hp hs hi
    have hh := hstep.valid hp hs hi hc (by omega)
    exact ih hh.1 hh.2.1 hh.2.2

end Hex.GraphIso.Nauty.Sparse.Binary
