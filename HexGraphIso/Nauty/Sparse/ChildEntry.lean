/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Equitable
public import HexGraphIso.Nauty.Sparse.PolicyScratch
public import HexGraphIso.Nauty.Equitable.Individualize
import all HexGraphIso.Nauty.Equitable.Step
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Individualizing a member of a bounded partition cell preserves the whole
label permutation, using the executed rotation's cell-content theorem. -/
theorem breakout_perm {n level tc len o : Nat} {lab ptn : Array Nat}
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level) (hc : IsCell ptn level tc len)
    (hb : tc + len ≤ n) (ho : o < len) :
    (breakout n lab ptn (level + 1) tc lab[tc + o]!).1.toList.Perm (List.range n) := by
  have hl : lab.size = n := by simpa using hp.length_eq
  have he : ptn[ptn.size - 1]! ≤ level := by simpa only [hs] using hend
  have hcells := breakout_cellsPerm (n := n) hc (by omega) (hl.trans hs.symm) ho
  have hf := cellsPerm_segN_perm hcells (by omega : n ≤ ptn.size) he hend
  rw [segN_eq_toList hl, segN_eq_toList ((breakout_lab_size _ _ _ _ _).trans hl)] at hf
  exact hf.symm.trans hp

/-- Partition projections of the actual sparse child policy. Cache
invalidation and first-path bookkeeping leave individualization unchanged. -/
theorem child_fields (first : Bool) (level tc tv : Nat) (s : State n) :
    let t := (policy (n := n)).child first level tc tv s
    t.lab = (breakout n s.lab s.ptn (level + 1) tc tv).1 ∧
    t.ptn = s.ptn.set! tc (level + 1) ∧ t.active = VSet.empty.insert tc := by
  cases first <;> exact ⟨rfl, rfl, rfl⟩

/-- The executed child policy supplies all entry facts for its next
refinement, including the certificate derived from the parent's equitability. -/
theorem child_entry (G : Hex.SparseGraph n) (first : Bool) (level numcells tc len o : Nat)
    (s : State n) (hp : s.lab.toList.Perm (List.range n))
    (h : NodeOk n level s.lab s.ptn s.active)
    (hb : Scratch.Bounded n s.canong.scratch) (hl : level ≤ n)
    (hcount : numcells = bcount s.ptn level n)
    (heq : Equitable (Graph.context G) level s.lab s.ptn)
    (hc : IsCell s.ptn level tc len) (hr : tc + len ≤ n) (hn : 1 < len) (ho : o < len) :
    let t := (policy (n := n)).child first level tc s.lab[tc + o]! s
    t.lab.toList.Perm (List.range n) ∧ NodeOk n (level + 1) t.lab t.ptn t.active ∧
    Scratch.Valid n t.lab t.ptn (level + 1) t.canong.scratch ∧
    numcells + 1 = bcount t.ptn (level + 1) n ∧
    CertInv (Graph.context G) (level + 1)
      { lab := t.lab, ptn := t.ptn, active := t.active, numcells := numcells + 1
        hint := 0, maxpos := 0, longcode := numcells + 1 } := by
  dsimp only
  have hf := child_fields first level tc s.lab[tc + o]! s
  have hend : s.ptn[n - 1]! ≤ level := by simpa only [h.ptnSize] using h.ptnEnd
  have hweak : ∀ q, q < n → s.ptn[q]! ≤ level ∨ level + 1 < s.ptn[q]! := by
    intro q _
    rcases h.vals q with hh | hh
    · exact Or.inl hh
    · exact Or.inr (by omega)
  have hmem := mem_cells_of_isCell (nn := n) (Nat.le_of_eq h.ptnSize.symm) h.ptnEnd hc (by omega)
    (by rw [h.ptnSize]; exact hr)
  have hopen := hc.2.2.1 tc (Nat.le_refl _) (by omega)
  have hsplit := bcount_breakout_eq hweak hopen (by rw [h.ptnSize]; omega) n (Nat.le_refl _)
  have hcert := certInv_breakout h.labSize h.ptnSize h.ptnEnd hweak
    (fun i j hi hj he => perm_injective hp hi hj he) hmem (by omega) (by omega : o ≤ tc + len - 1 - tc) heq
    (numcells := numcells)
  refine ⟨?_, ?_, child_valid first level tc _ s hb, ?_, ?_⟩
  · rw [hf.1]
    exact breakout_perm hp h.ptnSize hend hc hr ho
  · rw [hf.1, hf.2.1, hf.2.2]
    exact childNodeOk h.labSize h.labOk h.ptnSize h.ptnEnd h.vals hc hr ho
  · rw [hf.2.1, hsplit, ite_eq_left (by omega : tc < n), hcount]
  · rw [hf.1, hf.2.1, hf.2.2]
    exact hcert

end Hex.GraphIso.Nauty.Sparse
