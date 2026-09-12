/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ChildEntry

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The production visit runs the certified sparse refinement. -/
theorem visit_equitable (G : Hex.SparseGraph n) (level numcells : Nat) (s : State n)
    (hp : s.lab.toList.Perm (List.range n)) (h : NodeOk n level s.lab s.ptn s.active)
    (hb : Scratch.Bounded n s.canong.scratch) (hc : numcells = bcount s.ptn level n)
    (hinv : CertInv (Graph.context G) level
      { lab := s.lab, ptn := s.ptn, active := s.active, numcells
        hint := 0, maxpos := 0, longcode := numcells }) :
    let t := (visit (.ofGraph G) level numcells s).2.2
    Equitable (Graph.context G) level t.lab t.ptn := by
  exact refineWith_equitable G level s.lab s.ptn s.active numcells s.canong.scratch hp
    h.ptnSize (by simpa only [h.ptnSize] using h.ptnEnd) h.starts hb hc hinv

/-- Every individualized target-cell member has an equitable child after the
actual sparse policy's cache invalidation and production visit. -/
theorem child_equitable (G : Hex.SparseGraph n) (first : Bool) (level numcells tc len o : Nat)
    (s : State n) (hp : s.lab.toList.Perm (List.range n))
    (h : NodeOk n level s.lab s.ptn s.active)
    (hb : Scratch.Bounded n s.canong.scratch) (hl : level ≤ n)
    (hcount : numcells = bcount s.ptn level n)
    (heq : Equitable (Graph.context G) level s.lab s.ptn)
    (hc : IsCell s.ptn level tc len) (hr : tc + len ≤ n) (hn : 1 < len) (ho : o < len) :
    let child := (policy (n := n)).child first level tc s.lab[tc + o]! s
    let result := visit (.ofGraph G) (level + 1) (numcells + 1) child
    result.2.2.lab.toList.Perm (List.range n) ∧
    NodeOk n (level + 1) result.2.2.lab result.2.2.ptn result.2.2.active ∧
    Scratch.Valid n result.2.2.lab result.2.2.ptn (level + 1) result.2.2.canong.scratch ∧
    result.1 = bcount result.2.2.ptn (level + 1) n ∧
    Equitable (Graph.context G) (level + 1) result.2.2.lab result.2.2.ptn := by
  dsimp only
  let child := (policy (n := n)).child first level tc s.lab[tc + o]! s
  obtain ⟨hp', h', hb', hcount', hcert⟩ := child_entry G first level numcells tc len o s hp h hb hl
    hcount heq hc hr hn ho
  have hend : child.ptn[n - 1]! ≤ level + 1 := by simpa only [h'.ptnSize] using h'.ptnEnd
  have ht := refineWith_state G (level + 1) child.lab child.ptn child.active (numcells + 1)
    child.canong.scratch hp' h'.ptnSize hend h'.starts hb'.toBounded
  refine ⟨ht.1, visit_nodeOk G _ _ child hp' h' hb'.toBounded,
    visit_valid G _ _ child hp' h'.ptnSize hend h'.starts hb'.toBounded, ?_,
    visit_equitable G _ _ child hp' h' hb'.toBounded hcount' hcert⟩
  exact refineWith_count G _ _ _ _ _ _ hp' h'.ptnSize hend h'.starts hb'.toBounded hcount'

end Hex.GraphIso.Nauty.Sparse
