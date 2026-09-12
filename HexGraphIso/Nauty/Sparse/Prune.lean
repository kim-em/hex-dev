/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.PairsResult
import all HexGraphIso.Nauty.Policy.Pairs
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The native path invariant transports the root workspace to precisely
the pairs whose fixed sets cover the current individualized vertices. -/
theorem PathInv.pairs {G : GraphIso.Sparse.Colored n k} {level : Nat} {st : State n}
    (h : PathInv G level st) (hp : PairsOk G st) : LocalAutos (Graph.context G.graph) level st.frame :=
  h.stab.toLocal hp

/-- Every member removed by the native long filter is moved to a smaller
vertex by a checked automorphism stabilizing the current partition. -/
theorem PairsReady.long_drop {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells v : Nat}
    {st : State n} (h : PairsReady G tcLevel level numcells st) {cell : VSet n}
    (hv : v < n) (hm : cell.mem v = true)
    (hd : ((policy (n := n)).longprune cell st).mem v = false) :
    ∃ gamma, checkAutom (Graph.context G.graph).g gamma = true ∧ CellStab st.ptn level st.lab gamma ∧
      gamma[v]! < v :=
  longprune_drop hv hm hd (h.path.pairs h.pairs)

/-- Long filtering a whole current cell retains a representative reached
by a checked automorphism fixing the current path. The proof concerns the
literal native filter and does not assume complete generator discovery. -/
theorem PairsReady.long_carried {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells tc len : Nat}
    {st : State n} (h : PairsReady G tcLevel level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (v : Fin n)
    (hv : (windowSet n st.lab tc len).mem v.val = true) :
    ∃ gamma, checkAutom (Graph.context G.graph).g gamma = true ∧
      (∀ u, u < n → st.fixedpts.mem u = true → gamma[u]! = u) ∧
      CellStab st.ptn level st.lab gamma ∧
      (windowSet n st.lab tc len).mem gamma[v.val]! = true ∧
      ((policy (n := n)).longprune (windowSet n st.lab tc len) st).mem gamma[v.val]! = true :=
  longprune_carried (h.ready.partition hn hl).labOk h.ready.ok.labSize h.ready.ok.ptnSize
    (searchOk_end hn h.ready.ok hl) hc hb (h.path.pairs h.pairs) v.val v.isLt hv

end Hex.GraphIso.Nauty.Sparse
