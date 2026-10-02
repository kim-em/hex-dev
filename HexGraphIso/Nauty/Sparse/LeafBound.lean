/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.LeafCodes
public import HexGraphIso.Nauty.Sparse.Maximum
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The actual discrete classifier and exit satisfy both native fragment
bounds: they cover the candidate and install exactly the maximum permitted
by that candidate and the incoming incumbent. -/
theorem Comparison.leaf_bounded {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {cs bs fs : List Nat} {st : State n} (h : Comparison G.graph cs bs fs st)
    (hh : RouteHistory G.graph tcLevel cs.length cs.length n st)
    (hi : TraceReady G tcLevel cs.length n st) (hn : 0 < n) (hl : 1 ≤ cs.length) :
    let verdict := classify (.ofGraph G.graph) cs.length n st
    let out := (leafExit verdict.1 cs.length verdict.2).2
    ∃ bs' label, Label.ofArray? n st.lab = some label ∧
      ReturnCodes G.graph cs bs' fs out ∧
      Bounded ⟨cs ++ [codeSentinel], G.graph.relabel label.perm⟩
        (State.key G.graph bs st) (State.key G.graph bs' out) ∧
      Covers ⟨cs ++ [codeSentinel], G.graph.relabel label.perm⟩ (State.key G.graph bs' out) := by
  intro verdict out
  obtain ⟨bs', label, canon, hlabel, hcanon, hr, hmax⟩ := h.leaf_returned hh hi hn hl
  have hbefore : State.key G.graph bs st =
      some ⟨bs ++ [codeSentinel], G.graph.relabel canon.perm⟩ := by
    simp only [State.key, h.nonempty, ite_false, hcanon, Option.map_some]
  have he : State.key G.graph bs' out = some (incMax (State.key G.graph bs st)
      ⟨cs ++ [codeSentinel], G.graph.relabel label.perm⟩) := by
    rw [hbefore]
    exact hmax
  refine ⟨bs', label, hlabel, hr, Bounded.of_eq he, ?_⟩
  rw [he]
  exact Covers.incMax _ _

/-- A nonterminal code rejection leaves the actual incumbent unchanged,
so it satisfies the upper invariant for any enclosing subtree bound. -/
theorem Comparison.prune_bounded {G : Hex.SparseGraph n} {numcells : Nat}
    {cs bs fs : List Nat} {st : State n} (h : Comparison G cs bs fs st)
    (hnc : numcells ≠ n) (hbad : (classify (.ofGraph G) cs.length numcells st).1 = .bad)
    (bound : Key n) :
    let verdict := classify (.ofGraph G) cs.length numcells st
    let out := (leafExit verdict.1 cs.length verdict.2).2
    ReturnCodes G cs bs fs out ∧ Bounded bound (State.key G bs st) (State.key G bs out) := by
  intro verdict out
  obtain ⟨hr, he⟩ := h.prune_returned hnc hbad
  refine ⟨hr, ?_⟩
  rw [he]
  exact Bounded.refl _ _

end Hex.GraphIso.Nauty.Sparse
