/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.VisitCover
public import HexGraphIso.Nauty.Sparse.Maximum
import all HexGraphIso.Nauty.Sparse.Coverage
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A settled negative code comparison covers every continuation with
that prefix, independently of all subsequent refinement and sparse rows. -/
theorem Comparison.covers {G : Hex.SparseGraph n} {cs bs fs : List Nat} {st : State n}
    (h : Comparison G cs bs fs st) (hneg : st.compCanon < 0) (tail : Key n) :
    Covers (prefixKey cs tail) (State.key G bs st) := by
  have hcomp : st.compCanon = -1 := by
    rcases h.canonical.tri with ⟨he, _⟩ | ⟨_, _, _, _, _, _, he⟩
    · omega
    · rcases he with ⟨he, _⟩ | ⟨he, _, _⟩ <;> omega
  have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon (-1) := hcomp ▸ h.canonical
  obtain ⟨_, canon, _, hcanon, _⟩ := h.lower
  refine ⟨⟨bs ++ [codeSentinel], G.relabel canon.perm⟩, ?_, ?_⟩
  · simp only [State.key, h.nonempty, ite_false, hcanon, Option.map_some]
  · change (Key.cmp ⟨cs ++ tail.codes, tail.graph⟩
      ⟨bs ++ [codeSentinel], G.relabel canon.perm⟩).isLE = true
    rw [codes_less hm]
    rfl

/-- A negative comparison after the actual cached visit covers the full
unpruned node, including all descendants and their terminal row keys. -/
theorem NodeInv.code_cover {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells : Nat} {cs bs fs : List Nat} {st compared : State n}
    (h : NodeInv G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hf : n < (fuel + 1) + numcells)
    (hc : Comparison G.graph (cs ++ [(visit (.ofGraph G.graph) level numcells st).2.1]) bs fs compared)
    (hneg : compared.compCanon < 0) :
    Covers (prefixKey cs (subtreeKey G.graph tcLevel (fuel + 1) level st.lab st.ptn st.active numcells))
      (State.key G.graph bs compared) := by
  let key := subtreeKey G.graph tcLevel (fuel + 1) level st.lab st.ptn st.active numcells
  obtain ⟨suffix, hprefix⟩ := h.spec.key_prefix (tcLevel := tcLevel) hf
  have hcode : (refine (.ofGraph G.graph) level st.lab st.ptn st.active numcells).longcode =
      (visit (.ofGraph G.graph) level numcells st).2.1 := (h.visit_equiv hn hl).2.1
  have he : prefixKey cs key =
      prefixKey (cs ++ [(visit (.ofGraph G.graph) level numcells st).2.1]) ⟨suffix, key.graph⟩ := by
    change (⟨cs ++ key.codes, key.graph⟩ : Key n) = _
    change key.codes = _ at hprefix
    simp only [prefixKey, hprefix, hcode, List.append_assoc, List.singleton_append]
  change Covers (prefixKey cs key) _
  rw [he]
  exact hc.covers hneg _

/-- Native off-path preparation supplies the negative-prefix coverage
premise from the incoming comparison machines and its literal code write. -/
theorem NodeInv.prepare_cover {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel numcells : Nat} {cs bs fs : List Nat} {st : State n}
    (h : NodeInv G (cs.length + 1) numcells st) (hn : 0 < n)
    (hf : n < (fuel + 1) + numcells) (hc : Comparison G.graph cs bs fs st) :
    let p := prepareOther (.ofGraph G.graph) tcLevel (cs.length + 1) numcells st
    p.2.2.2.2.2.compCanon < 0 →
      Covers (prefixKey cs
        (subtreeKey G.graph tcLevel (fuel + 1) (cs.length + 1) st.lab st.ptn st.active numcells))
        (State.key G.graph bs p.2.2.2.2.2) := by
  intro p hneg
  have hlen : cs.length ≤ n := by
    have hb := bcount_le st.ptn (cs.length + 1) n
    have hd := h.spec.depth
    have hcount := h.spec.count
    omega
  exact h.code_cover hn (by omega) hf (hc.prepare tcLevel numcells hlen).1 hneg

end Hex.GraphIso.Nauty.Sparse
