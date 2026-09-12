/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstHistory
public import HexGraphIso.Nauty.Sparse.CodeBounds
public import HexGraphIso.Nauty.Sparse.CodeFields
public import HexGraphIso.Nauty.Sparse.CodeRead
public import HexGraphIso.Nauty.Policy.CodeState
import all HexGraphIso.Nauty.Policy.Selection
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The literal first leaf initializes both comparison machines with the
codes executed along its native descent. Their storage and code bounds are
derived from the descent, rather than assumed at the leaf. -/
theorem firstPath_codes {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel numcells last : Nat} {st leaf : State n}
    (hn : 0 < n)
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel 1 numcells st last leaf)
    (h : NodeInv G 1 numcells st) (htsize : n < st.firsttc.size)
    (hfsize : st.firstcode.size = n + 2) (hcsize : st.canoncode.size = n + 2) :
    ∃ codes, codes.length = last ∧
      Codes codes codes (firstterminal last leaf) ∧
      FirstCodeInv n codes codes (firstterminal last leaf).firstcode
        (firstterminal last leaf).eqlevFirst := by
  obtain ⟨xs, U, codes, trace, _, _, hstored, _, _, _⟩ :=
    firstPath_history hn path (Nat.le_refl _) h htsize (by omega)
  have hlen : codes.length = last := by
    have := trace.length
    have := trace.descent.length
    omega
  have hb : codes.length ≤ n := by
    have hr := trace.descent.ready h.refined
    have := hr.spec.depth
    have := hr.spec.count
    have := bcount_le U.ptn last n
    omega
  have hlt := trace.codes_lt (refineWith_code_lt _ _ _ _ _ _ _)
  have hvalues : ∀ i, 1 ≤ i → i ≤ codes.length → leaf.firstcode[i]! = codes[i - 1]! := by
    intro i hi hb
    have hs := hstored (i - 1) (by omega)
    simpa only [show 1 + (i - 1) = i by omega] using hs
  have hcc : leaf.canoncode.size = n + 2 := by rw [firstPath_canoncode path, hcsize]
  have hfc : leaf.firstcode.size = n + 2 := by
    rw [(Prod.mk.inj (firstPath_storeSize path)).1, hfsize]
  refine ⟨codes, hlen, ?_, ?_⟩
  · rw [← hlen]
    exact firstterminal_codes hcc hb hvalues hlt
  · rw [← hlen]
    exact firstterminal_firstCodeInv hfc hb hvalues hlt

/-- Initialization supplies an actual first leaf and both initialized
comparison machines. The readable incumbent is that leaf's sparse key. -/
theorem initial_codes (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    ∃ last leaf codes l,
      Generic.FirstPath (.ofGraph G.graph) 100 (n + 2) 1 p.2.length
        (initial (.ofGraph G.graph) p.1 p.2) last leaf ∧
      codes.length = last ∧ codes ≠ [] ∧ Label.ofArray? n leaf.lab = some l ∧
      Codes codes codes (firstterminal last leaf) ∧
      FirstCodeInv n codes codes (firstterminal last leaf).firstcode
        (firstterminal last leaf).eqlevFirst ∧
      State.best G.graph (firstterminal last leaf) =
        some ⟨codes ++ [codeSentinel], G.graph.relabel l.perm⟩ := by
  obtain ⟨last, leaf, path, hlast, hr⟩ := initial_path G hn
  obtain ⟨codes, hlen, hc, hf⟩ := firstPath_codes hn path (NodeInv.initial G hn)
    (by change n < (Array.replicate (n + 2) (-1 : Int)).size; simp)
    (by change (Array.replicate (n + 2) 0).size = n + 2; simp)
    (by change (Array.replicate (n + 2) 0).size = n + 2; simp)
  obtain ⟨l, hl⟩ := Label.ofArray?_exists (isPerm_of_cellsReach hr.ok.labSize hn hr.ok.reach)
  have hne : codes ≠ [] := by
    intro he
    rw [he] at hlen
    simp only [List.length_nil] at hlen
    omega
  refine ⟨last, leaf, codes, l, path, hlen, hne, hl, hc, hf, ?_⟩
  rw [← hlen] at hc ⊢
  exact firstterminal_best hc hne hl

end Hex.GraphIso.Nauty.Sparse
