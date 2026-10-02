/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FilterCover
public import HexGraphIso.Nauty.Sparse.ShortPair
public import HexGraphIso.Nauty.Sparse.Prune
import all HexGraphIso.Nauty.Sparse.Coverage

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A descending automorphism filter preserves coverage of the original
target cell. A carrier may land in a visited child or outside the previous
survivors; the established ranked coverage resolves either case. -/
theorem CellCover.pruned {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc len : Nat} {cs : List Nat} {st : State n}
    {live : Nat → Prop} {best : Option (Key n)} {filtered : VSet n}
    (h : CellCover G.graph tcLevel fuel level numcells tc len cs st live best)
    (hrdy : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hc : IsCell st.ptn level tc len) (hlen : 1 < len) (hr : tc + len ≤ n)
    (hf : n < fuel + (numcells + 1))
    (hsub : ∀ v, live v → (windowSet n st.lab tc len).mem v = true)
    (hdrop : ∀ v, live v → filtered.mem v = false →
      ∃ gamma, checkAutom (Graph.context G.graph).g gamma = true ∧
        CellStab st.ptn level st.lab gamma ∧ gamma[v]! < v) :
    CellCover G.graph tcLevel fuel level numcells tc len cs st
      (fun v => live v ∧ filtered.mem v = true) best := by
  apply ChildCover.filterDesc h
  · intro x y he hy
    rwa [he]
  · intro v hv
    cases hfiltered : filtered.mem v with
    | true => exact Or.inl ⟨hv, rfl⟩
    | false =>
      obtain ⟨gamma, ha, hs, hlt⟩ := hdrop v hv hfiltered
      refine Or.inr ⟨gamma[v]!, ?_, ?_, hlt⟩
      · exact windowSet_carry hs hc (by change tc + len ≤ st.frame.lab.size; rw [hrdy.ok.labSize]; exact hr)
          (labOk_of_reach hrdy.ok.labSize hrdy.ok.reach) (hsub v hv)
      · exact congrArg (prefixKey cs) (hrdy.vertex_key hn hl ha hs hc hlen hr (hsub v hv) hf tcLevel)

/-- The actual native long filter preserves coverage using the current
path's checked interpretation of every applicable stored pair. -/
theorem PairsReady.long_cover {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc len : Nat} {st : State n} {cell : VSet n}
    {cs : List Nat} {live : Nat → Prop} {best : Option (Key n)}
    (h : PairsReady G tcLevel level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hc : IsCell st.ptn level tc len) (hlen : 1 < len) (hr : tc + len ≤ n)
    (hf : n < fuel + (numcells + 1))
    (hcover : CellCover G.graph tcLevel fuel level numcells tc len cs st live best)
    (hsub : ∀ v, live v → (windowSet n st.lab tc len).mem v = true)
    (hmem : ∀ v, live v → cell.mem v = true) :
    CellCover G.graph tcLevel fuel level numcells tc len cs st
      (fun v => live v ∧ ((policy (n := n)).longprune cell st).mem v = true) best := by
  apply hcover.pruned h.ready hn hl hc hlen hr hf hsub
  intro v hv hd
  exact h.long_drop (windowSet_lt (hsub v hv)) (hmem v hv) hd

/-- Receiving a native short return preserves the frozen parent's child
coverage. The pair validity comes from the actual completed child, and the
key equality comes from transport of all its unpruned sparse leaves. -/
theorem PairsReady.return_cover {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel runFuel level numcells tc tv target len : Nat} {first : Bool}
    {cell : VSet n} {st : State n} {key : Nat → Key n} {guideBest : Option (Key n)}
    {cs : List Nat} {live : Nat → Prop} {best : Option (Key n)}
    (h : PairsReady G tcLevel level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (hrecord : CheapRecorded level tc st) (hcanon : st.gcaCanon ≤ level) (hcap : 0 < st.wsCap)
    (he : (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel runFuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).1 =
        .unwind target true)
    (hreceive : level ≤ target) (hguide : CanonGuide level tc st key guideBest st)
    (hc : IsCell st.ptn level tc len) (hlen : 1 < len) (hr : tc + len ≤ n)
    (hf : n < fuel + (numcells + 1))
    (hcover : CellCover G.graph tcLevel fuel level numcells tc len cs st live best)
    (hsub : ∀ v, live v → (windowSet n st.lab tc len).mem v = true)
    (hmem : ∀ v, live v → cell.mem v = true) :
    let raw := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel runFuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2
    let out := (policy (n := n)).leaveChild tv raw
    CellCover G.graph tcLevel fuel level numcells tc len cs st
      (fun v => live v ∧ ((policy (n := n)).shortprune cell out).mem v = true) best := by
  intro raw out
  apply hcover.pruned h.ready hn hl hc hlen hr hf hsub
  intro v hlive hd
  exact h.short_drop hn hl ht hv hrecord hcanon hcap he hreceive hguide
    v (windowSet_lt (hsub v hlive)) (hmem v hlive) hd

end Hex.GraphIso.Nauty.Sparse
