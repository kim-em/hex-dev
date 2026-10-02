/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxScope
public import HexGraphIso.Nauty.Sparse.MaxEmit
public import HexGraphIso.Nauty.Sparse.MaxReject
public import HexGraphIso.Nauty.Sparse.ExitBound
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxEmit
import all HexGraphIso.Nauty.Sparse.Maximum
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The exact native preparation and leaf action retain the entry's
cheap boundary, including code rejection and both automorphism exits. -/
theorem Frame.emit_noncheap (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n) :
    (f.emit G tcLevel).2.noncheaplevel = f.entry.noncheaplevel := by
  unfold Frame.emit
  rw [leafExit_noncheap, (classify_controls _ _ _ _).2]
  dsimp only [prepareOther]
  rw [(chooseTarget_controls false _ _ _ _ _).2]
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.noncheaplevel, ite_self]
  rfl

/-- Coverage of the emitting node propagates across every interrupted
cheap ancestor. Each step uses its actual selected child or a previously
covered negative-comparison branch, with incumbent growth retaining that
earlier coverage. The witness names the exact receiving ancestor. -/
theorem Scope.cheap_witness {G : GraphIso.Sparse.Colored n k} {tcLevel target : Nat}
    {f : Frame n} {bs : List Nat} {st : State n} {parents : Parents n} {best : Option (Key n)}
    (h : Scope G tcLevel f bs st parents) (hbelow : target < f.level - 1)
    (hcheap : st.noncheaplevel ≤ target + 1) (hcover : Covers (f.key G.graph tcLevel) best)
    (hgrows : Grows (State.key G.graph bs st) best) : Witness G tcLevel parents.frames target best := by
  have covered : ∀ d t p, f.level - t = d → parents t = some p →
      st.noncheaplevel ≤ t → Covers (p.node.key G.graph tcLevel) best := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro t p hd hp ht
      obtain ⟨ht1, htl, hpl, hpv⟩ := h.valid t p hp
      have hb := h.boundary t p hp
      have hpc : p.state.noncheaplevel ≤ p.node.level := by omega
      rcases hpv.collapse hpc with hdom | heq
      · exact hdom.grow ((h.grows t p hp).trans hgrows)
      · rw [heq]
        by_cases hlast : t = f.level - 1
        · obtain ⟨last, hl, hc⟩ := h.parent (by omega)
          have hpLast : p = last := Option.some.inj (hp.symm.trans (hlast ▸ hl))
          rw [hpLast, hc]
          exact hcover
        · obtain ⟨q, hq⟩ := h.complete (t + 1) (by omega) (by omega)
          obtain ⟨prev, hv, hchild⟩ := h.chain (t + 1) q hq (by omega)
          simp only [Nat.add_sub_cancel] at hv
          have hprev : prev = p := Option.some.inj (hv.symm.trans hp)
          rw [hprev] at hchild
          rw [hchild]
          exact ih (f.level - (t + 1)) (by omega) (t + 1) q rfl hq (by omega)
  obtain ⟨p, hp⟩ := h.complete (target + 1) (by omega) (by omega)
  have hc := covered (f.level - (target + 1)) (target + 1) p rfl hp hcheap
  have hv := (h.valid (target + 1) p hp).2.2.2
  refine ⟨p.node, ?_, hv.node, Or.inl hc⟩
  simp only [Parents.frames, hp, Option.map_some]

/-- An actual discrete emission returning to its cheap boundary satisfies
the full maximum contract at arbitrary depth and for either short flag. -/
theorem Frame.Valid.cheap_leaf {G : GraphIso.Sparse.Colored n k} {tcLevel target : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n} {short : Bool}
    (h : f.Valid G) (hs : Scope G tcLevel f bs f.entry parents)
    (hi : CodeEntry G tcLevel f.level f.numcells f.entry)
    (hc : Comparison G.graph f.codes bs fs f.entry)
    (hd : (prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).1 = n)
    (hfirst : f.entry.gcaFirst < f.level) (hcanon : f.entry.gcaCanon < f.level)
    (hbound : f.entry.noncheaplevel ≤ f.level)
    (hexit : (f.emit G.graph tcLevel).1 = .unwind target short)
    (hcheap : target = (f.emit G.graph tcLevel).2.noncheaplevel - 1) :
    MaxResult (f.key G.graph tcLevel) (State.key G.graph bs f.entry)
      (State.best G.graph (f.emit G.graph tcLevel).2) (f.level - 1)
      (Max.Witness G tcLevel parents.frames) (f.emit G.graph tcLevel).1 := by
  obtain ⟨_, _, hb, hcover⟩ := h.leaf_bound hi hc hd
  have ht : target < f.level := prepared_bound hfirst hcanon hbound hexit
  refine ⟨hb, ?_⟩
  rw [hexit]
  refine ⟨by omega, ?_⟩
  split
  · exact hcover
  · have hn := f.emit_noncheap G.graph tcLevel
    exact hs.cheap_witness (by omega) (by omega) hcover hb.grows

/-- Every actual nondiscrete rejection satisfies the complete return
contract. The return coordinate selects either the recorded code-prefix
witness or coverage propagated across its interrupted cheap ancestors. -/
theorem Frame.Valid.prune {G : GraphIso.Sparse.Colored n k} {tcLevel target : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n} {short : Bool}
    (h : f.Valid G) (hs : Scope G tcLevel f bs f.entry parents)
    (hc : Comparison G.graph f.codes bs fs f.entry)
    (hfirst : f.entry.gcaFirst < f.level) (hcanon : f.entry.gcaCanon < f.level)
    (hbound : f.entry.noncheaplevel ≤ f.level)
    (hexit : (f.emit G.graph tcLevel).1 = .unwind target short) :
    let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
    p.1 ≠ n → (classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1 = .bad →
      MaxResult (f.key G.graph tcLevel) (State.key G.graph bs f.entry)
        (State.best G.graph (f.emit G.graph tcLevel).2) (f.level - 1)
        (Max.Witness G tcLevel parents.frames) (f.emit G.graph tcLevel).1 := by
  intro p hd hbad
  rcases f.prune_target hexit hd hbad with hcode | hcheap
  · exact h.prune_code hs.codes hc hfirst hcanon hbound hexit hd hbad hcode
  · obtain ⟨_, hb, hcover⟩ := h.prune_bound hc hd hbad
    change target = p.2.2.2.2.2.noncheaplevel - 1 at hcheap
    have ht : target < f.level := prepared_bound hfirst hcanon hbound hexit
    have hn : p.2.2.2.2.2.noncheaplevel = f.entry.noncheaplevel := by
      dsimp only [p, prepareOther]
      rw [(chooseTarget_controls false _ _ _ _ _).2]
      unfold compareCodes
      simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.noncheaplevel, ite_self]
      rfl
    refine ⟨hb, ?_⟩
    rw [hexit]
    refine ⟨by omega, ?_⟩
    split
    · exact hcover
    · exact hs.cheap_witness (by omega) (by omega) hcover hb.grows

end Hex.GraphIso.Nauty.Sparse.Max
