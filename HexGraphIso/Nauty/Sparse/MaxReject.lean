/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxEmit
public import HexGraphIso.Nauty.Sparse.CodeScope
public import HexGraphIso.Nauty.Sparse.ExitBound
public import HexGraphIso.Nauty.Policy.Prune
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxEmit
import all HexGraphIso.Nauty.Sparse.Maximum
import all HexGraphIso.Nauty.Sparse.CodeScope
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Rejection of a nondiscrete node happens before row comparison and
leaves the state supplied to the native leaf exit unchanged. -/
theorem classify_pruned {g : Graph n} {level numcells : Nat} {st : State n}
    (hnc : numcells ≠ n) (hbad : (classify g level numcells st).1 = .bad) :
    st.compCanon < 0 ∧ classify g level numcells st = (.bad, st) := by
  rw [classify_eq] at hbad ⊢
  split
  · rename_i hd
    have hc : st.eqlevFirst ≠ level ∧ st.compCanon < 0 := by simpa using hd
    exact ⟨hc.2, rfl⟩
  · rename_i hd
    simp only [hd, bne_iff_ne.mpr hnc, ite_true] at hbad
    cases hbad

namespace Max

/-- The native rejected exit chooses either a code-supported return or
the explicit cheap boundary. This preserves both actual alternatives. -/
theorem bad_target {level target : Nat} {short : Bool} {st : State n}
    (he : (leafExit .bad level st).1 = .unwind target short) :
    st.eqlevCanon.toNat ≤ target ∨ target = st.noncheaplevel - 1 := by
  unfold leafExit at he
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at he
  split at he
  all_goals
    obtain ⟨t, s, hx, hbound⟩ := pruneReturn_target level { st with
      maxlevel := _, numbadleaves := st.numbadleaves + 1 }
    rw [he] at hx
    cases hx
    exact hbound

/-- A code-supported native rejection satisfies the complete maximum
return contract, even when it jumps past several intervening callers.
The ancestor witness is derived from recorded entries and actual codes. -/
theorem Frame.Valid.prune_code {G : GraphIso.Sparse.Colored n k} {tcLevel target : Nat}
    {f : Frame n} {frames : Frames n} {bs fs : List Nat} {short : Bool}
    (h : f.Valid G) (hs : CodeScope G f.codes frames)
    (hc : Comparison G.graph f.codes bs fs f.entry)
    (hfirst : f.entry.gcaFirst < f.level) (hcanon : f.entry.gcaCanon < f.level)
    (hcheap : f.entry.noncheaplevel ≤ f.level)
    (hexit : (f.emit G.graph tcLevel).1 = .unwind target short) :
    let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
    p.1 ≠ n → (classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1 = .bad →
      p.2.2.2.2.2.eqlevCanon.toNat ≤ target →
      MaxResult (f.key G.graph tcLevel) (State.key G.graph bs f.entry)
        (State.best G.graph (f.emit G.graph tcLevel).2) (f.level - 1)
        (Max.Witness G tcLevel frames) (f.emit G.graph tcLevel).1 := by
  intro p hd hbad hdiv
  obtain ⟨_, hb, hcover⟩ := h.prune_bound hc hd hbad
  have ht : target < f.level := prepared_bound hfirst hcanon hcheap hexit
  refine ⟨hb, ?_⟩
  rw [hexit]
  refine ⟨by omega, ?_⟩
  split
  · exact hcover
  · rename_i hne
    have hbelow : target < f.level - 1 := by omega
    have hlen := h.length
    have hdepth := h.depth
    have hm := hc.prepare tcLevel f.numcells (by omega)
    rw [hlen] at hm
    have hcomparison : Comparison G.graph (f.codes ++ [f.code G.graph]) bs fs p.2.2.2.2.2 := hm.1
    have hw := (hs.push h).rejected (tcLevel := tcLevel)
      (by simp only [List.length_append, List.length_singleton]; omega)
      hcomparison (classify_pruned hd hbad).1 hdiv
    have hw' : Max.Witness G tcLevel frames target (State.key G.graph bs p.2.2.2.2.2) :=
      (Max.Witness.below hbelow).mp hw
    rw [hm.2] at hw'
    exact hw'.grow hb.grows

/-- The actual nonterminal rejected dispatch exposes the precise split
needed by the code-return and cheap-subtree proofs. -/
theorem Frame.prune_target {G : Hex.SparseGraph n} {tcLevel target : Nat} {f : Frame n} {short : Bool}
    (hexit : (f.emit G tcLevel).1 = .unwind target short) :
    let p := prepareOther (.ofGraph G) tcLevel f.level f.numcells f.entry
    p.1 ≠ n → (classify (.ofGraph G) f.level p.1 p.2.2.2.2.2).1 = .bad →
      p.2.2.2.2.2.eqlevCanon.toNat ≤ target ∨ target = p.2.2.2.2.2.noncheaplevel - 1 := by
  intro p hd hbad
  have hc := (classify_pruned hd hbad).2
  change (leafExit (classify (.ofGraph G) f.level p.1 p.2.2.2.2.2).1 f.level
    (classify (.ofGraph G) f.level p.1 p.2.2.2.2.2).2).1 = .unwind target short at hexit
  rw [hc] at hexit
  exact bad_target hexit

end Max
end Hex.GraphIso.Nauty.Sparse
