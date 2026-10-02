/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CanonNode
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A native child return retains provenance when passed outward or
composed with the recovered parent's remaining siblings. -/
theorem canon_advance (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    {fuel cfuel : Nat} {next : Generic.SweepFn (State n) n}
    (hnext : (canonContract G).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n)
    (st out : State n) (exit : Exit) (hl : 1 ≤ level) (hi : Ready G level numcells st)
    (ht : Generic.Target State.frame level tc cell st)
    (hf : FrameOut G level level st out) (hc : CanonOut level st out) :
    CanonOut level st (Generic.advance (n + 2) next first level numcells tc tv1 tv cell index out exit).2.2 := by
  have hr := hi.recover hn hl hf
  have hcanon := CanonOut.recover hc (n + 2)
  have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) → ∀ index,
      CanonOut level st (next first level numcells tc tv1 (smaller.nextElem (some tv)) smaller index
        ((policy (n := n)).recover (n + 2) level out)).2.2 := by
    intro smaller hs index
    apply CanonOut.trans hcanon _ hr.2
    exact (hnext first level numcells tc tv1 (smaller.nextElem (some tv)) smaller index _
      ⟨hl, hr.1, (ht.subset hs).of_out hr.2.effect, fun _ hv => VSet.nextElem_mem hv⟩).2
  have hresume : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      CanonOut level st (Generic.resume (n + 2) next first level numcells tc tv1 tv smaller index out).2.2 := by
    intro smaller hs
    unfold Generic.resume
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact hcontinue _ (fun _ hv => hs _ (Nauty.longprune_subset hv)) _
    · exact hcontinue smaller hs _
  cases exit with
  | fuel => exact hc
  | done => exact hresume cell (fun _ hv => hv)
  | unwind target short =>
    unfold Generic.advance
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact hc
    · split
      · exact hresume _ (fun _ hv => Nauty.shortprune_subset (st := out.frame) hv)
      · exact hresume cell (fun _ hv => hv)

/-- The actual individualized child and following sweep compose their
canonical provenance, including first-child bookkeeping and skipped orbits. -/
theorem canon_sweep (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    {fuel cfuel : Nat} {descend : Generic.NodeFn (State n)} {next : Generic.SweepFn (State n) n}
    (hd : (canonContract G).nodeValid fuel descend) (hnext : (canonContract G).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n) (st : State n)
    (hl : 1 ≤ level) (h : Ready G level numcells st)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true) :
    CanonOut level st (Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell index st).2.2 := by
  have hch := h.child hn hl first ht hv
  have hout := hd (first && tv == tv1) (level + 1) (numcells + 1)
    ((policy (n := n)).child first level tc tv st) ⟨by omega, hch⟩
  unfold Generic.sweepStep
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  split
  · generalize he : descend (first && tv == tv1) (level + 1) (numcells + 1)
      ((policy (n := n)).child first level tc tv st) = r at hout ⊢
    obtain ⟨exit, out⟩ := r
    have hframe := h.child_frame hn hl first ht hv
      (by simpa only [Nat.add_sub_cancel] using hout.1)
    have hcanon := CanonOut.child first hn hl h ht hv hout.2
    split
    · exact canon_advance G hn hnext first level numcells tc tv1 tv index cell st _ exit hl h ht
        ((hframe.afterChild level tv1).leave tv) (CanonOut.fields hcanon rfl rfl)
    · exact canon_advance G hn hnext first level numcells tc tv1 tv index cell st _ exit hl h ht
        (hframe.leave tv) (CanonOut.fields hcanon rfl rfl)
  · exact (hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell _ st
      ⟨hl, h, ht, fun _ hv => VSet.nextElem_mem hv⟩).2

end Hex.GraphIso.Nauty.Sparse
