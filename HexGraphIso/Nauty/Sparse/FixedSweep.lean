/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FixedNode
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Policy.Generic.Calls
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every return arm retains the restored fixed set. A resumed sibling
receives fixed singletons in the recovered equitable parent partition. -/
theorem fixed_advance (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    {fuel cfuel : Nat} {next : Generic.SweepFn (State n) n}
    (hnext : (fixedContract G).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n)
    (st out : State n) (exit : Generic.Exit) (hl : 1 ≤ level) (h : Ready G level numcells st)
    (htarget : Generic.Target State.frame level tc cell st) (hf : FixedCells level st.frame)
    (hx : FrameOut G level level st out) (he : out.fixedpts = st.fixedpts) :
    (Generic.advance (n + 2) next first level numcells tc tv1 tv cell index out exit).2.2.fixedpts =
      st.fixedpts := by
  have hr := h.recover hn hl hx
  have hrf := fixed_recover hn hl h hf hx he
  have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      (next first level numcells tc tv1 (smaller.nextElem (some tv)) smaller
        (if first && Generic.Policy.orbit (n := n) ((policy (n := n)).recover (n + 2) level out) tv == tv1
          then index + 1 else index)
        ((policy (n := n)).recover (n + 2) level out)).2.2.fixedpts = st.fixedpts := by
    intro smaller hsub
    have ht := (htarget.subset hsub).of_out hr.2.effect
    have hh := hnext first level numcells tc tv1 (smaller.nextElem (some tv)) smaller
      (if first && Generic.Policy.orbit (n := n) ((policy (n := n)).recover (n + 2) level out) tv == tv1
        then index + 1 else index) _
      ⟨hl, hr.1, ht, (fun _ hv => VSet.nextElem_mem hv), hrf⟩
    exact hh.trans ((recover_fixed (n + 2) level out).trans he)
  have hresume : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      (Generic.resume (n + 2) next first level numcells tc tv1 tv smaller index out).2.2.fixedpts =
        st.fixedpts := by
    intro smaller hsub
    unfold Generic.resume
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact hcontinue _ (fun v hv => hsub v (Nauty.longprune_subset hv))
    · exact hcontinue smaller hsub
  cases exit with
  | fuel => exact he
  | done => exact hresume cell (fun _ hv => hv)
  | unwind target short =>
    unfold Generic.advance
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact he
    · split
      · exact hresume _ (fun _ hv => Nauty.shortprune_subset (st := out.frame) hv)
      · exact hresume cell (fun _ hv => hv)

/-- A child call restores its enlarged fixed set by induction; removing
its fresh temporary vertex restores exactly the parent's incoming set. -/
theorem fixed_sweep (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel : Nat)
    {fuel cfuel : Nat} {next : Generic.SweepFn (State n) n}
    (hd : (fixedContract G).nodeValid fuel (Generic.nodeCall (.ofGraph G.graph) (n + 2) tcLevel fuel))
    (hnext : (fixedContract G).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n) (st : State n)
    (hl : 1 ≤ level) (h : Ready G level numcells st)
    (htarget : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (hf : FixedCells level st.frame) :
    (Generic.sweepStep (n + 2) (Generic.nodeCall (.ofGraph G.graph) (n + 2) tcLevel fuel) next
      first level numcells tc tv1 tv cell index st).2.2.fixedpts = st.fixedpts := by
  have hchild := h.child hn hl first htarget hv
  have hcf := fixed_child first hn h hf htarget hv
  have hd := hd (first && tv == tv1) (level + 1) (numcells + 1) _ ⟨by omega, hchild, hcf.2⟩
  have hx := node_frame G hn (first && tv == tv1) tcLevel fuel (level + 1) (numcells + 1)
    _ (by omega) hchild
  have hparent := h.child_frame hn hl first htarget hv hx
  unfold Generic.sweepStep
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, Generic.nodeCall] at hd ⊢
  split
  · generalize hcall : Generic.node (first && tv == tv1) (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st) = r at hd hparent ⊢
    obtain ⟨exit, out⟩ := r
    have hrestore : out.fixedpts.erase tv = st.fixedpts := by
      apply fixed_restore (st := st) (out := out) _ hcf.1
      exact hd.trans (by cases first <;> rfl)
    split
    · exact fixed_advance G hn hnext first level numcells tc tv1 tv index cell st _ exit hl h htarget hf
        ((hparent.afterChild level tv1).leave tv) hrestore
    · exact fixed_advance G hn hnext first level numcells tc tv1 tv index cell st _ exit hl h htarget hf
        (hparent.leave tv) hrestore
  · exact hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell _ st
      ⟨hl, h, htarget, (fun _ hv => VSet.nextElem_mem hv), hf⟩

end Hex.GraphIso.Nauty.Sparse
