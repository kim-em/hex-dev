/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstPath
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The incumbent label fills each original colour cell with its own
vertices. This asserts label validity, independently of maximality. -/
@[expose] def CanonLabel (G : GraphIso.Sparse.Colored n k) (st : State n) : Prop :=
  st.canonlab.size = n ∧ CellsReach G.toDense st.canonlab

theorem FrameOut.canonical {G : GraphIso.Sparse.Colored n k} {base level : Nat} {st out : State n}
    (h : FrameOut G base level st out) (hc : CanonLabel G st) : CanonLabel G out := by
  rcases h.effect.canon with he | he
  · change out.canonlab = st.canonlab at he
    simpa only [CanonLabel, he] using hc
  · exact he

theorem CanonLabel.congr {G : GraphIso.Sparse.Colored n k} {st out : State n}
    (h : CanonLabel G st) (he : out.canonlab = st.canonlab) : CanonLabel G out := by
  simpa only [CanonLabel, he] using h

/-- Installing a reached leaf creates a complete, colour-respecting label. -/
theorem Ready.canonical {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : State n}
    (h : Ready G level numcells st) : CanonLabel G (firstterminal level st) := by
  unfold firstterminal
  exact ⟨h.ok.labSize, h.ok.reach⟩

/-- Recovery and all surviving siblings retain a valid incumbent installed
by a child, even when its exit returns past the parent. -/
theorem advance_canonical (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    (first : Bool) (tcLevel fuel cfuel level numcells tc tv1 tv index : Nat) (cell : VSet n)
    (st out : State n) (exit : Generic.Exit) (hl : 1 ≤ level) (h : Ready G level numcells st)
    (ht : Generic.Target State.frame level tc cell st) (hx : FrameOut G level level st out)
    (hc : CanonLabel G out) :
    CanonLabel G (Generic.advance (n + 2)
      (fun first level numcells tc tv1 cursor cell index st =>
        Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel
          level numcells tc tv1 cursor cell index st)
      first level numcells tc tv1 tv cell index out exit).2.2 := by
  let next : Generic.SweepFn (State n) n := fun first level numcells tc tv1 cursor cell index st =>
    Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel
      level numcells tc tv1 cursor cell index st
  have hr := h.recover hn hl hx
  have hcanon : CanonLabel G ((policy (n := n)).recover (n + 2) level out) := by
    apply hc.congr
    change (Nauty.recover (n + 2) level out).canonlab = out.canonlab
    unfold Nauty.recover recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
      apply_ite SearchState.canonlab, ite_self]
  have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) → ∀ index,
      CanonLabel G (next first level numcells tc tv1 (smaller.nextElem (some tv)) smaller index
        ((policy (n := n)).recover (n + 2) level out)).2.2 := by
    intro smaller hsub index
    exact (sweep_frame G hn first tcLevel fuel cfuel level numcells tc tv1 index _ smaller _ hl hr.1
      ((ht.subset hsub).of_out hr.2.effect) (fun _ hv => VSet.nextElem_mem hv)).canonical hcanon
  have hresume : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      CanonLabel G (Generic.resume (n + 2) next first level numcells tc tv1 tv smaller index out).2.2 := by
    intro smaller hsub
    unfold Generic.resume
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · apply hcontinue
      intro v hv
      exact hsub v (Nauty.longprune_subset hv)
    · exact hcontinue smaller hsub _
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

/-- Once the first child installs a valid incumbent, the entire first-path
sweep returns a valid incumbent. Later children may improve its label. -/
theorem sweep_first_canonical (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    (tcLevel fuel cfuel level numcells tc tv index : Nat) (cell : VSet n) (st : State n)
    (hl : 1 ≤ level) (h : Ready G level numcells st)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (horbit : Generic.Policy.orbit (n := n) st tv = tv)
    (hc : CanonLabel G (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child true level tc tv st)).2) :
    CanonLabel G (Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (cfuel + 1)
      level numcells tc tv (some tv) cell index st).2.2 := by
  have hd := node_frame G hn true tcLevel fuel (level + 1) (numcells + 1) _
    (by omega) (h.child hn hl true ht hv)
  rw [Generic.sweep]
  unfold Generic.sweepStep
  simp only [Bool.not_true, horbit, beq_self_eq_true, Bool.or_true,
    Bool.and_self, ite_true]
  generalize he : Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel
    (level + 1) (numcells + 1) ((policy (n := n)).child true level tc tv st) = r at hd hc ⊢
  obtain ⟨exit, out⟩ := r
  have hp := h.child_frame hn hl true ht hv hd
  exact advance_canonical G hn true tcLevel fuel cfuel level numcells tc tv tv index cell st _ exit
    hl h ht ((hp.afterChild level tv).leave tv) (hc.congr rfl)

end Hex.GraphIso.Nauty.Sparse
