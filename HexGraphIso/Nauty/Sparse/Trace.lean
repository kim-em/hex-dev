/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstReturn
public import HexGraphIso.Nauty.Sparse.StoreResult
public import HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Every entry of an emitted array is the forward map of a native
colour-preserving automorphism, and the array has exactly the graph order. -/
def Automorphism (G : GraphIso.Sparse.Colored n k) (values : Array Nat) : Prop :=
  values.size = n ∧ ∃ p : Perm n, GraphIso.Sparse.IsIso G G p ∧
    ∀ v : Fin n, values[v.val]! = (p.get v).val

/-- Soundness of every array in the executed, unbounded generator trace. -/
def TraceOk (G : GraphIso.Sparse.Colored n k) (st : State n) : Prop :=
  ∀ values ∈ st.genTrace, Automorphism G values

theorem classify_trace (g : Graph n) (level numcells : Nat) (st : State n) :
    (classify g level numcells st).2.genTrace = st.genTrace := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.genTrace, ite_self]

namespace TraceOk

variable {G : GraphIso.Sparse.Colored n k} {st out : State n}

theorem congr (h : TraceOk G st) (he : out.genTrace = st.genTrace) : TraceOk G out := by
  intro values hv
  rw [he] at hv
  exact h values hv

theorem initial (G : GraphIso.Sparse.Colored n k) (lab : Array Nat) (ends : List Nat) :
    TraceOk G (Sparse.initial (.ofGraph G.graph) lab ends) := by
  intro values hv
  change values ∈ (#[] : Array (Array Nat)) at hv
  simp at hv

theorem visit (h : TraceOk G st) (level numcells : Nat) :
    TraceOk G (Sparse.visit (.ofGraph G.graph) level numcells st).2.2 := h.congr rfl

theorem record (h : TraceOk G st) (level code : Nat) : TraceOk G (recordFirst level code st) := h.congr rfl

theorem compare (h : TraceOk G st) (level code : Nat) : TraceOk G (compareCodes level code st) := by
  apply h.congr
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.genTrace, ite_self]

theorem target (h : TraceOk G st) (first : Bool) (tcLevel level numcells : Nat) :
    TraceOk G (chooseTarget first (.ofGraph G.graph) tcLevel level numcells st).2.2.2 := by
  apply h.congr
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n => out.2.2.2.genTrace = st.genTrace)
  mvcgen
  all_goals simp_all +zetaDelta

theorem classify (h : TraceOk G st) (level numcells : Nat) :
    TraceOk G (Sparse.classify (.ofGraph G.graph) level numcells st).2 :=
  h.congr (classify_trace (.ofGraph G.graph) level numcells st)

theorem terminal (h : TraceOk G st) (level : Nat) : TraceOk G (firstterminal level st) := h.congr rfl

theorem cheap (h : TraceOk G st) (first : Bool) (level : Nat) : TraceOk G (cheapCheck first level st) := by
  unfold cheapCheck
  split <;> exact h.congr rfl

theorem child (h : TraceOk G st) (first : Bool) (level tc tv : Nat) :
    TraceOk G ((policy (n := n)).child first level tc tv st) := by
  cases first <;> exact h.congr rfl

theorem afterChild (h : TraceOk G st) (level tv : Nat) : TraceOk G (afterChildFirst level tv st) := h.congr rfl

theorem leave (h : TraceOk G st) (tv : Nat) :
    TraceOk G ((policy (n := n)).leaveChild tv st) := h.congr rfl

theorem recover (h : TraceOk G st) (inf level : Nat) :
    TraceOk G ((policy (n := n)).recover inf level st) := by
  apply h.congr
  change (recoverLevels level (recoverPtn inf level st)).genTrace = st.genTrace
  unfold recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.genTrace, ite_self]

theorem afterSweep (h : TraceOk G st) (first : Bool) (level size index : Nat) :
    TraceOk G ((policy (n := n)).afterSweep first level size index st) := by
  change TraceOk G (if first then { (Nauty.afterSweep first level size index st) with
    order := (Nauty.afterSweep first level size index st).order * index }
    else Nauty.afterSweep first level size index st)
  cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals unfold Nauty.afterSweep; split <;> exact h.congr rfl

/-- Each actual automorphism leaf action appends exactly its checked
workspace; every other action preserves the trace without appending. -/
theorem leaf (h : TraceOk G st) (leaf : Leaf) (level : Nat)
    (ha : leaf = .autoFirst ∨ leaf = .autoCanon → Automorphism G st.workperm) :
    TraceOk G (leafExit leaf level st).2 := by
  intro values hv
  cases leaf with
  | autoFirst =>
    rw [leafExit_trace, Array.mem_push] at hv
    exact hv.elim (h values) (fun he => he ▸ ha (Or.inl rfl))
  | autoCanon =>
    rw [leafExit_trace, Array.mem_push] at hv
    exact hv.elim (h values) (fun he => he ▸ ha (Or.inr rfl))
  | internal => exact h values hv
  | better sr => rw [leafExit_trace] at hv; exact h values hv
  | bad => rw [leafExit_trace] at hv; exact h values hv

end TraceOk

/-- Both native automorphism verdicts supply a sound array for the emitted
trace, using the frozen first history or the actual canonical row prefix. -/
theorem classify_auto {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat} {st : State n}
    (hn : 0 < n) (h : Ready G level numcells st)
    (hh : CheapHistory G.graph tcLevel level level numcells st)
    (hs : Store G.graph st) (hc : CanonLabel G st)
    (hf : st.firstlab.size = n ∧ CellsReach G.toDense st.firstlab) (hw : st.workperm.size = n) :
    let r := classify (.ofGraph G.graph) level numcells st
    r.1 = .autoFirst ∨ r.1 = .autoCanon → Automorphism G r.2.workperm := by
  intro r ha
  obtain ⟨l, hl⟩ := h.parse hn
  obtain ⟨f, hfl⟩ := Label.ofArray?_exists (isPerm_of_cellsReach hf.1 hn hf.2)
  obtain ⟨c, hcl, hprefix⟩ := hs
  refine ⟨(classify_workSize (.ofGraph G.graph) level numcells st).trans hw, ?_⟩
  rcases ha with ha | ha
  · exact ⟨l.perm.comp f.perm.inv, hh.first_iso (Prod.ext ha rfl) hw hl hfl h.ok.reach hf.2⟩
  · exact ⟨l.perm.comp c.perm.inv, classify_canon_iso G (Prod.ext ha rfl) hw hl hcl h.ok.reach hc.2 hprefix⟩

end Hex.GraphIso.Nauty.Sparse
