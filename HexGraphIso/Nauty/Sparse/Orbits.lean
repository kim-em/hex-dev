/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TraceResult
public import HexGraphIso.Nauty.Policy.Orbits
public import HexGraphIso.Nauty.Policy.Preserve
import all HexGraphIso.Nauty.Sparse.Trace
import all HexGraphIso.Nauty.Policy.Orbits
import all HexGraphIso.Nauty.Invariant.Orbits
import all HexGraphIso.Nauty.Policy.Preserve
import all HexGraphIso.Nauty.Search.State
import all HexGraphIso.Sparse.Run
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

variable {G : GraphIso.Sparse.Colored n k}

/-- An emitted automorphism array takes in-range vertices to in-range vertices. -/
theorem Automorphism.bound {values : Array Nat} (h : Automorphism G values)
    (v : Nat) (hv : v < n) : values[v]! < n := by
  obtain ⟨_, p, _, hp⟩ := h
  rw [hp ⟨v, hv⟩]
  exact (p.get ⟨v, hv⟩).isLt

/-- An emitted automorphism array is injective on the graph's vertices. -/
theorem Automorphism.inj {values : Array Nat} (h : Automorphism G values)
    (a b : Nat) (ha : a < n) (hb : b < n) (he : values[a]! = values[b]!) : a = b := by
  obtain ⟨_, p, _, hp⟩ := h
  rw [hp ⟨a, ha⟩, hp ⟨b, hb⟩] at he
  exact congrArg Fin.val (p.get_inj (Fin.ext he))

/-- Pointer bookkeeping relative to the literal generator trace. The
conditional form lets a completed trace justify its earlier joins; the
initialized search separately proves the condition unconditionally. -/
def OrbitTrace (G : GraphIso.Sparse.Colored n k) (st : State n) : Prop :=
  TraceOk G st → OrbSound (OrbConn st.genTrace.toList n) st.orbits n

namespace OrbitTrace

variable {st out : State n}

theorem congr (h : OrbitTrace G st) (ht : out.genTrace = st.genTrace)
    (ho : out.orbits = st.orbits) : OrbitTrace G out := by
  intro hv
  have hp := h (hv.congr ht.symm)
  simpa only [ht, ho] using hp

theorem initial (G : GraphIso.Sparse.Colored n k) (lab : Array Nat) (ends : List Nat) :
    OrbitTrace G (Sparse.initial (.ofGraph G.graph) lab ends) := by
  intro _
  exact orbSound_orbConn_init []

/-- An admission uses the new trace's permutation facts for the actual
`orbjoin`; the old pointer witnesses transport along literal trace growth. -/
theorem admit (h : OrbitTrace G st) : OrbitTrace G (Nauty.admit st) := by
  intro hv
  have hold : TraceOk G st := by
    intro values hm
    apply hv values
    rw [admit_trace, Array.mem_push]
    exact Or.inl hm
  have hmem : ∀ values ∈ (st.genTrace.push st.workperm).toList,
      Automorphism G values := by
    intro values hm
    apply hv values
    rw [admit_trace]
    simpa using hm
  rw [admit_trace, admit_orbits]
  apply orbjoin_orbConn (fun values hm => (hmem values hm).bound)
    (fun values hm => (hmem values hm).inj) (by simp)
  apply orbSound_orbConn_mono (gens := st.genTrace.toList) _ (h hold)
  intro values hm
  simp only [Array.toList_push, List.mem_append]
  exact Or.inl hm

/-- Both automorphism exits join with their appended array. Other exits
retain the pointer relation without requiring any classification premise. -/
theorem leaf (h : OrbitTrace G st) (leaf : Leaf) (level : Nat) :
    OrbitTrace G (leafExit leaf level st).2 := by
  cases leaf
  all_goals first
    | exact h.congr (leafExit_trace ..) (leafExit_orbits ..)
    | exact h.admit.congr (by rw [leafExit_trace, admit_trace])
        (by rw [leafExit_orbits, admit_orbits])

end OrbitTrace

/-- Native classification leaves the joined pointers unchanged. -/
theorem classify_orbits (g : Graph n) (level numcells : Nat) (st : State n) :
    (classify g level numcells st).2.orbits = st.orbits := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.orbits, ite_self]

/-- Every actual policy operation preserves the trace-relative relation,
including cache invalidation, first descent and the order accumulator. -/
theorem orbitPolicy (G : GraphIso.Sparse.Colored n k) (inf tcLevel : Nat) :
    Generic.Preserve (.ofGraph G.graph) inf tcLevel (OrbitTrace G) where
  visit := fun _ _ _ h => h.congr rfl rfl
  record := fun _ _ _ h => h.congr rfl rfl
  compare := by
    intro level code st h
    change OrbitTrace G (compareCodes level code st)
    apply h.congr
    all_goals unfold compareCodes
    all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.genTrace,
      apply_ite SearchState.orbits, ite_self]
  target := by
    intro first level numcells st h
    have he : let out := (chooseTarget first (.ofGraph G.graph) tcLevel level numcells st).2.2.2
        out.genTrace = st.genTrace ∧ out.orbits = st.orbits := by
      unfold chooseTarget
      apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n =>
        out.2.2.2.genTrace = st.genTrace ∧ out.2.2.2.orbits = st.orbits)
      mvcgen
      all_goals simp_all +zetaDelta
    exact h.congr he.1 he.2
  terminal := fun _ _ h => h.congr rfl rfl
  classify := fun level numcells st h => h.congr
    (classify_trace (.ofGraph G.graph) level numcells st)
    (classify_orbits (.ofGraph G.graph) level numcells st)
  leaf := fun leaf level _ h => h.leaf leaf level
  cheap := by
    intro first level st h
    change OrbitTrace G (cheapCheck first level st)
    unfold cheapCheck
    split <;> exact h.congr rfl rfl
  child := by intro first level tc tv st h; cases first <;> exact h.congr rfl rfl
  afterChild := fun _ _ _ h => h.congr rfl rfl
  leave := fun _ _ h => h.congr rfl rfl
  recover := by
    intro level st h
    apply h.congr
    all_goals change _ = _; unfold policy recoverLevels recoverPtn
    all_goals simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
      apply_ite SearchState.genTrace, apply_ite SearchState.orbits, ite_self]
  afterSweep := by
    intro first level size index st h
    change OrbitTrace G (if first then { (Nauty.afterSweep first level size index st) with
      order := (Nauty.afterSweep first level size index st).order * index }
      else Nauty.afterSweep first level size index st)
    cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals unfold Nauty.afterSweep; split <;> exact h.congr rfl rfl

/-- The conditional bookkeeping invariant holds for every executed call,
without any input validity or termination assumptions. -/
theorem node_orbitTrace (G : GraphIso.Sparse.Colored n k) (first : Bool)
    (inf tcLevel fuel level numcells : Nat) (st : State n) (h : OrbitTrace G st) :
    OrbitTrace G (Generic.node first (.ofGraph G.graph) inf tcLevel fuel level numcells st).2 :=
  Generic.node_sound (orbitPolicy G inf tcLevel).sound first fuel level numcells st h

/-- Every final pointer descends and is connected by a word in the emitted
trace. Generator validity is discharged by the initialized search theorem. -/
theorem runColored_orbits (G : GraphIso.Sparse.Colored n k) :
    OrbSound (OrbConn (runColored G).genTrace.toList n) (runColored G).orbits n := by
  apply (show OrbitTrace G (runColored G) from ?_) (runColored_trace G)
  let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
  have hi := OrbitTrace.initial G p.1 p.2
  change OrbitTrace G (finish (.ofGraph G.graph) (runState (.ofGraph G.graph) p.1 p.2).2)
  apply OrbitTrace.congr (st := (runState (.ofGraph G.graph) p.1 p.2).2) _ rfl rfl
  unfold runState
  split
  · exact hi.congr rfl rfl
  · exact node_orbitTrace G true (n + 2) 100 (n + 2) 1 p.2.length _ hi

/-- Each pointer consumed by the orbit filter has an in-range endpoint and
an explicit forward word over the search's own emitted arrays. -/
theorem orbit_word (G : GraphIso.Sparse.Colored n k) (v : Fin n) :
    (runColored G).orbits[v.val]! < n ∧
      WordConn (runColored G).genTrace.toList v.val (runColored G).orbits[v.val]! :=
  orbConn_of_ptr (runColored_orbits G) v.isLt

/-- A forward word of native automorphism arrays acts as a native
colour-preserving permutation, at every vertex simultaneously. -/
theorem word_iso (G : GraphIso.Sparse.Colored n k) :
    ∀ w : List (Array Nat), (∀ values ∈ w, Automorphism G values) →
      ∃ p : Perm n, GraphIso.Sparse.IsIso G G p ∧
        ∀ v : Fin n, (p.get v).val = applyWord w v.val
  | [], _ => ⟨Perm.id n, GraphIso.Sparse.IsIso.refl G, fun v => by simp [applyWord]⟩
  | values :: w, h => by
    obtain ⟨_, p, hp, hv⟩ := h values (List.mem_cons_self ..)
    obtain ⟨q, hq, hw⟩ := word_iso G w (fun a ha => h a (List.mem_cons_of_mem _ ha))
    refine ⟨q.comp p, hp.trans hq, fun v => ?_⟩
    rw [Perm.get_comp, hw, ← hv]
    rfl

/-- Every final orbit pointer is the image of its vertex under an actual
colour-preserving automorphism. No orbit or generator completeness is assumed. -/
theorem orbit_iso (G : GraphIso.Sparse.Colored n k) (v : Fin n) :
    ∃ p : Perm n, GraphIso.Sparse.IsIso G G p ∧
      (p.get v).val = (runColored G).orbits[v.val]! := by
  obtain ⟨_, w, hw, he⟩ := orbit_word G v
  obtain ⟨p, hp, hv⟩ := word_iso G w (fun values hm =>
    runColored_trace G values (by simpa using hw values hm))
  exact ⟨p, hp, (hv v).trans he⟩

end Hex.GraphIso.Nauty.Sparse
