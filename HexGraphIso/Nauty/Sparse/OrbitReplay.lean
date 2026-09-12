/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Orbits
public import HexGraphIso.Nauty.Invariant.OrbitComplete
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Sparse.Trace
import all HexGraphIso.Nauty.Policy.Orbits
import all HexGraphIso.Nauty.Policy.Preserve
import all HexGraphIso.Sparse.Run
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- The native orbit array and count are exactly the successive joins of
the full emitted trace. This is an invariant of the executed bookkeeping,
including redundant admissions, rather than another orbit computation. -/
def OrbitReplay (st : State n) : Prop :=
  (st.orbits, st.numorbits) = st.genTrace.toList.foldl
    (fun s gamma => orbjoin s.1 gamma n) (Array.ofFn (n := n) Fin.val, n)

theorem admit_numorbits {κ : Type} (st : SearchState n κ) :
    (admit st).numorbits = (orbjoin st.orbits st.workperm n).2 := by
  unfold admit pushAuto
  simp only [Id.run_pure]
  split <;> rfl

theorem leafExit_numorbits {κ : Type} (leaf : Leaf) (level : Nat) (st : SearchState n κ) :
    (leafExit leaf level st).2.numorbits =
      match leaf with
      | .autoFirst | .autoCanon => (orbjoin st.orbits st.workperm n).2
      | _ => st.numorbits := by
  cases leaf <;> unfold leafExit pruneReturn install pushAuto
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
    apply_ite SearchState.numorbits, admit_numorbits, ite_self]

namespace OrbitReplay

variable {st out : State n}

theorem congr (h : OrbitReplay st) (ht : out.genTrace = st.genTrace)
    (ho : out.orbits = st.orbits) (hc : out.numorbits = st.numorbits) : OrbitReplay out := by
  unfold OrbitReplay
  rw [ht, ho, hc]
  exact h

theorem initial (g : Graph n) (lab : Array Nat) (ends : List Nat) :
    OrbitReplay (Sparse.initial g lab ends) := by rfl

theorem admit (h : OrbitReplay st) : OrbitReplay (Nauty.admit st) := by
  unfold OrbitReplay
  rw [admit_trace, admit_orbits, admit_numorbits]
  simp only [Array.toList_push, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [← h]

theorem leaf (h : OrbitReplay st) (leaf : Leaf) (level : Nat) :
    OrbitReplay (leafExit leaf level st).2 := by
  cases leaf
  all_goals first
    | exact h.congr (leafExit_trace ..) (leafExit_orbits ..) (leafExit_numorbits ..)
    | exact h.admit.congr (by rw [leafExit_trace, admit_trace])
        (by rw [leafExit_orbits, admit_orbits]) (by rw [leafExit_numorbits, admit_numorbits])

end OrbitReplay

/-- Literal preparation, cache invalidation and level recovery preserve
both orbit fields and their exact relationship to the trace. -/
theorem orbitReplayPolicy (g : Graph n) (inf tcLevel : Nat) :
    Generic.Preserve g inf tcLevel (OrbitReplay (n := n)) where
  visit := fun _ _ _ h => h.congr rfl rfl rfl
  record := fun _ _ _ h => h.congr rfl rfl rfl
  compare := by
    intro level code st h
    change OrbitReplay (compareCodes level code st)
    apply h.congr
    all_goals unfold compareCodes
    all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.genTrace,
      apply_ite SearchState.orbits, apply_ite SearchState.numorbits, ite_self]
  target := by
    intro first level numcells st h
    have he : let out := (chooseTarget first g tcLevel level numcells st).2.2.2
        out.genTrace = st.genTrace ∧ out.orbits = st.orbits ∧ out.numorbits = st.numorbits := by
      unfold chooseTarget
      apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n =>
        out.2.2.2.genTrace = st.genTrace ∧ out.2.2.2.orbits = st.orbits ∧ out.2.2.2.numorbits = st.numorbits)
      mvcgen
      all_goals simp_all +zetaDelta
    exact h.congr he.1 he.2.1 he.2.2
  terminal := fun _ _ h => h.congr rfl rfl rfl
  classify := by
    intro level numcells st h
    apply h.congr (classify_trace g level numcells st) (classify_orbits g level numcells st)
    change (classify g level numcells st).2.numorbits = st.numorbits
    unfold classify
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
      apply_ite SearchState.numorbits, ite_self]
  leaf := fun leaf level _ h => h.leaf leaf level
  cheap := by
    intro first level st h
    change OrbitReplay (cheapCheck first level st)
    unfold cheapCheck
    split <;> exact h.congr rfl rfl rfl
  child := by intro first level tc tv st h; cases first <;> exact h.congr rfl rfl rfl
  afterChild := fun _ _ _ h => h.congr rfl rfl rfl
  leave := fun _ _ h => h.congr rfl rfl rfl
  recover := by
    intro level st h
    apply h.congr
    all_goals change _ = _; unfold policy recoverLevels recoverPtn
    all_goals simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
      apply_ite SearchState.genTrace, apply_ite SearchState.orbits, apply_ite SearchState.numorbits, ite_self]
  afterSweep := by
    intro first level size index st h
    change OrbitReplay (if first then { (Nauty.afterSweep first level size index st) with
      order := (Nauty.afterSweep first level size index st).order * index }
      else Nauty.afterSweep first level size index st)
    cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals unfold Nauty.afterSweep; split <;> exact h.congr rfl rfl rfl

/-- Every complete or truncated native node retains the exact orbit join
sequence. The statement needs no semantic assumption about the graph. -/
theorem node_orbitReplay (first : Bool) (g : Graph n) (inf tcLevel fuel level numcells : Nat)
    (st : State n) (h : OrbitReplay st) :
    OrbitReplay (Generic.node first g inf tcLevel fuel level numcells st).2 :=
  Generic.node_sound (orbitReplayPolicy g inf tcLevel).sound first fuel level numcells st h

/-- The actual final pointers and count are the joins of precisely the
emitted sparse generator arrays, including for the empty graph. -/
theorem runColored_orbitReplay (G : GraphIso.Sparse.Colored n k) : OrbitReplay (runColored G) := by
  let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
  have hi := OrbitReplay.initial (.ofGraph G.graph) p.1 p.2
  change OrbitReplay (finish (.ofGraph G.graph) (runState (.ofGraph G.graph) p.1 p.2).2)
  apply OrbitReplay.congr (st := (runState (.ofGraph G.graph) p.1 p.2).2) _ rfl rfl rfl
  unfold runState
  split
  · exact hi.congr rfl rfl rfl
  · exact node_orbitReplay true (.ofGraph G.graph) (n + 2) 100 (n + 2) 1 p.2.length _ hi

/-- Forgetting the count in the literal join sequence gives the same
array fold used in the abstract orbit closure lemmas. -/
theorem OrbitReplay.orbits {st : State n} (h : OrbitReplay st) :
    st.orbits = st.genTrace.toList.foldl (fun o gamma => (orbjoin o gamma n).1)
      (Array.ofFn (n := n) Fin.val) := by
  have he : ∀ (xs : List (Array Nat)) (o : Array Nat) (count : Nat),
      (xs.foldl (fun s gamma => orbjoin s.1 gamma n) (o, count)).1 =
        xs.foldl (fun o gamma => (orbjoin o gamma n).1) o := by
    intro xs
    induction xs with
    | nil => intros; rfl
    | cons gamma xs ih => intro o count; exact ih _ _
  exact (congrArg Prod.fst h).trans (he _ _ _)

end Hex.GraphIso.Nauty.Sparse
