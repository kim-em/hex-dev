/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstBoundary
public import HexGraphIso.Nauty.Sparse.Orbits
public import HexGraphIso.Nauty.Policy.Pairs
public import HexGraphIso.Nauty.Generation.Stabilizer
import all HexGraphIso.Nauty.Sparse.Trace
import all HexGraphIso.Nauty.Policy.Pairs
import all HexGraphIso.Nauty.Policy.Colors
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- The literal emitted array is the shared finite renaming array for its
native permutation. This is a proof identity, with no executed conversion. -/
theorem Automorphism.array {G : GraphIso.Sparse.Colored n k} {values : Array Nat}
    (h : Automorphism G values) :
    ∃ p : Perm n, GraphIso.Sparse.IsIso G G p ∧ values = renamingArray (renamingOf p) := by
  obtain ⟨hs, p, hp, hv⟩ := h
  refine ⟨p, hp, ?_⟩
  apply Array.ext (hs.trans (renamingArray_size _).symm)
  intro i hi hj
  have hin : i < n := by omega
  have hh := hv ⟨i, hin⟩
  rw [← renamingOf_lt p hin, ← renamingArray_get (renamingOf p) hin] at hh
  simpa only [getElem!_pos values i hi, getElem!_pos (renamingArray (renamingOf p)) i hj] using hh

/-- Native automorphism soundness supplies the shared row-checker contract
used in the pruning-pair mathematics. -/
theorem Automorphism.checked {G : GraphIso.Sparse.Colored n k} {values : Array Nat}
    (h : Automorphism G values) : checkAutom (Graph.context G.graph).g values = true := by
  obtain ⟨p, hp, rfl⟩ := h.array
  exact checkAutom_renaming (renamingOf p) (Graph.context_map G.graph G.graph p hp.adj_eq)

/-- Native colour preservation gives stabilization of the literal initial
ordered colour cells. -/
theorem Automorphism.colors {G : GraphIso.Sparse.Colored n k} {values : Array Nat}
    (h : Automorphism G values) (hn : 0 < n) : ColorStab G.toDense values := by
  obtain ⟨p, hp, rfl⟩ := h.array
  exact Generation.initial_stab ((GraphIso.Sparse.isIso_toDense G G p).mpr hp) hn

/-- Every retained pruning pair has checked, colour-preserving realizers
at the root partition. The bounded workspace may overwrite its last slot. -/
abbrev PairsOk (G : GraphIso.Sparse.Colored n k) (st : State n) : Prop :=
  Nauty.PairsOk G.toDense (Graph.context G.graph) st.frame

namespace PairsOk

variable {G : GraphIso.Sparse.Colored n k} {st out : State n}

theorem congr (h : PairsOk G st) (he : out.autos = st.autos) : PairsOk G out :=
  Nauty.PairsOk.congr h he

theorem push (h : PairsOk G st) {pair : VSet n × VSet n}
    (hp : PairOk (Graph.context G.graph).g
      (initPtn n (n + 2) (Nauty.initialPartition G.toDense).2)
      (Nauty.initialPartition G.toDense).1 1 pair.1 pair.2) :
    PairsOk G (pushAuto st pair) := by
  apply Nauty.PairsOk.congr (Nauty.PairsOk.push h hp)
  by_cases he : st.autos.size = st.wsCap <;> simp [pushAuto, State.frame, he]

/-- Both append and overwrite admission retain valid explicit pairs. -/
theorem admit (h : PairsOk G st) (hn : 0 < n) (ha : Automorphism G st.workperm) :
    PairsOk G (Nauty.admit st) := by
  have hr := Nauty.initial_nodeOk G.toDense hn
  exact (h.push (pairOk_fmperm hr.labOk hr.labSize hr.ptnSize hr.ptnEnd ha.checked (ha.colors hn))).congr
    (admit_autos st)

theorem prune (h : PairsOk G st) {level : Nat} (hb : CheapBoundary G level st)
    (hl : st.noncheaplevel ≤ level) : PairsOk G (pruneReturn level st).2 := by
  by_cases he : level ≠ st.noncheaplevel
  · apply (h.push (hb.ready hl he)).congr
    rw [pruneReturn_autos, ite_eq_left (bne_iff_ne.mpr he)]
    rfl
  · apply h.congr
    rw [pruneReturn_autos, ite_eq_right (by simpa using he)]

/-- Every shared leaf action preserves the native workspace once its
explicit automorphism or saved implicit boundary is justified. -/
theorem leaf (h : PairsOk G st) (hn : 0 < n) (leaf : Leaf) (level : Nat)
    (hb : CheapBoundary G level st) (hl : st.noncheaplevel ≤ level)
    (ha : leaf = .autoFirst ∨ leaf = .autoCanon → Automorphism G st.workperm) :
    PairsOk G (leafExit leaf level st).2 := by
  cases leaf
  all_goals first
    | exact h.congr (leafExit_autos ..)
    | exact (h.admit hn (ha (Or.inl rfl))).congr (leafExit_autos ..)
    | exact (h.admit hn (ha (Or.inr rfl))).congr (leafExit_autos ..)
    | exact (h.prune hb hl).congr (leafExit_autos ..)

theorem visit (h : PairsOk G st) (level numcells : Nat) :
    PairsOk G (Sparse.visit (.ofGraph G.graph) level numcells st).2.2 := h.congr rfl

theorem record (h : PairsOk G st) (level code : Nat) : PairsOk G (recordFirst level code st) := h.congr rfl

theorem compare (h : PairsOk G st) (level code : Nat) : PairsOk G (compareCodes level code st) := by
  apply h.congr
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.autos, ite_self]

theorem target (h : PairsOk G st) (first : Bool) (tcLevel level numcells : Nat) :
    PairsOk G (chooseTarget first (.ofGraph G.graph) tcLevel level numcells st).2.2.2 := by
  apply h.congr
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n => out.2.2.2.autos = st.autos)
  mvcgen
  all_goals simp_all +zetaDelta

theorem classify (h : PairsOk G st) (level numcells : Nat) :
    PairsOk G (Sparse.classify (.ofGraph G.graph) level numcells st).2 := by
  apply h.congr
  unfold Sparse.classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.autos, ite_self]

theorem cheap (h : PairsOk G st) (first : Bool) (level : Nat) : PairsOk G (cheapCheck first level st) := by
  unfold cheapCheck
  split <;> exact h.congr rfl

theorem child (h : PairsOk G st) (first : Bool) (level tc tv : Nat) :
    PairsOk G ((policy (n := n)).child first level tc tv st) := by
  cases first <;> exact h.congr rfl

theorem terminal (h : PairsOk G st) (level : Nat) : PairsOk G (firstterminal level st) := h.congr rfl

theorem afterChild (h : PairsOk G st) (level tv : Nat) : PairsOk G (afterChildFirst level tv st) := h.congr rfl

theorem leave (h : PairsOk G st) (tv : Nat) : PairsOk G ((policy (n := n)).leaveChild tv st) := h.congr rfl

theorem recover (h : PairsOk G st) (inf level : Nat) :
    PairsOk G ((policy (n := n)).recover inf level st) := by
  apply h.congr
  change (recoverLevels level (recoverPtn inf level st)).autos = st.autos
  unfold recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.autos, ite_self]

theorem afterSweep (h : PairsOk G st) (first : Bool) (level size index : Nat) :
    PairsOk G ((policy (n := n)).afterSweep first level size index st) := by
  change PairsOk G (if first then { (Nauty.afterSweep first level size index st) with
    order := (Nauty.afterSweep first level size index st).order * index }
    else Nauty.afterSweep first level size index st)
  cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals unfold Nauty.afterSweep; split <;> exact h.congr rfl

end PairsOk

/-- The native initialized pruning workspace is empty. -/
theorem initial_pairs (G : GraphIso.Sparse.Colored n k) (lab : Array Nat) (ends : List Nat) :
    PairsOk G (initial (.ofGraph G.graph) lab ends) := by
  intro pair hp
  change pair ∈ ([] : List (VSet n × VSet n)) at hp
  simp at hp

end Hex.GraphIso.Nauty.Sparse
