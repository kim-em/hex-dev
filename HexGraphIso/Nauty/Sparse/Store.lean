/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ClassifyStore
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The incumbent parses as a label and the allocated raw rows represent
exactly its installed prefix. Unfilled capacity is not a complete graph. -/
@[expose] def Store (G : Hex.SparseGraph n) (st : State n) : Prop :=
  ∃ l, Label.ofArray? n st.canonlab = some l ∧ st.canong.toRows.Prefix (G.relabel l.perm) st.samerows

/-- A candidate prefix justified by the actual comparison, ready for the
shared better-leaf installation. -/
@[expose] def Candidate (G : Hex.SparseGraph n) (st : State n) (same : Nat) : Prop :=
  ∃ l, Label.ofArray? n st.lab = some l ∧ st.canong.toRows.Prefix (G.relabel l.perm) same

namespace Store

variable {G : Hex.SparseGraph n} {st out : State n}

theorem congr (h : Store G st) (hr : out.canong.toRows = st.canong.toRows)
    (hc : out.canonlab = st.canonlab) (hs : out.samerows = st.samerows) : Store G out := by
  simpa only [Store, hr, hc, hs] using h

theorem visit (h : Store G st) (level numcells : Nat) :
    Store G (Sparse.visit (.ofGraph G) level numcells st).2.2 := h.congr rfl rfl rfl

theorem record (h : Store G st) (level code : Nat) : Store G (recordFirst level code st) :=
  h.congr rfl rfl rfl

theorem compare (h : Store G st) (level code : Nat) : Store G (compareCodes level code st) := by
  apply h.congr
  all_goals unfold compareCodes
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.canong,
    apply_ite SearchState.canonlab, apply_ite SearchState.samerows, ite_self]

theorem cheap (h : Store G st) (first : Bool) (level : Nat) : Store G (cheapCheck first level st) := by
  unfold cheapCheck
  split <;> exact h.congr rfl rfl rfl

theorem child (h : Store G st) (first : Bool) (level tc tv : Nat) :
    Store G ((policy (n := n)).child first level tc tv st) := by
  cases first <;> exact h.congr rfl rfl rfl

theorem afterChild (h : Store G st) (level tv : Nat) : Store G (afterChildFirst level tv st) :=
  h.congr rfl rfl rfl

theorem leave (h : Store G st) (tv : Nat) : Store G { st with fixedpts := st.fixedpts.erase tv } :=
  h.congr rfl rfl rfl

theorem afterSweep (h : Store G st) (first : Bool) (level size index : Nat) :
    Store G ((policy (n := n)).afterSweep first level size index st) := by
  change Store G (if first then { (Nauty.afterSweep first level size index st) with
    order := (Nauty.afterSweep first level size index st).order * index }
    else Nauty.afterSweep first level size index st)
  cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals unfold Nauty.afterSweep; split <;> exact h.congr rfl rfl rfl

theorem terminal (h : Store G st) (level : Nat) (l : Label n)
    (hl : Label.ofArray? n st.lab = some l) : Store G (firstterminal level st) := by
  obtain ⟨c, _, hc⟩ := h
  refine ⟨l, ?_, ?_⟩
  · unfold firstterminal
    exact hl
  · unfold firstterminal
    exact hc.relabel_zero

theorem finish (h : Store G st) : Store G (Sparse.finish (.ofGraph G) st) := by
  obtain ⟨l, hl, hp⟩ := h
  exact ⟨l, hl, updatecan_relabel G _ _ l _ hl hp⟩

/-- Classification preserves the old incumbent and prepares a parsed,
semantically valid candidate prefix for every better-leaf verdict. -/
theorem classify (h : Store G st) (level numcells : Nat) (l : Label n)
    (hl : Label.ofArray? n st.lab = some l) :
    let r := Sparse.classify (.ofGraph G) level numcells st
    Store G r.2 ∧ ∀ sr, r.1 = .better sr → Candidate G r.2 sr := by
  obtain ⟨c, hc, hp⟩ := h
  obtain ⟨hstore, hnew⟩ := classify_prefix G level numcells st l c hl hc hp
  obtain ⟨hlab, _, _, hcanon⟩ := classify_frame (.ofGraph G) level numcells st
  refine ⟨⟨c, ?_, hstore⟩, ?_⟩
  · rwa [hcanon]
  · intro sr he
    exact ⟨l, by rwa [hlab], hnew sr he⟩

end Store
end Hex.GraphIso.Nauty.Sparse
