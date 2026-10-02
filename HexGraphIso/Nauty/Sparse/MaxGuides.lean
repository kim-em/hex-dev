/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxScatter
public import HexGraphIso.Nauty.Sparse.MaxScope
public import HexGraphIso.Nauty.Sparse.CanonGuide
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- A suspended parent retains coverage of references pointing to its
own sweep. These are previously completed child keys, in its actual
ordering at suspension. -/
structure Parent.Guided (G : Hex.SparseGraph n) (tcLevel : Nat) (p : Parent n) : Prop where
  canonical : CanonGuide p.node.level p.tc p.state (p.key G tcLevel) (State.key G p.bs p.state) p.state
  first : p.state.gcaFirst = p.node.level →
    Covers (p.key G tcLevel p.state.firstlab[p.tc]!) (State.key G p.bs p.state) ∧
      cellsPerm p.state.ptn p.node.level p.state.lab p.state.firstlab

theorem Parent.Guided.vacuous {G : Hex.SparseGraph n} {tcLevel : Nat} {p : Parent n}
    (hf : p.state.gcaFirst < p.node.level) (hc : p.state.gcaCanon < p.node.level) :
    p.Guided G tcLevel := by
  refine ⟨CanonGuide.vacuous hc, ?_⟩
  intro he
  omega

/-- A reference still pointing to a suspended ancestor is literally the
reference retained there. Covered-reference data is stored at suspension;
incumbent growth is supplied separately by the established native scope. -/
structure Guides (G : Hex.SparseGraph n) (tcLevel : Nat) (st : State n) (parents : Parents n) : Prop where
  saved : ∀ t p, parents t = some p → p.Guided G tcLevel
  first : ∀ t p, parents t = some p → st.gcaFirst ≤ t →
    st.gcaFirst = p.state.gcaFirst ∧ st.firstlab = p.state.firstlab
  canonical : ∀ t p, parents t = some p → st.gcaCanon ≤ t →
    st.gcaCanon = p.state.gcaCanon ∧ st.canonlab = p.state.canonlab

theorem Guides.root (G : Hex.SparseGraph n) (tcLevel : Nat) (st : State n) :
    Guides G tcLevel st (fun _ => none) := by
  constructor <;> intro t p hp <;> cases hp

/-- Native local operations preserving the reference labels and their
ancestor counters retain all covered-reference associations. -/
theorem Guides.fields {G : Hex.SparseGraph n} {tcLevel : Nat} {st out : State n} {parents : Parents n}
    (h : Guides G tcLevel st parents)
    (hf : out.firstlab = st.firstlab) (hg : out.gcaFirst = st.gcaFirst)
    (hc : out.canonlab = st.canonlab) (ha : out.gcaCanon = st.gcaCanon) :
    Guides G tcLevel out parents := by
  refine ⟨h.saved, ?_, ?_⟩
  · intro t p hp ht
    rw [hg] at ht ⊢
    rw [hf]
    exact h.first t p hp ht
  · intro t p hp ht
    rw [ha] at ht ⊢
    rw [hc]
    exact h.canonical t p hp ht

/-- Suspending a covered parent and performing the actual sparse child
operation extends the reference associations. Cache invalidation and
first-path coset bookkeeping do not change either reference. -/
theorem Guides.child {G : Hex.SparseGraph n} {tcLevel : Nat} {p : Parent n} {parents : Parents n}
    (h : Guides G tcLevel p.state parents) (hp : p.Guided G tcLevel) :
    Guides G tcLevel (p.child G tcLevel).entry (parents.push p) := by
  have hf : (p.child G tcLevel).entry.firstlab = p.state.firstlab := by
    dsimp only [Parent.child]; cases p.first <;> rfl
  have hg : (p.child G tcLevel).entry.gcaFirst = p.state.gcaFirst := by
    dsimp only [Parent.child]; cases p.first <;> rfl
  have hc : (p.child G tcLevel).entry.canonlab = p.state.canonlab := by
    dsimp only [Parent.child]; cases p.first <;> rfl
  have ha : (p.child G tcLevel).entry.gcaCanon = p.state.gcaCanon := by
    dsimp only [Parent.child]; cases p.first <;> rfl
  constructor
  · intro t q hq
    simp only [Parents.push] at hq
    split at hq
    · cases hq; exact hp
    · exact h.saved t q hq
  · intro t q hq ht
    rw [hg] at ht ⊢
    rw [hf]
    simp only [Parents.push] at hq
    split at hq
    · cases hq; exact ⟨rfl, rfl⟩
    · exact h.first t q hq ht
  · intro t q hq ht
    rw [ha] at ht ⊢
    rw [hc]
    simp only [Parents.push] at hq
    split at hq
    · cases hq; exact ⟨rfl, rfl⟩
    · exact h.canonical t q hq ht

/-- A return retains earlier references whenever its counters still name
them. A first-child update points to the current level and therefore cannot
be mistaken for a reference belonging to an older suspended parent. -/
theorem Guides.change {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs : List Nat} {st out : State n} {parents : Parents n}
    (h : Guides G.graph tcLevel st parents) (hs : Scope G tcLevel f bs st parents)
    (hf : (out.gcaFirst = st.gcaFirst ∧ out.firstlab = st.firstlab) ∨ f.level ≤ out.gcaFirst)
    (hc : out.gcaCanon < f.level → out.gcaCanon = st.gcaCanon ∧ out.canonlab = st.canonlab) :
    Guides G.graph tcLevel out parents := by
  refine ⟨h.saved, ?_, ?_⟩
  · intro t p hp ht
    have hlevel := (hs.valid t p hp).2.1
    rcases hf with ⟨he, hl⟩ | he
    · have hh := h.first t p hp (by omega)
      exact ⟨he.trans hh.1, hl.trans hh.2⟩
    · omega
  · intro t p hp ht
    have hlevel := (hs.valid t p hp).2.1
    obtain ⟨he, hl⟩ := hc (by omega)
    have hh := h.canonical t p hp (by omega)
    exact ⟨he.trans hh.1, hl.trans hh.2⟩

end Hex.GraphIso.Nauty.Sparse.Max
