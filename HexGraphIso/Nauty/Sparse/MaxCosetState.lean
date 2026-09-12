/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxControl
public import HexGraphIso.Nauty.Sparse.Coset
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.MaxFirstResume
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- An active first ancestor identifies its suspended selected vertex
with the coset index used by native early-return bookkeeping. -/
def Cosets (st : State n) (parents : Parents n) : Prop :=
  ∀ t p, parents t = some p → st.gcaFirst = t → p.first = true ∧ st.cosetindex = p.chosen

theorem Cosets.root (st : State n) : Cosets st (fun _ => none) := by
  intro t p hp
  cases hp

theorem Cosets.fields {st out : State n} {parents : Parents n} (h : Cosets st parents)
    (hf : out.gcaFirst = st.gcaFirst) (hc : out.cosetindex = st.cosetindex) : Cosets out parents := by
  intro t p hp ht
  rw [hf] at ht
  obtain ⟨hfirst, hindex⟩ := h t p hp ht
  exact ⟨hfirst, hc.trans hindex⟩

theorem Frame.firstParent_coset (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n)
    (bs : List Nat) (tv : Nat) :
    (f.firstParent G tcLevel bs tv).state.cosetindex = f.entry.cosetindex := by
  let v := visit (.ofGraph G) f.level f.numcells f.entry
  dsimp only [Frame.firstParent]
  unfold cheapCheck
  split <;> exact chooseTarget_coset true (.ofGraph G) tcLevel f.level v.1
    (recordFirst f.level v.2.1 v.2.2)

theorem Frame.otherParent_coset (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n)
    (bs : List Nat) (tv : Nat) :
    (f.otherParent G tcLevel bs tv).state.cosetindex = f.entry.cosetindex := by
  let v := visit (.ofGraph G) f.level f.numcells f.entry
  dsimp only [Frame.otherParent]
  unfold cheapCheck
  split <;> exact (chooseTarget_coset false (.ofGraph G) tcLevel f.level v.1
    (compareCodes f.level v.2.1 v.2.2)).trans (compare_coset f.level v.2.1 v.2.2)

theorem Cosets.first_prepare {G : Hex.SparseGraph n} {tcLevel : Nat} {f : Frame n}
    {parents : Parents n} (h : Cosets f.entry parents) (bs : List Nat) (tv : Nat) :
    Cosets (f.firstParent G tcLevel bs tv).state parents :=
  h.fields (f.firstParent_refs G tcLevel bs tv).2.1 (f.firstParent_coset G tcLevel bs tv)

theorem Cosets.other_prepare {G : Hex.SparseGraph n} {tcLevel : Nat} {f : Frame n}
    {parents : Parents n} (h : Cosets f.entry parents) (bs : List Nat) (tv : Nat) :
    Cosets (f.otherParent G tcLevel bs tv).state parents :=
  h.fields (f.otherParent_refs G tcLevel bs tv).2.1 (f.otherParent_coset G tcLevel bs tv)

/-- First sweeps overwrite the selected index for their new child;
ordinary sweeps retain the older first ancestor's index. Before the
first leaf, counter zero names no suspended parent. -/
theorem Cosets.child {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {p : Parent n} {parents : Parents n} (h : Cosets p.state parents)
    (hs : Scope G tcLevel p.node p.bs p.state parents)
    (hfirst : p.first = true → p.state.gcaFirst = 0 ∨ p.state.gcaFirst = p.node.level)
    (hother : p.first = false → p.state.gcaFirst < p.node.level) :
    Cosets (p.child G.graph tcLevel).entry (parents.push p) := by
  let ch := p.child G.graph tcLevel
  have hgc : ch.entry.gcaFirst = p.state.gcaFirst := by
    dsimp only [ch, Parent.child]; cases p.first <;> rfl
  have hci : ch.entry.cosetindex = if p.first then p.chosen else p.state.cosetindex := by
    dsimp only [ch, Parent.child]; cases p.first <;> rfl
  intro t q hq ht
  change ch.entry.gcaFirst = t at ht
  rw [hgc] at ht
  by_cases he : t = p.node.level
  · simp only [Parents.push, ite_eq_left he] at hq
    cases hq
    have hf : p.first = true := by
      cases hf : p.first with
      | true => rfl
      | false => have := hother hf; omega
    refine ⟨hf, ?_⟩
    change ch.entry.cosetindex = p.chosen
    rw [hci, hf]
    rfl
  · simp only [Parents.push, ite_eq_right he] at hq
    cases hf : p.first with
    | true =>
      have hp := hs.valid t q hq
      rcases hfirst hf with hz | hl <;> omega
    | false =>
      obtain ⟨hfirst, hindex⟩ := h t q hq ht
      refine ⟨hfirst, ?_⟩
      change ch.entry.cosetindex = q.chosen
      rw [hci, hf]
      exact hindex

theorem Cosets.node {g : Graph n} {inf tcLevel fuel level numcells : Nat}
    {st : State n} {parents : Parents n} (h : Cosets st parents) :
    Cosets (Generic.node false g inf tcLevel fuel level numcells st).2 parents :=
  h.fields (node_gca ..) (node_coset ..)

/-- Returning an off-path child and recovering its parent retains all
older coset associations. The just-completed child is removed from the
suspended-parent map. -/
theorem Cosets.back {G : GraphIso.Sparse.Colored n k} {tcLevel fuel : Nat}
    {p : Parent n} {parents : Parents n}
    (h : Cosets (p.child G.graph tcLevel).entry (parents.push p))
    (hs : Scope G tcLevel p.node p.bs p.state parents) :
    Cosets (p.back G.graph tcLevel fuel) parents := by
  let ch := p.child G.graph tcLevel
  let raw := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
  let left := (policy (n := n)).leaveChild p.chosen raw
  have hn : Cosets raw (parents.push p) := h.node
  have hout : Cosets (p.back G.graph tcLevel fuel) (parents.push p) := hn.fields
    ((gcaPolicy (.ofGraph G.graph) (n + 2) tcLevel).recover p.node.level left)
    (recover_coset (n + 2) p.node.level left)
  intro t q hq ht
  apply hout t q _ ht
  have hb := (hs.valid t q hq).2.1
  simp only [Parents.push, ite_eq_right (by omega : t ≠ p.node.level)]
  exact hq

/-- First-child recovery names the receiving parent, so none of its
strictly older suspended parents can be mistaken for that first ancestor. -/
theorem Cosets.first_back {G : GraphIso.Sparse.Colored n k} {tcLevel fuel last : Nat}
    {p : Parent n} {parents : Parents n} {leaf : State n}
    (hs : Scope G tcLevel p.node p.bs p.state parents)
    (path : let ch := p.child G.graph tcLevel
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel ch.level ch.numcells ch.entry last leaf) :
    Cosets (p.firstBack G.graph tcLevel fuel) parents := by
  intro t q hq ht
  have hg := (p.firstBack_counters path).1
  have hb := (hs.valid t q hq).2.1
  omega

end Hex.GraphIso.Nauty.Sparse.Max
