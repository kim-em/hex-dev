/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.CodeScope
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- A native call or sweep retains its frozen ancestor chain, recorded
code prefixes, incumbent growth and the actual cheap-boundary counters. -/
structure Scope (G : GraphIso.Sparse.Colored n k) (tcLevel : Nat) (f : Frame n)
    (bs : List Nat) (st : State n) (parents : Parents n) : Prop where
  codes : CodeScope G f.codes parents.frames
  complete : ∀ t, 1 ≤ t → t < f.level → ∃ p, parents t = some p
  valid : ∀ t p, parents t = some p →
    1 ≤ t ∧ t < f.level ∧ p.node.level = t ∧ p.Valid G tcLevel
  parent : 1 < f.level → ∃ p, parents (f.level - 1) = some p ∧ p.child G.graph tcLevel = f
  chain : ∀ t p, parents t = some p → 1 < t →
    ∃ prev, parents (t - 1) = some prev ∧ prev.child G.graph tcLevel = p.node
  grows : ∀ t p, parents t = some p → Grows (State.key G.graph p.bs p.state) (State.key G.graph bs st)
  boundary : ∀ t p, parents t = some p →
    st.noncheaplevel = p.state.noncheaplevel ∨ t + 1 ≤ st.noncheaplevel

theorem Scope.root (G : GraphIso.Sparse.Colored n k) (tcLevel : Nat)
    (numcells : Nat) (entry st : State n) (bs : List Nat) :
    Scope G tcLevel ⟨1, numcells, [], entry⟩ bs st (fun _ => none) := by
  constructor
  · exact CodeScope.root G
  · intro t ht hl
    change t < 1 at hl
    omega
  · intro t p hp; cases hp
  · intro h; change 1 < 1 at h; omega
  · intro t p hp; cases hp
  · intro t p hp; cases hp
  · intro t p hp; cases hp

/-- Native local work or a returned child can update the current state
without changing any suspended entry. The proved counter alternative
and incumbent growth suffice to retain all ancestor obligations. -/
theorem Scope.change {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {f : Frame n}
    {bs ds : List Nat} {st out : State n} {parents : Parents n}
    (h : Scope G tcLevel f bs st parents)
    (hg : Grows (State.key G.graph bs st) (State.key G.graph ds out))
    (hb : out.noncheaplevel = st.noncheaplevel ∨ f.level ≤ out.noncheaplevel) :
    Scope G tcLevel f ds out parents := by
  refine ⟨h.codes, h.complete, h.valid, h.parent, h.chain,
    fun t p hp => (h.grows t p hp).trans hg, ?_⟩
  intro t p hp
  have ht := (h.valid t p hp).2.1
  have hh := h.boundary t p hp
  rcases hb with he | he
  · rwa [he]
  · exact Or.inr (by omega)

/-- Suspending the current parent and individualizing its selected vertex
constructs the next node's entire ancestor scope. -/
theorem Scope.push {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {p : Parent n} {parents : Parents n}
    (h : Scope G tcLevel p.node p.bs p.state parents) (hp : p.Valid G tcLevel) :
    Scope G tcLevel (p.child G.graph tcLevel) p.bs (p.child G.graph tcLevel).entry (parents.push p) := by
  have hl := hp.node.positive
  have hkey : State.key G.graph p.bs (p.child G.graph tcLevel).entry = State.key G.graph p.bs p.state := by
    dsimp only [Parent.child]
    cases p.first <;> rfl
  have hb : (p.child G.graph tcLevel).entry.noncheaplevel = p.state.noncheaplevel := by
    dsimp only [Parent.child]
    cases p.first <;> rfl
  constructor
  · change CodeScope G (p.node.codes ++ [p.node.code G.graph]) (parents.push p).frames
    rw [Parents.push_frames hl]
    exact h.codes.push hp.node
  · intro t ht htl
    change t < p.node.level + 1 at htl
    by_cases he : t = p.node.level
    · exact ⟨p, by simp only [Parents.push, he, ↓reduceIte]⟩
    · obtain ⟨q, hq⟩ := h.complete t ht (by omega)
      exact ⟨q, by simpa only [Parents.push, ite_eq_right he] using hq⟩
  · intro t q hq
    by_cases he : t = p.node.level
    · simp only [Parents.push, he, ↓reduceIte, Option.some.injEq] at hq
      subst q
      exact ⟨by omega, by change t < p.node.level + 1; omega, he.symm, hp⟩
    · have hq' : parents t = some q := by simpa only [Parents.push, ite_eq_right he] using hq
      obtain ⟨ht, htl, hlevel, hv⟩ := h.valid t q hq'
      exact ⟨ht, by change t < p.node.level + 1; omega, hlevel, hv⟩
  · intro _
    refine ⟨p, ?_, rfl⟩
    change (parents.push p) (p.node.level + 1 - 1) = some p
    simp only [Nat.add_sub_cancel, Parents.push, ↓reduceIte]
  · intro t q hq ht
    by_cases he : t = p.node.level
    · simp only [Parents.push, he, ↓reduceIte, Option.some.injEq] at hq
      subst q
      obtain ⟨prev, hprev, hchild⟩ := h.parent (by omega)
      refine ⟨prev, ?_, hchild⟩
      simpa only [Parents.push, he, ite_eq_right (by omega : p.node.level - 1 ≠ p.node.level)] using hprev
    · have hq' : parents t = some q := by simpa only [Parents.push, ite_eq_right he] using hq
      obtain ⟨prev, hprev, hchild⟩ := h.chain t q hq' ht
      have htl := (h.valid t q hq').2.1
      refine ⟨prev, ?_, hchild⟩
      simpa only [Parents.push, ite_eq_right (by omega : t - 1 ≠ p.node.level)] using hprev
  · intro t q hq
    rw [hkey]
    by_cases he : t = p.node.level
    · simp only [Parents.push, he, ↓reduceIte, Option.some.injEq] at hq
      subst q
      exact Grows.refl _
    · apply h.grows t q
      simpa only [Parents.push, ite_eq_right he] using hq
  · intro t q hq
    rw [hb]
    by_cases he : t = p.node.level
    · simp only [Parents.push, he, ↓reduceIte, Option.some.injEq] at hq
      subst q
      exact Or.inl rfl
    · apply h.boundary t q
      simpa only [Parents.push, ite_eq_right he] using hq

end Hex.GraphIso.Nauty.Sparse.Max
