/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxContext
public import HexGraphIso.Nauty.Policy.MaxSuspend
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.MaxSuspend
import all HexGraphIso.Nauty.Policy.FirstBoundary
import all HexGraphIso.Nauty.Policy.FirstPath
import all HexGraphIso.Nauty.Policy.FirstEntry
import all HexGraphIso.Nauty.Policy.Orbits
import all HexGraphIso.Nauty.Invariant.Orbits
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Before any generator is admitted, sound orbit pointers are identities. -/
theorem empty_orbits {st : Search n} (h : OrbitsOk st) (he : st.genTrace = #[]) :
    ∀ v, v < n → st.orbits[v]! = v := by
  intro v hv
  obtain ⟨_, _, w, hw, happ⟩ := (h.2 v hv).2
  cases w with
  | nil => exact happ.symm
  | cons a w =>
    have hm := hw a (List.mem_cons_self ..)
    simp only [he, Array.toList_empty, List.not_mem_nil] at hm

/-- An actual call retains its entry boundary or replaces it by a boundary
at least as deep as the call, including on the initial descent. -/
theorem NodeInput.boundary {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {first : Bool} {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel first f bs fs parents) :
    let out := (node first ctx (n + 2) tcLevel fuel f.level f.numcells f.entry).2
    out.noncheaplevel = f.entry.noncheaplevel ∨ f.level ≤ out.noncheaplevel := by
  cases first with
  | false => exact node_boundary h.frame.positive
  | true =>
    obtain ⟨hp, _, _, _, ht, _⟩ := h.entry
    have hn0 : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
    obtain ⟨last, leaf, path⟩ := firstPath_exists (ctx := ctx) (tcLevel := tcLevel)
      hn0 h.frame.positive h.frame.partition (empty_orbits hp.orbits ht) h.fuel
    exact firstPath_boundary path h.frame.positive

/-- Every captured ancestor retains its cheap-boundary alternative after
the actual node call. No maximum or leaf-coverage premise is required. -/
theorem NodeInput.boundaries {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {first : Bool} {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel first f bs fs parents) :
    let out := (node first ctx (n + 2) tcLevel fuel f.level f.numcells f.entry).2
    ∀ t p, parents t = some p →
      out.noncheaplevel = p.state.noncheaplevel ∨ t + 1 ≤ out.noncheaplevel := by
  intro out t p hp
  have ha := h.scope.boundary t p hp
  have hl := (h.scope.valid t p hp).2.1
  have hb : out.noncheaplevel = f.entry.noncheaplevel ∨ f.level ≤ out.noncheaplevel := h.boundary
  rcases hb with hb | hb
  · rwa [hb]
  · exact Or.inr (by omega)

/-- Suspending a parent initializes its boundary equality; the actual
individualization preserves every older ancestor's boundary alternative. -/
theorem SweepInput.child_boundaries {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n} {st : Search n}
    {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents) :
    let p : Parent n := ⟨l, st, tv, bs, fs⟩
    let ch := (p.child ctx tcLevel).entry
    ∀ t q, (parents.push p) t = some q →
      ch.noncheaplevel = q.state.noncheaplevel ∨ t + 1 ≤ ch.noncheaplevel := by
  intro p ch t q hq
  have hc : ch.noncheaplevel = st.noncheaplevel := by
    dsimp only [ch, p, Parent.child]
    cases hf : l.first <;> rfl
  dsimp only [Parents.push] at hq
  split at hq
  · cases hq
    exact Or.inl hc
  · rw [hc]
    exact h.scope.boundary t q hq

/-- Clamping at a resumed sweep preserves the alternative at every
strictly older saved parent, even if the child created a deeper boundary. -/
theorem NodeInput.recovered_boundaries {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level : Nat} {first : Bool} {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel first f bs fs parents) :
    let out := (node first ctx (n + 2) tcLevel fuel f.level f.numcells f.entry).2
    let ready := recoverLevels level (recoverPtn (n + 2) level out)
    ∀ t p, parents t = some p → t < level →
      ready.noncheaplevel = p.state.noncheaplevel ∨ t + 1 ≤ ready.noncheaplevel := by
  intro out ready t p hp ht
  have hb : out.noncheaplevel = p.state.noncheaplevel ∨ t + 1 ≤ out.noncheaplevel := h.boundaries t p hp
  dsimp only [ready]
  rw [recover_noncheap]
  split
  · exact Or.inr (by omega)
  · exact hb

end Hex.GraphIso.Nauty.Max
