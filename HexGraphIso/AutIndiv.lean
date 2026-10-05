/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Autos
import all HexGraphIso.Autos
import all HexGraphIso.Colored
import all HexGraphIso.Iso

public section

namespace Hex.GraphIso.Aut

variable {n k : Nat} {G : Colored n k} {v : Fin n}

/-- Individualizing a vertex succeeds when its original colour cell
contains another vertex. -/
theorem indiv_exists (w : Fin n) (hne : w ≠ v)
    (hcolor : G.coloring.cells[w] = G.coloring.cells[v]) :
    ∃ H, indiv? G v = some H := by
  let colors := Hex.Vector.ofFn' fun u : Fin n =>
    if u = v then (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))
    else ⟨(G.coloring.cells[u]).val, Nat.lt_succ_of_lt (G.coloring.cells[u]).isLt⟩
  have honto : ∀ c : Fin (k + 1), ∃ u : Fin n, colors.get u = c := by
    intro c
    by_cases hc : c.val = k
    · refine ⟨v, ?_⟩
      apply Fin.ext
      simp only [colors, Hex.Vector.get_eq_getElem, Fin.getElem_fin, Hex.Vector.getElem_ofFn', ite_true]
      exact hc.symm
    · have hlt : c.val < k := by have := c.isLt; omega
      obtain ⟨u, hu⟩ := G.coloring.onto ⟨c.val, hlt⟩
      change G.coloring.cells[u] = ⟨c.val, hlt⟩ at hu
      by_cases he : u = v
      · subst u
        refine ⟨w, ?_⟩
        apply Fin.ext
        simp only [colors, Hex.Vector.get_eq_getElem, Fin.getElem_fin, Hex.Vector.getElem_ofFn', hne, ite_false]
        exact congrArg Fin.val (hcolor.trans hu)
      · refine ⟨u, ?_⟩
        apply Fin.ext
        simp only [colors, Hex.Vector.get_eq_getElem, Fin.getElem_fin, Hex.Vector.getElem_ofFn', he, ite_false]
        exact congrArg Fin.val hu
  unfold indiv? Coloring.ofVector?
  rw [dite_eq_left honto]
  exact ⟨_, rfl⟩

/-- The checked individualization keeps the graph and splits exactly the
selected vertex into a new final colour. -/
theorem indiv_fields {H : Colored n (k + 1)} (h : indiv? G v = some H) :
    H.graph = G.graph ∧ ∀ u, (H.coloring.cells[u]).val =
      if u = v then k else (G.coloring.cells[u]).val := by
  unfold indiv? Coloring.ofVector? at h
  split at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst H
    exact ⟨rfl, fun u => by simp only [Fin.getElem_fin, Hex.Vector.getElem_ofFn']; split <;> rfl⟩
  · simp at h

/-- Automorphisms after individualization are exactly the automorphisms
of the original graph that fix the selected vertex. -/
theorem indiv_isIso {H : Colored n (k + 1)} (h : indiv? G v = some H) (p : Perm n) :
    IsIso H H p ↔ IsIso G G p ∧ p.get v = v := by
  obtain ⟨hgraph, hcolors⟩ := indiv_fields h
  have hfix : IsIso H H p → p.get v = v := by
    intro hp
    have hc := congrArg Fin.val (hp.1 v)
    rw [hcolors, hcolors, ite_eq_left rfl] at hc
    by_cases he : p.get v = v
    · exact he
    · rw [ite_eq_right he] at hc
      have := (G.coloring.cells[p.get v]).isLt
      omega
  constructor
  · intro hp
    have hv := hfix hp
    refine ⟨⟨?_, ?_⟩, hv⟩
    · intro u
      by_cases he : u = v
      · subst u
        exact congrArg G.coloring.cells.get hv
      · have hpu : p.get u ≠ v := fun hpu => he (p.get_inj (hpu.trans hv.symm))
        apply Fin.ext
        have hc := congrArg Fin.val (hp.1 u)
        simpa only [hcolors, ite_eq_right he, ite_eq_right hpu] using hc
    · simpa only [hgraph] using hp.2
  · rintro ⟨hp, hv⟩
    constructor
    · intro u
      apply Fin.ext
      rw [hcolors, hcolors]
      by_cases he : u = v
      · subst u
        rw [hv]
      · have hpu : p.get u ≠ v := fun hpu => he (p.get_inj (hpu.trans hv.symm))
        rw [ite_eq_right he, ite_eq_right hpu, hp.1 u]
    · simpa only [hgraph] using hp.2

end Hex.GraphIso.Aut
