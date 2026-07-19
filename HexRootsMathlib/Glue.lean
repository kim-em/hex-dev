/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Bisection

public section

/-!
# Structural contract for square-component gluing

The executable union-by-insertion algorithm preserves the input multiset
exactly.  Consequently its guarded wrapper always takes the normal branch;
on duplicate-free inputs its output components are internally duplicate-free
and pairwise disjoint.
-/

namespace HexRootsMathlib

namespace Glue

/-- The exact edge relation used by the executable gluer. -/
@[expose] def Edge (s t : Hex.DyadicSquare) : Prop :=
  Hex.DyadicSquare.adjacent s t = true

/-- Undirected executable edge adjacency. -/
@[expose] def Linked (s t : Hex.DyadicSquare) : Prop := Edge s t ∨ Edge t s

theorem linked_symm {s t : Hex.DyadicSquare} : Linked s t → Linked t s := Or.symm

/-- Every predicate invariant across internal adjacency edges is constant on
the component. This induced-graph formulation records that paths stay inside
the component, which is exactly what downstream semantic propagation needs. -/
@[expose] def Connected (component : List Hex.DyadicSquare) : Prop :=
  component ≠ [] ∧
    ∀ P : Hex.DyadicSquare → Prop,
      (∀ s ∈ component, ∀ t ∈ component, Linked s t → (P s ↔ P t)) →
      ∀ s ∈ component, ∀ t ∈ component, P s ↔ P t

/-- Distinct components have no executable adjacency edge in either
direction. Together with coverage and connectedness this is maximality. -/
@[expose] def Separated (components : List (List Hex.DyadicSquare)) : Prop :=
  ∀ c ∈ components, ∀ d ∈ components, c ≠ d →
    ∀ s ∈ c, ∀ t ∈ d, ¬Edge s t ∧ ¬Edge t s

theorem touches_iff {s : Hex.DyadicSquare} {component : List Hex.DyadicSquare} :
    s.touches component = true ↔ ∃ t ∈ component, Linked s t := by
  simp [Hex.DyadicSquare.touches, Linked, Edge]

theorem not_touches_iff {s : Hex.DyadicSquare}
    {component : List Hex.DyadicSquare} :
    s.touches component = false ↔
      ∀ t ∈ component, ¬Edge s t ∧ ¬Edge t s := by
  rw [← Bool.not_eq_true]
  simp only [touches_iff, Linked, not_exists, not_and, not_or]

private theorem invariant_inserted {s x : Hex.DyadicSquare}
    {components : List (List Hex.DyadicSquare)}
    (hconnected : ∀ c ∈ components, Connected c)
    {P : Hex.DyadicSquare → Prop}
    (hinvariant : ∀ a ∈ s :: (components.filter s.touches).flatten,
      ∀ b ∈ s :: (components.filter s.touches).flatten,
        Linked a b → (P a ↔ P b))
    (hx : x ∈ s :: (components.filter s.touches).flatten) : P x ↔ P s := by
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact Iff.rfl
  · rw [List.mem_flatten] at hx
    obtain ⟨c, hc, hxc⟩ := hx
    have hcmem : c ∈ components := (List.mem_filter.mp hc).1
    have htouch : s.touches c = true := (List.mem_filter.mp hc).2
    obtain ⟨w, hwc, hsw⟩ := touches_iff.mp htouch
    have hcsub : ∀ u ∈ c,
        u ∈ s :: (components.filter s.touches).flatten := by
      intro u hu
      exact List.mem_cons_of_mem s (List.mem_flatten.mpr ⟨c, hc, hu⟩)
    have hxw := (hconnected c hcmem).2 P
      (fun a ha b hb hab => hinvariant a (hcsub a ha) b (hcsub b hb) hab)
      x hxc w hwc
    exact hxw.trans (hinvariant w (hcsub w hwc) s (by simp) (linked_symm hsw))

/-- Inserting a square preserves connectedness of every component. -/
theorem connected_glueInsert {s : Hex.DyadicSquare}
    {components : List (List Hex.DyadicSquare)}
    (hconnected : ∀ c ∈ components, Connected c) :
    ∀ c ∈ Hex.glueInsert s components, Connected c := by
  intro c hc
  simp only [Hex.glueInsert, List.partition_eq_filter_filter,
    List.mem_cons] at hc
  rcases hc with rfl | hc
  · constructor
    · simp
    · intro P hinvariant x hx y hy
      exact (invariant_inserted hconnected hinvariant hx).trans
        (invariant_inserted hconnected hinvariant hy).symm
  · have hc' : c ∈ components := (List.mem_filter.mp hc).1
    refine ⟨(hconnected c hc').1, ?_⟩
    intro P hinvariant x hx y hy
    exact (hconnected c hc').2 P hinvariant x hx y hy

/-- Every component returned by `glueList` is edge-connected. -/
theorem connected_glueList (squares : List Hex.DyadicSquare) :
    ∀ c ∈ Hex.glueList squares, Connected c := by
  induction squares with
  | nil => simp [Hex.glueList]
  | cons s squares ih =>
      simpa only [Hex.glueList] using connected_glueInsert ih

private theorem noEdge_inserted_separate {s x y : Hex.DyadicSquare}
    {components : List (List Hex.DyadicSquare)}
    (hseparated : Separated components)
    {d : List Hex.DyadicSquare}
    (hd : d ∈ components.filter (!s.touches ·))
    (hx : x ∈ s :: (components.filter s.touches).flatten)
    (hy : y ∈ d) : ¬Edge x y ∧ ¬Edge y x := by
  have hdmem : d ∈ components := (List.mem_filter.mp hd).1
  have hdnot : s.touches d = false := by
    have := (List.mem_filter.mp hd).2
    simpa using this
  have hsd := not_touches_iff.mp hdnot y hy
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact hsd
  · rw [List.mem_flatten] at hx
    obtain ⟨c, hc, hxc⟩ := hx
    have hcmem : c ∈ components := (List.mem_filter.mp hc).1
    have hctouch : s.touches c = true := (List.mem_filter.mp hc).2
    have hcd : c ≠ d := by
      intro h
      subst c
      simp [hdnot] at hctouch
    exact hseparated c hcmem d hdmem hcd x hxc y hy

/-- Inserting a square preserves the absence of cross-component edges. -/
theorem separated_glueInsert {s : Hex.DyadicSquare}
    {components : List (List Hex.DyadicSquare)}
    (hseparated : Separated components) :
    Separated (Hex.glueInsert s components) := by
  intro c hc d hd hcd x hxc y hyd
  simp only [Hex.glueInsert, List.partition_eq_filter_filter,
    List.mem_cons] at hc hd
  rcases hc with rfl | hc
  · rcases hd with rfl | hd
    · exact (hcd rfl).elim
    · exact noEdge_inserted_separate hseparated hd hxc hyd
  · rcases hd with rfl | hd
    · have h := noEdge_inserted_separate hseparated hc hyd hxc
      exact ⟨h.2, h.1⟩
    · have hcmem : c ∈ components := (List.mem_filter.mp hc).1
      have hdmem : d ∈ components := (List.mem_filter.mp hd).1
      exact hseparated c hcmem d hdmem hcd x hxc y hyd

/-- Distinct components returned by `glueList` have no edge between them. -/
theorem separated_glueList (squares : List Hex.DyadicSquare) :
    Separated (Hex.glueList squares) := by
  induction squares with
  | nil => simp [Hex.glueList, Separated]
  | cons s squares ih =>
      simpa only [Hex.glueList] using separated_glueInsert ih

end Glue

/-- Inserting one square into a partial component partition preserves the
flattened multiset, up to order. -/
theorem flatten_glueInsert_perm (s : Hex.DyadicSquare)
    (components : List (List Hex.DyadicSquare)) :
    (Hex.glueInsert s components).flatten.Perm (s :: components.flatten) := by
  let touches := s.touches
  have hpartition := List.filter_append_perm touches components
  have hflatten := hpartition.flatten
  simpa [Hex.glueInsert, touches, Function.comp_def] using hflatten.cons s

/-- `glueList` is a partition of the input list at the multiset level. -/
theorem flatten_glueList_perm (squares : List Hex.DyadicSquare) :
    (Hex.glueList squares).flatten.Perm squares := by
  induction squares with
  | nil => simp [Hex.glueList]
  | cons s squares ih =>
      exact (flatten_glueInsert_perm s (Hex.glueList squares)).trans
        (ih.cons s)

/-- The executable array gluer preserves its input multiset exactly. -/
theorem flatten_glue_perm (squares : Array Hex.DyadicSquare) :
    ((Hex.glue squares).toList.map Array.toList).flatten.Perm squares.toList := by
  have hmap : (Hex.glueList squares.toList).map
      (Array.toList ∘ List.toArray) = Hex.glueList squares.toList := by
    induction Hex.glueList squares.toList with
    | nil => rfl
    | cons l ls ih => simp [Function.comp_def]
  rw [Hex.glue, List.map_map, hmap]
  exact flatten_glueList_perm squares.toList

/-- Every input square occurs in an output component of `glue`. -/
theorem mem_glue {squares : Array Hex.DyadicSquare} {s : Hex.DyadicSquare}
    (hs : s ∈ squares.toList) :
    ∃ c ∈ (Hex.glue squares).toList, s ∈ c.toList := by
  have hs' : s ∈ ((Hex.glue squares).toList.map Array.toList).flatten :=
    (flatten_glue_perm squares).mem_iff.mpr hs
  rw [List.mem_flatten] at hs'
  obtain ⟨l, hl, hsl⟩ := hs'
  rw [List.mem_map] at hl
  obtain ⟨c, hc, rfl⟩ := hl
  exact ⟨c, hc, hsl⟩

/-- The defensive branch of `glueCovered` is unreachable: the structurally
recursive gluer already preserves every input member. -/
theorem glueCovered_eq_glue (squares : Array Hex.DyadicSquare) :
    Hex.glueCovered squares = Hex.glue squares := by
  rw [Hex.glueCovered]
  split
  · rfl
  · rename_i h
    exfalso
    apply h
    intro s hs
    exact mem_glue hs

/-- The guarded gluer preserves the input multiset exactly. -/
theorem flatten_glueCovered_perm (squares : Array Hex.DyadicSquare) :
    ((Hex.glueCovered squares).toList.map Array.toList).flatten.Perm squares.toList := by
  rw [glueCovered_eq_glue]
  exact flatten_glue_perm squares

/-- Every member of an output component came from the input array. -/
theorem mem_of_mem_glueCovered {squares : Array Hex.DyadicSquare}
    {component : Array Hex.DyadicSquare} {s : Hex.DyadicSquare}
    (hc : component ∈ (Hex.glueCovered squares).toList)
    (hs : s ∈ component.toList) : s ∈ squares.toList := by
  apply (flatten_glueCovered_perm squares).mem_iff.mp
  rw [List.mem_flatten]
  exact ⟨component.toList, List.mem_map.mpr ⟨component, hc, rfl⟩, hs⟩

/-- Duplicate-free input gives duplicate-free, pairwise-disjoint output
components. -/
theorem glueCovered_nodup_disjoint {squares : Array Hex.DyadicSquare}
    (h : squares.toList.Nodup) :
    (∀ c ∈ (Hex.glueCovered squares).toList, c.toList.Nodup) ∧
      (Hex.glueCovered squares).toList.Pairwise
        (fun c d => List.Disjoint c.toList d.toList) := by
  have hout : ((Hex.glueCovered squares).toList.map Array.toList).flatten.Nodup :=
    (flatten_glueCovered_perm squares).nodup_iff.mpr h
  rw [List.nodup_flatten] at hout
  constructor
  · intro c hc
    apply hout.1 c.toList
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  · exact List.pairwise_map.mp hout.2

/-- Every guarded output component is edge-connected. -/
theorem glueCovered_connected (squares : Array Hex.DyadicSquare) :
    ∀ c ∈ (Hex.glueCovered squares).toList, Glue.Connected c.toList := by
  rw [glueCovered_eq_glue, Hex.glue]
  intro c hc
  change c ∈ (Hex.glueList squares.toList).map List.toArray at hc
  rw [List.mem_map] at hc
  obtain ⟨l, hl, rfl⟩ := hc
  simpa using Glue.connected_glueList squares.toList l hl

/-- Distinct guarded output components have no adjacency edge between any
pair of their members, the maximality half of the gluing contract. -/
theorem glueCovered_separated (squares : Array Hex.DyadicSquare) :
    ∀ c ∈ (Hex.glueCovered squares).toList,
      ∀ d ∈ (Hex.glueCovered squares).toList, c ≠ d →
      ∀ s ∈ c.toList, ∀ t ∈ d.toList,
        ¬Glue.Edge s t ∧ ¬Glue.Edge t s := by
  rw [glueCovered_eq_glue, Hex.glue]
  intro c hc d hd hcd
  change c ∈ (Hex.glueList squares.toList).map List.toArray at hc
  change d ∈ (Hex.glueList squares.toList).map List.toArray at hd
  rw [List.mem_map] at hc hd
  obtain ⟨l, hl, rfl⟩ := hc
  obtain ⟨m, hm, rfl⟩ := hd
  have hlm : l ≠ m := by
    intro h
    subst m
    exact hcd rfl
  exact Glue.separated_glueList squares.toList l hl m hm hlm

end HexRootsMathlib
