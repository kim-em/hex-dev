/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootList
public import HexRealClosureMathlib.TowerRoots

public section

namespace Hex.RealClosure.Tower.Root
variable {registry : BaseContext.Registry} {parent : Context registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]

private theorem compare_lt (model : Model parent K) (a b : Root parent) :
    a.compare b = .lt ↔ a.denote model < b.denote model := by
  rw [a.compare_correct b model]
  exact compare_lt_iff_lt

private theorem compare_eq (model : Model parent K) (a b : Root parent) :
    a.compare b = .eq ↔ a.denote model = b.denote model := by
  rw [a.compare_correct b model]
  exact compare_eq_iff_eq

private theorem compare_gt (model : Model parent K) (a b : Root parent) :
    a.compare b = .gt ↔ b.denote model < a.denote model := by
  rw [a.compare_correct b model]
  exact compare_gt_iff_gt

/-- Removing equal boundaries loses no interpreted root value. -/
theorem insert_mem (model : Model parent K) (a : Root parent) (values : List (Root parent)) (x : K) :
    x ∈ (Root.insert a values).map (fun root => root.denote model) ↔
      x = a.denote model ∨ x ∈ values.map (fun root => root.denote model) := by
  induction values with
  | nil => simp [insert]
  | cons b rest ih =>
    cases order : a.compare b with
    | lt => simp [insert, order, eq_comm]
    | eq =>
      have equal := (compare_eq model a b).mp order
      simp [insert, order, equal, eq_comm]
    | gt => simp only [insert, order, List.map_cons, List.mem_cons, ih]; tauto

/-- Native insertion preserves strict order of interpreted, distinct boundaries. -/
theorem insert_sorted (model : Model parent K) (a : Root parent) (values : List (Root parent))
    (ordered : values.Pairwise (fun a b => a.denote model < b.denote model)) :
    (Root.insert a values).Pairwise (fun a b => a.denote model < b.denote model) := by
  induction values with
  | nil => simp [insert]
  | cons b rest ih =>
    obtain ⟨before, tail⟩ := List.pairwise_cons.mp ordered
    cases order : a.compare b with
    | lt =>
      have less := (compare_lt model a b).mp order
      simp only [insert, order, List.pairwise_cons]
      exact ⟨fun x hx => by
        rcases List.mem_cons.mp hx with rfl | present
        · exact less
        · exact less.trans (before x present), before, tail⟩
    | eq => simpa [insert, order] using ordered
    | gt =>
      have greater := (compare_gt model a b).mp order
      simp only [insert, order, List.pairwise_cons]
      refine ⟨?_, ih tail⟩
      intro x present
      have hx : x.denote model ∈ (Root.insert a rest).map (fun root => root.denote model) := List.mem_map.mpr ⟨x, present, rfl⟩
      rcases (insert_mem model a rest _).mp hx with equal | old
      · exact equal ▸ greater
      · obtain ⟨y, member, same⟩ := List.mem_map.mp old
        exact same ▸ before y member

private theorem fold_mem (model : Model parent K) (values sorted : List (Root parent)) (x : K) :
    x ∈ (values.foldl (fun acc a => Root.insert a acc) sorted).map (fun root => root.denote model) ↔
      x ∈ sorted.map (fun root => root.denote model) ∨ x ∈ values.map (fun root => root.denote model) := by
  induction values generalizing sorted with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.mem_cons]
    rw [insert_mem model]
    tauto

/-- Boundary sorting retains precisely the same interpreted root values. -/
theorem sort_mem (model : Model parent K) (values : List (Root parent)) (x : K) :
    x ∈ (Root.sort values).map (fun root => root.denote model) ↔ x ∈ values.map (fun root => root.denote model) := by
  simpa only [Root.sort, List.map_nil, List.not_mem_nil, false_or, List.map_reverse,
    List.mem_reverse] using fold_mem model values.reverse [] x

private theorem fold_sorted (model : Model parent K) (values sorted : List (Root parent))
    (ordered : sorted.Pairwise (fun a b => a.denote model < b.denote model)) :
    (values.foldl (fun acc a => Root.insert a acc) sorted).Pairwise
      (fun a b => a.denote model < b.denote model) := by
  induction values generalizing sorted with
  | nil => exact ordered
  | cons a rest ih => exact ih _ (insert_sorted model a sorted ordered)

/-- Every boundary occurs once in strict interpreted order. -/
theorem sort_sorted (model : Model parent K) (values : List (Root parent)) :
    (Root.sort values).Pairwise (fun a b => a.denote model < b.denote model) :=
  fold_sorted model values.reverse [] (by simp)

end Hex.RealClosure.Tower.Root

/-- info: 'Hex.RealClosure.Tower.Root.sort_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Root.sort_mem

/-- info: 'Hex.RealClosure.Tower.Root.sort_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Root.sort_sorted
