/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootOrder
public import HexRealClosureMathlib.IsolationRoots

public section

namespace Hex.RealClosure.Isolation
open HexPolyMathlib.Interpret

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E]
variable [DecidableEq Ctx] [Div E]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (φ : E → K) (hz : ∀ a, φ a = 0 ↔ a = 0)
variable (h1 : φ 1 = 1) (ha : ∀ a b, φ (a + b) = φ a + φ b)
variable (hs : ∀ a b, φ (a - b) = φ a - φ b)
variable (hm : ∀ a b, φ (a * b) = φ a * φ b)
variable (hnat : ∀ n : Nat, φ (n : E) = (n : K))
variable {sign : E → Int} (hsign : ∀ a, sign a = (SignType.sign (φ a) : Int))

/-- Interpret both actual isolation output forms in the same ambient field. -/
@[expose] noncomputable def Root.value {context : Ctx} : Root sign context → K
  | .point x => φ x
  | .selected d => d.root φ hz h1 ha hs hm hnat hsign

include hz h1 hs in
/-- The actual mixed-comparison query evaluates to root minus point. -/
theorem difference_eval (point : E) (x : K) :
    (interpret φ hz (difference point)).eval x = x - φ point := by
  have mono : interpret φ hz (DensePoly.monomial 1 (1 : E)) = Polynomial.X := by
    ext i
    by_cases h : i = 1
    · simp [coeff_interpret, DensePoly.coeff_monomial, Polynomial.coeff_X, h, h1]
    · simp [coeff_interpret, DensePoly.coeff_monomial, Polynomial.coeff_X, h,
        (hz (Zero.zero : E)).mpr rfl, eq_comm]

  rw [difference, interpret_sub φ hz hs, mono, interpret_C]
  simp

/-- A semantic difference sign has the ordinary field comparison. -/
theorem signOrder_sub (x y : K) :
    signOrder (SignType.sign (x - y) : Int) = .ok (Ord.compare x y) := by
  rcases lt_trichotomy x y with less | same | greater
  · simp [signOrder, sign_eq_neg_one_iff.mpr (sub_neg.mpr less),
      compare_lt_iff_lt.mpr less]
  · subst y
    simp [signOrder]
  · simp [signOrder, sign_eq_one_iff.mpr (sub_pos.mpr greater),
      compare_gt_iff_gt.mpr greater]

include hz h1 ha hs hm hnat hsign in
/-- Point comparisons denote the order in the common ambient field. -/
theorem Root.compare_points {context : Ctx} (a b : E) :
    (Root.point a : Root sign context).compare (.point b) = .ok (Ord.compare (φ a) (φ b)) := by
  simp only [Root.compare, hsign, hs]
  exact signOrder_sub (φ a) (φ b)

include hz h1 ha hs hm hnat hsign in
/-- A successful selected-root/point comparison is its mathematical order. -/
theorem Root.compare_selected_point {context : Ctx}
    (d : SignDet.Descriptor E Ctx sign context) (point : E) {order : Ordering}
    (accepted : (Root.selected d).compare (.point point) = .ok order) :
    order = Ord.compare (d.root φ hz h1 ha hs hm hnat hsign) (φ point) := by
  cases built : d.buildSigns [difference point] with
  | error error => simp [Root.compare, built] at accepted
  | ok signs =>
    have value := signs.value_at_root φ hz h1 ha hs hm hnat hsign
    rw [difference_eval φ hz h1 hs] at value
    have same : (Except.ok (Ord.compare (d.root φ hz h1 ha hs hm hnat hsign) (φ point)) :
        Except SignDet.BuildError Ordering) =
        Except.ok order := by
      simpa only [Root.compare, built, value, signOrder_sub] using accepted
    exact (Except.ok.inj same).symm

private theorem compare_swap (x y : K) : (Ord.compare x y).swap = Ord.compare y x := by
  rcases lt_trichotomy x y with less | same | greater
  · simp [compare_lt_iff_lt.mpr less, compare_gt_iff_gt.mpr less]
  · subst y
    simp
  · simp [compare_gt_iff_gt.mpr greater, compare_lt_iff_lt.mpr greater]

include hz h1 ha hs hm hnat hsign in
/-- The opposite mixed comparison also has its actual mathematical order. -/
theorem Root.compare_point_selected {context : Ctx}
    (point : E) (d : SignDet.Descriptor E Ctx sign context) {order : Ordering}
    (accepted : (Root.point point).compare (.selected d) = .ok order) :
    order = Ord.compare (φ point) (d.root φ hz h1 ha hs hm hnat hsign) := by
  cases built : d.buildSigns [difference point] with
  | error error => simp [Root.compare, built] at accepted
  | ok signs =>
    have value := signs.value_at_root φ hz h1 ha hs hm hnat hsign
    rw [difference_eval φ hz h1 hs] at value
    have same : (Except.ok (Ord.compare (φ point) (d.root φ hz h1 ha hs hm hnat hsign)) :
        Except SignDet.BuildError Ordering) = Except.ok order := by
      simpa only [Root.compare, built, value, signOrder_sub, compare_swap] using accepted
    exact (Except.ok.inj same).symm

include hz h1 ha hs hm hnat hsign in
/-- Sorting cannot omit or introduce any mathematical root value. This theorem
does not assert strict order for descriptor pairs without upstream Thom order. -/
theorem Root.sort_values {context : Ctx} {roots out : List (Root sign context)}
    (accepted : Root.sort roots = .ok out) :
    (out.map (Root.value φ hz h1 ha hs hm hnat hsign)).Perm
      (roots.map (Root.value φ hz h1 ha hs hm hnat hsign)) :=
  (Root.sort_perm accepted).map _

include hz h1 ha hs hm hnat hsign in
/-- Collecting the executable forms gives precisely the proved completion values. -/
theorem Output.entries_values {context : Ctx} (output : Output sign context) :
    output.entries.map (Root.value φ hz h1 ha hs hm hnat hsign) = output.values φ hz h1 ha hs hm hnat hsign := by
  simp [Output.entries, Output.values, Root.value, List.map_map, Function.comp_def]

include hz h1 ha hs hm hnat hsign in
/-- A successful sort of completed isolation retains exact coverage and
distinctness for the original polynomial. Strict order is a separate gate. -/
theorem Completion.sort_spec (hn : ∀ a, φ (-a) = -φ a)
    (hi : ∀ a, φ a⁻¹ = (φ a)⁻¹) {context : Ctx} {p : DensePoly E}
    (completion : Completion sign context p) {out : List (Root sign context)}
    (accepted : Root.sort completion.roots.entries = .ok out) :
    (∀ x, x ∈ out.map (Root.value φ hz h1 ha hs hm hnat hsign) ↔
      (interpret φ hz p).IsRoot x) ∧
      (out.map (Root.value φ hz h1 ha hs hm hnat hsign)).Nodup := by
  have preserved := Root.sort_values φ hz h1 ha hs hm hnat hsign accepted
  rw [Output.entries_values φ hz h1 ha hs hm hnat hsign] at preserved
  exact ⟨fun x => preserved.mem_iff.trans
    (completion.coverage φ hz h1 ha hs hm hnat hsign hn hi x),
    preserved.nodup_iff.mpr (completion.nodup φ hz h1 ha hs hm hnat hsign hn hi)⟩

end Hex.RealClosure.Isolation

/-- info: 'Hex.RealClosure.Isolation.Root.compare_selected_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Root.compare_selected_point
/-- info: 'Hex.RealClosure.Isolation.Completion.sort_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Completion.sort_spec

/-- info: 'Hex.RealClosure.Isolation.Root.compare_point_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Root.compare_point_selected
