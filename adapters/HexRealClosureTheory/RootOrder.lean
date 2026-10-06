/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootOrder
public import HexRealClosureTheory.IsolationRoots
public import HexSignDetTheory.SelectedProducer
public import HexSignDetTheory.ComparisonProducer

public section

namespace Hex.RealClosure.Isolation
open HexPolyTheory.Interpret

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
theorem pointQuery_eval (point : E) (x : K) :
    (interpret φ hz (pointQuery point)).eval x = x - φ point := by
  have mono : interpret φ hz (DensePoly.monomial 1 (1 : E)) = Polynomial.X := by
    ext i
    by_cases h : i = 1
    · simp [coeff_interpret, DensePoly.coeff_monomial, Polynomial.coeff_X, h, h1]
    · simp [coeff_interpret, DensePoly.coeff_monomial, Polynomial.coeff_X, h,
        (hz (Zero.zero : E)).mpr rfl, eq_comm]

  rw [pointQuery, interpret_sub φ hz hs, mono, interpret_C]
  simp

/-- A semantic pointQuery sign has the ordinary field comparison. -/
theorem signOrder_sub (x y : K) :
    signOrder (SignType.sign (x - y) : Int) = .ok (Ord.compare x y) := by
  rcases lt_trichotomy x y with less | same | greater
  · simp [signOrder, sign_eq_neg_one_iff.mpr (sub_neg.mpr less),
      compare_lt_iff_lt.mpr less]
  · subst y
    simp [signOrder]
  · simp [signOrder, sign_eq_one_iff.mpr (sub_pos.mpr greater),
      compare_gt_iff_gt.mpr greater]

include hs hsign in
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
  cases built : d.buildSigns [pointQuery point] with
  | error error => simp [Root.compare, built] at accepted
  | ok signs =>
    have value := signs.value_at_root φ hz h1 ha hs hm hnat hsign
    rw [pointQuery_eval φ hz h1 hs] at value
    have same : (Except.ok (Ord.compare (d.root φ hz h1 ha hs hm hnat hsign) (φ point)) :
        Except SignDet.BuildError Ordering) =
        Except.ok order := by
      simpa only [Root.compare, built, value, signOrder_sub] using accepted
    exact (Except.ok.inj same).symm

omit [Field K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
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
  cases built : d.buildSigns [pointQuery point] with
  | error error => simp [Root.compare, built] at accepted
  | ok signs =>
    have value := signs.value_at_root φ hz h1 ha hs hm hnat hsign
    rw [pointQuery_eval φ hz h1 hs] at value
    have same : (Except.ok (Ord.compare (φ point) (d.root φ hz h1 ha hs hm hnat hsign)) :
        Except SignDet.BuildError Ordering) = Except.ok order := by
      simpa only [Root.compare, built, value, signOrder_sub, compare_swap] using accepted
    exact (Except.ok.inj same).symm

include hz h1 ha hs hm hnat hsign in
/-- The upstream selected-sign success theorem discharges every mixed guard. -/
theorem Root.compare_selected (hn : ∀ a, φ (-a) = -φ a)
    (hi : ∀ a, φ a⁻¹ = (φ a)⁻¹) {context : Ctx}
    (d : SignDet.Descriptor E Ctx sign context) (point : E) :
    (Root.selected d).compare (.point point) =
      .ok (Ord.compare (d.root φ hz h1 ha hs hm hnat hsign) (φ point)) := by
  obtain ⟨signs, built⟩ := d.buildSigns_success φ hz h1 ha hs hm hnat hsign hn hi [pointQuery point]
  have value := signs.value_at_root φ hz h1 ha hs hm hnat hsign
  rw [pointQuery_eval φ hz h1 hs] at value
  simp only [Root.compare, built, value, signOrder_sub]

include hz h1 ha hs hm hnat hsign in
/-- Point/selected-root comparison also succeeds unconditionally under the
actual coefficient interpretation laws. -/
theorem Root.compare_point (hn : ∀ a, φ (-a) = -φ a)
    (hi : ∀ a, φ a⁻¹ = (φ a)⁻¹) {context : Ctx}
    (point : E) (d : SignDet.Descriptor E Ctx sign context) :
    (Root.point point).compare (.selected d) =
      .ok (Ord.compare (φ point) (d.root φ hz h1 ha hs hm hnat hsign)) := by
  obtain ⟨signs, built⟩ := d.buildSigns_success φ hz h1 ha hs hm hnat hsign hn hi [pointQuery point]
  have value := signs.value_at_root φ hz h1 ha hs hm hnat hsign
  rw [pointQuery_eval φ hz h1 hs] at value
  simp only [Root.compare, built, value, signOrder_sub, compare_swap]

include hz h1 ha hs hm hnat hsign in
/-- Every comparison of actual isolation roots succeeds and returns their
mathematical order, including descriptors with different defining heads. -/
theorem Root.compare_correct (hn : ∀ a, φ (-a) = -φ a)
    (hi : ∀ a, φ a⁻¹ = (φ a)⁻¹) (hd : ∀ a b, φ (a / b) = φ a / φ b)
    {context : Ctx} (left right : Root sign context) :
    left.compare right = .ok (Ord.compare
      (left.value φ hz h1 ha hs hm hnat hsign)
      (right.value φ hz h1 ha hs hm hnat hsign)) := by
  cases left with
  | point a =>
    cases right with
    | point b => exact Root.compare_points φ hs hsign a b
    | selected b => exact Root.compare_point φ hz h1 ha hs hm hnat hsign hn hi a b
  | selected a =>
    cases right with
    | point b => exact Root.compare_selected φ hz h1 ha hs hm hnat hsign hn hi a b
    | selected b =>
      obtain ⟨comparison, built⟩ :=
        a.buildComparison_success φ hz h1 ha hs hm hnat hsign hn hi hd b
      simp only [Root.compare, built]
      rw [comparison.order_root φ hz h1 ha hs hm hnat hsign]
      change Except.ok _ = Except.ok (Ord.compare
        (a.root φ hz h1 ha hs hm hnat hsign) (b.root φ hz h1 ha hs hm hnat hsign))
      rcases lt_trichotomy (a.root φ hz h1 ha hs hm hnat hsign)
        (b.root φ hz h1 ha hs hm hnat hsign) with less | same | greater
      · simp [less, compare_lt_iff_lt.mpr less]
      · simp [same]
      · simp [greater.not_gt, greater, compare_gt_iff_gt.mpr greater]

include hz h1 ha hs hm hnat hsign in
/-- Equality returned by any successful comparison identifies exactly equal
mathematical root values, including two different defining polynomials. -/
theorem Root.compare_eq {context : Ctx} (left right : Root sign context) {order : Ordering}
    (accepted : left.compare right = .ok order) :
    order = .eq ↔ left.value φ hz h1 ha hs hm hnat hsign =
      right.value φ hz h1 ha hs hm hnat hsign := by
  cases left with
  | point a =>
    cases right with
    | point b =>
      rw [Root.compare_points φ hs hsign] at accepted
      rw [← Except.ok.inj accepted]
      exact compare_eq_iff_eq
    | selected d =>
      rw [Root.compare_point_selected φ hz h1 ha hs hm hnat hsign a d accepted]
      exact compare_eq_iff_eq
  | selected a =>
    cases right with
    | point b =>
      rw [Root.compare_selected_point φ hz h1 ha hs hm hnat hsign a b accepted]
      exact compare_eq_iff_eq
    | selected b =>
      cases built : a.buildComparison b with
      | error error => simp [Root.compare, built] at accepted
      | ok comparison =>
        have same : comparison.order = order := by simpa only [Root.compare, built, Except.ok.injEq] using accepted
        rw [← same]
        exact comparison.eq_iff_root_eq φ hz h1 ha hs hm hnat hsign

include hz h1 ha hs hm hnat hsign in
/-- Sorting cannot omit or introduce any mathematical root value.
`Root.sort_sorted` proves strict order under the remaining operation laws. -/
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
distinctness for the original polynomial. Strict order remains a separate proof. -/
theorem Completion.sort_values (hn : ∀ a, φ (-a) = -φ a)
    (hi : ∀ a, φ a⁻¹ = (φ a)⁻¹) {context : Ctx} {p : DensePoly E}
    (completion : Completion sign context p) {out : List (Root sign context)}
    (accepted : completion.sort = .ok out) :
    (∀ x, x ∈ out.map (Root.value φ hz h1 ha hs hm hnat hsign) ↔
      (interpret φ hz p).IsRoot x) ∧
      (out.map (Root.value φ hz h1 ha hs hm hnat hsign)).Nodup := by
  have preserved := Root.sort_values φ hz h1 ha hs hm hnat hsign accepted
  rw [Output.entries_values φ hz h1 ha hs hm hnat hsign] at preserved
  exact ⟨fun x => preserved.mem_iff.trans
    (completion.coverage φ hz h1 ha hs hm hnat hsign hn hi x),
    preserved.nodup_iff.mpr (completion.nodup φ hz h1 ha hs hm hnat hsign hn hi)⟩

variable (hn : ∀ a, φ (-a) = -φ a) (hi : ∀ a, φ a⁻¹ = (φ a)⁻¹)
variable (hd : ∀ a b, φ (a / b) = φ a / φ b)

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Inserting a mathematically distinct root cannot reach a comparison
diagnostic or the duplicate-root branch. -/
theorem Root.insertBy_success {context : Ctx} {A : Type x} (key : A → Root sign context) (root : A)
    (roots : List A)
    (distinct : (key root).value φ hz h1 ha hs hm hnat hsign ∉
      roots.map (fun a => (key a).value φ hz h1 ha hs hm hnat hsign)) :
    ∃ out, Root.insertBy key root roots = .ok out := by
  induction roots with
  | nil => exact ⟨[root], rfl⟩
  | cons first rest ih =>
    have different : (key root).value φ hz h1 ha hs hm hnat hsign ≠
        (key first).value φ hz h1 ha hs hm hnat hsign := by
      intro same
      exact distinct (by simp [same])
    have compared := (key root).compare_correct φ hz h1 ha hs hm hnat hsign hn hi hd (key first)
    rcases lt_or_gt_of_ne different with less | greater
    · rw [compare_lt_iff_lt.mpr less] at compared
      exact ⟨root :: first :: rest, by simp [Root.insertBy, compared]⟩
    · rw [compare_gt_iff_gt.mpr greater] at compared
      obtain ⟨out, inserted⟩ := ih (fun member => distinct (by simp [member]))
      exact ⟨first :: out, by simp [Root.insertBy, compared, inserted]⟩

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Successful insertion preserves strict mathematical order. -/
theorem Root.insertBy_sorted {context : Ctx} {A : Type x} (key : A → Root sign context) (root : A)
    {roots out : List A}
    (sorted : roots.Pairwise fun a b =>
      (key a).value φ hz h1 ha hs hm hnat hsign < (key b).value φ hz h1 ha hs hm hnat hsign)
    (accepted : Root.insertBy key root roots = .ok out) :
    out.Pairwise fun a b =>
      (key a).value φ hz h1 ha hs hm hnat hsign < (key b).value φ hz h1 ha hs hm hnat hsign := by
  induction roots generalizing out with
  | nil =>
    have same : out = [root] := by simpa [Root.insertBy] using accepted.symm
    simp [same]
  | cons first rest ih =>
    obtain ⟨before, ordered⟩ := List.pairwise_cons.mp sorted
    have compared := (key root).compare_correct φ hz h1 ha hs hm hnat hsign hn hi hd (key first)
    rcases lt_trichotomy ((key root).value φ hz h1 ha hs hm hnat hsign)
      ((key first).value φ hz h1 ha hs hm hnat hsign) with less | same | greater
    · rw [compare_lt_iff_lt.mpr less] at compared
      have output : out = root :: first :: rest := by
        simpa [Root.insertBy, compared] using accepted.symm
      rw [output, List.pairwise_cons]
      refine ⟨?_, sorted⟩
      intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact less
      · exact less.trans (before other member)
    · rw [compare_eq_iff_eq.mpr same] at compared
      simp [Root.insertBy, compared] at accepted
    · rw [compare_gt_iff_gt.mpr greater] at compared
      cases inserted : Root.insertBy key root rest with
      | error error => simp [Root.insertBy, compared, inserted] at accepted
      | ok result =>
        have output : out = first :: result := by
          simpa [Root.insertBy, compared, inserted] using accepted.symm
        rw [output, List.pairwise_cons]
        refine ⟨?_, ih ordered inserted⟩
        intro other member
        have present := (Root.insertBy_perm key root inserted).mem_iff.mp member
        rcases List.mem_cons.mp present with rfl | present
        · exact greater
        · exact before other present

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- The actual diagnostic-preserving sort is strictly ordered whenever it
succeeds, rather than merely permuting the input roots. -/
theorem Root.sortBy_sorted {context : Ctx} {A : Type x} (key : A → Root sign context) {roots out : List A}
    (accepted : Root.sortBy key roots = .ok out) :
    (out.map (fun a => (key a).value φ hz h1 ha hs hm hnat hsign)).Pairwise (· < ·) := by
  apply List.pairwise_map.mpr
  induction roots generalizing out with
  | nil =>
    have same : out = [] := by simpa [Root.sortBy] using accepted.symm
    simp [same]
  | cons root rest ih =>
    cases sorted : Root.sortBy key rest with
    | error error => simp [Root.sortBy, sorted] at accepted
    | ok result =>
      have inserted : Root.insertBy key root result = .ok out := by
        simpa [Root.sortBy, sorted] using accepted
      exact Root.insertBy_sorted φ hz h1 ha hs hm hnat hsign hn hi hd key root
        (ih sorted) inserted

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- A list of distinct mathematical root values has a successful actual
sort and a strictly increasing output. -/
theorem Root.sortBy_success {context : Ctx} {A : Type x} (key : A → Root sign context) (roots : List A)
    (distinct : (roots.map (fun a => (key a).value φ hz h1 ha hs hm hnat hsign)).Nodup) :
    ∃ out, Root.sortBy key roots = .ok out ∧
      (out.map (fun a => (key a).value φ hz h1 ha hs hm hnat hsign)).Pairwise (· < ·) := by
  have success : ∃ out, Root.sortBy key roots = .ok out := by
    induction roots with
    | nil => exact ⟨[], rfl⟩
    | cons root rest ih =>
      obtain ⟨absent, distinct⟩ := List.nodup_cons.mp distinct
      obtain ⟨result, sorted⟩ := ih distinct
      have preserved := (Root.sortBy_perm key sorted).map
        (fun a => (key a).value φ hz h1 ha hs hm hnat hsign)
      obtain ⟨out, inserted⟩ := Root.insertBy_success φ hz h1 ha hs hm hnat hsign hn hi hd
        key root result (fun member => absent (preserved.mem_iff.mp member))
      exact ⟨out, by simp [Root.sortBy, sorted, inserted]⟩
  obtain ⟨out, sorted⟩ := success
  exact ⟨out, sorted, Root.sortBy_sorted φ hz h1 ha hs hm hnat hsign hn hi hd key sorted⟩

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- The root-only specialization of successful strict sorting. -/
theorem Root.sort_success {context : Ctx} (roots : List (Root sign context))
    (distinct : (roots.map (Root.value φ hz h1 ha hs hm hnat hsign)).Nodup) :
    ∃ out, Root.sort roots = .ok out ∧
      (out.map (Root.value φ hz h1 ha hs hm hnat hsign)).Pairwise (· < ·) :=
  Root.sortBy_success φ hz h1 ha hs hm hnat hsign hn hi hd id roots distinct

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Successful root-only sorting has strict mathematical order. -/
theorem Root.sort_sorted {context : Ctx} {roots out : List (Root sign context)}
    (accepted : Root.sort roots = .ok out) :
    (out.map (Root.value φ hz h1 ha hs hm hnat hsign)).Pairwise (· < ·) :=
  Root.sortBy_sorted φ hz h1 ha hs hm hnat hsign hn hi hd id accepted

end Hex.RealClosure.Isolation

/-- info: 'Hex.RealClosure.Isolation.Root.compare_selected_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Root.compare_selected_point
/-- info: 'Hex.RealClosure.Isolation.Completion.sort_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Completion.sort_values

/-- info: 'Hex.RealClosure.Isolation.Root.compare_point_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Root.compare_point_selected

/-- info: 'Hex.RealClosure.Isolation.Root.compare_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Root.compare_selected
/-- info: 'Hex.RealClosure.Isolation.Root.compare_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Root.compare_point
/-- info: 'Hex.RealClosure.Isolation.Root.compare_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Root.compare_eq

/-- info: 'Hex.RealClosure.Isolation.Root.compare_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Root.compare_correct

/-- info: 'Hex.RealClosure.Isolation.Root.sort_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Root.sort_success

/-- info: 'Hex.RealClosure.Isolation.Root.sort_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Root.sort_sorted
