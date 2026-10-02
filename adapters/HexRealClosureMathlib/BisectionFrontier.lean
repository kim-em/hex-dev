/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BisectionFrontier
public import HexRealClosureMathlib.BisectionRoots

public section

namespace Hex.RealClosure.Bisection
open HexPolyMathlib.Interpret HexSturmMathlib HexRealRootsMathlib.Tarski

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K]
variable (φ : E → K) (hz : ∀ a, φ a = 0 ↔ a = 0)
variable (h1 : φ 1 = 1) (ha : ∀ a b, φ (a + b) = φ a + φ b)
variable (hs : ∀ a b, φ (a - b) = φ a - φ b)
variable (hm : ∀ a b, φ (a * b) = φ a * φ b)
variable (sign : E → Int) (hzero : ∀ a, sign a = 0 ↔ φ a = 0)
variable (hn : ∀ a, φ (-a) = -φ a) (hi : ∀ a, φ a⁻¹ = (φ a)⁻¹)
variable (hnat : ∀ n : Nat, φ (n : E) = (n : K))
variable (hpos : ∀ a, sign a = 1 ↔ 0 < φ a) (hneg : ∀ a, sign a < 0 ↔ φ a < 0)

/-- Roots emitted so far together with active roots in the retained intervals. -/
@[expose] def Frontier.Roots (frontier : Frontier sign) (x : K) : Prop :=
  (∃ r ∈ frontier.removed, x = φ r) ∨
    (interpret φ hz frontier.head).IsRoot x ∧
      ∃ bounds ∈ frontier.cells.map (fun cell => (cell.lower, cell.upper)),
        InInterval (.finite (φ bounds.1)) (.finite (φ bounds.2)) x

/-- Distinct retained open intervals have no common point. -/
@[expose] def Frontier.Disjoint (frontier : Frontier sign) : Prop :=
  (frontier.cells.map (fun cell => (cell.lower, cell.upper))).Pairwise
    (fun a b => ∀ x : K, InInterval (.finite (φ a.1)) (.finite (φ a.2)) x →
      ¬ InInterval (.finite (φ b.1)) (.finite (φ b.2)) x)

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- Every stored finite cell has the domain of its actual current head. -/
theorem Cell.domain_valid {p : DensePoly E} (cell : Cell sign p) :
    Domain φ hz p (.finite cell.lower) (.finite cell.upper) := by
  have valid := prepared_domain φ hz ha hs hm sign hneg hzero h1 hn hi hnat hpos
    cell.domain cell.bound.1
  simpa only [cell.bound.2.1, cell.bound.2.2.1, cell.bound.2.2.2] using valid

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- The native cell constructor succeeds exactly on admissible finite domains. -/
theorem Cell.prepare?_success (p : DensePoly E) (lower upper : E) :
    (Cell.prepare? sign p lower upper).isSome = true ↔
      Domain φ hz p (.finite lower) (.finite upper) := by
  rw [Cell.prepare?_isSome]
  exact prepare_isSome φ hz ha hs hm sign hneg hzero h1 hn hi hnat hpos
    p (.finite lower) (.finite upper)

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- Deflation preserves all old pending domains, without requiring the cut to
lie inside them. Both their endpoints and their counts must be recomputed. -/
theorem Cell.reprepare?_success {p : DensePoly E} {point : E}
    (cell : Cell sign p) (d : Deflation p point) :
    (cell.reprepare? d.quotient).isSome = true := by
  have old := cell.domain_valid φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg
  unfold Cell.reprepare?
  apply (Cell.prepare?_success φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg
    d.quotient cell.lower cell.upper).mpr
  exact ⟨d.quotient_nonzero φ hz h1 hs hm, d.squarefree φ hz h1 hs hm old.2.1,
    old.2.2.1, d.nonvanishing φ hz h1 hs hm _ old.2.2.2.1,
    d.nonvanishing φ hz h1 hs hm _ old.2.2.2.2⟩

private theorem mapM_success {α β : Type u} (f : α → Option β)
    (total : ∀ a, ∃ b, f a = some b) (values : List α) :
    ∃ result, values.mapM f = some result := by
  induction values with
  | nil => exact ⟨[], rfl⟩
  | cons value values ih =>
    obtain ⟨output, ho⟩ := total value
    obtain ⟨rest, hr⟩ := ih
    exact ⟨output :: rest, by simp [List.mapM_cons, ho, hr]⟩

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- Rebinding all pending cells succeeds under the same interpretation as
shared preparation. No cell is exempt because it previously had count one. -/
theorem Mode.reprepare?_success {p : DensePoly E} {point : E}
    (mode : Mode sign p point) (cells : List (Cell sign p)) :
    (mode.reprepare? cells).isSome = true := by
  cases mode with
  | regular _ => rfl
  | root d =>
    obtain ⟨pending, hp⟩ := mapM_success (fun cell : Cell sign p => cell.reprepare? d.quotient)
      (fun cell => by
        have h := cell.reprepare?_success φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg d
        cases hc : cell.reprepare? d.quotient with
        | none => simp [hc] at h
        | some output => exact ⟨output, rfl⟩) cells
    change (cells.mapM (fun cell : Cell sign p => cell.reprepare? d.quotient)).isSome = true
    rw [hp]
    rfl

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- Every selected native step succeeds: its chosen cell supplies the domain,
and all pending cells are checked against the actual new head. -/
theorem Frontier.advance?_success (frontier : Frontier sign)
    (selected : Cell sign frontier.head) (rest : List (Cell sign frontier.head))
    (chosen : select frontier.cells = some (selected, rest)) :
    (frontier.advance? selected rest chosen).isSome = true := by
  rw [Frontier.advance?_isSome]
  have hsplit := bisect?_success φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg
    frontier.head selected.lower selected.upper
    (selected.domain_valid φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg)
  cases hb : Bisection.bisect? sign frontier.head selected.lower selected.upper with
  | none => simp [hb] at hsplit
  | some split => exact ⟨split, rfl,
      split.mode.reprepare?_success φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg rest⟩

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- The entire finite traversal succeeds under the shared coefficient
interpretation, including every pending-cell recomputation. -/
theorem traverse?_success (budget : Nat) (frontier : Frontier sign) :
    (traverse? budget frontier).isSome = true := by
  induction budget generalizing frontier with
  | zero => rfl
  | succ budget ih =>
    simp only [traverse?]
    split
    · rfl
    · rename_i cell rest hc
      have total := frontier.advance?_success φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg
        cell rest hc
      cases hn : frontier.advance? cell rest hc with
      | none => simp [hn] at total
      | some next => simpa [hn] using ih next

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- A checked step preserves every root represented by the frontier. This
uses the actual split and re-prepared intervals, including count-one cells. -/
theorem Frontier.advance?_roots (frontier : Frontier sign)
    (selected : Cell sign frontier.head) (rest : List (Cell sign frontier.head))
    (chosen : select frontier.cells = some (selected, rest)) {next : Frontier sign}
    (accepted : frontier.advance? selected rest chosen = some next) (x : K) :
    frontier.Roots φ hz sign x ↔ next.Roots φ hz sign x := by
  obtain ⟨split, hsplit, pending, hpending, hhead, hremoved, hcoords⟩ :=
    frontier.advance?_result selected rest chosen accepted
  rw [split.mode.reprepare?_endpoints rest hpending] at hcoords
  have perm := (select_perm chosen).map (fun cell => (cell.lower, cell.upper))
  have intervals :
      (∃ bounds ∈ frontier.cells.map (fun cell => (cell.lower, cell.upper)),
        InInterval (.finite (φ bounds.1)) (.finite (φ bounds.2)) x) ↔
      InInterval (.finite (φ selected.lower)) (.finite (φ selected.upper)) x ∨
        ∃ bounds ∈ rest.map (fun cell => (cell.lower, cell.upper)),
          InInterval (.finite (φ bounds.1)) (.finite (φ bounds.2)) x := by
    constructor
    · rintro ⟨bounds, hb, hx⟩
      have hm := perm.mem_iff.mp hb
      simp only [List.map_cons, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact Or.inl hx
      · exact Or.inr ⟨bounds, hm, hx⟩
    · rintro (hx | ⟨bounds, hb, hx⟩)
      · exact ⟨(selected.lower, selected.upper), perm.mem_iff.mpr (by simp), hx⟩
      · exact ⟨bounds, perm.mem_iff.mpr (by simp [hb]), hx⟩
  have partition := split.partition φ hz h1 hs hm ha hzero hn hi hnat hpos hneg x
  simp only [split.left_bound.2.1, split.right_bound.2.1,
    split.left_bound.2.2.1, split.left_bound.2.2.2,
    split.right_bound.2.2.1, split.right_bound.2.2.2, Endpoint.map] at partition
  have root := split.mode.roots φ hz h1 hs hm x
  simp only [Frontier.Roots, hhead, hremoved, hcoords, intervals,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    Option.mem_toList]
  simp only [or_and_right, exists_or, exists_eq_left]
  simp only [Option.mem_def] at root partition
  constructor
  · rintro (old | ⟨hp, selected | pending⟩)
    · exact Or.inl (Or.inl old)
    · rcases partition.mp ⟨hp, selected⟩ with cut | left | right
      · exact Or.inl (Or.inr cut)
      · exact Or.inr ⟨left.1, Or.inl (Or.inl left.2)⟩
      · exact Or.inr ⟨right.1, Or.inl (Or.inr right.2)⟩
    · rcases root.mp hp with cut | active
      · exact Or.inl (Or.inr cut)
      · exact Or.inr ⟨active, Or.inr pending⟩
  · rintro ((old | cut) | ⟨active, (left | right) | pending⟩)
    · exact Or.inl old
    · have original := partition.mpr (Or.inl cut)
      exact Or.inr ⟨original.1, Or.inl original.2⟩
    · have original := partition.mpr (Or.inr (Or.inl ⟨active, left⟩))
      exact Or.inr ⟨original.1, Or.inl original.2⟩
    · have original := partition.mpr (Or.inr (Or.inr ⟨active, right⟩))
      exact Or.inr ⟨original.1, Or.inl original.2⟩
    · exact Or.inr ⟨root.mpr (Or.inr active), Or.inr pending⟩

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- Finite traversal preserves the complete frontier root coverage. -/
theorem traverse?_roots (budget : Nat) (frontier : Frontier sign) {result : Frontier sign}
    (accepted : traverse? budget frontier = some result) (x : K) :
    frontier.Roots φ hz sign x ↔ result.Roots φ hz sign x := by
  induction budget generalizing frontier with
  | zero =>
    simp only [traverse?, Option.some.injEq] at accepted
    subst result
    rfl
  | succ budget ih =>
    simp only [traverse?] at accepted
    split at accepted
    · simp only [Option.some.injEq] at accepted
      subst result
      rfl
    · rename_i cell rest hc
      cases hnext : frontier.advance? cell rest hc with
      | none => simp [hnext] at accepted
      | some next =>
        simp [hnext] at accepted
        exact (frontier.advance?_roots φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg
          cell rest hc hnext x).trans (ih next accepted)

omit [IsStrictOrderedRing K] in
/-- An accepted initial frontier contains exactly the original roots inside
its supplied open interval, with no removed points. -/
theorem Frontier.prepare?_roots {p : DensePoly E} {lower upper : E}
    {frontier : Frontier sign} (accepted : Frontier.prepare? sign p lower upper = some frontier)
    (x : K) : frontier.Roots φ hz sign x ↔
      (interpret φ hz p).IsRoot x ∧ InInterval (.finite (φ lower)) (.finite (φ upper)) x := by
  obtain ⟨head, removed, _, coords⟩ := Frontier.prepare?_result accepted
  simp [Frontier.Roots, head, removed, coords]

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- Once emitted, a coefficient root is excluded from every later active head. -/
theorem Frontier.advance?_nonvanishing (frontier : Frontier sign)
    (selected : Cell sign frontier.head) (rest : List (Cell sign frontier.head))
    (chosen : select frontier.cells = some (selected, rest)) {next : Frontier sign}
    (accepted : frontier.advance? selected rest chosen = some next)
    (old : ∀ r ∈ frontier.removed, ¬ (interpret φ hz frontier.head).IsRoot (φ r)) :
    ∀ r ∈ next.removed, ¬ (interpret φ hz next.head).IsRoot (φ r) := by
  obtain ⟨split, _, _, _, hhead, hremoved, _⟩ :=
    frontier.advance?_result selected rest chosen accepted
  intro r hr
  rw [hremoved] at hr
  rw [hhead]
  rcases List.mem_append.mp hr with earlier | emitted
  · intro active
    exact old r earlier ((split.mode.roots φ hz h1 hs hm (φ r)).mpr (Or.inr active))
  · have cut : r = midpoint selected.lower selected.upper :=
      split.mode.mem_removed r (by simpa only [Option.mem_toList, Option.mem_def] using emitted)
    subst r
    obtain ⟨left, _⟩ := split.domains φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg
    exact left.2.2.2.2

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- A successful traversal continues to exclude every emitted root. -/
theorem traverse?_nonvanishing (budget : Nat) (frontier : Frontier sign)
    {result : Frontier sign} (accepted : traverse? budget frontier = some result)
    (old : ∀ r ∈ frontier.removed, ¬ (interpret φ hz frontier.head).IsRoot (φ r)) :
    ∀ r ∈ result.removed, ¬ (interpret φ hz result.head).IsRoot (φ r) := by
  induction budget generalizing frontier with
  | zero =>
    simp only [traverse?, Option.some.injEq] at accepted
    subst result
    exact old
  | succ budget ih =>
    simp only [traverse?] at accepted
    split at accepted
    · simp only [Option.some.injEq] at accepted
      subst result
      exact old
    · rename_i cell rest hc
      cases hnext : frontier.advance? cell rest hc with
      | none => simp [hnext] at accepted
      | some next =>
        simp [hnext] at accepted
        exact ih next accepted (frontier.advance?_nonvanishing φ hz h1 ha hs hm sign
          hzero hn hi hnat hpos hneg cell rest hc hnext old)

include hz h1 hs hm in
omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- A step emits no value equal to an earlier emitted value. This is semantic
inequality and does not assert equality laws on raw coefficient syntax. -/
theorem Frontier.advance?_distinct (frontier : Frontier sign)
    (selected : Cell sign frontier.head) (rest : List (Cell sign frontier.head))
    (chosen : select frontier.cells = some (selected, rest)) {next : Frontier sign}
    (accepted : frontier.advance? selected rest chosen = some next)
    (excluded : ∀ r ∈ frontier.removed, ¬ (interpret φ hz frontier.head).IsRoot (φ r))
    (old : frontier.removed.Pairwise (fun a b => φ a ≠ φ b)) :
    next.removed.Pairwise (fun a b => φ a ≠ φ b) := by
  obtain ⟨split, _, _, _, _, hremoved, _⟩ :=
    frontier.advance?_result selected rest chosen accepted
  rw [hremoved, List.pairwise_append]
  refine ⟨old, ?_, ?_⟩
  · cases split.mode.removed <;> simp
  · intro a ha b hb heq
    have member : b ∈ split.mode.removed := by
      simpa only [Option.mem_toList, Option.mem_def] using hb
    have root := (split.mode.roots φ hz h1 hs hm (φ b)).mpr (Or.inl ⟨b, member, rfl⟩)
    exact excluded a ha (heq.symm ▸ root)

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- Traversal preserves distinctness of the emitted mathematical values. -/
theorem traverse?_distinct (budget : Nat) (frontier : Frontier sign)
    {result : Frontier sign} (accepted : traverse? budget frontier = some result)
    (excluded : ∀ r ∈ frontier.removed, ¬ (interpret φ hz frontier.head).IsRoot (φ r))
    (old : frontier.removed.Pairwise (fun a b => φ a ≠ φ b)) :
    result.removed.Pairwise (fun a b => φ a ≠ φ b) := by
  induction budget generalizing frontier with
  | zero =>
    simp only [traverse?, Option.some.injEq] at accepted
    subst result
    exact old
  | succ budget ih =>
    simp only [traverse?] at accepted
    split at accepted
    · simp only [Option.some.injEq] at accepted
      subst result
      exact old
    · rename_i cell rest hc
      cases hnext : frontier.advance? cell rest hc with
      | none => simp [hnext] at accepted
      | some next =>
        simp [hnext] at accepted
        apply ih next accepted
        · exact frontier.advance?_nonvanishing φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg
            cell rest hc hnext excluded
        · exact frontier.advance?_distinct φ hz h1 hs hm sign
            cell rest hc hnext excluded old

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- A step preserves disjointness of the actual retained intervals. -/
theorem Frontier.advance?_disjoint (frontier : Frontier sign)
    (selected : Cell sign frontier.head) (rest : List (Cell sign frontier.head))
    (chosen : select frontier.cells = some (selected, rest)) {next : Frontier sign}
    (accepted : frontier.advance? selected rest chosen = some next)
    (old : frontier.Disjoint φ sign) : next.Disjoint φ sign := by
  obtain ⟨split, _, pending, hpending, _, _, hcoords⟩ :=
    frontier.advance?_result selected rest chosen accepted
  rw [split.mode.reprepare?_endpoints rest hpending] at hcoords
  have perm := (select_perm chosen).map (fun cell => (cell.lower, cell.upper))
  have symm {a b : E × E}
      (h : ∀ x : K, InInterval (.finite (φ a.1)) (.finite (φ a.2)) x →
        ¬ InInterval (.finite (φ b.1)) (.finite (φ b.2)) x) :
      ∀ x : K, InInterval (.finite (φ b.1)) (.finite (φ b.2)) x →
        ¬ InInterval (.finite (φ a.1)) (.finite (φ a.2)) x := by
    intro x hb ha
    exact h x ha hb
  have original := old.perm perm symm
  simp only [List.map_cons, List.pairwise_cons] at original
  obtain ⟨against, remaining⟩ := original
  obtain ⟨leftDomain, rightDomain⟩ :=
    split.domains φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg
  have hl : φ selected.lower < φ (midpoint selected.lower selected.upper) := leftDomain.2.2.1
  have hu : φ (midpoint selected.lower selected.upper) < φ selected.upper := rightDomain.2.2.1
  unfold Frontier.Disjoint
  rw [hcoords]
  simp only [List.cons_append, List.nil_append, List.pairwise_cons]
  refine ⟨?_, ?_, remaining⟩
  · intro bounds hb x hx hy
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · simp only [inInterval_iff] at hx hy
      exact lt_asymm hx.2 hy.1
    · apply against bounds hb x
      · simp only [inInterval_iff] at hx ⊢
        exact ⟨hx.1, hx.2.trans hu⟩
      · exact hy
  · intro bounds hb x hx hy
    apply against bounds hb x
    · simp only [inInterval_iff] at hx ⊢
      exact ⟨hl.trans hx.1, hx.2⟩
    · exact hy

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- Every frontier's current head is semantically nonzero. -/
theorem Frontier.head_nonzero (frontier : Frontier sign) :
    interpret φ hz frontier.head ≠ 0 := by
  obtain ⟨cell, member⟩ := List.exists_mem_of_ne_nil _ frontier.nonempty
  exact (cell.domain_valid φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg).1

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- Disjoint retained intervals remain disjoint through the entire traversal. -/
theorem traverse?_disjoint (budget : Nat) (frontier : Frontier sign)
    {result : Frontier sign} (accepted : traverse? budget frontier = some result)
    (old : frontier.Disjoint φ sign) : result.Disjoint φ sign := by
  induction budget generalizing frontier with
  | zero =>
    simp only [traverse?, Option.some.injEq] at accepted
    subst result
    exact old
  | succ budget ih =>
    simp only [traverse?] at accepted
    split at accepted
    · simp only [Option.some.injEq] at accepted
      subst result
      exact old
    · rename_i cell rest hc
      cases hnext : frontier.advance? cell rest hc with
      | none => simp [hnext] at accepted
      | some next =>
        simp [hnext] at accepted
        exact ih next accepted (frontier.advance?_disjoint φ hz h1 ha hs hm sign
          hzero hn hi hnat hpos hneg cell rest hc hnext old)

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- The capped entry point succeeds under the shared coefficient interpretation. -/
theorem Frontier.refine?_success (frontier : Frontier sign) :
    frontier.refine?.isSome = true :=
  traverse?_success φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg _ frontier

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- Preparing and refining a finite interval preserves exactly its original
roots, within the fixed node allowance. Emitted values are distinct and
excluded from the current head; retained intervals are disjoint. -/
theorem Frontier.refine?_spec {p : DensePoly E} {lower upper : E}
    {initial result : Frontier sign}
    (prepared : Frontier.prepare? sign p lower upper = some initial)
    (refined : initial.refine? = some result) :
    result.nodes ≤ 2 * (p.natDegree + 1) ∧
    (∀ x : K, result.Roots φ hz sign x ↔
      (interpret φ hz p).IsRoot x ∧ InInterval (.finite (φ lower)) (.finite (φ upper)) x) ∧
    result.removed.Pairwise (fun a b => φ a ≠ φ b) ∧
    (∀ r ∈ result.removed, ¬ (interpret φ hz result.head).IsRoot (φ r)) ∧
    result.Disjoint φ sign ∧
    (select result.cells = none ∨ result.nodes = 2 * (p.natDegree + 1)) := by
  obtain ⟨head, removed, nodes, coords⟩ := Frontier.prepare?_result prepared
  have excluded : ∀ r ∈ initial.removed, ¬ (interpret φ hz initial.head).IsRoot (φ r) := by
    simp [removed]
  have distinct : initial.removed.Pairwise (fun a b => φ a ≠ φ b) := by simp [removed]
  have disjoint : initial.Disjoint φ sign := by simp [Frontier.Disjoint, coords]
  have trace : traverse? (2 * (initial.head.natDegree + 1)) initial = some result := refined
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [head, nodes, Nat.zero_add] using traverse?_nodes _ initial trace
  · intro x
    exact (traverse?_roots φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg _ initial trace x).symm.trans
      (Frontier.prepare?_roots φ hz sign prepared x)
  · exact traverse?_distinct φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg _ initial trace excluded distinct
  · exact traverse?_nonvanishing φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg _ initial trace excluded
  · exact traverse?_disjoint φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg _ initial trace disjoint
  · simpa only [head, nodes, Nat.zero_add] using traverse?_stopped _ initial trace

end Hex.RealClosure.Bisection

/-- info: 'Hex.RealClosure.Bisection.Cell.domain_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Cell.domain_valid
/-- info: 'Hex.RealClosure.Bisection.Cell.prepare?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Cell.prepare?_success
/-- info: 'Hex.RealClosure.Bisection.Cell.reprepare?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Cell.reprepare?_success
/-- info: 'Hex.RealClosure.Bisection.Mode.reprepare?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Mode.reprepare?_success
/-- info: 'Hex.RealClosure.Bisection.Frontier.advance?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Frontier.advance?_success
/-- info: 'Hex.RealClosure.Bisection.traverse?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.traverse?_success

/-- info: 'Hex.RealClosure.Bisection.Frontier.advance?_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Frontier.advance?_roots
/-- info: 'Hex.RealClosure.Bisection.traverse?_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.traverse?_roots
/-- info: 'Hex.RealClosure.Bisection.Frontier.prepare?_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Frontier.prepare?_roots
/-- info: 'Hex.RealClosure.Bisection.Frontier.advance?_nonvanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Frontier.advance?_nonvanishing

/-- info: 'Hex.RealClosure.Bisection.traverse?_nonvanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.traverse?_nonvanishing
/-- info: 'Hex.RealClosure.Bisection.Frontier.advance?_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Frontier.advance?_distinct
/-- info: 'Hex.RealClosure.Bisection.traverse?_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.traverse?_distinct

/-- info: 'Hex.RealClosure.Bisection.Frontier.advance?_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Frontier.advance?_disjoint

/-- info: 'Hex.RealClosure.Bisection.Frontier.head_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Frontier.head_nonzero

/-- info: 'Hex.RealClosure.Bisection.traverse?_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.traverse?_disjoint

/-- info: 'Hex.RealClosure.Bisection.Frontier.refine?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Frontier.refine?_success

/-- info: 'Hex.RealClosure.Bisection.Frontier.refine?_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Frontier.refine?_spec
