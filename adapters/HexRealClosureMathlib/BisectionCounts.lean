/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BisectionFrontier
public import HexSturmMathlib.Soundness

public section

namespace Hex.RealClosure.Bisection
open HexPolyMathlib.Interpret HexSturmMathlib HexRealRootsMathlib.Tarski

private def union {K : Type v} [DecidableEq K] (sets : List (Finset K)) : Finset K :=
  sets.foldr (fun a b => a ∪ b) ∅

private theorem mem_union {K : Type v} [DecidableEq K] (sets : List (Finset K)) (x : K) :
    x ∈ union sets ↔ ∃ s ∈ sets, x ∈ s := by
  induction sets with
  | nil => simp [union]
  | cons head rest ih =>
    change x ∈ head ∪ union rest ↔ _
    rw [Finset.mem_union, ih]
    constructor
    · rintro (hx | ⟨s, hs, hx⟩)
      · exact ⟨head, by simp, hx⟩
      · exact ⟨s, List.mem_cons_of_mem _ hs, hx⟩
    · rintro ⟨s, hs, hx⟩
      rcases List.mem_cons.mp hs with rfl | hs
      · exact Or.inl hx
      · exact Or.inr ⟨s, hs, hx⟩

private theorem union_disjoint {K : Type v} [DecidableEq K] (head : Finset K)
    (sets : List (Finset K)) (all : ∀ s ∈ sets, _root_.Disjoint head s) :
    _root_.Disjoint head (union sets) := by
  apply Finset.disjoint_left.mpr
  intro x hx hm
  obtain ⟨s, hs, hxs⟩ := (mem_union sets x).mp hm
  exact Finset.disjoint_left.mp (all s hs) hx hxs

private theorem union_card {K : Type v} [DecidableEq K] (sets : List (Finset K))
    (disjoint : sets.Pairwise _root_.Disjoint) : (union sets).card = (sets.map Finset.card).sum := by
  induction sets with
  | nil => simp [union]
  | cons head rest ih =>
    obtain ⟨all, tail⟩ := List.pairwise_cons.mp disjoint
    change (head ∪ union rest).card = (head.card :: rest.map Finset.card).sum
    rw [Finset.card_union_of_disjoint (union_disjoint head rest all), List.sum_cons, ih tail]

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

/-- Finite semantic root set of an emitted-root list and its retained cells.
This is not an executable root constructor. -/
noncomputable def Frontier.rootSet (frontier : Frontier sign) : Finset K :=
  (frontier.removed.map φ).toFinset ∪ union
    (frontier.cells.map fun cell => rootsIn (interpret φ hz frontier.head)
      (.finite (φ cell.lower)) (.finite (φ cell.upper)))

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- Semantic membership matches the actual frontier coverage predicate. -/
theorem Frontier.mem_rootSet (frontier : Frontier sign) (x : K) :
    x ∈ frontier.rootSet φ hz sign ↔ frontier.Roots φ hz sign x := by
  have hp := frontier.head_nonzero φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg
  simp only [Frontier.rootSet, Finset.mem_union, List.mem_toFinset, List.mem_map, mem_union,
    Polynomial.IsRoot.def, Frontier.Roots]
  constructor
  · rintro (⟨r, hr, rfl⟩ | ⟨_, ⟨cell, hc, rfl⟩, hx⟩)
    · exact Or.inl ⟨r, hr, rfl⟩
    · obtain ⟨root, interval⟩ := (mem_rootsIn_iff _ hp _ _ x).mp hx
      exact Or.inr ⟨root, (cell.lower, cell.upper), ⟨cell, hc, rfl⟩, interval⟩
  · rintro (⟨r, hr, rfl⟩ | ⟨root, _, ⟨cell, hc, rfl⟩, hx⟩)
    · exact Or.inl ⟨r, hr, rfl⟩
    · exact Or.inr ⟨_, ⟨cell, hc, rfl⟩, (mem_rootsIn_iff _ hp _ _ x).mpr ⟨root, hx⟩⟩

variable [IsRealClosed K] (hsign : ∀ a, sign a = (SignType.sign (φ a) : Int))

include hz h1 ha hs hm hnat hn hi hsign in
/-- The stored count equals the mathematical number of roots in its actual
interval. This uses the shared query-soundness theorem and inherits #10389. -/
theorem Cell.count_card {p : DensePoly E} (cell : Cell sign p) :
    cell.count = (rootsIn (interpret φ hz p)
      (.finite (φ cell.lower)) (.finite (φ cell.upper))).card := by
  rw [cell.count_eq, queryPrepared_sound φ hz h1 ha hs hm hnat sign hsign hn hi
    cell.domain cell.bound.1 1]
  simp only [interpret_one φ hz h1, cell.bound.2.1, cell.bound.2.2.1,
    cell.bound.2.2.2, Endpoint.map, rootSum_one]

include hz h1 ha hs hm hnat hn hi hsign in
private theorem counts_card {p : DensePoly E} (cells : List (Cell sign p)) :
    (cells.map (·.count)).sum = ((cells.map fun cell =>
      (rootsIn (interpret φ hz p) (.finite (φ cell.lower)) (.finite (φ cell.upper))).card).sum : Nat) := by
  induction cells with
  | nil => simp
  | cons cell cells ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    rw [cell.count_card φ hz h1 ha hs hm sign hn hi hnat hsign, ih]

include hz h1 ha hs hm hnat hn hi hsign in
/-- Disjoint retained intervals and distinct excluded emissions make the sum
of cached counts plus emitted values equal the frontier's finite root count. -/
theorem Frontier.rootSet_card (frontier : Frontier sign)
    (disjoint : frontier.Disjoint φ sign)
    (distinct : frontier.removed.Pairwise (fun a b => φ a ≠ φ b))
    (excluded : ∀ r ∈ frontier.removed, ¬ (interpret φ hz frontier.head).IsRoot (φ r)) :
    (frontier.cells.map (·.count)).sum + frontier.removed.length =
      (frontier.rootSet φ hz sign).card := by
  let sets := frontier.cells.map fun cell => rootsIn (interpret φ hz frontier.head)
    (.finite (φ cell.lower)) (.finite (φ cell.upper))
  have separated : sets.Pairwise _root_.Disjoint := by
    apply List.pairwise_map.mpr
    have source := List.pairwise_map.mp disjoint
    apply source.imp
    intro a b hab
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hab x ((mem_rootsIn _ _ _ _).mp hx).2 ((mem_rootsIn _ _ _ _).mp hy).2
  have noOverlap : _root_.Disjoint (frontier.removed.map φ).toFinset (union sets) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    obtain ⟨_, hs, hx⟩ := (mem_union sets (φ r)).mp hy
    obtain ⟨cell, _, rfl⟩ := List.mem_map.mp hs
    exact excluded r hr (Polynomial.isRoot_of_mem_roots ((mem_rootsIn _ _ _ _).mp hx).1)
  have emitted : (frontier.removed.map φ).Nodup :=
    List.nodup_iff_pairwise_ne.mpr (List.pairwise_map.mpr distinct)
  have hc := union_card sets separated
  have counts := counts_card φ hz h1 ha hs hm sign hn hi hnat hsign frontier.cells
  unfold Frontier.rootSet
  rw [Finset.card_union_of_disjoint noOverlap, List.toFinset_card_of_nodup emitted, List.length_map]
  have cardEq : (union sets).card = (frontier.cells.map fun cell =>
      (rootsIn (interpret φ hz frontier.head) (.finite (φ cell.lower)) (.finite (φ cell.upper))).card).sum := by
    simpa only [sets, List.map_map, Function.comp_def] using hc
  rw [cardEq, Nat.cast_add, counts]
  exact add_comm _ _

include hz h1 ha hs hm hnat hn hi hsign in
/-- The capped entry preserves the original interval's root count, including
emitted values and all retained cached counts. It inherits only #10389. -/
theorem Frontier.refine?_count {p : DensePoly E} {lower upper : E}
    {initial result : Frontier sign}
    (prepared : Frontier.prepare? sign p lower upper = some initial)
    (refined : initial.refine? = some result) :
    (result.cells.map (·.count)).sum + result.removed.length =
      (rootsIn (interpret φ hz p) (.finite (φ lower)) (.finite (φ upper))).card := by
  have hsg := sign_spec φ sign hsign
  obtain ⟨_, coverage, distinct, excluded, disjoint, _⟩ :=
    Frontier.refine?_spec φ hz h1 ha hs hm sign (fun a => (hsg a).2.2.1)
      hn hi hnat (fun a => (hsg a).1) (fun a => (hsg a).2.1) prepared refined
  have nonzero := initial.head_nonzero φ hz h1 ha hs hm sign
    (fun a => (hsg a).2.2.1) hn hi hnat (fun a => (hsg a).1) (fun a => (hsg a).2.1)
  rw [(Frontier.prepare?_result prepared).1] at nonzero
  have equal : result.rootSet φ hz sign =
      rootsIn (interpret φ hz p) (.finite (φ lower)) (.finite (φ upper)) := by
    ext x
    rw [result.mem_rootSet φ hz h1 ha hs hm sign (fun a => (hsg a).2.2.1)
      hn hi hnat (fun a => (hsg a).1) (fun a => (hsg a).2.1), coverage x,
      mem_rootsIn_iff _ nonzero]
    rfl
  rw [← equal]
  exact result.rootSet_card φ hz h1 ha hs hm sign hn hi hnat hsign disjoint distinct excluded

end Hex.RealClosure.Bisection

/-- info: 'Hex.RealClosure.Bisection.Cell.count_card' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Cell.count_card
/-- info: 'Hex.RealClosure.Bisection.Frontier.rootSet_card' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Frontier.rootSet_card
/-- info: 'Hex.RealClosure.Bisection.Frontier.refine?_count' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Frontier.refine?_count

/-- info: 'Hex.RealClosure.Bisection.Frontier.mem_rootSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Frontier.mem_rootSet
