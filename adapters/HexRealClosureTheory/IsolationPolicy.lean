/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.IsolationPolicy
public import HexRealClosureTheory.IsolationTotal

public section

namespace Hex.RealClosure.Isolation.Policy
open HexPolyTheory.Interpret HexRealRootsTheory HexRealRootsTheory.Tarski

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (φ : E → K) (hz : ∀ a, φ a = 0 ↔ a = 0)
variable (h1 : φ 1 = 1) (ha : ∀ a b, φ (a + b) = φ a + φ b)
variable (hs : ∀ a b, φ (a - b) = φ a - φ b)
variable (hm : ∀ a b, φ (a * b) = φ a * φ b)
variable (sign : E → Int) (hsign : ∀ a, sign a = (SignType.sign (φ a) : Int))
variable (hn : ∀ a, φ (-a) = -φ a) (hi : ∀ a, φ a⁻¹ = (φ a)⁻¹)
variable (hnat : ∀ n : Nat, φ (n : E) = (n : K))

include hz h1 ha hs hm hn hi hnat hsign in
/-- Every permitted finite policy dispatches every nonzero squarefree input.
Omitting an optimization never adds a coefficient precision requirement. -/
theorem dispatch?_success (policy : Policy) (p : DensePoly E)
    (nonzero : interpret φ hz p ≠ 0) (squarefree : Squarefree (interpret φ hz p)) :
    (policy.dispatch? sign p).isSome = true := by
  have standard := Isolation.dispatch?_success φ hz h1 ha hs hm sign hsign hn hi hnat p nonzero squarefree
  have whole := (Whole.prepare?_success φ hz h1 ha hs hm sign hsign hn hi hnat p).mpr
    ⟨nonzero, squarefree⟩
  cases policy with
  | standard => exact standard
  | whole => simpa only [dispatch?, Option.isSome_map] using whole
  | bounded =>
    unfold dispatch?
    cases bound : Bounds.find? sign p with
    | none => simpa only [Option.isSome_map] using whole
    | some b =>
      cases prepared : Bisection.Frontier.prepare? sign p (-b.value) b.value with
      | none => simp [Isolation.dispatch?, bound, prepared] at standard
      | some frontier => simp [prepared]

include hz h1 ha hs hm hn hi hnat hsign in
private theorem standard_roots (p : DensePoly E) (route : Route sign p)
    (returned : Isolation.dispatch? sign p = some route) (x : K) :
    route.Roots φ hz sign x ↔ (interpret φ hz p).IsRoot x := by
  have present : (Isolation.search? sign p).isSome = true := by
    rw [Isolation.search?_isSome, returned]
    rfl
  cases searched : Isolation.search? sign p with
  | none => simp [searched] at present
  | some search =>
    have same := Option.some.inj (search.computed.symm.trans returned)
    rw [← same]
    exact search.roots φ hz h1 ha hs hm sign hsign hn hi hnat x

private theorem whole_roots (p : DensePoly E) (whole : Whole sign p) (x : K) :
    (Route.whole whole).Roots φ hz sign x ↔ (interpret φ hz p).IsRoot x := by
  change (interpret φ hz whole.domain.head).IsRoot x ∧
    InInterval (whole.domain.lower.map φ) (whole.domain.upper.map φ) x ↔ _
  rw [whole.bound.2.1, whole.bound.2.2.1, whole.bound.2.2.2]
  simp only [Endpoint.map, inInterval_univ, and_true]

include hz h1 ha hs hm hn hi hnat hsign in
/-- The actual retained route covers precisely the original polynomial's
roots for every permitted choice, including whole-line BKR alone. -/
theorem dispatch?_roots (policy : Policy) (p : DensePoly E) (route : Route sign p)
    (returned : policy.dispatch? sign p = some route) (x : K) :
    route.Roots φ hz sign x ↔ (interpret φ hz p).IsRoot x := by
  cases policy with
  | standard => exact standard_roots φ hz h1 ha hs hm sign hsign hn hi hnat p route returned x
  | whole =>
    cases prepared : Whole.prepare? sign p with
    | none => simp [dispatch?, prepared] at returned
    | some whole =>
      have same : route = .whole whole := by simpa [dispatch?, prepared] using returned.symm
      rw [same]
      exact whole_roots φ hz sign p whole x
  | bounded =>
    cases bound : Bounds.find? sign p with
    | none =>
      cases prepared : Whole.prepare? sign p with
      | none => simp [dispatch?, bound, prepared] at returned
      | some whole =>
        have same : route = .whole whole := by simpa [dispatch?, bound, prepared] using returned.symm
        rw [same]
        exact whole_roots φ hz sign p whole x
    | some b =>
      cases prepared : Bisection.Frontier.prepare? sign p (-b.value) b.value with
      | none => simp [dispatch?, bound, prepared] at returned
      | some frontier =>
        have same : route = .bounded b frontier := by
          simpa [dispatch?, bound, prepared] using returned.symm
        rw [same]
        change frontier.Roots φ hz sign x ↔ _
        rw [Bisection.Frontier.prepare?_roots φ hz sign prepared x]
        constructor
        · exact And.left
        · intro root
          obtain ⟨lower, upper⟩ := (b.roots φ hz h1 hn hs hm sign hsign p).2 x root
          exact ⟨root, by simpa only [inInterval_finite, hn] using And.intro lower upper⟩

variable {Ctx : Type w} [DecidableEq Ctx]

include hz h1 ha hs hm hn hi hnat hsign in
/-- Every policy completes the same lawful squarefree isolation domain,
including the policy that omits both finite optimizations. -/
theorem complete?_success (policy : Policy) (context : Ctx) (p : DensePoly E)
    (nonzero : interpret φ hz p ≠ 0) (squarefree : Squarefree (interpret φ hz p)) :
    ∃ out, policy.complete? sign context p = .ok (some out) := by
  have total := dispatch?_success φ hz h1 ha hs hm sign hsign hn hi hnat policy p nonzero squarefree
  cases policy with
  | standard =>
    obtain ⟨out, built⟩ := Isolation.complete?_success φ hz h1 ha hs hm hnat hsign hn hi
      context p nonzero squarefree
    exact ⟨out.roots, by simp [Except.map, complete?, built]⟩
  | bounded =>
    cases dispatched : dispatch? .bounded sign p with
    | none => simp [dispatched] at total
    | some route =>
      obtain ⟨out, built⟩ := route.complete_success φ hz h1 ha hs hm hnat hsign hn hi context
      exact ⟨out, by simp [Except.map, complete?, dispatched, built]⟩
  | whole =>
    cases dispatched : dispatch? .whole sign p with
    | none => simp [dispatched] at total
    | some route =>
      obtain ⟨out, built⟩ := route.complete_success φ hz h1 ha hs hm hnat hsign hn hi context
      exact ⟨out, by simp [Except.map, complete?, dispatched, built]⟩

include hz h1 ha hs hm hn hi hnat hsign in
/-- Actual complete outputs cover exactly the original roots, regardless
of the permitted optimization choices. No success is merely assumed by the
ordinary operation: `complete?_success` supplies it under the field laws. -/
theorem complete?_coverage (policy : Policy) (context : Ctx) (p : DensePoly E)
    (out : Output sign context) (built : policy.complete? sign context p = .ok (some out)) (x : K) :
    x ∈ out.values φ hz h1 ha hs hm hnat hsign ↔ (interpret φ hz p).IsRoot x := by
  cases policy with
  | standard =>
    cases produced : Isolation.complete? sign context p with
    | error error => simp [Except.map, complete?, produced] at built
    | ok result =>
      cases result with
      | none => simp [Except.map, complete?, produced] at built
      | some completion =>
        have same : out = completion.roots := by simpa [Except.map, complete?, produced] using built.symm
        rw [same]
        exact completion.coverage φ hz h1 ha hs hm hnat hsign hn hi x
  | bounded =>
    cases dispatched : dispatch? .bounded sign p with
    | none => simp [Except.map, complete?, dispatched] at built
    | some route =>
      cases completed : route.complete context with
      | error error => simp [Except.map, complete?, dispatched, completed] at built
      | ok result =>
        have same : out = result := by simpa [Except.map, complete?, dispatched, completed] using built.symm
        rw [same]
        exact (route.complete_coverage φ hz h1 ha hs hm hnat hsign hn hi completed x).trans
          (dispatch?_roots φ hz h1 ha hs hm sign hsign hn hi hnat .bounded p route dispatched x)
  | whole =>
    cases dispatched : dispatch? .whole sign p with
    | none => simp [Except.map, complete?, dispatched] at built
    | some route =>
      cases completed : route.complete context with
      | error error => simp [Except.map, complete?, dispatched, completed] at built
      | ok result =>
        have same : out = result := by simpa [Except.map, complete?, dispatched, completed] using built.symm
        rw [same]
        exact (route.complete_coverage φ hz h1 ha hs hm hnat hsign hn hi completed x).trans
          (dispatch?_roots φ hz h1 ha hs hm sign hsign hn hi hnat .whole p route dispatched x)

include hz h1 ha hs hm hn hi hnat hsign in
private theorem whole_nodup (context : Ctx) (p : DensePoly E)
    (stored : Whole sign p) (out : Output sign context)
    (built : (Route.whole stored).complete context = .ok out) :
    (out.values φ hz h1 ha hs hm hnat hsign).Nodup := by
  cases produced : SignDet.Descriptor.buildRoots sign context stored.domain.head
      stored.domain.lower stored.domain.upper with
  | error error => simp [Route.complete, produced] at built
  | ok result =>
    cases result with
    | none => simp [Route.complete, produced] at built
    | some roots =>
      have same : out = ⟨[], roots⟩ := by simpa [Route.complete, produced] using built.symm
      rw [same]
      simpa only [Output.values, List.map_nil, List.nil_append] using
        (SignDet.Descriptor.buildRoots_coverage φ hz h1 ha hs hm hnat hsign produced).2

include hz h1 ha hs hm hn hi hnat hsign in
private theorem bounded_nodup (context : Ctx) (p : DensePoly E)
    (bound : Bounds.Bound sign p) (frontier : Bisection.Frontier sign)
    (prepared : Bisection.Frontier.prepare? sign p (-bound.value) bound.value = some frontier)
    (out : Output sign context) (built : (Route.bounded bound frontier).complete context = .ok out) :
    (out.values φ hz h1 ha hs hm hnat hsign).Nodup := by
  obtain ⟨_, removed, _, coords⟩ := Bisection.Frontier.prepare?_result prepared
  cases produced : completeCells context frontier.cells with
  | error error => simp [Route.complete, produced] at built
  | ok roots =>
    have same : out = ⟨frontier.removed, roots⟩ := by simpa [Route.complete, produced] using built.symm
    rw [same, Output.values, removed, List.map_nil, List.nil_append]
    apply completeCells_nodup φ hz h1 ha hs hm hnat hsign hn hi context _ produced
    simpa only [Bisection.Frontier.Disjoint, List.pairwise_map] using
      (show frontier.Disjoint φ sign from by simp [Bisection.Frontier.Disjoint, coords])

include hz h1 ha hs hm hn hi hnat hsign in
/-- Omitting bisection or finite bounds still emits every root exactly once. -/
theorem complete?_nodup (policy : Policy) (context : Ctx) (p : DensePoly E)
    (out : Output sign context) (built : policy.complete? sign context p = .ok (some out)) :
    (out.values φ hz h1 ha hs hm hnat hsign).Nodup := by
  cases policy with
  | standard =>
    cases produced : Isolation.complete? sign context p with
    | error error => simp [Except.map, complete?, produced] at built
    | ok result =>
      cases result with
      | none => simp [Except.map, complete?, produced] at built
      | some completion =>
        have same : out = completion.roots := by simpa [Except.map, complete?, produced] using built.symm
        rw [same]
        exact completion.nodup φ hz h1 ha hs hm hnat hsign hn hi
  | whole =>
    cases prepared : Whole.prepare? sign p with
    | none => simp [complete?, dispatch?, prepared] at built
    | some stored =>
      have completed : (Route.whole stored).complete context = .ok out := by
        cases result : (Route.whole stored).complete context <;>
          simp_all [complete?, dispatch?, Except.map]
      exact whole_nodup φ hz h1 ha hs hm sign hsign hn hi hnat context p stored out completed
  | bounded =>
    cases bound : Bounds.find? sign p with
    | none =>
      cases prepared : Whole.prepare? sign p with
      | none => simp [complete?, dispatch?, bound, prepared] at built
      | some stored =>
        have completed : (Route.whole stored).complete context = .ok out := by
          cases result : (Route.whole stored).complete context <;>
            simp_all [complete?, dispatch?, Except.map]
        exact whole_nodup φ hz h1 ha hs hm sign hsign hn hi hnat context p stored out completed
    | some b =>
      cases prepared : Bisection.Frontier.prepare? sign p (-b.value) b.value with
      | none => simp [complete?, dispatch?, bound, prepared] at built
      | some frontier =>
        have completed : (Route.bounded b frontier).complete context = .ok out := by
          cases result : (Route.bounded b frontier).complete context <;>
            simp_all [complete?, dispatch?, Except.map]
        exact bounded_nodup φ hz h1 ha hs hm sign hsign hn hi hnat context p b frontier prepared out completed

include hz h1 ha hs hm hn hi hnat hsign in
/-- Changing the permitted policy preserves the exact mathematical root set. -/
theorem complete?_agreement (left right : Policy) (context : Ctx) (p : DensePoly E)
    (a b : Output sign context) (first : left.complete? sign context p = .ok (some a))
    (second : right.complete? sign context p = .ok (some b)) (x : K) :
    x ∈ a.values φ hz h1 ha hs hm hnat hsign ↔ x ∈ b.values φ hz h1 ha hs hm hnat hsign :=
  (complete?_coverage φ hz h1 ha hs hm sign hsign hn hi hnat left context p a first x).trans
    (complete?_coverage φ hz h1 ha hs hm sign hsign hn hi hnat right context p b second x).symm

/-- info: 'Hex.RealClosure.Isolation.Policy.complete?_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Policy.complete?_nodup

/-- info: 'Hex.RealClosure.Isolation.Policy.complete?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Policy.complete?_success

/-- info: 'Hex.RealClosure.Isolation.Policy.complete?_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Policy.complete?_agreement

/-- info: 'Hex.RealClosure.Isolation.Policy.dispatch?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Policy.dispatch?_success

/-- info: 'Hex.RealClosure.Isolation.Policy.dispatch?_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Policy.dispatch?_roots

end Hex.RealClosure.Isolation.Policy
