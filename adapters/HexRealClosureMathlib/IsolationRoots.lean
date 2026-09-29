/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.IsolationRoots
public import HexRealClosureMathlib.Isolation
public import HexRealClosureMathlib.BisectionCounts
public import HexSignDetMathlib.RootList

public section

namespace Hex.RealClosure.Isolation
open HexPolyMathlib.Interpret HexRealRootsMathlib.Tarski

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [DecidableEq Ctx]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K]
variable (φ : E → K) (hz : ∀ a, φ a = 0 ↔ a = 0)
variable (h1 : φ 1 = 1) (ha : ∀ a b, φ (a + b) = φ a + φ b)
variable (hs : ∀ a b, φ (a - b) = φ a - φ b)
variable (hm : ∀ a b, φ (a * b) = φ a * φ b)
variable (hnat : ∀ n : Nat, φ (n : E) = (n : K))
variable {sign : E → Int} (hsign : ∀ a, sign a = (SignType.sign (φ a) : Int))
variable (hn : ∀ a, φ (-a) = -φ a) (hi : ∀ a, φ a⁻¹ = (φ a)⁻¹)

include hz h1 ha hs hm hnat hsign hn hi in
/-- A completed absent domain cannot have a nonzero squarefree mathematical
head. In particular, a failed capped refinement on a valid domain is never
silently reported as absent. -/
theorem complete?_none_invalid {context : Ctx} (p : DensePoly E)
    (absent : complete? sign context p = .ok none) :
    interpret φ hz p = 0 ∨ ¬ Squarefree (interpret φ hz p) := by
  by_contra invalid
  have nonzero : interpret φ hz p ≠ 0 := by
    intro zero
    exact invalid (Or.inl zero)
  have squarefree : Squarefree (interpret φ hz p) := by
    by_contra notSimple
    exact invalid (Or.inr notSimple)
  have total := search?_success φ hz h1 ha hs hm sign hsign hn hi hnat p
    nonzero squarefree
  rw [complete?_none_search absent] at total
  cases total

variable [IsRealClosed K]

/-- Mathematical values of the actual emitted points and root descriptors. -/
@[expose] noncomputable def Output.values {context : Ctx} (roots : Output sign context) : List K :=
  roots.points.map φ ++ roots.descriptors.map
    (fun d => d.root φ hz h1 ha hs hm hnat hsign)

include hz h1 ha hs hm hnat hsign hn hi in
private theorem enumeration_coverage {context : Ctx} {head : DensePoly E}
    {lower upper : Endpoint E} {out : List (SignDet.Descriptor E Ctx sign context)}
    (accepted : SignDet.Descriptor.buildRoots sign context head lower upper = .ok (some out))
    (x : K) :
    x ∈ out.map (fun d => d.root φ hz h1 ha hs hm hnat hsign) ↔
      (interpret φ hz head).IsRoot x ∧ InInterval (lower.map φ) (upper.map φ) x := by
  have coverage := SignDet.Descriptor.buildRoots_coverage φ hz h1 ha hs hm hnat hsign accepted
  have nonzero := (SignDet.Descriptor.buildRoots_domain φ hz h1 ha hs hm hnat hsign hn hi accepted).1
  rw [← coverage.1 x, mem_rootsIn_iff _ nonzero]
  rfl

include hz h1 ha hs hm hnat hsign hn hi in
/-- Retained-domain validity eliminates the absent enumeration result. -/
theorem cell_enumeration_present (context : Ctx) {head : DensePoly E}
    (cell : Bisection.Cell sign head) :
    SignDet.Descriptor.buildRoots sign context head (.finite cell.lower) (.finite cell.upper) ≠ .ok none := by
  have hsg := HexSturmMathlib.sign_spec φ sign hsign
  have valid := cell.domain_valid φ hz h1 ha hs hm sign (fun a => (hsg a).2.2.1)
    hn hi hnat (fun a => (hsg a).1) (fun a => (hsg a).2.1)
  intro absent
  exact (SignDet.Descriptor.buildRoots_none_iff φ hz h1 ha hs hm hnat hsign hn hi
    context head (.finite cell.lower) (.finite cell.upper)).mp absent valid

include hz h1 ha hs hm hnat hsign hn hi in
/-- Whole-line domain validity eliminates the absent enumeration result. -/
theorem Whole.enumeration_present (context : Ctx) {p : DensePoly E} (whole : Whole sign p) :
    SignDet.Descriptor.buildRoots sign context whole.domain.head
      whole.domain.lower whole.domain.upper ≠ .ok none := by
  have valid := whole.domain_valid φ hz h1 ha hs hm sign hsign hn hi hnat
  intro absent
  apply (SignDet.Descriptor.buildRoots_none_iff φ hz h1 ha hs hm hnat hsign hn hi
    context whole.domain.head whole.domain.lower whole.domain.upper).mp absent
  simpa only [whole.bound.2.1, whole.bound.2.2.1, whole.bound.2.2.2] using valid

include hz h1 ha hs hm hnat hsign hn hi in
/-- Count-zero cells are empty, count-one descriptors select their unique
root without derivatives, and unresolved enumeration covers every root once. -/
theorem completeCell_spec (context : Ctx) {head : DensePoly E}
    (cell : Bisection.Cell sign head)
    {out : List (SignDet.Descriptor E Ctx sign context)}
    (accepted : completeCell context cell = .ok out) :
    (∀ x : K, x ∈ out.map (fun d => d.root φ hz h1 ha hs hm hnat hsign) ↔
      (interpret φ hz head).IsRoot x ∧
        InInterval (.finite (φ cell.lower)) (.finite (φ cell.upper)) x) ∧
      (out.map fun d => d.root φ hz h1 ha hs hm hnat hsign).Nodup := by
  have hsg := HexSturmMathlib.sign_spec φ sign hsign
  have nonzero := (cell.domain_valid φ hz h1 ha hs hm sign (fun a => (hsg a).2.2.1)
    hn hi hnat (fun a => (hsg a).1) (fun a => (hsg a).2.1)).1
  by_cases empty : cell.count = 0
  · have output : out = [] := by simpa only [completeCell, empty, ↓reduceIte, Except.ok.injEq] using accepted.symm
    subst out
    have card := cell.count_card φ hz h1 ha hs hm sign hn hi hnat hsign
    have hcard : (rootsIn (interpret φ hz head) (.finite (φ cell.lower))
        (.finite (φ cell.upper))).card = 0 := by
      exact_mod_cast card.symm.trans empty
    have noRoots := Finset.card_eq_zero.mp hcard
    refine ⟨?_, by simp⟩
    intro x
    constructor
    · simp
    · intro root
      have member := (mem_rootsIn_iff _ nonzero _ _ x).mpr root
      simpa [noRoots] using member
  · by_cases single : cell.count = 1
    · let raw : SignDet.RawDescriptor E Ctx :=
        ⟨context, head, .finite cell.lower, .finite cell.upper, [], []⟩
      cases built : SignDet.buildPrepared context cell.domain [] with
      | error error => simp [completeCell, single, built] at accepted
      | ok replay =>
        cases restored : SignDet.Descriptor.ofReplay? sign context raw replay.val with
        | none => simp [completeCell, single, built, raw, restored] at accepted
        | some descriptor =>
          have output : out = [descriptor] := by
            simpa [completeCell, single, built, raw, restored] using accepted.symm
          subst out
          have binding := SignDet.Descriptor.ofReplay_raw restored
          refine ⟨?_, by simp⟩
          intro x
          simp only [List.map_cons, List.map_nil, List.mem_singleton]
          constructor
          · intro same
            subst x
            have root := (descriptor.root_spec φ hz h1 ha hs hm hnat hsign).1
            rw [binding] at root
            exact (mem_rootsIn_iff _ nonzero _ _ _).mp root
          · intro root
            apply descriptor.root_unique φ hz h1 ha hs hm hnat hsign x
            · rw [binding]
              exact (mem_rootsIn_iff _ nonzero _ _ x).mpr root
            · simp [binding, raw, SignDet.RawDescriptor.queries, SignDet.signsAt]
    · cases produced : SignDet.Descriptor.buildRoots sign context head
        (.finite cell.lower) (.finite cell.upper) with
      | error error => simp [completeCell, empty, single, produced] at accepted
      | ok result =>
        cases result with
        | none => simp [completeCell, empty, single, produced] at accepted
        | some roots =>
          have output : out = roots := by
            simpa only [completeCell, empty, single, ↓reduceIte, produced, Except.ok.injEq] using accepted.symm
          subst out
          exact ⟨fun x => by
            simpa only [Endpoint.map] using
              enumeration_coverage φ hz h1 ha hs hm hnat hsign hn hi produced x,
            (SignDet.Descriptor.buildRoots_coverage φ hz h1 ha hs hm hnat hsign produced).2⟩

include hz h1 ha hs hm hnat hsign hn hi in
/-- Completion covers the union of every actual retained open cell. -/
theorem completeCells_coverage (context : Ctx) {head : DensePoly E}
    (cells : List (Bisection.Cell sign head))
    {out : List (SignDet.Descriptor E Ctx sign context)}
    (accepted : completeCells context cells = .ok out) (x : K) :
    x ∈ out.map (fun d => d.root φ hz h1 ha hs hm hnat hsign) ↔
      ∃ cell ∈ cells, (interpret φ hz head).IsRoot x ∧
        InInterval (.finite (φ cell.lower)) (.finite (φ cell.upper)) x := by
  induction cells generalizing out with
  | nil =>
    have empty : out = [] := by simpa only [completeCells, Except.ok.injEq] using accepted.symm
    simp [empty]
  | cons cell cells ih =>
    obtain ⟨roots, rest, produced, remaining, output⟩ := completeCells_cons accepted
    rw [output, List.map_append, List.mem_append,
      (completeCell_spec φ hz h1 ha hs hm hnat hsign hn hi context cell produced).1 x,
      ih remaining]
    simp only [List.mem_cons]
    constructor
    · rintro (root | ⟨other, member, root⟩)
      · exact ⟨cell, Or.inl rfl, root⟩
      · exact ⟨other, Or.inr member, root⟩
    · rintro ⟨other, rfl | member, root⟩
      · exact Or.inl root
      · exact Or.inr ⟨other, member, root⟩

include hz h1 ha hs hm hnat hsign hn hi in
/-- Shared enumeration of disjoint cells cannot emit one mathematical root
more than once, even when the original polynomial has several real roots. -/
theorem completeCells_nodup (context : Ctx) {head : DensePoly E}
    (cells : List (Bisection.Cell sign head))
    {out : List (SignDet.Descriptor E Ctx sign context)}
    (accepted : completeCells context cells = .ok out)
    (disjoint : cells.Pairwise fun a b => ∀ x : K,
      InInterval (.finite (φ a.lower)) (.finite (φ a.upper)) x →
        ¬ InInterval (.finite (φ b.lower)) (.finite (φ b.upper)) x) :
    (out.map fun d => d.root φ hz h1 ha hs hm hnat hsign).Nodup := by
  induction cells generalizing out with
  | nil =>
    have empty : out = [] := by simpa only [completeCells, Except.ok.injEq] using accepted.symm
    simp [empty]
  | cons cell cells ih =>
    obtain ⟨roots, rest, produced, remaining, output⟩ := completeCells_cons accepted
    obtain ⟨separate, disjoint⟩ := List.pairwise_cons.mp disjoint
    rw [output, List.map_append, List.nodup_append]
    refine ⟨(completeCell_spec φ hz h1 ha hs hm hnat hsign hn hi context cell produced).2,
      ih remaining disjoint, ?_⟩
    intro x member y later same
    subst y
    have inside := ((completeCell_spec φ hz h1 ha hs hm hnat hsign hn hi context cell produced).1 x).mp member
    obtain ⟨other, present, _, insideOther⟩ :=
      (completeCells_coverage φ hz h1 ha hs hm hnat hsign hn hi context _ remaining x).mp later
    exact separate other present x inside.2 insideOther

include hz h1 ha hs hm hnat hsign hn hi in
/-- Successful descriptor completion preserves exactly the root values of
its actual capped route, including all previously emitted cut points. -/
theorem Route.complete_coverage {context : Ctx} {p : DensePoly E}
    (route : Route sign p) {out : Output sign context}
    (accepted : route.complete context = .ok out) (x : K) :
    x ∈ out.values φ hz h1 ha hs hm hnat hsign ↔ route.Roots φ hz sign x := by
  cases route with
  | bounded bound frontier =>
    cases produced : completeCells context frontier.cells with
    | error error => simp [Route.complete, produced] at accepted
    | ok roots =>
      have output : out = ⟨frontier.removed, roots⟩ := by
        simpa only [Route.complete, produced, Except.ok.injEq] using accepted.symm
      rw [output]
      simp only [Output.values, List.mem_append]
      rw [completeCells_coverage φ hz h1 ha hs hm hnat hsign hn hi context _ produced x]
      simp only [Route.Roots, Bisection.Frontier.Roots, List.mem_map]
      aesop
  | whole stored =>
    cases produced : SignDet.Descriptor.buildRoots sign context stored.domain.head
        stored.domain.lower stored.domain.upper with
    | error error => simp [Route.complete, produced] at accepted
    | ok result =>
      cases result with
      | none => simp [Route.complete, produced] at accepted
      | some roots =>
        have output : out = ⟨[], roots⟩ := by
          simpa only [Route.complete, produced, Except.ok.injEq] using accepted.symm
        rw [output]
        simpa only [Output.values, List.map_nil, List.nil_append, Route.Roots] using
          enumeration_coverage φ hz h1 ha hs hm hnat hsign hn hi produced x

include hz h1 ha hs hm hnat hsign hn hi in
/-- Every successful actual isolation completion contains exactly all roots
of the original input. Producer totality and global ordering are separate. -/
theorem Completion.coverage {context : Ctx} {p : DensePoly E}
    (completion : Completion sign context p) (x : K) :
    x ∈ completion.roots.values φ hz h1 ha hs hm hnat hsign ↔
      (interpret φ hz p).IsRoot x :=
  (completion.search.route.complete_coverage φ hz h1 ha hs hm hnat hsign hn hi
    completion.computed x).trans
      (completion.search.roots φ hz h1 ha hs hm sign hsign hn hi hnat x)

include hz h1 ha hs hm hnat hsign hn hi in
/-- Actual completion emits each mathematical root exactly once. Bisection
points are excluded from the remaining head and its cells are disjoint. -/
theorem Completion.nodup {context : Ctx} {p : DensePoly E}
    (completion : Completion sign context p) :
    (completion.roots.values φ hz h1 ha hs hm hnat hsign).Nodup := by
  have accepted := completion.computed
  cases route : completion.search.route with
  | bounded bound frontier =>
    rw [route] at accepted
    obtain ⟨_, _, distinct, excluded, disjoint, _⟩ :=
      completion.search.bounded_spec φ hz h1 ha hs hm sign hsign hn hi hnat route
    cases produced : completeCells context frontier.cells with
    | error error => simp [Route.complete, produced] at accepted
    | ok roots =>
      have output : completion.roots = ⟨frontier.removed, roots⟩ := by
        simpa only [Route.complete, produced, Except.ok.injEq] using accepted.symm
      rw [output, Output.values, List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · have pairwise : (frontier.removed.map φ).Pairwise (fun a b => a ≠ b) :=
          List.pairwise_map.mpr distinct
        exact pairwise.nodup
      · apply completeCells_nodup φ hz h1 ha hs hm hnat hsign hn hi context _ produced
        simpa only [Bisection.Frontier.Disjoint, List.pairwise_map] using disjoint
      · intro x member y later same
        subst y
        obtain ⟨point, present, rfl⟩ := List.mem_map.mp member
        obtain ⟨cell, _, root, _⟩ :=
          (completeCells_coverage φ hz h1 ha hs hm hnat hsign hn hi context _ produced
            (φ point)).mp later
        exact excluded point present root
  | whole stored =>
    rw [route] at accepted
    cases produced : SignDet.Descriptor.buildRoots sign context stored.domain.head
        stored.domain.lower stored.domain.upper with
    | error error => simp [Route.complete, produced] at accepted
    | ok result =>
      cases result with
      | none => simp [Route.complete, produced] at accepted
      | some roots =>
        have output : completion.roots = ⟨[], roots⟩ := by
          simpa only [Route.complete, produced, Except.ok.injEq] using accepted.symm
        rw [output]
        simpa only [Output.values, List.map_nil, List.nil_append] using
          (SignDet.Descriptor.buildRoots_coverage φ hz h1 ha hs hm hnat hsign produced).2

end Hex.RealClosure.Isolation

/-- info: 'Hex.RealClosure.Isolation.complete?_none_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Isolation.complete?_none_invalid

/-- info: 'Hex.RealClosure.Isolation.completeCells_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.completeCells_coverage
/-- info: 'Hex.RealClosure.Isolation.Route.complete_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Route.complete_coverage
/-- info: 'Hex.RealClosure.Isolation.Completion.coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Completion.coverage

/-- info: 'Hex.RealClosure.Isolation.completeCells_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.completeCells_nodup
/-- info: 'Hex.RealClosure.Isolation.Completion.nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Completion.nodup

/-- info: 'Hex.RealClosure.Isolation.completeCell_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.completeCell_spec
/-- info: 'Hex.RealClosure.Isolation.cell_enumeration_present' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.cell_enumeration_present
/-- info: 'Hex.RealClosure.Isolation.Whole.enumeration_present' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Whole.enumeration_present
