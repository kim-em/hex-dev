/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.IsolationRoots
public import HexSignDetTheory.ThomRoots

public section

namespace Hex.RealClosure.Isolation
open HexPolyTheory.Interpret HexRealRootsTheory

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [DecidableEq Ctx]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (φ : E → K) (hz : ∀ a, φ a = 0 ↔ a = 0)
variable (h1 : φ 1 = 1) (ha : ∀ a b, φ (a + b) = φ a + φ b)
variable (hs : ∀ a b, φ (a - b) = φ a - φ b)
variable (hm : ∀ a b, φ (a * b) = φ a * φ b)
variable (hnat : ∀ n : Nat, φ (n : E) = (n : K))
variable {sign : E → Int} (hsign : ∀ a, sign a = (SignType.sign (φ a) : Int))
variable (hn : ∀ a, φ (-a) = -φ a) (hi : ∀ a, φ a⁻¹ = (φ a)⁻¹)

include hz h1 ha hs hm hnat hsign hn hi in
/-- Every retained cell has a successful actual completion. Count-one cells
reuse their prepared domain with no derivative queries; other nonempty cells
consume the shared universal enumeration theorem. -/
theorem completeCell_success (context : Ctx) {head : DensePoly E}
    (cell : Bisection.Cell sign head) :
    ∃ roots, completeCell context cell = .ok roots := by
  by_cases empty : cell.count = 0
  · exact ⟨[], by simp [completeCell, empty]⟩
  have hsg := HexSturmTheory.sign_spec φ sign hsign
  have domain := cell.domain_valid φ hz h1 ha hs hm sign (fun a => (hsg a).2.2.1)
    hn hi hnat (fun a => (hsg a).1) (fun a => (hsg a).2.1)
  by_cases single : cell.count = 1
  · let raw : SignDet.RawDescriptor E Ctx :=
      ⟨context, head, .finite cell.lower, .finite cell.upper, [], []⟩
    obtain ⟨replay, built, _⟩ := SignDet.buildPrepared_roots φ hz h1 ha hs hm hnat
      hn hi sign hsign context cell.domain cell.bound.1 [] true
    have checked : replay.val.check sign context head
        (.finite cell.lower) (.finite cell.upper) raw.queries = true := by
      simpa only [raw, SignDet.RawDescriptor.queries, List.map_nil,
        cell.bound.1, cell.bound.2.1, cell.bound.2.2.1, cell.bound.2.2.2] using replay.property
    have cardinal : (Tarski.rootsIn (interpret φ hz head)
        (.finite (φ cell.lower)) (.finite (φ cell.upper))).card = 1 := by
      exact_mod_cast (cell.count_card φ hz h1 ha hs hm sign hn hi hnat hsign).symm.trans single
    have degree : 0 < head.natDegree := by
      have bound := Tarski.rootsIn_card_le (interpret φ hz head)
        (.finite (φ cell.lower)) (.finite (φ cell.upper))
      rw [cardinal, natDegree_interpret] at bound
      omega
    have formed : raw.wellFormed = true := by
      simp [raw, SignDet.RawDescriptor.wellFormed, degree]
    have count : (replay.val.table checked).count raw.signs = 1 := by
      rw [SignDet.Replay.table_lookup,
        replay.val.count_roots φ hz h1 ha hs hm hnat sign hsign context head
          (.finite cell.lower) (.finite cell.upper) raw.queries checked raw.signs]
      simpa [raw, SignDet.RawDescriptor.queries, SignDet.signsAt, Endpoint.map] using cardinal
    let descriptor := SignDet.Descriptor.ofTable raw replay.val formed rfl checked count
    have restored : SignDet.Descriptor.ofReplay? sign context
        ⟨context, head, .finite cell.lower, .finite cell.upper, [], []⟩ replay.val =
        some descriptor :=
      SignDet.Descriptor.ofReplay_ofTable raw replay.val formed rfl checked count
    exact ⟨[descriptor], by simp [completeCell, empty, single, built, restored]⟩
  · obtain ⟨roots, built⟩ := SignDet.Descriptor.buildRoots_success φ hz h1 ha hs hm hnat
      hsign hn hi context head (.finite cell.lower) (.finite cell.upper) domain
    exact ⟨roots, by simp [completeCell, empty, single, built]⟩

include hz h1 ha hs hm hnat hsign hn hi in
/-- Completing any finite list of retained cells succeeds in predecessor
order using their actual prepared domains. -/
theorem completeCells_success (context : Ctx) {head : DensePoly E}
    (cells : List (Bisection.Cell sign head)) :
    ∃ roots, completeCells context cells = .ok roots := by
  induction cells with
  | nil => exact ⟨[], rfl⟩
  | cons cell cells ih =>
    obtain ⟨first, built⟩ := completeCell_success φ hz h1 ha hs hm hnat hsign hn hi context cell
    obtain ⟨rest, remaining⟩ := ih
    exact ⟨first ++ rest, by simp [completeCells, built, remaining]⟩

include hz h1 ha hs hm hnat hsign hn hi in
/-- Both actual isolation routes complete successfully. The whole-line
fallback requires no finite coefficient bound or rational separation. -/
theorem Route.complete_success {p : DensePoly E} (context : Ctx) (route : Route sign p) :
    ∃ roots, route.complete context = .ok roots := by
  cases route with
  | bounded bound frontier =>
    obtain ⟨roots, built⟩ :=
      completeCells_success φ hz h1 ha hs hm hnat hsign hn hi context frontier.cells
    exact ⟨⟨frontier.removed, roots⟩, by simp [Route.complete, built]⟩
  | whole stored =>
    have domain : HexSturmTheory.Domain φ hz stored.domain.head
        stored.domain.lower stored.domain.upper := by
      simpa only [stored.bound.2.1, stored.bound.2.2.1, stored.bound.2.2.2] using
        stored.domain_valid φ hz h1 ha hs hm sign hsign hn hi hnat
    obtain ⟨roots, built⟩ := SignDet.Descriptor.buildRoots_success φ hz h1 ha hs hm hnat
      hsign hn hi context stored.domain.head stored.domain.lower stored.domain.upper domain
    exact ⟨⟨[], roots⟩, by simp [Route.complete, built]⟩

include hz h1 ha hs hm hnat hsign hn hi in
/-- Every nonzero squarefree polynomial has an actual successful capped
isolation result. No successful producer output is a hypothesis. -/
theorem complete?_success (context : Ctx) (p : DensePoly E)
    (nonzero : interpret φ hz p ≠ 0) (squarefree : Squarefree (interpret φ hz p)) :
    ∃ result, complete? sign context p = .ok (some result) := by
  have success := search?_success φ hz h1 ha hs hm sign hsign hn hi hnat p nonzero squarefree
  cases searched : search? sign p with
  | none => simp [searched] at success
  | some search =>
    obtain ⟨roots, completed⟩ :=
      search.route.complete_success φ hz h1 ha hs hm hnat hsign hn hi context
    exact complete?_of_search search searched roots completed

end Hex.RealClosure.Isolation

/-- info: 'Hex.RealClosure.Isolation.completeCell_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.completeCell_success

/-- info: 'Hex.RealClosure.Isolation.complete?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.complete?_success
