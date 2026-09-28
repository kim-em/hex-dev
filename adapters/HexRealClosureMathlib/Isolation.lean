/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Isolation
public import HexSturmMathlib.Soundness
public import HexRealClosureMathlib.Bounds
public import HexRealClosureMathlib.BisectionFrontier

public section

namespace Hex.RealClosure.Isolation
open HexPolyMathlib.Interpret HexSturmMathlib HexRealRootsMathlib.Tarski

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K]
variable (φ : E → K) (hz : ∀ a, φ a = 0 ↔ a = 0)
variable (h1 : φ 1 = 1) (ha : ∀ a b, φ (a + b) = φ a + φ b)
variable (hs : ∀ a b, φ (a - b) = φ a - φ b)
variable (hm : ∀ a b, φ (a * b) = φ a * φ b)
variable (sign : E → Int) (hsign : ∀ a, sign a = (SignType.sign (φ a) : Int))
variable (hn : ∀ a, φ (-a) = -φ a) (hi : ∀ a, φ a⁻¹ = (φ a)⁻¹)
variable (hnat : ∀ n : Nat, φ (n : E) = (n : K))

include hz h1 ha hs hm hn hi hnat hsign in
/-- Whole-line preparation succeeds exactly for nonzero squarefree input.
Infinite endpoints require no finite coefficient bound. -/
theorem Whole.prepare?_success (p : DensePoly E) :
    (Whole.prepare? sign p).isSome = true ↔
      interpret φ hz p ≠ 0 ∧ Squarefree (interpret φ hz p) := by
  have hsg := sign_spec φ sign hsign
  rw [Whole.prepare?_isSome, prepare_isSome φ hz ha hs hm sign
    (fun a => (hsg a).2.1) (fun a => (hsg a).2.2.1) h1 hn hi hnat
    (fun a => (hsg a).1)]
  simp [Domain, EndpointLt, Nonvanishing]

include hz h1 ha hs hm hn hi hnat hsign in
/-- The prescribed bounded-or-whole-line dispatch succeeds on every nonzero
squarefree polynomial under coefficient interpretation. This theorem concerns
preparation and capped refinement, not descriptor enumeration. -/
theorem dispatch?_success (p : DensePoly E)
    (nonzero : interpret φ hz p ≠ 0) (squarefree : Squarefree (interpret φ hz p)) :
    (dispatch? sign p).isSome = true := by
  have hsg := sign_spec φ sign hsign
  unfold dispatch?
  split
  · have total := (Whole.prepare?_success φ hz h1 ha hs hm sign hsign hn hi hnat p).mpr
      ⟨nonzero, squarefree⟩
    cases h : Whole.prepare? sign p with
    | none => simp [h] at total
    | some whole => rfl
  · rename_i bound _
    have domain := bound.domain φ hz h1 hn hs hm sign hsign p squarefree
    have total := (Bisection.Cell.prepare?_success φ hz h1 ha hs hm sign
      (fun a => (hsg a).2.2.1) hn hi hnat (fun a => (hsg a).1)
      (fun a => (hsg a).2.1) p (-bound.value) bound.value).mpr domain
    cases hcell : Bisection.Cell.prepare? sign p (-bound.value) bound.value with
    | none => simp [hcell] at total
    | some cell =>
      have initial : (Bisection.Frontier.prepare? sign p (-bound.value) bound.value).isSome = true := by
        rw [Bisection.Frontier.prepare?_isSome, hcell]
        rfl
      cases hp : Bisection.Frontier.prepare? sign p (-bound.value) bound.value with
      | none => simp [hp] at initial
      | some frontier =>
        have refined := frontier.refine?_success φ hz h1 ha hs hm sign
          (fun a => (hsg a).2.2.1) hn hi hnat (fun a => (hsg a).1) (fun a => (hsg a).2.1)
        cases hr : frontier.refine? with
        | none => simp [hr] at refined
        | some result => simp [hr]

include hz h1 ha hs hm hn hi hnat hsign in
/-- The checked search wrapper succeeds on the same nonzero squarefree input. -/
theorem search?_success (p : DensePoly E)
    (nonzero : interpret φ hz p ≠ 0) (squarefree : Squarefree (interpret φ hz p)) :
    (search? sign p).isSome = true := by
  rw [search?_isSome]
  exact dispatch?_success φ hz h1 ha hs hm sign hsign hn hi hnat p nonzero squarefree

/-- Mathematical roots awaiting descriptor completion in a returned route. -/
@[expose] def Route.Roots {p : DensePoly E} (route : Route sign p) (x : K) : Prop :=
  match route with
  | .bounded _ frontier => frontier.Roots φ hz sign x
  | .whole _ => (interpret φ hz p).IsRoot x

include hz h1 ha hs hm hn hi hnat hsign in
/-- Every checked search retains exactly all roots of its original polynomial,
including when the finite coefficient bound search fails. -/
theorem Search.roots {p : DensePoly E} (result : Search sign p) (x : K) :
    result.route.Roots φ hz sign x ↔ (interpret φ hz p).IsRoot x := by
  have hsg := sign_spec φ sign hsign
  cases route : result.route with
  | whole whole => rfl
  | bounded bound frontier =>
    have computed := result.computed
    rw [route] at computed
    obtain ⟨_, initial, prepared, refined⟩ := dispatch?_bounded computed
    obtain ⟨_, coverage, _⟩ := Bisection.Frontier.refine?_spec φ hz h1 ha hs hm sign
      (fun a => (hsg a).2.2.1) hn hi hnat (fun a => (hsg a).1)
      (fun a => (hsg a).2.1) prepared refined
    change frontier.Roots φ hz sign x ↔ _
    rw [coverage x]
    constructor
    · exact And.left
    · intro root
      obtain ⟨lower, upper⟩ := (bound.roots φ hz h1 hn hs hm sign hsign p).2 x root
      refine ⟨root, ?_⟩
      simpa only [inInterval_finite, hn] using And.intro lower upper

include hz h1 ha hs hm hn hi hnat hsign in
/-- The stored whole-line domain is admissible for its exact input. -/
theorem Whole.domain_valid {p : DensePoly E} (whole : Whole sign p) :
    Domain φ hz p .negInf .posInf := by
  have hsg := sign_spec φ sign hsign
  have valid := prepared_domain φ hz ha hs hm sign (fun a => (hsg a).2.1)
    (fun a => (hsg a).2.2.1) h1 hn hi hnat (fun a => (hsg a).1)
    whole.domain whole.bound.1
  simpa only [whole.bound.2.1, whole.bound.2.2.1, whole.bound.2.2.2] using valid

end Hex.RealClosure.Isolation

/-- info: 'Hex.RealClosure.Isolation.Whole.prepare?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Whole.prepare?_success
/-- info: 'Hex.RealClosure.Isolation.dispatch?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.dispatch?_success
/-- info: 'Hex.RealClosure.Isolation.search?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.search?_success
/-- info: 'Hex.RealClosure.Isolation.Search.roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Search.roots
/-- info: 'Hex.RealClosure.Isolation.Whole.domain_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Whole.domain_valid
