/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Bisection
public import HexRealClosureTheory.Deflation

public section

namespace Hex.RealClosure.Bisection
open HexPolyTheory.Interpret HexSturmTheory

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K]
variable (φ : E → K) (hz : ∀ a, φ a = 0 ↔ a = 0)
variable (h1 : φ 1 = 1) (ha : ∀ a b, φ (a + b) = φ a + φ b)
variable (hs : ∀ a b, φ (a - b) = φ a - φ b)
variable (hm : ∀ a b, φ (a * b) = φ a * φ b)
variable (sign : E → Int) (hzero : ∀ a, sign a = 0 ↔ φ a = 0)

include hz h1 hs hm ha hzero in
omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Native classification succeeds for every point of a nonzero polynomial. -/
theorem Mode.read?_success (p : DensePoly E) (point : E) (hp : interpret φ hz p ≠ 0) :
    (Mode.read? sign p point).isSome = true := by
  unfold Mode.read?
  split
  · rename_i hr
    have hroot : (interpret φ hz p).IsRoot (φ point) := by
      rw [Polynomial.IsRoot.def, eval_interpret φ hz ha hm]
      exact (hzero _).mp hr
    have hd := (deflate?_success φ hz h1 hs hm p point).mpr ⟨hp, hroot⟩
    simpa using hd
  · rfl

include hz h1 hs hm ha hzero in
/-- The active head admits both new open domains. Deflation excludes the cut
root without dropping any other roots or retaining stale endpoint evidence. -/
theorem Mode.domains {p : DensePoly E} {point : E} (mode : Mode sign p point)
    (lower upper : Endpoint E) (domain : Domain φ hz p lower upper)
    (hl : EndpointLt φ lower (.finite point)) (hu : EndpointLt φ (.finite point) upper) :
    Domain φ hz mode.head lower (.finite point) ∧
      Domain φ hz mode.head (.finite point) upper := by
  cases mode with
  | regular nonroot =>
    have hn : Nonvanishing φ (interpret φ hz p) (.finite point) := by
      change (interpret φ hz p).eval (φ point) ≠ 0
      rw [eval_interpret φ hz ha hm]
      exact fun h => nonroot ((hzero _).mpr h)
    exact ⟨⟨domain.1, domain.2.1, hl, domain.2.2.2.1, hn⟩,
      ⟨domain.1, domain.2.1, hu, hn, domain.2.2.2.2⟩⟩
  | root d => exact d.domains φ hz h1 hs hm lower upper domain hl hu

variable [NatCast E] [Neg E] [Inv E]
variable (hn : ∀ a, φ (-a) = -φ a) (hi : ∀ a, φ a⁻¹ = (φ a)⁻¹)
variable (hnat : ∀ n : Nat, φ (n : E) = (n : K))
variable (hpos : ∀ a, sign a = 1 ↔ 0 < φ a) (hneg : ∀ a, sign a < 0 ↔ φ a < 0)

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- Both actual fresh preparations succeed at every strictly interior cut of
an admissible input. No field laws are imposed on native stored syntax. -/
theorem split?_success (p : DensePoly E) (lower upper : Endpoint E) (point : E)
    (domain : Domain φ hz p lower upper)
    (hl : EndpointLt φ lower (.finite point)) (hu : EndpointLt φ (.finite point) upper) :
    (split? sign p lower upper point).isSome = true := by
  have hleft := (endpoint_lt φ hs sign hneg lower (.finite point)).mpr hl
  have hright := (endpoint_lt φ hs sign hneg (.finite point) upper).mpr hu
  rw [split?_isSome]
  have hmodes := Mode.read?_success φ hz h1 ha hs hm sign hzero p point domain.1
  cases hc : Mode.read? sign p point with
  | none => simp [hc] at hmodes
  | some mode =>
    obtain ⟨dl, dr⟩ := mode.domains φ hz h1 ha hs hm sign hzero lower upper domain hl hu
    have hdl := (prepare_isSome φ hz ha hs hm sign hneg hzero h1 hn hi hnat hpos
      mode.head lower (.finite point)).mpr dl
    have hdr := (prepare_isSome φ hz ha hs hm sign hneg hzero h1 hn hi hnat hpos
      mode.head (.finite point) upper).mpr dr
    exact ⟨hleft, hright, mode, rfl, hdl, hdr⟩

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- Every returned split owns two semantically admissible domains bound to
its actual active head, even without a caller-supplied domain premise. -/
theorem Split.domains {p : DensePoly E} {lower upper : Endpoint E} {point : E}
    (split : Split sign p lower upper point) :
    Domain φ hz split.mode.head lower (.finite point) ∧
      Domain φ hz split.mode.head (.finite point) upper := by
  have hl := prepared_domain φ hz ha hs hm sign hneg hzero h1 hn hi hnat hpos
    split.left split.left_bound.1
  have hr := prepared_domain φ hz ha hs hm sign hneg hzero h1 hn hi hnat hpos
    split.right split.right_bound.1
  constructor
  · simpa only [split.left_bound.2.1, split.left_bound.2.2.1, split.left_bound.2.2.2] using hl
  · simpa only [split.right_bound.2.1, split.right_bound.2.2.1, split.right_bound.2.2.2] using hr

include h1 ha hm hi in
omit [Zero E] [DecidableEq E] [Sub E] [DecidableEq K] [LinearOrder K]
  [IsStrictOrderedRing K] [NatCast E] [Neg E] in
/-- The native midpoint denotes the ordered-field arithmetic mean. -/
theorem midpoint_value (lower upper : E) :
    φ (midpoint lower upper) = (φ lower + φ upper) / 2 := by
  simp only [midpoint, hm, ha, hi, h1, one_add_one_eq_two, div_eq_mul_inv]

include hz h1 ha hs hm hzero hn hi hnat hpos hneg in
/-- Every finite admissible interval admits its actual deterministic split. -/
theorem bisect?_success (p : DensePoly E) (lower upper : E)
    (domain : Domain φ hz p (.finite lower) (.finite upper)) :
    (bisect? sign p lower upper).isSome = true := by
  apply split?_success φ hz h1 ha hs hm sign hzero hn hi hnat hpos hneg _ _ _ _ domain
  · change φ lower < φ (midpoint lower upper)
    rw [midpoint_value φ h1 ha hm hi]
    exact left_lt_add_div_two.mpr domain.2.2.1
  · change φ (midpoint lower upper) < φ upper
    rw [midpoint_value φ h1 ha hm hi]
    exact add_div_two_lt_right.mpr domain.2.2.1

end Hex.RealClosure.Bisection

/-- info: 'Hex.RealClosure.Bisection.Mode.read?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Mode.read?_success

/-- info: 'Hex.RealClosure.Bisection.Mode.domains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Mode.domains

/-- info: 'Hex.RealClosure.Bisection.split?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.split?_success

/-- info: 'Hex.RealClosure.Bisection.midpoint_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.midpoint_value

/-- info: 'Hex.RealClosure.Bisection.bisect?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.bisect?_success

/-- info: 'Hex.RealClosure.Bisection.Split.domains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Split.domains
