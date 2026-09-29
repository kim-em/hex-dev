/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Isolation
public import HexRealClosureMathlib.BisectionFactor

public section

namespace Hex.RealClosure.Isolation
open HexPolyMathlib.Interpret Bisection

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E]
variable [Field K] [DecidableEq K]
variable (φ : E → K) (hz : ∀ a, φ a = 0 ↔ a = 0)
variable (h1 : φ 1 = 1) (hs : ∀ a b, φ (a - b) = φ a - φ b)
variable (hm : ∀ a b, φ (a * b) = φ a * φ b)

include hz h1 hs hm in
/-- A checked bounded search retains exact deflation provenance, including
the original scalar, through its actual dispatcher and returned frontier. -/
theorem Search.bounded_factor {sign : E → Int} {p : DensePoly E}
    (result : Search sign p) {bound : Bounds.Bound sign p} {frontier : Frontier sign}
    (route : result.route = .bounded bound frontier) :
    interpret φ hz p = rootProduct φ frontier.removed * interpret φ hz frontier.head := by
  have computed := result.computed
  rw [route] at computed
  obtain ⟨_, initial, prepared, refined⟩ := dispatch?_bounded computed
  exact Frontier.refine?_factor φ hz h1 hs hm prepared refined

include hz h1 hs hm in
/-- Descriptor completion can use the actual active head without losing
any nonmonic or negative input scalar. -/
theorem Search.bounded_leadingCoeff {sign : E → Int} {p : DensePoly E}
    (result : Search sign p) {bound : Bounds.Bound sign p} {frontier : Frontier sign}
    (route : result.route = .bounded bound frontier) :
    (interpret φ hz frontier.head).leadingCoeff = (interpret φ hz p).leadingCoeff := by
  rw [result.bounded_factor φ hz h1 hs hm route, Polynomial.leadingCoeff_mul,
    (rootProduct_monic φ frontier.removed).leadingCoeff, one_mul]

include hz h1 hs hm in
/-- Each emitted root accounts for one degree of the original input.
The native domain companion supplies the nonzero active-head premise. -/
theorem Search.bounded_degree {sign : E → Int} {p : DensePoly E}
    (result : Search sign p) {bound : Bounds.Bound sign p} {frontier : Frontier sign}
    (route : result.route = .bounded bound frontier)
    (nonzero : interpret φ hz frontier.head ≠ 0) :
    p.natDegree = frontier.head.natDegree + frontier.removed.length := by
  have computed := result.computed
  rw [route] at computed
  obtain ⟨_, initial, prepared, refined⟩ := dispatch?_bounded computed
  exact Frontier.refine?_degree φ hz h1 hs hm prepared refined nonzero

end Hex.RealClosure.Isolation

/-- info: 'Hex.RealClosure.Isolation.Search.bounded_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Search.bounded_factor
/-- info: 'Hex.RealClosure.Isolation.Search.bounded_leadingCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Search.bounded_leadingCoeff
/-- info: 'Hex.RealClosure.Isolation.Search.bounded_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.Search.bounded_degree
