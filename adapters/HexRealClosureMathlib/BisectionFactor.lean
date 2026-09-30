/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BisectionFrontier

public section

namespace Hex.RealClosure.Bisection
open HexPolyMathlib.Interpret

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E]
variable [Field K] [DecidableEq K]
variable (φ : E → K) (hz : ∀ a, φ a = 0 ↔ a = 0)
variable (h1 : φ 1 = 1) (hs : ∀ a b, φ (a - b) = φ a - φ b)
variable (hm : ∀ a b, φ (a * b) = φ a * φ b)

/-- Product of the literal linear factors for emitted coefficient values. -/
@[expose] noncomputable def rootProduct (roots : List E) : Polynomial K :=
  (roots.map fun root => Polynomial.X - Polynomial.C (φ root)).prod

omit [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E] [DecidableEq K] in
/-- Appending emitted roots appends their factors in the same order. -/
theorem rootProduct_append (roots more : List E) :
    rootProduct φ (roots ++ more) = rootProduct φ roots * rootProduct φ more := by
  simp only [rootProduct, List.map_append, List.prod_append]

omit [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E] [DecidableEq K] in
/-- Emitted linear factors have product leading coefficient one. -/
theorem rootProduct_monic (roots : List E) : (rootProduct φ roots).Monic := by
  induction roots with
  | nil => simp [rootProduct]
  | cons root roots ih =>
    change ((Polynomial.X - Polynomial.C (φ root)) * rootProduct φ roots).Monic
    exact (Polynomial.monic_X_sub_C _).mul ih

omit [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E] [DecidableEq K] in
/-- The product degree counts emitted factors, including repeated values. -/
theorem rootProduct_degree (roots : List E) :
    (rootProduct φ roots).natDegree = roots.length := by
  induction roots with
  | nil => simp [rootProduct]
  | cons root roots ih =>
    change ((Polynomial.X - Polynomial.C (φ root)) * rootProduct φ roots).natDegree =
      roots.length + 1
    rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) (rootProduct_monic φ roots).ne_zero,
      Polynomial.natDegree_X_sub_C, ih]
    omega

include hz h1 hs hm in
/-- A classified cut preserves the exact polynomial, including its scalar. -/
theorem Mode.factor {sign : E → Int} {p : DensePoly E} {point : E}
    (mode : Mode sign p point) :
    interpret φ hz p = rootProduct φ mode.removed.toList * interpret φ hz mode.head := by
  cases mode with
  | regular _ => simp [Mode.removed, Mode.head, rootProduct]
  | root d => simpa [Mode.removed, Mode.head, rootProduct] using d.factor φ hz h1 hs hm

variable [NatCast E] [Neg E] [Inv E]

/-- Polynomial reconstructed from the actual emitted roots and active head. -/
@[expose] noncomputable def Frontier.product {sign : E → Int} (frontier : Frontier sign) : Polynomial K :=
  rootProduct φ frontier.removed * interpret φ hz frontier.head

include hz h1 hs hm in
/-- One actual advancement preserves the emitted-factor product times the
actual returned head. Re-preparing pending cells introduces no extra factor. -/
theorem Frontier.advance?_factor {sign : E → Int} (frontier : Frontier sign)
    (selected : Cell sign frontier.head) (rest : List (Cell sign frontier.head))
    (chosen : select frontier.cells = some (selected, rest)) {next : Frontier sign}
    (accepted : frontier.advance? selected rest chosen = some next) :
    next.product φ hz = frontier.product φ hz := by
  obtain ⟨split, _, _, _, head, removed, _⟩ :=
    frontier.advance?_result selected rest chosen accepted
  simp only [Frontier.product, head, removed, rootProduct_append, mul_assoc]
  rw [← split.mode.factor φ hz h1 hs hm]

include hz h1 hs hm in
/-- Every successful finite traversal preserves the exact factorization,
without needing ordering, root counts or squarefreeness assumptions. -/
theorem traverse?_factor {sign : E → Int} (budget : Nat) (frontier : Frontier sign)
    {result : Frontier sign} (accepted : traverse? budget frontier = some result) :
    result.product φ hz = frontier.product φ hz := by
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
    · rename_i cell rest chosen
      cases hnext : frontier.advance? cell rest chosen with
      | none => simp [hnext] at accepted
      | some next =>
        simp [hnext] at accepted
        exact (ih next accepted).trans
          (frontier.advance?_factor φ hz h1 hs hm cell rest chosen hnext)

include hz h1 hs hm in
/-- Preparing and refining returns the original polynomial as the emitted
linear factors times the actual active head, with its original leading scalar. -/
theorem Frontier.refine?_factor {sign : E → Int} {p : DensePoly E} {lower upper : E}
    {initial result : Frontier sign}
    (prepared : Frontier.prepare? sign p lower upper = some initial)
    (refined : initial.refine? = some result) :
    interpret φ hz p = rootProduct φ result.removed * interpret φ hz result.head := by
  obtain ⟨head, removed, _, _⟩ := Frontier.prepare?_result prepared
  have preserved := traverse?_factor φ hz h1 hs hm _ initial refined
  simpa only [Frontier.product, head, removed, rootProduct, List.map_nil,
    List.prod_nil, one_mul] using preserved.symm

include hz h1 hs hm in
/-- Capped refinement preserves the interpreted original leading coefficient,
including every nonmonic or negative scalar. -/
theorem Frontier.refine?_leadingCoeff {sign : E → Int} {p : DensePoly E} {lower upper : E}
    {initial result : Frontier sign}
    (prepared : Frontier.prepare? sign p lower upper = some initial)
    (refined : initial.refine? = some result) :
    (interpret φ hz result.head).leadingCoeff = (interpret φ hz p).leadingCoeff := by
  rw [Frontier.refine?_factor φ hz h1 hs hm prepared refined, Polynomial.leadingCoeff_mul,
    (rootProduct_monic φ result.removed).leadingCoeff, one_mul]

include hz h1 hs hm in
/-- The original degree is the active-head degree plus emitted factors.
The nonzero active head can be supplied by the frontier domain theorem. -/
theorem Frontier.refine?_degree {sign : E → Int} {p : DensePoly E} {lower upper : E}
    {initial result : Frontier sign}
    (prepared : Frontier.prepare? sign p lower upper = some initial)
    (refined : initial.refine? = some result)
    (nonzero : interpret φ hz result.head ≠ 0) :
    p.natDegree = result.head.natDegree + result.removed.length := by
  have identity := congrArg Polynomial.natDegree
    (Frontier.refine?_factor φ hz h1 hs hm prepared refined)
  rw [Polynomial.natDegree_mul (rootProduct_monic φ result.removed).ne_zero nonzero,
    rootProduct_degree, natDegree_interpret, natDegree_interpret] at identity
  omega

end Hex.RealClosure.Bisection

/-- info: 'Hex.RealClosure.Bisection.Mode.factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Mode.factor
/-- info: 'Hex.RealClosure.Bisection.Frontier.advance?_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Frontier.advance?_factor
/-- info: 'Hex.RealClosure.Bisection.traverse?_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.traverse?_factor
/-- info: 'Hex.RealClosure.Bisection.Frontier.refine?_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Frontier.refine?_factor

/-- info: 'Hex.RealClosure.Bisection.rootProduct_monic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.rootProduct_monic

/-- info: 'Hex.RealClosure.Bisection.rootProduct_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.rootProduct_degree

/-- info: 'Hex.RealClosure.Bisection.Frontier.refine?_leadingCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Frontier.refine?_leadingCoeff

/-- info: 'Hex.RealClosure.Bisection.Frontier.refine?_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Frontier.refine?_degree
