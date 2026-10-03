/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.CoefficientSignsConformance
public meta import HexRealClosureMathlib.CoefficientSignsConformance
public meta import HexRealClosure.SignFacts
public import HexRealClosure.SignFacts
import all HexRealClosure.Algebraic
import all HexPoly.Euclid.DivGcd

public section

namespace Hex.RealClosure.Algebraic.PackingConformance

open CoefficientSignsConformance

@[expose] def literal : Element context :=
  Element.restore stored 1 sign_checked (by decide +kernel)

@[expose] def small : Element context :=
  Element.restore (2 * Sturm.Fixtures.x) 1 reduced_sign (by decide +kernel)

@[expose] def facts : List (SignFact context) :=
  [⟨2 * Sturm.Fixtures.x, 1, reduced_sign⟩]

@[expose] def literalFacts : List (SignFact context) :=
  [⟨stored, 1, sign_checked⟩]

private theorem clean : context.canReduce = true := by
  rw [context.reduce_checked]
  simp only [context, Context.root_adjoin, Context.clean_adjoin,
    CoefficientSignsConformance.source_raw,
    Hex.SignDet.Conformance.singletonRaw, ← Array.all_toList]
  decide +kernel

@[expose] def reduction (p : DensePoly Rat) : DensePoly Rat :=
  (DensePoly.divModMonic p Sturm.Fixtures.p (by
    change Sturm.Fixtures.p.leadingCoeff = 1
    decide +kernel)).2

theorem reduction_eq : reduction = context.reduce := by
  funext p
  rw [Context.reduce, dite_eq_left clean]
  simp only [context, Context.root_adjoin,
    CoefficientSignsConformance.source_raw,
    Hex.SignDet.Conformance.singletonRaw, reduction]

theorem literal_sign : literal.sign = 1 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem cached_add : ((Element.cachedAdd reduction reduction_eq facts).add small 0).sign = 1 := by
  decide +kernel

theorem native_add : (small + 0).sign = 1 := by
  have h := cached_add
  rw [Element.cachedAdd_eq reduction reduction_eq facts] at h
  exact h

set_option maxRecDepth 32768 in
theorem canonical_zero :
    ((Element.cachedSub reduction reduction_eq ([] : List (SignFact context))).sub small small).polynomial = 0 ∧
    ((Element.cachedSub reduction reduction_eq ([] : List (SignFact context))).sub small small).sign = 0 ∧
    (Element.cachedOne reduction reduction_eq ([] : List (SignFact context))).one.sign = 1 ∧
    ((Element.cachedNatCast reduction reduction_eq ([] : List (SignFact context))).natCast 3).sign = 1 := by
  decide +kernel

set_option maxRecDepth 32768 in
example :
    ((Element.cachedAdd reduction reduction_eq ([] : List (SignFact context))).add small 0) =
      (Element.missing (small.polynomial + (0 : Element context).polynomial)).val := by
  change Element.pack reduction reduction_eq []
    (small.polynomial + (0 : Element context).polynomial) = _
  apply Element.pack_missing
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 32768 in
example : Element.pack reduction reduction_eq literalFacts stored = (Element.missing stored).val := by
  apply Element.pack_missing
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 32768 in
example : True := by
  fail_if_success
    have : ((Element.cachedAdd reduction reduction_eq ([] : List (SignFact context))).add small 0).sign = 1 := by
      decide +kernel
  trivial

#guard ((Element.cachedAdd reduction reduction_eq ([] : List (SignFact context))).add small 0).sign == 1

set_option maxRecDepth 32768 in
example :
    ((Element.cachedNeg reduction reduction_eq ([] : List (SignFact context))).neg
      (Element.cachedOne reduction reduction_eq ([] : List (SignFact context))).one).sign = -1 := by
  decide +kernel

theorem literal_decoding :
    SignFact.read facts (2 * Sturm.Fixtures.x) 1 = some small ∧
    SignFact.read facts (2 * Sturm.Fixtures.x) (-1) = none ∧
    SignFact.read facts (2 * Sturm.Fixtures.x) 0 = none ∧
    SignFact.read (context := context) [] (2 * Sturm.Fixtures.x) 1 = none ∧
    SignFact.read facts stored 1 = none ∧
    SignFact.read literalFacts stored 1 = some literal := by
  decide +kernel

@[expose] def foreign :=
  Context.adjoin CoefficientSignsConformance.source (fun _ => false)

set_option maxRecDepth 32768 in
private theorem foreign_query : foreign.queryPoly Sturm.Fixtures.p = 0 := by
  simp only [Context.queryPoly, Context.queryRemainder, foreign, Context.root_adjoin,
    CoefficientSignsConformance.source_raw,
    Hex.SignDet.Conformance.singletonRaw, DensePoly.pseudoDivMod,
    ← Array.foldl_toList, Array.toList_range]
  decide +kernel

theorem foreign_zero : foreign.signPoly Sturm.Fixtures.p = 0 := by
  rw [Context.signPoly, foreign_query, foreign.signQuery_const 0 (by decide +kernel)]
  decide +kernel

@[expose] def zeroFacts : List (SignFact foreign) :=
  [⟨Sturm.Fixtures.p, 0, foreign_zero⟩]

private theorem foreign_reduce : (fun p : DensePoly Rat => p) = foreign.reduce := by
  funext p
  have hc : foreign.canReduce = false := by
    rw [foreign.reduce_checked]
    simp only [foreign, Context.root_adjoin, Context.clean_adjoin,
      CoefficientSignsConformance.source_raw,
      Hex.SignDet.Conformance.singletonRaw, ← Array.all_toList]
    decide +kernel
  rw [Context.reduce, dite_eq_right (by rw [hc]; decide)]

/- A nonconstant retained representative that vanishes at the selected root
packs to canonical zero using a supplied zero sign. -/
set_option maxRecDepth 32768 in
example :
    1 < Sturm.Fixtures.p.size ∧
    Element.pack (fun p => p) foreign_reduce zeroFacts Sturm.Fixtures.p = 0 := by
  decide +kernel

example : True := by
  fail_if_success
    have : List (SignFact foreign) := facts
  trivial

/-- info: 'Hex.RealClosure.Algebraic.PackingConformance.native_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms native_add
/-- info: 'Hex.RealClosure.Algebraic.Element.pack_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Element.pack_eq
/-- info: 'Hex.RealClosure.Algebraic.SignFact.read_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignFact.read_sound

end Hex.RealClosure.Algebraic.PackingConformance
