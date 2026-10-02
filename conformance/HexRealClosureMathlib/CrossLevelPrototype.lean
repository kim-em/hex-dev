/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.CoefficientSignsConformance
import all HexRealClosure.Algebraic
import all HexSignDet.Descriptor

public section

namespace Hex.RealClosure.Algebraic.CrossLevelPrototype

open CoefficientSignsConformance

@[expose] def literal : Element context :=
  Element.restore stored 1 sign_checked (by decide +kernel)

theorem literal_sign : literal.sign = 1 := by
  decide +kernel

structure Fact where
  polynomial : DensePoly Rat
  sign : Int
  checked : context.signPoly polynomial = sign

@[expose] def findSign (facts : List Fact) (p : DensePoly Rat) :
    Option {s : Int // context.signPoly p = s} :=
  match facts with
  | [] => none
  | f :: fs =>
    if h : f.polynomial = p then
      some ⟨f.sign, h ▸ f.checked⟩
    else findSign fs p

@[expose] def pack (facts : List Fact) (p : DensePoly Rat) : Element context :=
  let kept := context.reduce p
  match findSign facts kept with
  | none => Element.ofPoly p
  | some f =>
    if h : f.val = 0 then 0
    else Element.restore kept f.val f.property h

theorem pack_eq (facts : List Fact) (p : DensePoly Rat) :
    pack facts p = Element.ofPoly p := by
  unfold pack
  dsimp only
  cases h : findSign facts (context.reduce p) with
  | none => simp only
  | some f =>
    simp only
    split
    · rename_i hz
      exact (Element.ofPoly_eq_zero p (f.property.trans hz)).symm
    · rename_i hn
      exact (Element.ofPoly_restore p f.val f.property hn).symm

@[expose, instance_reducible] def add (facts : List Fact) : Add (Element context) :=
  ⟨fun a b => pack facts (a.polynomial + b.polynomial)⟩

theorem add_eq (facts : List Fact) : add facts = (inferInstance : Add (Element context)) := by
  apply congrArg Add.mk
  funext a b
  exact pack_eq facts _

@[expose] def facts : List Fact :=
  [⟨2 * Sturm.Fixtures.x, 1, reduced_sign⟩]

@[expose] def small : Element context :=
  Element.restore (2 * Sturm.Fixtures.x) 1 reduced_sign (by decide +kernel)

private theorem clean : context.canReduce = true := by
  rw [context.reduce_checked]
  simp only [context, Context.root_adjoin, Context.clean_adjoin,
    Hex.SignDetMathlib.GraphSignsConformance.source_raw,
    Hex.SignDet.Conformance.singletonRaw, ← Array.all_toList]
  decide +kernel

set_option maxRecDepth 32768 in
theorem cached_add :
    (@HAdd.hAdd (Element context) (Element context) (Element context)
      (@instHAdd _ (add facts)) small 0).sign = 1 := by
  change (pack facts (small.polynomial + (0 : Element context).polynomial)).sign = 1
  simp only [small, Element.restore_polynomial, Element.polynomial_zero]
  unfold pack
  have hr : context.reduce (2 * Sturm.Fixtures.x + 0) = 2 * Sturm.Fixtures.x := by
    rw [Context.reduce, dite_eq_left clean]
    simp only [context, Context.root_adjoin,
      Hex.SignDetMathlib.GraphSignsConformance.source_raw,
      Hex.SignDet.Conformance.singletonRaw]
    decide +kernel
  have hf : findSign facts (context.reduce (2 * Sturm.Fixtures.x + 0)) =
      some ⟨1, by rw [hr]; exact reduced_sign⟩ := by
    simp only [hr, facts, findSign, ↓reduceDIte]
  simp only [hf, Int.reduceEq, ↓reduceDIte, Element.restore_sign]

theorem native_add : (small + 0).sign = 1 := by
  have h := cached_add
  rw [add_eq facts] at h
  exact h

theorem missing_fact : findSign [] (2 * Sturm.Fixtures.x) = none := rfl

/-- info: 'Hex.RealClosure.Algebraic.CrossLevelPrototype.native_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms native_add

/-- info: 'Hex.RealClosure.Algebraic.CrossLevelPrototype.pack_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pack_eq

end Hex.RealClosure.Algebraic.CrossLevelPrototype
