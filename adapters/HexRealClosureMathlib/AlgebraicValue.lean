/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealClosureMathlib.Algebraic
public import Mathlib.Algebra.Order.Field.Subfield
public section
namespace Hex.RealClosure.Algebraic
variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable (hsign : ∀ a, coeffSign a = (SignType.sign (f a) : Int))
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
variable (hd : ∀ a b, f (a / b) = f a / f b)

/-- The selected values form a genuine subfield; closure follows from the
actual executable operations, rather than field laws on representatives. -/
@[expose] noncomputable def Context.field (context : Context E Ctx coeffSign parent) : Subfield K where
  carrier := Set.range (Element.denote f hz h1 ha hs hm hnat hsign (context := context))
  zero_mem' := ⟨0, Element.denote_zero f hz h1 ha hs hm hnat hsign⟩
  one_mem' := ⟨1, Element.denote_one f hz h1 ha hs hm hnat hsign hn hi⟩
  add_mem' := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, Element.denote_add f hz h1 ha hs hm hnat hsign hn hi x y⟩
  neg_mem' := by
    rintro a ⟨x, rfl⟩
    exact ⟨-x, Element.denote_neg f hz h1 ha hs hm hnat hsign hn hi x⟩
  mul_mem' := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, Element.denote_mul f hz h1 ha hs hm hnat hsign hn hi x y⟩
  inv_mem' := by
    rintro a ⟨x, rfl⟩
    exact ⟨x⁻¹, Element.denote_inv f hz h1 ha hs hm hnat hsign hn hi hd x⟩

/-- Mathematical selected values, with the field and order inherited from
their image subfield. Core constructors do not consume these semantic laws. -/
noncomputable abbrev Value (context : Context E Ctx coeffSign parent) :=
  context.field f hz h1 ha hs hm hnat hsign hn hi hd

-- The value type has lawful field and order instances inherited from the image.
noncomputable example (context : Context E Ctx coeffSign parent) :
    Field (Value f hz h1 ha hs hm hnat hsign hn hi hd context) := inferInstance
noncomputable example (context : Context E Ctx coeffSign parent) :
    LinearOrder (Value f hz h1 ha hs hm hnat hsign hn hi hd context) := inferInstance
noncomputable example (context : Context E Ctx coeffSign parent) :
    IsStrictOrderedRing (Value f hz h1 ha hs hm hnat hsign hn hi hd context) := inferInstance

@[expose] noncomputable def Element.toValue {context : Context E Ctx coeffSign parent}
    (a : Element context) : context.field f hz h1 ha hs hm hnat hsign hn hi hd :=
  ⟨a.denote f hz h1 ha hs hm hnat hsign, ⟨a, rfl⟩⟩

include hn hi hd in
theorem Element.toValue_equal {context : Context E Ctx coeffSign parent}
    (a b : Element context) :
    a.toValue f hz h1 ha hs hm hnat hsign hn hi hd =
      b.toValue f hz h1 ha hs hm hnat hsign hn hi hd ↔ a.equal b = true := by
  rw [Subtype.ext_iff, toValue, toValue]
  exact (Element.equal_spec f hz h1 ha hs hm hnat hsign hn hi a b).symm

include hn hi hd in
theorem Element.toValue_surjective {context : Context E Ctx coeffSign parent} :
    Function.Surjective (Element.toValue f hz h1 ha hs hm hnat hsign hn hi hd
      (context := context)) := by
  intro y
  obtain ⟨a, ha⟩ := y.property
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact ha

namespace Element
variable {context : Context E Ctx coeffSign parent}

include hn hi hd in
theorem toValue_zero : toValue f hz h1 ha hs hm hnat hsign hn hi hd
    (0 : Element context) = 0 := by
  apply Subtype.ext
  exact denote_zero f hz h1 ha hs hm hnat hsign

include hn hi hd in
theorem toValue_one : toValue f hz h1 ha hs hm hnat hsign hn hi hd
    (1 : Element context) = 1 := by
  apply Subtype.ext
  exact denote_one f hz h1 ha hs hm hnat hsign hn hi

include hn hi hd in
theorem toValue_add (a b : Element context) :
    (a + b).toValue f hz h1 ha hs hm hnat hsign hn hi hd =
      a.toValue f hz h1 ha hs hm hnat hsign hn hi hd +
        b.toValue f hz h1 ha hs hm hnat hsign hn hi hd := by
  apply Subtype.ext
  exact denote_add f hz h1 ha hs hm hnat hsign hn hi a b

include hn hi hd in
theorem toValue_sub (a b : Element context) :
    (a - b).toValue f hz h1 ha hs hm hnat hsign hn hi hd =
      a.toValue f hz h1 ha hs hm hnat hsign hn hi hd -
        b.toValue f hz h1 ha hs hm hnat hsign hn hi hd := by
  apply Subtype.ext
  exact denote_sub f hz h1 ha hs hm hnat hsign hn hi a b

include hn hi hd in
theorem toValue_neg (a : Element context) :
    (-a).toValue f hz h1 ha hs hm hnat hsign hn hi hd =
      -(a.toValue f hz h1 ha hs hm hnat hsign hn hi hd) := by
  apply Subtype.ext
  exact denote_neg f hz h1 ha hs hm hnat hsign hn hi a

include hn hi hd in
theorem toValue_mul (a b : Element context) :
    (a * b).toValue f hz h1 ha hs hm hnat hsign hn hi hd =
      a.toValue f hz h1 ha hs hm hnat hsign hn hi hd *
        b.toValue f hz h1 ha hs hm hnat hsign hn hi hd := by
  apply Subtype.ext
  exact denote_mul f hz h1 ha hs hm hnat hsign hn hi a b

include hn hi hd in
theorem toValue_inv (a : Element context) :
    (a⁻¹).toValue f hz h1 ha hs hm hnat hsign hn hi hd =
      (a.toValue f hz h1 ha hs hm hnat hsign hn hi hd)⁻¹ := by
  apply Subtype.ext
  exact denote_inv f hz h1 ha hs hm hnat hsign hn hi hd a

include hn hi hd in
theorem toValue_div (a b : Element context) :
    (a / b).toValue f hz h1 ha hs hm hnat hsign hn hi hd =
      a.toValue f hz h1 ha hs hm hnat hsign hn hi hd /
        b.toValue f hz h1 ha hs hm hnat hsign hn hi hd := by
  apply Subtype.ext
  exact denote_div f hz h1 ha hs hm hnat hsign hn hi hd a b

include hn hi hd in
theorem toValue_nat (n : Nat) :
    (n : Element context).toValue f hz h1 ha hs hm hnat hsign hn hi hd = n := by
  apply Subtype.ext
  exact denote_nat f hz h1 ha hs hm hnat hsign hn hi n

include hn hi hd in
theorem sign_toValue (a : Element context) : a.sign =
    (SignType.sign (a.toValue f hz h1 ha hs hm hnat hsign hn hi hd) : Int) := by
  rw [a.sign_spec f hz h1 ha hs hm hnat hsign hn hi]
  congr 1

end Element

/-- Semantic equality on stored representatives. Its equivalence laws follow
from the actual sign-query semantics; no representative field laws are assumed. -/
@[expose] noncomputable def Context.setoid (context : Context E Ctx coeffSign parent) :
    Setoid (Element context) where
  r a b := a.equal b = true
  iseqv := {
    refl := fun a => (Element.equal_spec f hz h1 ha hs hm hnat hsign hn hi a a).mpr rfl
    symm := by
      intro a b h
      exact (Element.equal_spec f hz h1 ha hs hm hnat hsign hn hi b a).mpr
        ((Element.equal_spec f hz h1 ha hs hm hnat hsign hn hi a b).mp h).symm
    trans := by
      intro a b c hab hbc
      exact (Element.equal_spec f hz h1 ha hs hm hnat hsign hn hi a c).mpr
        (((Element.equal_spec f hz h1 ha hs hm hnat hsign hn hi a b).mp hab).trans
          ((Element.equal_spec f hz h1 ha hs hm hnat hsign hn hi b c).mp hbc)) }

@[expose] noncomputable def Context.quotientMap (context : Context E Ctx coeffSign parent) :
    Quotient (context.setoid f hz h1 ha hs hm hnat hsign hn hi) →
      context.field f hz h1 ha hs hm hnat hsign hn hi hd :=
  Quotient.lift (Element.toValue f hz h1 ha hs hm hnat hsign hn hi hd)
    (fun a b h => (Element.toValue_equal f hz h1 ha hs hm hnat hsign hn hi hd a b).mpr h)

/-- The field of selected values is precisely the semantic quotient of storage. -/
noncomputable def Context.quotientEquiv (context : Context E Ctx coeffSign parent) :
    Quotient (context.setoid f hz h1 ha hs hm hnat hsign hn hi) ≃
      context.field f hz h1 ha hs hm hnat hsign hn hi hd :=
  Equiv.ofBijective (context.quotientMap f hz h1 ha hs hm hnat hsign hn hi hd) (by
    constructor
    · intro x y hxy
      induction x using Quotient.inductionOn with
      | _ a =>
        induction y using Quotient.inductionOn with
        | _ b =>
          apply Quotient.sound
          exact (Element.toValue_equal f hz h1 ha hs hm hnat hsign hn hi hd a b).mp hxy
    · intro y
      obtain ⟨a, ha⟩ := Element.toValue_surjective f hz h1 ha hs hm hnat hsign hn hi hd y
      exact ⟨Quotient.mk _ a, ha⟩)
/-- info: 'Hex.RealClosure.Algebraic.Context.quotientEquiv' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Algebraic.Context.quotientEquiv
/-- info: 'Hex.RealClosure.Algebraic.Element.toValue_inv' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Algebraic.Element.toValue_inv
end Hex.RealClosure.Algebraic
