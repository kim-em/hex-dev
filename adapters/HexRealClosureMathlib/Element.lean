/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Canonical
public import HexRealClosure.Element
public import HexRealAlgebraicMathlib.Laws

public section

namespace Hex.RealClosure

theorem isZero_iff {context : Nat} (d : Root context) (p : DensePoly Rat) :
    isZero d p = true ↔ evalCanonical p d.toCanonical = 0 :=
  Hex.RealAlgebraicNumber.Laws.beq_iff _ _

theorem evalCanonical_zero (x : Hex.RealAlgebraicNumber) :
    evalCanonical (0 : DensePoly Rat) x = 0 := by
  apply Hex.RealAlgebraicNumber.toReal_injective
  rw [evalCanonical_real]
  simp [realPoly]

namespace Element

theorem ofPoly_value {context : Nat} {d : Root context} (p : DensePoly Rat) :
    (ofPoly p : Element d).value = evalCanonical p d.toCanonical := by
  by_cases h : isZero d p = false
  · simp [ofPoly, h, value]
  · have ht : isZero d p = true := Bool.eq_true_of_ne_false h
    have hz := (isZero_iff d p).mp ht
    simp [ofPoly, h, value, hz]

theorem value_eq_eval {context : Nat} {d : Root context} (a : Element d) :
    a.value = evalCanonical a.polynomial d.toCanonical := by
  cases a with
  | none => simp [value, polynomial, evalCanonical_zero]
  | some v => rfl

theorem value_eq_denote {context : Nat} {d : Root context} (a : Element d) :
    a.value.toReal = a.toExpression.denote := by
  rw [value_eq_eval, evalCanonical_real, d.toCanonical_real]
  rfl

theorem eq_zero_iff {context : Nat} {d : Root context} (a : Element d) :
    a = 0 ↔ a.value = 0 := by
  cases a with
  | none =>
    change (none : Element d) = none ↔ (0 : Hex.RealAlgebraicNumber) = 0
    simp
  | some v =>
    have hne : isZero d v.1 = false := v.2
    have hv : evalCanonical v.1 d.toCanonical ≠ 0 := by
      intro hz
      have hb := (isZero_iff d v.1).mpr hz
      simp [hne] at hb
    simp [value, hv]

theorem ofPoly_eq_zero_iff {context : Nat} {d : Root context} (p : DensePoly Rat) :
    (ofPoly p : Element d) = 0 ↔ evalCanonical p d.toCanonical = 0 := by
  rw [eq_zero_iff, ofPoly_value]

theorem value_add {context : Nat} {d : Root context} (a b : Element d) :
    (add a b).value = a.value + b.value := by
  have h := Expression.toCanonical_add a.toExpression b.toExpression
  rw [add, ofPoly_value, value_eq_eval a, value_eq_eval b]
  simpa [Expression.toCanonical, Expression.add, toExpression] using h

theorem value_mul {context : Nat} {d : Root context} (a b : Element d) :
    (mul a b).value = a.value * b.value := by
  have h := Expression.toCanonical_mul a.toExpression b.toExpression
  rw [mul, ofPoly_value, value_eq_eval a, value_eq_eval b]
  simpa [Expression.toCanonical, Expression.mul, toExpression] using h

theorem value_neg {context : Nat} {d : Root context} (a : Element d) :
    (neg a).value = -a.value := by
  cases a with
  | none => simp [neg, value]
  | some v =>
    rw [neg, ofPoly_value]
    apply Hex.RealAlgebraicNumber.toReal_injective
    rw [evalCanonical_real, d.toCanonical_real,
      Hex.RealAlgebraicNumber.neg_toReal, value_eq_denote]
    exact Expression.denote_neg (⟨v.1⟩ : Expression d)

theorem value_sub {context : Nat} {d : Root context} (a b : Element d) :
    (sub a b).value = a.value - b.value := by
  rw [sub, ofPoly_value]
  apply Hex.RealAlgebraicNumber.toReal_injective
  rw [evalCanonical_real, d.toCanonical_real,
    Hex.RealAlgebraicNumber.sub_toReal,
    value_eq_denote, value_eq_denote]
  exact Expression.denote_sub a.toExpression b.toExpression

theorem value_zero {context : Nat} {d : Root context} :
    (0 : Element d).value = 0 := rfl

theorem value_one {context : Nat} {d : Root context} :
    (1 : Element d).value = 1 := by
  change (ofPoly (1 : DensePoly Rat) : Element d).value = 1
  rw [ofPoly_value]
  apply Hex.RealAlgebraicNumber.toReal_injective
  rw [evalCanonical_real, d.toCanonical_real,
    Hex.RealAlgebraicNumber.one_toReal]
  simpa [Expression.denote, Expression.one] using Expression.denote_one (d := d)

theorem candidate_value {context : Nat} {d : Root context} (e : Expression d)
    (ha : e.denote ≠ 0) :
    (ofPoly e.inverseCandidate.polynomial : Element d).value =
      e.toCanonical⁻¹ := by
  rw [ofPoly_value]
  apply Hex.RealAlgebraicNumber.toReal_injective
  rw [evalCanonical_real, d.toCanonical_real,
    Hex.RealAlgebraicNumber.inv_toReal, Expression.toCanonical_real]
  exact eq_inv_of_mul_eq_one_right
    (Expression.candidate_mul_eq_one_of_nonzero e ha)

theorem value_inv {context : Nat} {d : Root context} (a : Element d) :
    (inv a).value = a.value⁻¹ := by
  cases a with
  | none =>
    change (0 : Hex.RealAlgebraicNumber) = (0 : Hex.RealAlgebraicNumber)⁻¹
    exact Hex.RealAlgebraicNumber.Laws.inv_zero.symm
  | some v =>
    let e : Expression d := ⟨v.1⟩
    have ha : e.denote ≠ 0 := by
      intro hz
      have hr : (evalCanonical v.1 d.toCanonical).toReal = 0 := by
        rw [evalCanonical_real, d.toCanonical_real]
        exact hz
      have he : evalCanonical v.1 d.toCanonical = 0 :=
        Hex.RealAlgebraicNumber.toReal_injective (by simpa using hr)
      have hb := (isZero_iff d v.1).mpr he
      simp [v.2] at hb
    simpa only [inv, value, Expression.toCanonical, e] using
      candidate_value e ha

theorem inverse?_none_iff {context : Nat} {d : Root context} (a : Element d) :
    a.inverse? = none ↔ a = 0 := by
  cases a with
  | none =>
    change (none : Option (Element d)) = none ↔ (none : Element d) = none
    simp
  | some v => simp [inverse?]

theorem inverse?_eq_some_inv {context : Nat} {d : Root context} (a : Element d)
    (ha : a ≠ 0) : a.inverse? = some (inv a) := by
  cases a with
  | none => contradiction
  | some v => rfl

theorem inverse?_sound {context : Nat} {d : Root context} (a b : Element d)
    (h : a.inverse? = some b) : a.value * b.value = 1 := by
  have ha : a ≠ 0 := by
    intro hz
    have hn := (inverse?_none_iff a).mpr hz
    simp [hn] at h
  rw [inverse?_eq_some_inv a ha] at h
  cases Option.some.inj h
  rw [value_inv]
  apply Hex.RealAlgebraicNumber.Laws.mul_inv_cancel
  intro hv
  exact ha ((eq_zero_iff a).mpr hv)

theorem value_div {context : Nat} {d : Root context} (a b : Element d) :
    (a / b).value = a.value / b.value := by
  change (mul a (inv b)).value = a.value / b.value
  rw [value_mul, value_inv]
  exact (Hex.RealAlgebraicNumber.Laws.div_eq_mul_inv _ _).symm

theorem value_natCast {context : Nat} {d : Root context} (n : Nat) :
    (n : Element d).value = (n : Hex.RealAlgebraicNumber) := by
  change (ofPoly (DensePoly.C (n : Rat)) : Element d).value =
    Hex.RealAlgebraicNumber.ofRat n
  rw [ofPoly_value]
  apply Hex.RealAlgebraicNumber.toReal_injective
  rw [evalCanonical_real, d.toCanonical_real,
    Hex.RealAlgebraicNumber.ofRat_toReal]
  simp [realPoly, HexPolyMathlib.Interpret.interpret_C, ratCast]

theorem sign_sound {context : Nat} {d : Root context} (a : Element d) :
    a.sign = (SignType.sign a.toExpression.denote : Int) := by
  rw [sign, Hex.RealAlgebraicNumber.sign_eq, value_eq_denote]
  by_cases hn : a.toExpression.denote < 0
  · simp [hn, sign_eq_neg_one_iff.mpr hn]
  · by_cases hz : a.toExpression.denote = 0
    · simp [hz]
    · have hp : 0 < a.toExpression.denote :=
        lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      simp [hn, hz, sign_eq_one_iff.mpr hp]

theorem sign_zero_iff {context : Nat} {d : Root context} (a : Element d) :
    a.sign = 0 ↔ a = 0 := by
  rw [sign, Hex.RealAlgebraicNumber.sign_eq]
  have hreal : a.value.toReal = 0 ↔ a.value = 0 := by
    constructor
    · intro h
      apply Hex.RealAlgebraicNumber.toReal_injective
      simpa using h
    · intro h
      simp [h]
  rw [eq_zero_iff, ← hreal]
  by_cases hn : a.value.toReal < 0
  · simp [hn, ne_of_lt hn]
  · by_cases hz : a.value.toReal = 0
    · simp [hz]
    · simp [hn, hz]

theorem equal_iff {context : Nat} {d : Root context} (a b : Element d) :
    equal a b = true ↔ a.value = b.value := by
  rw [equal, Option.isNone_iff_eq_none]
  change sub a b = (0 : Element d) ↔ a.value = b.value
  rw [eq_zero_iff, value_sub]
  exact sub_eq_zero

theorem value_transport {context : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : SignDet.Reencoding d head lower upper) (a : Element d) :
    (transport r a).value = a.value := by
  cases a with
  | none => rfl
  | some v =>
    rw [transport, ofPoly_value]
    apply Hex.RealAlgebraicNumber.toReal_injective
    rw [evalCanonical_real, Root.toCanonical_real r.target, value_eq_denote]
    exact Expression.denote_transport r (⟨v.1⟩ : Expression d)

theorem value_rebind {context version : Nat} {d : Root context}
    (r : Rebinding d version) (a : Element d) :
    (rebind r a).value = a.value := by
  cases a with
  | none => rfl
  | some v =>
    rw [rebind, ofPoly_value]
    apply Hex.RealAlgebraicNumber.toReal_injective
    rw [evalCanonical_real, Root.toCanonical_real r.target, value_eq_denote]
    exact Expression.denote_rebind r (⟨v.1⟩ : Expression d)

theorem value_refine {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version) (a : Element d) :
    (refine r a).value = a.value := by
  cases a with
  | none => rfl
  | some v =>
    rw [refine, ofPoly_value, value_eq_eval (some v : Element d)]
    simpa [Expression.toCanonical, Expression.refine, Expression.rebind,
      Expression.transport, toExpression, polynomial] using
      Expression.toCanonical_refine r (⟨v.1⟩ : Expression d)

end Element

/-- The values of packed rational selected-root expressions form a subfield
of the canonical real algebraic numbers. -/
def valueField {context : Nat} (d : Root context) :
    Subfield Hex.RealAlgebraicNumber where
  carrier := {x | ∃ a : Element d, a.value = x}
  zero_mem' := ⟨0, Element.value_zero⟩
  one_mem' := ⟨1, Element.value_one⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, Element.value_add a b⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, Element.value_neg a⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, Element.value_mul a b⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a⁻¹, Element.value_inv a⟩

/-- The lawful semantic field of a checked rational selected root. -/
abbrev Value {context : Nat} (d : Root context) := valueField d

/-- Forget the stored polynomial while retaining its exact selected value. -/
def Element.toValue {context : Nat} {d : Root context} (a : Element d) : Value d :=
  ⟨a.value, by
    change ∃ b : Element d, b.value = a.value
    exact ⟨a, rfl⟩⟩

theorem Element.toValue_eq_iff {context : Nat} {d : Root context}
    (a b : Element d) : a.toValue = b.toValue ↔ Element.equal a b = true := by
  rw [Element.equal_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem Element.toValue_surjective {context : Nat} {d : Root context} :
    Function.Surjective (Element.toValue (d := d)) := by
  intro x
  obtain ⟨a, ha⟩ := x.property
  refine ⟨a, ?_⟩
  exact Subtype.ext ha

theorem Element.toValue_zero {context : Nat} {d : Root context} :
    (0 : Element d).toValue = 0 :=
  Subtype.ext (Element.value_zero (d := d))

theorem Element.toValue_eq_zero_iff {context : Nat} {d : Root context}
    (a : Element d) : a.toValue = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply (Element.eq_zero_iff a).mpr
    have hv := congrArg Subtype.val h
    simpa [Element.toValue] using hv
  · intro h
    subst a
    exact Element.toValue_zero (d := d)

theorem Element.toValue_one {context : Nat} {d : Root context} :
    (1 : Element d).toValue = 1 := by
  apply Subtype.ext
  simpa only [Element.toValue, OneMemClass.coe_one] using
    Element.value_one (d := d)

theorem Element.toValue_add {context : Nat} {d : Root context}
    (a b : Element d) : (a + b).toValue = a.toValue + b.toValue :=
  Subtype.ext (Element.value_add a b)

theorem Element.toValue_neg {context : Nat} {d : Root context}
    (a : Element d) : (-a).toValue = -a.toValue :=
  Subtype.ext (Element.value_neg a)

theorem Element.toValue_sub {context : Nat} {d : Root context}
    (a b : Element d) : (a - b).toValue = a.toValue - b.toValue :=
  Subtype.ext (Element.value_sub a b)

theorem Element.toValue_mul {context : Nat} {d : Root context}
    (a b : Element d) : (a * b).toValue = a.toValue * b.toValue :=
  Subtype.ext (Element.value_mul a b)

theorem Element.toValue_inv {context : Nat} {d : Root context}
    (a : Element d) : a⁻¹.toValue = a.toValue⁻¹ :=
  Subtype.ext (Element.value_inv a)

theorem Element.toValue_div {context : Nat} {d : Root context}
    (a b : Element d) : (a / b).toValue = a.toValue / b.toValue :=
  Subtype.ext (Element.value_div a b)

theorem Element.toValue_natCast {context : Nat} {d : Root context} (n : Nat) :
    (n : Element d).toValue = (n : Value d) :=
  Subtype.ext (Element.value_natCast (d := d) n)

example {context : Nat} (d : Root context) : Field (Value d) := inferInstance
example {context : Nat} (d : Root context) : LinearOrder (Value d) := inferInstance
example {context : Nat} (d : Root context) : IsStrictOrderedRing (Value d) := inferInstance

end Hex.RealClosure

/-- info: 'Hex.RealClosure.Element.eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Element.eq_zero_iff
/-- info: 'Hex.RealClosure.Element.value_inv' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Element.value_inv
/-- info: 'Hex.RealClosure.Element.equal_iff' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Element.equal_iff
/-- info: 'Hex.RealClosure.Element.value_refine' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Element.value_refine
