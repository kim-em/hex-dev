/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.FrameFormat
public import HexRealClosure.TowerOrder
public import HexRealClosureMathlib.Algebraic
public import HexPolyMathlib.GrindTransport
public import Mathlib.Algebra.Order.Field.Subfield

public section

namespace Hex.RealClosure.Tower

/-- Interpretation of one immutable native context in an ordered field.
These are companion conclusions, never arguments of executable constructors.
Literal equality of stored nonzero expressions need not reflect equality here. -/
structure Model {registry : BaseContext.Registry} (context : Context registry)
    (K : Type u) [Field K] [LinearOrder K] where
  value : context.Value → K
  zero_iff : ∀ a, value a = 0 ↔ a = 0
  one : value 1 = 1
  add : ∀ a b, value (a + b) = value a + value b
  sub : ∀ a b, value (a - b) = value a - value b
  mul : ∀ a b, value (a * b) = value a * value b
  nat : ∀ n : Nat, value (n : context.Value) = (n : K)
  neg : ∀ a, value (-a) = -value a
  inv : ∀ a, value a⁻¹ = (value a)⁻¹
  div : ∀ a b, value (a / b) = value a / value b
  sign : ∀ a, context.sign a = (SignType.sign (value a) : Int)

variable {registry : BaseContext.Registry} {K : Type u}
variable [Field K] [LinearOrder K]

namespace Model

/-- Transport an interpretation along literal equality of native contexts. -/
noncomputable def cast {context other : Context registry} (model : Model context K)
    (h : context = other) : Model other K := h ▸ model

private theorem cast_map {context other : Context registry} (model : Model context K)
    (h : context = other) {A : Type} (f : A → context.Value) (g : A → other.Value)
    (hg : HEq g f) (a : A) : (model.cast h).value (g a) = model.value (f a) := by
  cases h
  cases eq_of_heq hg
  rfl

private theorem cast_value {context other : Context registry} (model : Model context K)
    (h : context = other) (a : context.Value) (b : other.Value) (hb : HEq b a) :
    (model.cast h).value b = model.value a := by
  cases h
  cases eq_of_heq hb
  rfl

/-- Mathematical values of the native context form a genuine subfield. -/
@[expose] noncomputable def field {context : Context registry} (model : Model context K) : Subfield K where
  carrier := Set.range model.value
  zero_mem' := ⟨0, (model.zero_iff 0).mpr rfl⟩
  one_mem' := ⟨1, model.one⟩
  add_mem' := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, model.add x y⟩
  neg_mem' := by
    rintro a ⟨x, rfl⟩
    exact ⟨-x, model.neg x⟩
  mul_mem' := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, model.mul x y⟩
  inv_mem' := by
    rintro a ⟨x, rfl⟩
    exact ⟨x⁻¹, model.inv x⟩

/-- A stored expression maps to its mathematical value with inherited field
and order laws. This map identifies semantically equal nonzero expressions. -/
@[expose] noncomputable def toValue {context : Context registry} (model : Model context K)
    (a : context.Value) : model.field := ⟨model.value a, ⟨a, rfl⟩⟩

@[simp] theorem coe_toValue {context : Context registry} (model : Model context K)
    (a : context.Value) : (model.toValue a : K) = model.value a := rfl

theorem toValue_equal {context : Context registry} (model : Model context K)
    (a b : context.Value) : model.toValue a = model.toValue b ↔ model.value a = model.value b :=
  Subtype.ext_iff

theorem toValue_surjective {context : Context registry} (model : Model context K) :
    Function.Surjective model.toValue := by
  intro a
  obtain ⟨x, hx⟩ := a.property
  exact ⟨x, Subtype.ext hx⟩

section Order
variable [DecidableEq K] [IsStrictOrderedRing K] {context : Context registry}

omit [DecidableEq K] [IsStrictOrderedRing K] in
private theorem sign_zero (a : K) : (SignType.sign a : Int) = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply sign_eq_zero_iff.mp
    cases hs : SignType.sign a <;> simp_all
  · intro h
    subst a
    simp

omit [DecidableEq K] [IsStrictOrderedRing K] in
private theorem sign_neg (a : K) : (SignType.sign a : Int) < 0 ↔ a < 0 := by
  rw [← (sign_eq_neg_one_iff (a := a))]
  cases SignType.sign a <;> decide

omit [IsStrictOrderedRing K] in
/-- Executable context equality compares the interpreted mathematical values. -/
theorem equal_spec (model : Model context K) (a b : context.Value) :
    context.equal a b = decide (model.value a = model.value b) := by
  simp only [Context.equal, model.sign, model.sub, sign_zero, sub_eq_zero]

/-- Executable comparison uses the order on the same mathematical values. -/
theorem compare_spec (model : Model context K) (a b : context.Value) :
    context.compare a b =
      if model.value a < model.value b then .lt
      else if model.value a = model.value b then .eq else .gt := by
  simp only [Context.compare, model.sign, model.sub, sign_neg, sign_zero,
    sub_neg, sub_eq_zero]
end Order

section Base
variable {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
variable (context : BaseContext.Context registry B sign)

/-- An embedding of the actual canonical base gives the native wrapper's
interpretation. `fieldOfGrind` preserves every executable operation and cast. -/
noncomputable def base
    (f : letI : Field B := HexPolyMathlib.fieldOfGrind; B →+* K)
    (hsign : ∀ a, sign a = (SignType.sign (f a) : Int)) :
    Model (Context.base context) K := by
  letI : Field B := HexPolyMathlib.fieldOfGrind
  exact
    { value := fun a => f a.stored
      zero_iff := fun a => (map_eq_zero f).trans (BaseContext.Element.stored_eq_zero a)
      one := f.map_one
      add := fun a b => f.map_add a.stored b.stored
      sub := fun a b => map_sub f a.stored b.stored
      mul := fun a b => f.map_mul a.stored b.stored
      nat := fun n => map_natCast f n
      neg := fun a => map_neg f a.stored
      inv := fun a => map_inv₀ f a.stored
      div := fun a b => map_div₀ f a.stored b.stored
      sign := fun a => hsign a.stored }
end Base

section Root
variable [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]
variable {E : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable {sign : E → Int} {clean : E → Bool} {codec : SignDet.ValueCodec E}
variable {binding : Signature}
variable (chain : Chain registry E sign clean codec binding)
variable (model : Model (.pack chain) K)
variable (descriptor : SignDet.Descriptor E Signature sign binding)
variable (frame : Literal) (encoded : Literal.ofJson (rootData codec descriptor) = some frame)

/-- Propagate the full interpretation through an actual native root level.
This works at every depth and derives the child laws from predecessor laws;
no field structure is asserted on stored algebraic expressions. -/
noncomputable def root : Model (.pack (.root chain descriptor frame encoded)) K where
  value := Algebraic.Element.denote model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign
  zero_iff := Algebraic.Element.denote_eq_zero model.value model.zero_iff model.one
    model.add model.sub model.mul model.nat model.sign model.neg model.inv
  one := Algebraic.Element.denote_one model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign model.neg model.inv
  add := Algebraic.Element.denote_add model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign model.neg model.inv
  sub := Algebraic.Element.denote_sub model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign model.neg model.inv
  mul := Algebraic.Element.denote_mul model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign model.neg model.inv
  nat := Algebraic.Element.denote_nat model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign model.neg model.inv
  neg := Algebraic.Element.denote_neg model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign model.neg model.inv
  inv := Algebraic.Element.denote_inv model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign model.neg model.inv model.div
  div := Algebraic.Element.denote_div model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign model.neg model.inv model.div
  sign := Algebraic.Element.sign_spec model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign model.neg model.inv

/-- The actual native constant-polynomial inclusion preserves every value. -/
theorem root_embed (a : E) :
    (model.root chain descriptor frame encoded).value
      (Algebraic.Element.ofCoeff a) = model.value a :=
  Algebraic.Element.denote_ofCoeff model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign model.neg model.inv a

/-- The native generator denotes the root selected by this exact descriptor. -/
theorem root_generator :
    (model.root chain descriptor frame encoded).value
      (Algebraic.Element.ofPoly (DensePoly.ofCoeffs #[0, 1])) =
      descriptor.root model.value model.zero_iff model.one model.add model.sub
        model.mul model.nat model.sign := by
  dsimp only [root]
  rw [Algebraic.Element.denote_ofPoly model.value model.zero_iff model.one
    model.add model.sub model.mul model.nat model.sign model.neg model.inv]
  have hz : model.value (@Zero.zero E inferInstance) = 0 :=
    (model.zero_iff (@Zero.zero E inferInstance)).mpr rfl
  have hx : HexPolyMathlib.Interpret.interpret model.value model.zero_iff
      (DensePoly.ofCoeffs #[0, 1]) = Polynomial.X := by
    apply Polynomial.ext
    intro i
    rw [HexPolyMathlib.Interpret.coeff_interpret, DensePoly.coeff_ofCoeffs]
    cases i with
    | zero => simp [model.zero_iff 0 |>.mpr rfl]
    | succ i => cases i with
      | zero => simp [model.one]
      | succ i =>
        simpa [Polynomial.coeff_X, show i + 1 + 1 ≠ 1 by omega] using
          hz
  simp only [Algebraic.Context.evalPoly, hx, Polynomial.eval_X,
    Algebraic.Context.rootValue, Algebraic.Context.root_adjoin]

end Root

section Adjoin
variable [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]
variable {context : Context registry}

/-- Interpret the child returned by the public total native constructor.
The selected root and predecessor operations are the existing native ones. -/
noncomputable def adjoin (model : Model context K)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature) :
    Model (context.adjoin descriptor).context K := by
  cases context with
  | pack chain =>
    let extension := Context.adjoin (.pack chain) descriptor
    exact (model.root chain descriptor extension.frame extension.encoded).cast
      (Context.adjoin_native chain descriptor).1.symm

/-- The public extension's actual embedding preserves the old interpretation. -/
theorem adjoin_embed (model : Model context K)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)
    (a : context.Value) :
    (model.adjoin descriptor).value ((context.adjoin descriptor).embed a) = model.value a := by
  cases context with
  | pack chain =>
    unfold adjoin
    rw [cast_map _ _ _ _ (Context.adjoin_native chain descriptor).2.1]
    exact model.root_embed chain descriptor _ _ a

/-- The public generator has the same selected embedding as its descriptor. -/
theorem adjoin_generator (model : Model context K)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature) :
    (model.adjoin descriptor).value (context.adjoin descriptor).generator =
      descriptor.root model.value model.zero_iff model.one model.add model.sub
        model.mul model.nat model.sign := by
  cases context with
  | pack chain =>
    unfold adjoin
    rw [cast_value _ _ _ _ (Context.adjoin_native chain descriptor).2.2]
    exact model.root_generator chain descriptor _ _

/-- Extension preserves the result of actual semantic equality checks. -/
theorem adjoin_equal (model : Model context K)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)
    (a b : context.Value) :
    (context.adjoin descriptor).context.equal
      ((context.adjoin descriptor).embed a) ((context.adjoin descriptor).embed b) =
      context.equal a b := by
  rw [(model.adjoin descriptor).equal_spec, model.equal_spec,
    model.adjoin_embed, model.adjoin_embed]

/-- Extension preserves the result of actual ordered comparisons. -/
theorem adjoin_compare (model : Model context K)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)
    (a b : context.Value) :
    (context.adjoin descriptor).context.compare
      ((context.adjoin descriptor).embed a) ((context.adjoin descriptor).embed b) =
      context.compare a b := by
  rw [(model.adjoin descriptor).compare_spec, model.compare_spec,
    model.adjoin_embed, model.adjoin_embed]

/-- Every native child expression retains a polynomial representative evaluated
at the selected generator. No degree bound or literal equality is asserted. -/
theorem adjoin_polynomial (model : Model context K)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)
    (a : (context.adjoin descriptor).context.Value) :
    ∃ p : DensePoly context.Value,
      (model.adjoin descriptor).value a =
        (HexPolyMathlib.Interpret.interpret model.value model.zero_iff p).eval
          ((model.adjoin descriptor).value (context.adjoin descriptor).generator) := by
  cases context with
  | pack chain =>
    let extension := Context.adjoin (.pack chain) descriptor
    have hc := (Context.adjoin_native chain descriptor).1
    let b := _root_.cast (congrArg Context.Value hc) a
    refine ⟨Algebraic.Element.polynomial b, ?_⟩
    rw [model.adjoin_generator]
    unfold adjoin
    rw [cast_value _ _ b a (cast_heq _ _).symm]
    simp only [root, Algebraic.Element.denote, Algebraic.Context.evalPoly,
      Algebraic.Context.rootValue, Algebraic.Context.root_adjoin]

/-- Successive native root levels include the predecessor's entire value field. -/
theorem adjoin_mono (model : Model context K)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature) :
    model.field ≤ (model.adjoin descriptor).field := by
  rintro a ⟨x, rfl⟩
  exact ⟨(context.adjoin descriptor).embed x, model.adjoin_embed descriptor x⟩
end Adjoin

end Model
end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Model.base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.base
/-- info: 'Hex.RealClosure.Tower.Model.adjoin' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.adjoin
/-- info: 'Hex.RealClosure.Tower.Model.adjoin_embed' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.adjoin_embed
