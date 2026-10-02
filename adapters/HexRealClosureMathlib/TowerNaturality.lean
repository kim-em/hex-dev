/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TowerTransport
public import HexRealClosureMathlib.TransportPolynomial

public section

namespace Hex.RealClosure.Tower.Model

variable {registry : BaseContext.Registry} {context : Context registry}
variable {K : Type u} {L : Type v}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]
variable [Field L] [LinearOrder L] [DecidableEq L] [IsStrictOrderedRing L] [IsRealClosed L]

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]
  [Field L] [LinearOrder L] [DecidableEq L] [IsStrictOrderedRing L] [IsRealClosed L] in
/-- A native model is determined by its interpretation of stored values. -/
theorem value_ext (left right : Model context K)
    (agree : ∀ a, left.value a = right.value a) : left = right := by
  cases left
  cases right
  cases funext agree
  rfl

omit [IsStrictOrderedRing K] [IsRealClosed K] in
/-- Native polynomial evaluation in a child depends only on its predecessor
interpretation and the interpreted generator. -/
theorem child_eval (model : Model context K)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)
    (child : Model (context.adjoin descriptor).context K)
    (compatible : ∀ a, child.value ((context.adjoin descriptor).embed a) = model.value a)
    (p : DensePoly context.Value) :
    child.value ((DensePoly.ofCoeffs (p.toArray.map (context.adjoin descriptor).embed)).eval
      (context.adjoin descriptor).generator) =
        (HexPolyMathlib.Interpret.interpret model.value model.zero_iff p).eval
          (child.value (context.adjoin descriptor).generator) := by
  rw [← HexPolyMathlib.Interpret.eval_interpret child.value child.zero_iff child.add child.mul]
  congr 1
  apply Polynomial.ext
  intro i
  rw [HexPolyMathlib.Interpret.coeff_interpret, HexPolyMathlib.Interpret.coeff_interpret]
  have zero : (context.adjoin descriptor).embed 0 = 0 := (child.zero_iff _).mp (by
    rw [compatible]; exact (model.zero_iff 0).mpr rfl)
  have coefficient := Transport.polynomial_coeff (context.adjoin descriptor).embed zero p i
  change (DensePoly.ofCoeffs (p.toArray.map (context.adjoin descriptor).embed)).coeff i =
    (context.adjoin descriptor).embed (p.coeff i) at coefficient
  rw [coefficient, compatible]

/-- Every compatible interpretation of an actual child reads its stored
representative as the corresponding polynomial in that child's generator. -/
theorem child_value (model : Model context K)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)
    (child : Model (context.adjoin descriptor).context K)
    (compatible : ∀ a, child.value ((context.adjoin descriptor).embed a) = model.value a)
    (a : (context.adjoin descriptor).context.Value) :
    child.value a =
      (HexPolyMathlib.Interpret.interpret model.value model.zero_iff
        (context.polynomial descriptor a)).eval
          (child.value (context.adjoin descriptor).generator) := by
  let evaluated := (DensePoly.ofCoeffs
    ((context.polynomial descriptor a).toArray.map (context.adjoin descriptor).embed)).eval
      (context.adjoin descriptor).generator
  have equal : (model.adjoin descriptor).value a =
      (model.adjoin descriptor).value evaluated := by
    rw [model.child_eval descriptor (model.adjoin descriptor) (model.adjoin_embed descriptor)]
    exact model.adjoin_value descriptor a
  have zero : a - evaluated = 0 := ((model.adjoin descriptor).zero_iff _).mp (by
    rw [(model.adjoin descriptor).sub, equal, sub_self])
  have equal' : child.value a = child.value evaluated := sub_eq_zero.mp (by
    rw [← child.sub, zero]; exact (child.zero_iff 0).mpr rfl)
  exact equal'.trans (model.child_eval descriptor child compatible _)

/-- Compatibility on predecessor values determines the selected generator in
any lawful ordered interpretation of the actual native child. -/
theorem child_generator (model : Model context K)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)
    (child : Model (context.adjoin descriptor).context K)
    (compatible : ∀ a, child.value ((context.adjoin descriptor).embed a) = model.value a) :
    child.value (context.adjoin descriptor).generator =
      (model.adjoin descriptor).value (context.adjoin descriptor).generator := by
  rw [model.adjoin_generator]
  apply (descriptor.constraints_iff model.value model.zero_iff model.one model.add model.sub
    model.mul model.nat model.sign _).mp
  rw [← descriptor.constraints_at_root model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign]
  unfold Hex.SignDet.signsAt
  apply List.map_congr_left
  intro p _
  let evaluated := (DensePoly.ofCoeffs (p.toArray.map (context.adjoin descriptor).embed)).eval
    (context.adjoin descriptor).generator
  have same : (SignType.sign (child.value evaluated) : Int) =
      (SignType.sign ((model.adjoin descriptor).value evaluated) : Int) :=
    (child.sign evaluated).symm.trans ((model.adjoin descriptor).sign evaluated)
  rw [model.child_eval descriptor child compatible p,
    model.child_eval descriptor (model.adjoin descriptor) (model.adjoin_embed descriptor) p,
    model.adjoin_generator] at same
  exact same

/-- An arbitrary child model compatible with the predecessor is exactly its
descriptor-based interpretation, on every actual stored value. -/
theorem adjoin_unique (model : Model context K)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)
    (child : Model (context.adjoin descriptor).context K)
    (compatible : ∀ a, child.value ((context.adjoin descriptor).embed a) = model.value a) :
    child = model.adjoin descriptor := by
  apply value_ext
  intro a
  rw [model.child_value descriptor child compatible a, model.adjoin_value,
    model.child_generator descriptor child compatible]

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]
  [DecidableEq L] [IsStrictOrderedRing L] [IsRealClosed L] in
private theorem transfer_eq {source : Context registry} (reference : Model source L)
    (other : Model source K)
    (a b : source.Value) (equal : reference.value a = reference.value b) :
    other.value a = other.value b := by
  have zero : a - b = 0 := (reference.zero_iff _).mp (by
    rw [reference.sub, equal, sub_self])
  apply sub_eq_zero.mp
  rw [← other.sub, zero]
  exact (other.zero_iff 0).mpr rfl

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]
  [DecidableEq L] [IsStrictOrderedRing L] [IsRealClosed L] in
/-- Restrict an arbitrary target interpretation through a native inclusion.
One compatible reference interpretation in an independent field proves the
executable inclusion laws; the resulting source model uses the supplied
target's actual values. -/
@[expose] noncomputable def comap {source target : Context registry}
    (original : Model source L) (reference : Model target L) (other : Model target K)
    (includeValue : source.Value → target.Value)
    (preserved : ∀ a, reference.value (includeValue a) = original.value a) :
    Model source K where
  value := fun a => other.value (includeValue a)
  zero_iff := by
    intro a
    rw [other.zero_iff, ← reference.zero_iff, preserved, original.zero_iff]
  one := by
    have equal := transfer_eq reference other (includeValue 1) 1 (by
      rw [preserved, original.one, reference.one])
    exact equal.trans other.one
  add := by
    intro a b
    have equal := transfer_eq reference other (includeValue (a + b))
      (includeValue a + includeValue b) (by rw [reference.add, preserved, preserved,
        preserved, original.add])
    exact equal.trans (other.add _ _)
  sub := by
    intro a b
    have equal := transfer_eq reference other (includeValue (a - b))
      (includeValue a - includeValue b) (by rw [reference.sub, preserved, preserved,
        preserved, original.sub])
    exact equal.trans (other.sub _ _)
  mul := by
    intro a b
    have equal := transfer_eq reference other (includeValue (a * b))
      (includeValue a * includeValue b) (by rw [reference.mul, preserved, preserved,
        preserved, original.mul])
    exact equal.trans (other.mul _ _)
  nat := by
    intro n
    have equal := transfer_eq reference other (includeValue n) n (by
      rw [preserved, original.nat, reference.nat])
    exact equal.trans (other.nat n)
  neg := by
    intro a
    have equal := transfer_eq reference other (includeValue (-a)) (-includeValue a) (by
      rw [reference.neg, preserved, preserved, original.neg])
    exact equal.trans (other.neg _)
  inv := by
    intro a
    have equal := transfer_eq reference other (includeValue a⁻¹) (includeValue a)⁻¹ (by
      rw [reference.inv, preserved, preserved, original.inv])
    exact equal.trans (other.inv _)
  div := by
    intro a b
    have equal := transfer_eq reference other (includeValue (a / b))
      (includeValue a / includeValue b) (by rw [reference.div, preserved, preserved,
        preserved, original.div])
    exact equal.trans (other.div _ _)
  sign := by
    intro a
    rw [← other.sign, reference.sign, preserved, original.sign]

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
/-- Restrict an arbitrary model of a finite root suffix to its initial
predecessor. The independent reference supplies existence for the native
inclusion laws; the resulting values come entirely from the old model. -/
@[expose] noncomputable def restrict {source : Context registry}
    (reference : Model source L) (suffix : Suffix source)
    (old : Model suffix.context K) : Model source K :=
  reference.comap (reference.extend suffix) old suffix.embed (reference.extend_embed suffix)

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
/-- Restriction reads the old model through the actual native suffix inclusion. -/
@[simp] theorem restrict_value {source : Context registry}
    (reference : Model source L) (suffix : Suffix source)
    (old : Model suffix.context K) (a : source.Value) :
    (reference.restrict suffix old).value a = old.value (suffix.embed a) := rfl

/-- Agreement on the initial predecessor determines every arbitrary model
of a validated finite root suffix, at all depths. -/
theorem extend_unique {source : Context registry} (original : Model source K)
    (suffix : Suffix source) (other : Model suffix.context K)
    (compatible : ∀ a, other.value (suffix.embed a) = original.value a) :
    other = original.extend suffix := by
  induction suffix with
  | nil => exact value_ext _ _ compatible
  | @root parent descriptor rest ih =>
    let middle := (original.adjoin descriptor).comap
      ((original.adjoin descriptor).extend rest) other rest.embed
      ((original.adjoin descriptor).extend_embed rest)
    have parent_compatible : ∀ a,
        middle.value ((parent.adjoin descriptor).embed a) = original.value a := compatible
    have same : middle = original.adjoin descriptor :=
      original.adjoin_unique descriptor middle parent_compatible
    have finished : other = middle.extend rest := ih middle other (fun _ => rfl)
    rw [same] at finished
    exact finished

/-- Adjoining a validated root commutes with an ordered ambient embedding.
The equality describes every actual stored child value, including general
nonmonic representatives; no syntax injectivity is assumed. -/
theorem map_adjoin (model : Model context K) (embedding : K →+* L)
    (ordered : StrictMono embedding)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)
    (a : (context.adjoin descriptor).context.Value) :
    ((model.map embedding ordered).adjoin descriptor).value a =
      embedding ((model.adjoin descriptor).value a) := by
  have same := (model.map embedding ordered).adjoin_unique descriptor
    ((model.adjoin descriptor).map embedding ordered) (fun a => by
      change embedding ((model.adjoin descriptor).value ((context.adjoin descriptor).embed a)) = _
      rw [model.adjoin_embed]; rfl)
  exact congrArg (fun interpreted : Model (context.adjoin descriptor).context L =>
    interpreted.value a) same.symm

/-- Rebuilding the interpretation of a finite validated root suffix commutes
with the same ordered ambient embedding at every depth. -/
theorem map_extend {source : Context registry} (model : Model source K)
    (embedding : K →+* L) (ordered : StrictMono embedding) (suffix : Suffix source)
    (a : suffix.context.Value) :
    ((model.map embedding ordered).extend suffix).value a =
      embedding ((model.extend suffix).value a) := by
  have same := (model.map embedding ordered).extend_unique suffix
    ((model.extend suffix).map embedding ordered) (fun a => by
      change embedding ((model.extend suffix).value (suffix.embed a)) = _
      rw [model.extend_embed]; rfl)
  exact congrArg (fun interpreted : Model suffix.context L => interpreted.value a) same.symm

omit [IsStrictOrderedRing K] [IsRealClosed K] in
/-- The interpretation of a native base supplies its actual coefficient
field homomorphism, without an additional agreement hypothesis. -/
@[expose] noncomputable def baseHom {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (model : Model (Context.base base) K) :
    letI : Field B := HexPolyMathlib.fieldOfGrind
    B →+* K := by
  letI : Field B := HexPolyMathlib.fieldOfGrind
  exact
    { toFun := fun a => model.value (⟨a⟩ : BaseContext.Element base)
      map_zero' := (model.zero_iff 0).mpr rfl
      map_one' := model.one
      map_add' := fun a b => model.add ⟨a⟩ ⟨b⟩
      map_mul' := fun a b => model.mul ⟨a⟩ ⟨b⟩ }

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
/-- The extracted coefficient homomorphism interprets each native base value. -/
theorem baseHom_value {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (model : Model (Context.base base) K) (a : (Context.base base).Value) :
    model.baseHom base a.stored = model.value a := rfl

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
/-- The extracted base homomorphism agrees with its actual executable sign. -/
theorem baseHom_sign {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (model : Model (Context.base base) K) (a : B) :
    sign a = (SignType.sign (model.baseHom base a) : Int) :=
  model.sign (⟨a⟩ : BaseContext.Element base)

end Hex.RealClosure.Tower.Model

/-- info: 'Hex.RealClosure.Tower.Model.map_adjoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.map_adjoin

/-- info: 'Hex.RealClosure.Tower.Model.map_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.map_extend

/-- info: 'Hex.RealClosure.Tower.Model.adjoin_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.adjoin_unique

/-- info: 'Hex.RealClosure.Tower.Model.extend_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.extend_unique
