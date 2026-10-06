/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.Basic
public import HexOrderedFnTheory.Infinitesimal
public import HexPolyTheory.GrindTransport
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

public section

namespace Hex.RealClosure

attribute [local instance 2000] Field.toGrindField

universe u v

/-- An ordered algebraic real closure of a semantic coefficient field.
This companion object is not an executable carrier or a native constructor premise. -/
structure Ambient (K : Type u) [Field K] [LinearOrder K] where
  Carrier : Type u
  field : Field Carrier
  order : LinearOrder Carrier
  ordered : letI := field; letI := order; IsStrictOrderedRing Carrier
  closed : letI := field; IsRealClosed Carrier
  inclusion : letI := field; K →+* Carrier
  monotone : letI := field; letI := order; StrictMono inclusion
  algebraic : letI := field; ∀ x : Carrier, ∃ p : Polynomial K,
    p ≠ 0 ∧ p.eval₂ inclusion x = 0

namespace Ambient

variable {K : Type u} [Field K] [LinearOrder K]

instance (ambient : Ambient K) : Field ambient.Carrier := ambient.field
instance (ambient : Ambient K) : LinearOrder ambient.Carrier := ambient.order
instance (ambient : Ambient K) : IsStrictOrderedRing ambient.Carrier := ambient.ordered
instance (ambient : Ambient K) : IsRealClosed ambient.Carrier := ambient.closed

variable [IsStrictOrderedRing K]

/-- Tau Ceti supplies the ordered real closure, including algebraicity over
the actual inclusion rather than a separately chosen base embedding. -/
theorem exists_ambient : Nonempty (Ambient K) := by
  obtain ⟨R, field, order, ordered, closed, inclusion, monotone, algebraic⟩ :=
    TauCeti.RealClosure.exists_realClosure K
  letI : Field R := field
  letI : LinearOrder R := order
  let : Algebra K R := inclusion.toAlgebra
  let : Algebra.IsAlgebraic K R := algebraic
  refine ⟨⟨R, field, order, ordered, closed, inclusion, monotone, ?_⟩⟩
  intro x
  obtain ⟨p, hp, root⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) x
  exact ⟨p, hp, root⟩

/-- Choose an ambient model from the proved ordered-field existence theorem.
No supplied real-closed field or Archimedean premise is required. -/
noncomputable def ofField (K : Type u) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] : Ambient K := Classical.choice exists_ambient

variable (ambient : Ambient K)

omit [IsStrictOrderedRing K] in
theorem inclusion_lt (a b : K) : ambient.inclusion a < ambient.inclusion b ↔ a < b :=
  ambient.monotone.lt_iff_lt

omit [IsStrictOrderedRing K] in
theorem inclusion_zero (a : K) : ambient.inclusion a = 0 ↔ a = 0 :=
  ambient.inclusion.map_eq_zero_iff

omit [IsStrictOrderedRing K] in
/-- The ambient inclusion preserves the prescribed coefficient signs. -/
theorem inclusion_sign (a : K) :
    SignType.sign (ambient.inclusion a) = SignType.sign a := by
  rcases lt_trichotomy a 0 with negative | rfl | positive
  · have h := ambient.monotone negative
    rw [map_zero] at h
    simp [negative, h]
  · simp
  · have h := ambient.monotone positive
    rw [map_zero] at h
    simp [positive, h]

omit [IsStrictOrderedRing K] in
/-- A positive coefficient below one has a positive square root strictly
between it and one in the actual ambient algebraic real closure. -/
theorem exists_sqrt (a : K) (ha : 0 < a) (hsmall : a < 1) :
    ∃ s : ambient.Carrier, 0 < s ∧ s ^ 2 = ambient.inclusion a ∧
      ambient.inclusion a < s ∧ s < 1 := by
  have positive : 0 < ambient.inclusion a := by
    simpa only [map_zero] using ambient.monotone ha
  have small : ambient.inclusion a < 1 := by
    simpa only [map_one] using ambient.monotone hsmall
  obtain ⟨r, square⟩ := IsRealClosed.exists_eq_pow_of_nonneg positive.le (n := 2) (by decide)
  have hsquare : |r| ^ 2 = ambient.inclusion a := by rw [sq_abs]; exact square.symm
  have hnonneg : 0 ≤ |r| := abs_nonneg r
  have hpos : 0 < |r| := by nlinarith
  have hlt : |r| < 1 := by nlinarith
  have hbetween : ambient.inclusion a < |r| := by nlinarith
  exact ⟨|r|, hpos, hsquare, hbetween, hlt⟩

section Infinitesimal

open scoped Hex.OrderedFn.Infinitesimal

variable {L : Type u} [Field L] [LinearOrder L] [IsStrictOrderedRing L] [DecidableEq L]

/-- An unconditional algebraic real closure of the ordered infinitesimal field. -/
noncomputable def infinitesimal (L : Type u) [Field L] [LinearOrder L]
    [IsStrictOrderedRing L] [DecidableEq L] : Ambient (Hex.RationalFn L) :=
  ofField (Hex.RationalFn L)

/-- Include the old ordered field as constants in the algebraic real closure
of its infinitesimal rational-function extension. -/
@[expose] noncomputable def coefficientHom
    (model : Ambient (Hex.RationalFn L)) : L →+* model.Carrier :=
  model.inclusion.comp (HexRationalFnTheory.constantHom (K := L))

/-- The old coefficient field keeps its strict order in the enlarged ambient. -/
theorem coefficientHom_strictMono (model : Ambient (Hex.RationalFn L)) :
    StrictMono (coefficientHom model) := by
  intro a b less
  exact model.monotone
    ((Hex.OrderedFn.Infinitesimal.C_lt a b).mpr less)

theorem coefficientHom_apply (model : Ambient (Hex.RationalFn L)) (a : L) :
    coefficientHom model a = model.inclusion (Hex.RationalFn.C a) := rfl

/-- Map an ordered coefficient field into the same semantic infinitesimal
extension used for the old ambient field. -/
@[expose] noncomputable def mappedHom {B : Type v} [Field B] [DecidableEq B]
    (f : B →+* L) (model : Ambient (Hex.RationalFn L)) :
    Hex.RationalFn B →+* model.Carrier :=
  model.inclusion.comp (HexRationalFnTheory.mapHom f)

/-- Mapping a base coefficient agrees with the ambient constant inclusion. -/
theorem mappedHom_C {B : Type v} [Field B] [DecidableEq B]
    (f : B →+* L) (model : Ambient (Hex.RationalFn L)) (a : B) :
    mappedHom f model (Hex.RationalFn.C a) = coefficientHom model (f a) := by
  change model.inclusion (HexRationalFnTheory.mapHom f (Hex.RationalFn.C a)) =
    model.inclusion (Hex.RationalFn.C (f a))
  rw [HexRationalFnTheory.mapHom_C]

/-- Both mapped fraction fields use the same infinitesimal indeterminate. -/
theorem mappedHom_X {B : Type v} [Field B] [DecidableEq B]
    (f : B →+* L) (model : Ambient (Hex.RationalFn L)) :
    mappedHom f model (Hex.RationalFn.X : Hex.RationalFn B) =
      model.inclusion (Hex.RationalFn.X : Hex.RationalFn L) := by
  change model.inclusion (HexRationalFnTheory.mapHom f Hex.RationalFn.X) = _
  rw [HexRationalFnTheory.mapHom_X]

/-- The mapped infinitesimal base keeps its strict order in the common ambient. -/
theorem mappedHom_strictMono {B : Type v} [Field B] [DecidableEq B]
    [LinearOrder B] [IsStrictOrderedRing B]
    (f : B →+* L) (ordered : StrictMono f)
    (model : Ambient (Hex.RationalFn L)) : StrictMono (mappedHom f model) :=
  model.monotone.comp (Hex.OrderedFn.Infinitesimal.mapHom_strictMono f ordered)

/-- The native sign of a mapped infinitesimal fraction is its semantic sign. -/
theorem mappedHom_sign {B : Type v} [Field B] [DecidableEq B]
    [LinearOrder B]
    (f : B →+* L) (ordered : StrictMono f)
    (model : Ambient (Hex.RationalFn L)) (q : Hex.RationalFn B) :
    Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign q =
      (SignType.sign (mappedHom f model q) : Int) := by
  change Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign q =
    (SignType.sign (model.inclusion (HexRationalFnTheory.mapHom f q)) : Int)
  rw [model.inclusion_sign]
  have mappedSign :
      Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign
        (HexRationalFnTheory.mapHom f q) =
        (SignType.sign (HexRationalFnTheory.mapHom f q) : Int) := by
    rw [Hex.OrderedFn.Infinitesimal.sign_orderSign]
    exact congrArg (fun s : SignType => (s : Int))
      (Hex.OrderedFn.Infinitesimal.embed_strictMono.sign_comp _)
  rw [← mappedSign]
  exact (Hex.OrderedFn.Infinitesimal.mapHom_sign f ordered q).symm

/-- A supplied native coefficient sign suffices for semantic fraction signs;
the coefficient field needs no Mathlib order instance. -/
theorem mappedHom_sign_of {B : Type v} [Field B] [DecidableEq B]
    (f : B →+* L) (baseSign : B → Int)
    (agrees : ∀ a, baseSign a = (SignType.sign (f a) : Int))
    (model : Ambient (Hex.RationalFn L)) (q : Hex.RationalFn B) :
    Hex.OrderedFn.Infinitesimal.sign baseSign q =
      (SignType.sign (mappedHom f model q) : Int) := by
  change Hex.OrderedFn.Infinitesimal.sign baseSign q =
    (SignType.sign (model.inclusion (HexRationalFnTheory.mapHom f q)) : Int)
  rw [model.inclusion_sign]
  have mappedSign :
      Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign
        (HexRationalFnTheory.mapHom f q) =
        (SignType.sign (HexRationalFnTheory.mapHom f q) : Int) := by
    rw [Hex.OrderedFn.Infinitesimal.sign_orderSign]
    exact congrArg (fun s : SignType => (s : Int))
      (Hex.OrderedFn.Infinitesimal.embed_strictMono.sign_comp _)
  rw [← mappedSign]
  exact Hex.OrderedFn.Infinitesimal.mapHom_sign_of f baseSign agrees q

set_option linter.overlappingInstances false in
/-- Interpret the executable rational-function carrier with its original
Grind field dictionary through the mapped ambient homomorphism. -/
@[expose] noncomputable def mappedNativeHom {B : Type v} [Field B]
    [g : Lean.Grind.Field B] [DecidableEq B]
    (compatible : Field.toGrindField (K := B) = g)
    (f : B →+* L)
    (model : Ambient (Hex.RationalFn L)) :
    letI : Field (@Hex.RationalFn B g inferInstance) := HexPolyTheory.fieldOfGrind
    @Hex.RationalFn B g inferInstance →+* model.Carrier := by
  letI : Field (@Hex.RationalFn B g inferInstance) := HexPolyTheory.fieldOfGrind
  subst g
  exact mappedHom f model

set_option linter.overlappingInstances false in
/-- The executable constant embedding agrees with the mapped ambient base. -/
theorem mappedNativeHom_C {B : Type v} [Field B] [g : Lean.Grind.Field B]
    [DecidableEq B] (compatible : Field.toGrindField (K := B) = g)
    (f : B →+* L) (model : Ambient (Hex.RationalFn L)) (a : B) :
    mappedNativeHom compatible f model (@Hex.RationalFn.C B g inferInstance a) =
      coefficientHom model (f a) := by
  subst g
  exact mappedHom_C f model a

set_option linter.overlappingInstances false in
/-- The executable indeterminate is the same semantic infinitesimal. -/
theorem mappedNativeHom_X {B : Type v} [Field B] [g : Lean.Grind.Field B]
    [DecidableEq B] (compatible : Field.toGrindField (K := B) = g)
    (f : B →+* L) (model : Ambient (Hex.RationalFn L)) :
    mappedNativeHom compatible f model (@Hex.RationalFn.X B g inferInstance) =
      model.inclusion (Hex.RationalFn.X : Hex.RationalFn L) := by
  subst g
  exact mappedHom_X f model

set_option linter.overlappingInstances false in
/-- The executable fraction sign agrees with the mapped semantic value. -/
theorem mappedNativeHom_sign {B : Type v} [Field B]
    [g : Lean.Grind.Field B] [DecidableEq B]
    (compatible : Field.toGrindField (K := B) = g)
    (f : B →+* L) (baseSign : B → Int)
    (agrees : ∀ a, baseSign a = (SignType.sign (f a) : Int))
    (model : Ambient (Hex.RationalFn L)) (q : @Hex.RationalFn B g inferInstance) :
    Hex.OrderedFn.Infinitesimal.sign baseSign q =
      (SignType.sign (mappedNativeHom compatible f model q) : Int) := by
  subst g
  exact mappedHom_sign_of f baseSign agrees model q

/-- The actual indeterminate remains positive in any ordered algebraic
real closure of the infinitesimal field. -/
theorem X_pos (model : Ambient (Hex.RationalFn L)) :
    0 < model.inclusion (Hex.RationalFn.X : Hex.RationalFn L) := by
  simpa only [map_zero] using model.monotone Hex.OrderedFn.Infinitesimal.X_pos

/-- The semantic infinitesimal is below every positive old coefficient. -/
theorem X_lt_coefficient (model : Ambient (Hex.RationalFn L))
    (a : L) (positive : 0 < a) :
    model.inclusion (Hex.RationalFn.X : Hex.RationalFn L) < coefficientHom model a := by
  rw [coefficientHom_apply]
  exact model.monotone (Hex.OrderedFn.Infinitesimal.X_lt_C a positive)

-- The explicit compatibility premise identifies the two field dictionaries.
set_option linter.overlappingInstances false in
/-- Interpret native fractions through their proved field-dictionary equality.
The source field retains the executable arithmetic through `fieldOfGrind`. -/
noncomputable def nativeHom [g : Lean.Grind.Field L]
    (compatible : Field.toGrindField (K := L) = g)
    (model : Ambient (@Hex.RationalFn L (Field.toGrindField (K := L)) inferInstance)) :
    letI : Field (@Hex.RationalFn L g inferInstance) := HexPolyTheory.fieldOfGrind
    @Hex.RationalFn L g inferInstance →+* model.Carrier := by
  letI : Field (@Hex.RationalFn L g inferInstance) := HexPolyTheory.fieldOfGrind
  exact
    { toFun := fun f => model.inclusion
        (cast (congrArg (fun G => @Hex.RationalFn L G inferInstance) compatible.symm) f)
      map_zero' := by subst g; exact model.inclusion.map_zero
      map_one' := by subst g; exact model.inclusion.map_one
      map_add' := by intro f h; subst g; exact model.inclusion.map_add f h
      map_mul' := by intro f h; subst g; exact model.inclusion.map_mul f h }

set_option linter.overlappingInstances false in
/-- Native fraction interpretation is the original ambient inclusion after
transporting across the proved field-dictionary equality. -/
theorem nativeHom_apply [g : Lean.Grind.Field L]
    (compatible : Field.toGrindField (K := L) = g)
    (model : Ambient (@Hex.RationalFn L (Field.toGrindField (K := L)) inferInstance))
    (q : @Hex.RationalFn L g inferInstance) :
    nativeHom compatible model q =
      model.inclusion
        (cast (congrArg (fun G => @Hex.RationalFn L G inferInstance) compatible.symm) q) :=
  by subst g; rfl

-- The explicit compatibility premise identifies the two field dictionaries.
set_option linter.overlappingInstances false in
/-- The native indeterminate maps to the same infinitesimal in the ambient model. -/
theorem nativeHom_X [g : Lean.Grind.Field L]
    (compatible : Field.toGrindField (K := L) = g)
    (model : Ambient (@Hex.RationalFn L (Field.toGrindField (K := L)) inferInstance)) :
    nativeHom compatible model (@Hex.RationalFn.X L g inferInstance) =
      model.inclusion (@Hex.RationalFn.X L (Field.toGrindField (K := L)) inferInstance) := by
  subst g
  rfl

-- The explicit compatibility premise identifies the two field dictionaries.
set_option linter.overlappingInstances false in
/-- Native coefficients use the same inclusion as the semantic fraction field. -/
theorem nativeHom_C [g : Lean.Grind.Field L]
    (compatible : Field.toGrindField (K := L) = g)
    (model : Ambient (@Hex.RationalFn L (Field.toGrindField (K := L)) inferInstance))
    (a : L) :
    nativeHom compatible model (@Hex.RationalFn.C L g inferInstance a) =
      model.inclusion (@Hex.RationalFn.C L (Field.toGrindField (K := L)) inferInstance a) := by
  subst g
  rfl

-- The explicit compatibility premise identifies the two field dictionaries.
set_option linter.overlappingInstances false in
/-- Native coefficient signs agree with the actual ordered ambient interpretation. -/
theorem nativeHom_sign [g : Lean.Grind.Field L]
    (compatible : Field.toGrindField (K := L) = g)
    (model : Ambient (@Hex.RationalFn L (Field.toGrindField (K := L)) inferInstance))
    (f : @Hex.RationalFn L g inferInstance) :
    Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign f =
      (SignType.sign (nativeHom compatible model f) : Int) := by
  subst g
  change Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign f =
    (SignType.sign (model.inclusion f) : Int)
  rw [model.inclusion_sign]
  rw [Hex.OrderedFn.Infinitesimal.sign_orderSign]
  exact congrArg (fun s : SignType => (s : Int))
    (Hex.OrderedFn.Infinitesimal.embed_strictMono.sign_comp f)

set_option linter.overlappingInstances false in
/-- The native fraction interpretation preserves and reflects canonical zero. -/
theorem nativeHom_zero [g : Lean.Grind.Field L]
    (compatible : Field.toGrindField (K := L) = g)
    (model : Ambient (@Hex.RationalFn L (Field.toGrindField (K := L)) inferInstance))
    (f : @Hex.RationalFn L g inferInstance) : nativeHom compatible model f = 0 ↔ f = 0 := by
  letI : Field (@Hex.RationalFn L g inferInstance) := HexPolyTheory.fieldOfGrind
  exact (nativeHom compatible model).map_eq_zero_iff

set_option linter.overlappingInstances false in
/-- The native total inverse is interpreted without replacing its operations. -/
theorem nativeHom_inv [g : Lean.Grind.Field L]
    (compatible : Field.toGrindField (K := L) = g)
    (model : Ambient (@Hex.RationalFn L (Field.toGrindField (K := L)) inferInstance))
    (f : @Hex.RationalFn L g inferInstance) :
    nativeHom compatible model f⁻¹ = (nativeHom compatible model f)⁻¹ := by
  letI : Field (@Hex.RationalFn L g inferInstance) := HexPolyTheory.fieldOfGrind
  exact map_inv₀ (nativeHom compatible model) f

set_option linter.overlappingInstances false in
/-- Native division uses the same interpreted field operations. -/
theorem nativeHom_div [g : Lean.Grind.Field L]
    (compatible : Field.toGrindField (K := L) = g)
    (model : Ambient (@Hex.RationalFn L (Field.toGrindField (K := L)) inferInstance))
    (f h : @Hex.RationalFn L g inferInstance) :
    nativeHom compatible model (f / h) =
      nativeHom compatible model f / nativeHom compatible model h := by
  letI : Field (@Hex.RationalFn L g inferInstance) := HexPolyTheory.fieldOfGrind
  exact map_div₀ (nativeHom compatible model) f h

/-- The positive square root of the represented infinitesimal lies above it. -/
theorem exists_sqrt_X (model : Ambient (Hex.RationalFn L)) :
    ∃ s : model.Carrier, 0 < s ∧ s ^ 2 = model.inclusion Hex.RationalFn.X ∧
      model.inclusion Hex.RationalFn.X < s ∧ s < 1 := by
  apply model.exists_sqrt Hex.RationalFn.X Hex.OrderedFn.Infinitesimal.X_pos
  simpa only [Hex.RationalFn.C_one] using
    Hex.OrderedFn.Infinitesimal.X_lt_C (1 : L) zero_lt_one

/-- The reciprocal of the represented infinitesimal exceeds each integer in
its actual ordered algebraic ambient extension. -/
theorem inv_X_gt_int (model : Ambient (Hex.RationalFn L)) (n : ℤ) :
    (n : model.Carrier) < (model.inclusion Hex.RationalFn.X)⁻¹ := by
  simpa only [map_intCast, map_inv₀] using
    model.monotone (Hex.OrderedFn.Infinitesimal.intCast_lt_inv_X (K := L) n)

/-- Every positive predecessor coefficient remains above a positive square
root of the new infinitesimal in the ambient extension. -/
theorem sqrt_X_lt_C (model : Ambient (Hex.RationalFn L)) (s : model.Carrier)
    (hs : 0 < s) (square : s ^ 2 = model.inclusion Hex.RationalFn.X)
    (a : L) (ha : 0 < a) : s < model.inclusion (Hex.RationalFn.C a) := by
  have ca : (0 : Hex.RationalFn L) < Hex.RationalFn.C a := by
    simpa only [Hex.RationalFn.C_zero] using
      (Hex.OrderedFn.Infinitesimal.C_lt (0 : L) a).mpr ha
  have positive : 0 < model.inclusion (Hex.RationalFn.C a) := by
    simpa only [map_zero] using model.monotone ca
  have bound := model.monotone
    (Hex.OrderedFn.Infinitesimal.X_lt_C (a * a) (mul_pos ha ha))
  rw [Hex.RationalFn.C_mul, map_mul, ← pow_two] at bound
  nlinarith

/-- Construct the square-root witness without a supplied real-closed model. -/
example : ∃ s : (infinitesimal ℚ).Carrier,
    0 < s ∧ s ^ 2 = (infinitesimal ℚ).inclusion Hex.RationalFn.X ∧
      (infinitesimal ℚ).inclusion Hex.RationalFn.X < s ∧ s < 1 :=
  exists_sqrt_X (infinitesimal ℚ)

/-- One chosen two-level ambient model realizes a square root of the second
infinitesimal below every power of the embedded first infinitesimal. -/
example :
    ∃ s : (infinitesimal (Hex.RationalFn ℚ)).Carrier,
      0 < s ∧ s ^ 2 = (infinitesimal (Hex.RationalFn ℚ)).inclusion Hex.RationalFn.X ∧
      (infinitesimal (Hex.RationalFn ℚ)).inclusion Hex.RationalFn.X < s ∧
      ∀ n : ℕ, s < (infinitesimal (Hex.RationalFn ℚ)).inclusion
        (Hex.RationalFn.C ((Hex.RationalFn.X : Hex.RationalFn ℚ) ^ n)) := by
  let model := infinitesimal (Hex.RationalFn ℚ)
  obtain ⟨s, positive, square, above, _⟩ := exists_sqrt_X model
  refine ⟨s, positive, square, above, fun n => ?_⟩
  exact sqrt_X_lt_C model s positive square _ (pow_pos Hex.OrderedFn.Infinitesimal.X_pos n)

end Infinitesimal

end Ambient
end Hex.RealClosure

/-- info: 'Hex.RealClosure.Ambient.exists_ambient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.exists_ambient

/-- info: 'Hex.RealClosure.Ambient.ofField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.ofField

/-- info: 'Hex.RealClosure.Ambient.exists_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.exists_sqrt

/-- info: 'Hex.RealClosure.Ambient.infinitesimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.infinitesimal

/-- info: 'Hex.RealClosure.Ambient.coefficientHom_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.coefficientHom_strictMono

/-- info: 'Hex.RealClosure.Ambient.mappedNativeHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.mappedNativeHom

/-- info: 'Hex.RealClosure.Ambient.mappedNativeHom_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.mappedNativeHom_sign

/-- info: 'Hex.RealClosure.Ambient.mappedHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.mappedHom

/-- info: 'Hex.RealClosure.Ambient.mappedHom_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.mappedHom_strictMono

/-- info: 'Hex.RealClosure.Ambient.mappedHom_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.mappedHom_sign

/-- info: 'Hex.RealClosure.Ambient.X_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.X_pos

/-- info: 'Hex.RealClosure.Ambient.X_lt_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.X_lt_coefficient

/-- info: 'Hex.RealClosure.Ambient.exists_sqrt_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.exists_sqrt_X

/-- info: 'Hex.RealClosure.Ambient.inv_X_gt_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.inv_X_gt_int

/-- info: 'Hex.RealClosure.Ambient.sqrt_X_lt_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.sqrt_X_lt_C

/-- info: 'Hex.RealClosure.Ambient.nativeHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.nativeHom

/-- info: 'Hex.RealClosure.Ambient.nativeHom_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.nativeHom_sign

/-- info: 'Hex.RealClosure.Ambient.nativeHom_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Ambient.nativeHom_zero
