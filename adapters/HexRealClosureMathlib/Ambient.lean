/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.Basic
public import HexOrderedFnMathlib.Infinitesimal
public import HexPolyMathlib.GrindTransport
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

public section

-- The two field dictionaries are explicitly related by `compatible`.
set_option linter.overlappingInstances false

namespace Hex.RealClosure

attribute [local instance 2000] Field.toGrindField

universe u

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
  letI : Algebra K R := inclusion.toAlgebra
  letI : Algebra.IsAlgebraic K R := algebraic
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
    simp [sign_apply, negative, h, negative.not_gt, h.not_gt]
  · simp
  · have h := ambient.monotone positive
    rw [map_zero] at h
    simp [sign_apply, positive, h]

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

/-- Interpret native fractions through their proved field-dictionary equality.
The source field retains the executable arithmetic through `fieldOfGrind`. -/
noncomputable def nativeHom [g : Lean.Grind.Field L]
    (compatible : Field.toGrindField (K := L) = g)
    (model : Ambient (@Hex.RationalFn L (Field.toGrindField (K := L)) inferInstance)) :
    letI : Field (@Hex.RationalFn L g inferInstance) := HexPolyMathlib.fieldOfGrind
    @Hex.RationalFn L g inferInstance →+* model.Carrier := by
  letI : Field (@Hex.RationalFn L g inferInstance) := HexPolyMathlib.fieldOfGrind
  exact
    { toFun := fun f => model.inclusion
        (cast (congrArg (fun G => @Hex.RationalFn L G inferInstance) compatible.symm) f)
      map_zero' := by subst g; exact model.inclusion.map_zero
      map_one' := by subst g; exact model.inclusion.map_one
      map_add' := by intro f h; subst g; exact model.inclusion.map_add f h
      map_mul' := by intro f h; subst g; exact model.inclusion.map_mul f h }

/-- The native indeterminate maps to the same infinitesimal in the ambient model. -/
theorem nativeHom_X [g : Lean.Grind.Field L]
    (compatible : Field.toGrindField (K := L) = g)
    (model : Ambient (@Hex.RationalFn L (Field.toGrindField (K := L)) inferInstance)) :
    nativeHom compatible model (@Hex.RationalFn.X L g inferInstance) =
      model.inclusion (@Hex.RationalFn.X L (Field.toGrindField (K := L)) inferInstance) := by
  subst g
  rfl

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
example (n : ℕ) :
    ∃ s : (infinitesimal (Hex.RationalFn ℚ)).Carrier,
      0 < s ∧ s ^ 2 = (infinitesimal (Hex.RationalFn ℚ)).inclusion Hex.RationalFn.X ∧
      (infinitesimal (Hex.RationalFn ℚ)).inclusion Hex.RationalFn.X < s ∧
      s < (infinitesimal (Hex.RationalFn ℚ)).inclusion
        (Hex.RationalFn.C ((Hex.RationalFn.X : Hex.RationalFn ℚ) ^ n)) := by
  let model := infinitesimal (Hex.RationalFn ℚ)
  obtain ⟨s, positive, square, above, _⟩ := exists_sqrt_X model
  exact ⟨s, positive, square, above, sqrt_X_lt_C model s positive square _
    (pow_pos Hex.OrderedFn.Infinitesimal.X_pos n)⟩

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
